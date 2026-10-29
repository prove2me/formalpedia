-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1568_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:26:34.90526+00:00
-- url     : https://prove2.me/submissions/00df9eab-4d5b-4e0a-ac42-f202874540f3

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
theorem support_rectangle_w1568_s0_0 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-814008333/5000000000 : ℝ)*x 0 + (46967951/80000000 : ℝ)*x 1 + (243927431/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (814008333/5000000000 : ℝ)^4633 ≤ (2431749267999/25000000000000 : ℝ)^3609 := by
    have hnat : (814008333 : ℕ)^4633*25000000000000^3609 ≤ 2431749267999^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814008333 5000000000 2431749267999 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46967951/80000000 : ℝ)^4633 ≤ (12619059987211/25000000000000 : ℝ)^3609 := by
    have hnat : (46967951 : ℕ)^4633*25000000000000^3609 ≤ 12619059987211^3609*80000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46967951 80000000 12619059987211 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243927431/500000000 : ℝ)^4633 ≤ (39796762964221/100000000000000 : ℝ)^3609 := by
    have hnat : (243927431 : ℕ)^4633*100000000000000^3609 ≤ 39796762964221^3609*500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243927431 500000000 39796762964221 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-814008333/5000000000 : ℝ), (46967951/80000000 : ℝ), (243927431/500000000 : ℝ)] ![(2431749267999/25000000000000 : ℝ), (12619059987211/25000000000000 : ℝ), (39796762964221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-814008333/5000000000 : ℝ)|^4633 ≤ (2431749267999/25000000000000 : ℝ)^3609
        have hw : |(-814008333/5000000000 : ℝ)|=(814008333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46967951/80000000 : ℝ)|^4633 ≤ (12619059987211/25000000000000 : ℝ)^3609
        have hw : |(46967951/80000000 : ℝ)|=(46967951/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(243927431/500000000 : ℝ)|^4633 ≤ (39796762964221/100000000000000 : ℝ)^3609
        have hw : |(243927431/500000000 : ℝ)|=(243927431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s0_1 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2732952621/5000000000 : ℝ)*x 0 + (-2180426007/10000000000 : ℝ)*x 1 + (4878548623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2732952621/5000000000 : ℝ)^4633 ≤ (11512446754633/25000000000000 : ℝ)^3609 := by
    have hnat : (2732952621 : ℕ)^4633*25000000000000^3609 ≤ 11512446754633^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732952621 5000000000 11512446754633 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2180426007/10000000000 : ℝ)^4633 ≤ (707672497999/5000000000000 : ℝ)^3609 := by
    have hnat : (2180426007 : ℕ)^4633*5000000000000^3609 ≤ 707672497999^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180426007 10000000000 707672497999 5000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4878548623/10000000000 : ℝ)^4633 ≤ (39796762995637/100000000000000 : ℝ)^3609 := by
    have hnat : (4878548623 : ℕ)^4633*100000000000000^3609 ≤ 39796762995637^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4878548623 10000000000 39796762995637 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2732952621/5000000000 : ℝ), (-2180426007/10000000000 : ℝ), (4878548623/10000000000 : ℝ)] ![(11512446754633/25000000000000 : ℝ), (707672497999/5000000000000 : ℝ), (39796762995637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2732952621/5000000000 : ℝ)|^4633 ≤ (11512446754633/25000000000000 : ℝ)^3609
        have hw : |(2732952621/5000000000 : ℝ)|=(2732952621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2180426007/10000000000 : ℝ)|^4633 ≤ (707672497999/5000000000000 : ℝ)^3609
        have hw : |(-2180426007/10000000000 : ℝ)|=(2180426007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4878548623/10000000000 : ℝ)|^4633 ≤ (39796762995637/100000000000000 : ℝ)^3609
        have hw : |(4878548623/10000000000 : ℝ)|=(4878548623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s0_2 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341619081/625000000 : ℝ)*x 0 + (60981857/125000000 : ℝ)*x 1 + (-2180426017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341619081/625000000 : ℝ)^4633 ≤ (23024893801281/50000000000000 : ℝ)^3609 := by
    have hnat : (341619081 : ℕ)^4633*50000000000000^3609 ≤ 23024893801281^3609*625000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341619081 625000000 23024893801281 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (60981857/125000000 : ℝ)^4633 ≤ (39796762335897/100000000000000 : ℝ)^3609 := by
    have hnat : (60981857 : ℕ)^4633*100000000000000^3609 ≤ 39796762335897^3609*125000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60981857 125000000 39796762335897 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180426017/10000000000 : ℝ)^4633 ≤ (14153450043309/100000000000000 : ℝ)^3609 := by
    have hnat : (2180426017 : ℕ)^4633*100000000000000^3609 ≤ 14153450043309^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180426017 10000000000 14153450043309 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341619081/625000000 : ℝ), (60981857/125000000 : ℝ), (-2180426017/10000000000 : ℝ)] ![(23024893801281/50000000000000 : ℝ), (39796762335897/100000000000000 : ℝ), (14153450043309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341619081/625000000 : ℝ)|^4633 ≤ (23024893801281/50000000000000 : ℝ)^3609
        have hw : |(341619081/625000000 : ℝ)|=(341619081/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(60981857/125000000 : ℝ)|^4633 ≤ (39796762335897/100000000000000 : ℝ)^3609
        have hw : |(60981857/125000000 : ℝ)|=(60981857/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2180426017/10000000000 : ℝ)|^4633 ≤ (14153450043309/100000000000000 : ℝ)^3609
        have hw : |(-2180426017/10000000000 : ℝ)|=(2180426017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s0_3 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1032591787/2500000000 : ℝ)*x 0 + (386631279/1250000000 : ℝ)*x 1 + (271629361/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032591787/2500000000 : ℝ)^4633 ≤ (16069455560993/50000000000000 : ℝ)^3609 := by
    have hnat : (1032591787 : ℕ)^4633*50000000000000^3609 ≤ 16069455560993^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032591787 2500000000 16069455560993 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386631279/1250000000 : ℝ)^4633 ≤ (22171336151443/100000000000000 : ℝ)^3609 := by
    have hnat : (386631279 : ℕ)^4633*100000000000000^3609 ≤ 22171336151443^3609*1250000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386631279 1250000000 22171336151443 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271629361/500000000 : ℝ)^4633 ≤ (22844876357849/50000000000000 : ℝ)^3609 := by
    have hnat : (271629361 : ℕ)^4633*50000000000000^3609 ≤ 22844876357849^3609*500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271629361 500000000 22844876357849 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1032591787/2500000000 : ℝ), (386631279/1250000000 : ℝ), (271629361/500000000 : ℝ)] ![(16069455560993/50000000000000 : ℝ), (22171336151443/100000000000000 : ℝ), (22844876357849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1032591787/2500000000 : ℝ)|^4633 ≤ (16069455560993/50000000000000 : ℝ)^3609
        have hw : |(1032591787/2500000000 : ℝ)|=(1032591787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386631279/1250000000 : ℝ)|^4633 ≤ (22171336151443/100000000000000 : ℝ)^3609
        have hw : |(386631279/1250000000 : ℝ)|=(386631279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271629361/500000000 : ℝ)|^4633 ≤ (22844876357849/50000000000000 : ℝ)^3609
        have hw : |(271629361/500000000 : ℝ)|=(271629361/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s0_4 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-815542799/5000000000 : ℝ)*x 0 + (245178569/500000000 : ℝ)*x 1 + (5845085121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (815542799/5000000000 : ℝ)^4633 ≤ (9750542072197/100000000000000 : ℝ)^3609 := by
    have hnat : (815542799 : ℕ)^4633*100000000000000^3609 ≤ 9750542072197^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815542799 5000000000 9750542072197 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245178569/500000000 : ℝ)^4633 ≤ (20029496748329/50000000000000 : ℝ)^3609 := by
    have hnat : (245178569 : ℕ)^4633*50000000000000^3609 ≤ 20029496748329^3609*500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245178569 500000000 20029496748329 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5845085121/10000000000 : ℝ)^4633 ≤ (6273808051729/12500000000000 : ℝ)^3609 := by
    have hnat : (5845085121 : ℕ)^4633*12500000000000^3609 ≤ 6273808051729^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5845085121 10000000000 6273808051729 12500000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-815542799/5000000000 : ℝ), (245178569/500000000 : ℝ), (5845085121/10000000000 : ℝ)] ![(9750542072197/100000000000000 : ℝ), (20029496748329/50000000000000 : ℝ), (6273808051729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-815542799/5000000000 : ℝ)|^4633 ≤ (9750542072197/100000000000000 : ℝ)^3609
        have hw : |(-815542799/5000000000 : ℝ)|=(815542799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(245178569/500000000 : ℝ)|^4633 ≤ (20029496748329/50000000000000 : ℝ)^3609
        have hw : |(245178569/500000000 : ℝ)|=(245178569/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5845085121/10000000000 : ℝ)|^4633 ≤ (6273808051729/12500000000000 : ℝ)^3609
        have hw : |(5845085121/10000000000 : ℝ)|=(5845085121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s0_5 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194595911/10000000000 : ℝ)*x 0 + (-1213892143/10000000000 : ℝ)*x 1 + (1169017193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194595911/10000000000 : ℝ)^4633 ≤ (43136392305919/100000000000000 : ℝ)^3609 := by
    have hnat : (5194595911 : ℕ)^4633*100000000000000^3609 ≤ 43136392305919^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194595911 10000000000 43136392305919 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213892143/10000000000 : ℝ)^4633 ≤ (3336566982553/50000000000000 : ℝ)^3609 := by
    have hnat : (1213892143 : ℕ)^4633*50000000000000^3609 ≤ 3336566982553^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213892143 10000000000 3336566982553 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1169017193/2000000000 : ℝ)^4633 ≤ (12547618429343/25000000000000 : ℝ)^3609 := by
    have hnat : (1169017193 : ℕ)^4633*25000000000000^3609 ≤ 12547618429343^3609*2000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169017193 2000000000 12547618429343 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194595911/10000000000 : ℝ), (-1213892143/10000000000 : ℝ), (1169017193/2000000000 : ℝ)] ![(43136392305919/100000000000000 : ℝ), (3336566982553/50000000000000 : ℝ), (12547618429343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194595911/10000000000 : ℝ)|^4633 ≤ (43136392305919/100000000000000 : ℝ)^3609
        have hw : |(5194595911/10000000000 : ℝ)|=(5194595911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1213892143/10000000000 : ℝ)|^4633 ≤ (3336566982553/50000000000000 : ℝ)^3609
        have hw : |(-1213892143/10000000000 : ℝ)|=(1213892143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1169017193/2000000000 : ℝ)|^4633 ≤ (12547618429343/25000000000000 : ℝ)^3609
        have hw : |(1169017193/2000000000 : ℝ)|=(1169017193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s0_6 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129864981/250000000 : ℝ)*x 0 + (292254199/500000000 : ℝ)*x 1 + (-242778043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129864981/250000000 : ℝ)^4633 ≤ (43136427793901/100000000000000 : ℝ)^3609 := by
    have hnat : (129864981 : ℕ)^4633*100000000000000^3609 ≤ 43136427793901^3609*250000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129864981 250000000 43136427793901 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292254199/500000000 : ℝ)^4633 ≤ (98028226243/195312500000 : ℝ)^3609 := by
    have hnat : (292254199 : ℕ)^4633*195312500000^3609 ≤ 98028226243^3609*500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292254199 500000000 98028226243 195312500000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242778043/2000000000 : ℝ)^4633 ≤ (1334624071811/20000000000000 : ℝ)^3609 := by
    have hnat : (242778043 : ℕ)^4633*20000000000000^3609 ≤ 1334624071811^3609*2000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242778043 2000000000 1334624071811 20000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129864981/250000000 : ℝ), (292254199/500000000 : ℝ), (-242778043/2000000000 : ℝ)] ![(43136427793901/100000000000000 : ℝ), (98028226243/195312500000 : ℝ), (1334624071811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129864981/250000000 : ℝ)|^4633 ≤ (43136427793901/100000000000000 : ℝ)^3609
        have hw : |(129864981/250000000 : ℝ)|=(129864981/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(292254199/500000000 : ℝ)|^4633 ≤ (98028226243/195312500000 : ℝ)^3609
        have hw : |(292254199/500000000 : ℝ)|=(292254199/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-242778043/2000000000 : ℝ)|^4633 ≤ (1334624071811/20000000000000 : ℝ)^3609
        have hw : |(-242778043/2000000000 : ℝ)|=(242778043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s0_7 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4137602611/10000000000 : ℝ)*x 0 + (214944079/400000000 : ℝ)*x 1 + (788530993/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4137602611/10000000000 : ℝ)^4633 ≤ (8052800858661/25000000000000 : ℝ)^3609 := by
    have hnat : (4137602611 : ℕ)^4633*25000000000000^3609 ≤ 8052800858661^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137602611 10000000000 8052800858661 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (214944079/400000000 : ℝ)^4633 ≤ (5631736923793/12500000000000 : ℝ)^3609 := by
    have hnat : (214944079 : ℕ)^4633*12500000000000^3609 ≤ 5631736923793^3609*400000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214944079 400000000 5631736923793 12500000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788530993/2500000000 : ℝ)^4633 ≤ (22734901158859/100000000000000 : ℝ)^3609 := by
    have hnat : (788530993 : ℕ)^4633*100000000000000^3609 ≤ 22734901158859^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788530993 2500000000 22734901158859 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4137602611/10000000000 : ℝ), (214944079/400000000 : ℝ), (788530993/2500000000 : ℝ)] ![(8052800858661/25000000000000 : ℝ), (5631736923793/12500000000000 : ℝ), (22734901158859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4137602611/10000000000 : ℝ)|^4633 ≤ (8052800858661/25000000000000 : ℝ)^3609
        have hw : |(4137602611/10000000000 : ℝ)|=(4137602611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(214944079/400000000 : ℝ)|^4633 ≤ (5631736923793/12500000000000 : ℝ)^3609
        have hw : |(214944079/400000000 : ℝ)|=(214944079/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788530993/2500000000 : ℝ)|^4633 ≤ (22734901158859/100000000000000 : ℝ)^3609
        have hw : |(788530993/2500000000 : ℝ)|=(788530993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1568_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3521/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24779/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4631/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4631 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4631*1^1024 ≤ 0^1024*1^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4631/1024 : ℝ) ≤ (793052355969921313/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4631 ≤ (793052355969921313/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4631*50000000000000000000^1024 ≤ 793052355969921313^1024*5^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 793052355969921313 50000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (793052355969921313/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4631 := by
      have hnat : (1 : ℕ)^1024*1^4631 ≤ 1^4631*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50793052355969921313/50000000000000000000 : ℝ) ≤ (5017428548344629/5000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (50793052355969921313/50000000000000000000 : ℝ)^1024 ≤ (5017428548344629/5000000000000000 : ℝ)^4631 := by
      have hnat : (50793052355969921313 : ℕ)^1024*5000000000000000^4631 ≤ 5017428548344629^4631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50793052355969921313 50000000000000000000 5017428548344629 5000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017428548344629/5000000000000000 : ℝ)) (X := (50793052355969921313/50000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25793052355969921313/25000000000000000000 : ℝ) ≤ (2517428548344629/2500000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (25793052355969921313/25000000000000000000 : ℝ)^1024 ≤ (2517428548344629/2500000000000000 : ℝ)^4631 := by
      have hnat : (25793052355969921313 : ℕ)^1024*2500000000000000^4631 ≤ 2517428548344629^4631*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25793052355969921313 25000000000000000000 2517428548344629 2500000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517428548344629/2500000000000000 : ℝ)) (X := (25793052355969921313/25000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17428548344629/2000000000000000 : ℝ)*(0 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17428548344629/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(793052355969921313/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17428548344629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4631/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17428548344629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5017428548344629/5000000000000000 : ℝ) by norm_num, show 1+(793052355969921313/50000000000000000000 : ℝ)+(0 : ℝ)=(50793052355969921313/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(793052355969921313/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17428548344629/2000000000000000 : ℝ)*(2/5 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17428548344629/2000000000000000 : ℝ)*(2/5 : ℝ)=(2517428548344629/2500000000000000 : ℝ) by norm_num, show 1+2*(793052355969921313/50000000000000000000 : ℝ)=(25793052355969921313/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17428548344629/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17428548344629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17428548344629/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17428548344629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17428548344629/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17428548344629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-814008333/5000000000 : ℝ)*X 0 0+(46967951/80000000 : ℝ)*X 0 1+(243927431/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2732952621/5000000000 : ℝ)*X 1 0+(-2180426007/10000000000 : ℝ)*X 1 1+(4878548623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((341619081/625000000 : ℝ)*X 2 0+(60981857/125000000 : ℝ)*X 2 1+(-2180426017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1032591787/2500000000 : ℝ)*X 0 0+(386631279/1250000000 : ℝ)*X 0 1+(271629361/500000000 : ℝ)*X 0 2+(1032591787/2500000000 : ℝ)*X 1 0+(386631279/1250000000 : ℝ)*X 1 1+(271629361/500000000 : ℝ)*X 1 2+(1032591787/2500000000 : ℝ)*X 2 0+(386631279/1250000000 : ℝ)*X 2 1+(271629361/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-815542799/5000000000 : ℝ)*X 0 0+(245178569/500000000 : ℝ)*X 0 1+(5845085121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194595911/10000000000 : ℝ)*X 1 0+(-1213892143/10000000000 : ℝ)*X 1 1+(1169017193/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((129864981/250000000 : ℝ)*X 2 0+(292254199/500000000 : ℝ)*X 2 1+(-242778043/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4137602611/10000000000 : ℝ)*X 0 0+(214944079/400000000 : ℝ)*X 0 1+(788530993/2500000000 : ℝ)*X 0 2+(4137602611/10000000000 : ℝ)*X 1 0+(214944079/400000000 : ℝ)*X 1 1+(788530993/2500000000 : ℝ)*X 1 2+(4137602611/10000000000 : ℝ)*X 2 0+(214944079/400000000 : ℝ)*X 2 1+(788530993/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (133332059796914521492401/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24909319/100000000000000 : ℝ)*(base1) + (66049911/12500000000000 : ℝ)*(base19) + (10767079/2000000000000 : ℝ)*(base23) + (33768497/50000000000000 : ℝ)*(upper3) + (16848073/25000000000000 : ℝ)*(upper5) + (717526411283659/100000000000000 : ℝ)*(major0) + (717526411283659/100000000000000 : ℝ)*(major1) + (717526411283659/100000000000000 : ℝ)*(major2) + (201522823895129/20000000000000 : ℝ)*(sp0) + (503807772338887/50000000000000 : ℝ)*(sp1) + (125951941840389/12500000000000 : ℝ)*(sp2) + (213717897546657/50000000000000 : ℝ)*(sp3) + (123656921/6250000000000 : ℝ)*(sp4) + (105074947/12500000000000 : ℝ)*(sp7) + (427436660602209/100000000000000 : ℝ)*(f.failure) + (503808036538531/50000000000000 : ℝ)*(f.sum) + (203685237117511/100000000000000000000000000000 : ℝ)*base65 + (364867107517511/200000000000000000000000000000 : ℝ)*base67 + (1476251026517511/200000000000000000000000000000 : ℝ)*base69 + (539964864917511/200000000000000000000000000000 : ℝ)*base71 + (177827105117511/100000000000000000000000000000 : ℝ)*base73 + (1165113777317511/200000000000000000000000000000 : ℝ)*base75 + (606582896117511/200000000000000000000000000000 : ℝ)*base77 + (771405374517511/200000000000000000000000000000 : ℝ)*base79 + (445843603317511/100000000000000000000000000000 : ℝ)*base81 + (76918837/10000000000000000000000 : ℝ)*base90 + (76918837/10000000000000000000000 : ℝ)*base92 + (76918837/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39628343335800150746271/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (319074743/50000000000000 : ℝ)*(base19) + (370774787/25000000000000 : ℝ)*(base23) + (204871361/100000000000000 : ℝ)*(base32) + (68200991/20000000000000 : ℝ)*(upper3) + (18393253/25000000000000 : ℝ)*(upper5) + (151267544620967/20000000000000 : ℝ)*(major0) + (151267544620967/20000000000000 : ℝ)*(major1) + (151267544620967/20000000000000 : ℝ)*(major2) + (142606531/100000000000000 : ℝ)*(sp1) + (1644039411/50000000000000 : ℝ)*(sp2) + (531059144414189/50000000000000 : ℝ)*(sp4) + (1062117508072361/100000000000000 : ℝ)*(sp5) + (132764189706301/12500000000000 : ℝ)*(sp6) + (450556688320971/100000000000000 : ℝ)*(sp7) + (450556893192333/100000000000000 : ℝ)*(f.failure) + (531059144414189/50000000000000 : ℝ)*(f.sum) + (24477990496243/20000000000000000000000000000 : ℝ)*base65 + (43884479363757/40000000000000000000000000000 : ℝ)*base68 + (174529873236243/40000000000000000000000000000 : ℝ)*base69 + (84012829076243/40000000000000000000000000000 : ℝ)*base71 + (4886967536243/20000000000000000000000000000 : ℝ)*base73 + (8289615636243/40000000000000000000000000000 : ℝ)*base75 + (22465634716243/40000000000000000000000000000 : ℝ)*base77 + (91214020163757/40000000000000000000000000000 : ℝ)*base80 + (96522152876243/20000000000000000000000000000 : ℝ)*base81 + (73757231/10000000000000000000000 : ℝ)*base89 + (73757231/10000000000000000000000 : ℝ)*base91 + (73757231/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1568_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3521/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24779/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1568_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1568_s1_0 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1767126329/10000000000 : ℝ)*x 0 + (5535971941/10000000000 : ℝ)*x 1 + (5123916859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1767126329/10000000000 : ℝ)^4633 ≤ (10806647589817/100000000000000 : ℝ)^3609 := by
    have hnat : (1767126329 : ℕ)^4633*100000000000000^3609 ≤ 10806647589817^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767126329 10000000000 10806647589817 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5535971941/10000000000 : ℝ)^4633 ≤ (4680895745193/10000000000000 : ℝ)^3609 := by
    have hnat : (5535971941 : ℕ)^4633*10000000000000^3609 ≤ 4680895745193^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5535971941 10000000000 4680895745193 10000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123916859/10000000000 : ℝ)^4633 ≤ (42384394944381/100000000000000 : ℝ)^3609 := by
    have hnat : (5123916859 : ℕ)^4633*100000000000000^3609 ≤ 42384394944381^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123916859 10000000000 42384394944381 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1767126329/10000000000 : ℝ), (5535971941/10000000000 : ℝ), (5123916859/10000000000 : ℝ)] ![(10806647589817/100000000000000 : ℝ), (4680895745193/10000000000000 : ℝ), (42384394944381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1767126329/10000000000 : ℝ)|^4633 ≤ (10806647589817/100000000000000 : ℝ)^3609
        have hw : |(-1767126329/10000000000 : ℝ)|=(1767126329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5535971941/10000000000 : ℝ)|^4633 ≤ (4680895745193/10000000000000 : ℝ)^3609
        have hw : |(5535971941/10000000000 : ℝ)|=(5535971941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123916859/10000000000 : ℝ)|^4633 ≤ (42384394944381/100000000000000 : ℝ)^3609
        have hw : |(5123916859/10000000000 : ℝ)|=(5123916859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s1_1 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344194263/2500000000 : ℝ)*x 0 + (-1982705231/10000000000 : ℝ)*x 1 + (256195833/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344194263/2500000000 : ℝ)^4633 ≤ (45088072310947/100000000000000 : ℝ)^3609 := by
    have hnat : (1344194263 : ℕ)^4633*100000000000000^3609 ≤ 45088072310947^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344194263 2500000000 45088072310947 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1982705231/10000000000 : ℝ)^4633 ≤ (12527534842287/100000000000000 : ℝ)^3609 := by
    have hnat : (1982705231 : ℕ)^4633*100000000000000^3609 ≤ 12527534842287^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982705231 10000000000 12527534842287 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256195833/500000000 : ℝ)^4633 ≤ (2119219641561/5000000000000 : ℝ)^3609 := by
    have hnat : (256195833 : ℕ)^4633*5000000000000^3609 ≤ 2119219641561^3609*500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256195833 500000000 2119219641561 5000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344194263/2500000000 : ℝ), (-1982705231/10000000000 : ℝ), (256195833/500000000 : ℝ)] ![(45088072310947/100000000000000 : ℝ), (12527534842287/100000000000000 : ℝ), (2119219641561/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344194263/2500000000 : ℝ)|^4633 ≤ (45088072310947/100000000000000 : ℝ)^3609
        have hw : |(1344194263/2500000000 : ℝ)|=(1344194263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1982705231/10000000000 : ℝ)|^4633 ≤ (12527534842287/100000000000000 : ℝ)^3609
        have hw : |(-1982705231/10000000000 : ℝ)|=(1982705231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(256195833/500000000 : ℝ)|^4633 ≤ (2119219641561/5000000000000 : ℝ)^3609
        have hw : |(256195833/500000000 : ℝ)|=(256195833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s1_2 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688388479/5000000000 : ℝ)*x 0 + (5123917077/10000000000 : ℝ)*x 1 + (-1982704811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688388479/5000000000 : ℝ)^4633 ≤ (22544035649517/50000000000000 : ℝ)^3609 := by
    have hnat : (2688388479 : ℕ)^4633*50000000000000^3609 ≤ 22544035649517^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688388479 5000000000 22544035649517 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5123917077/10000000000 : ℝ)^4633 ≤ (423843972593/1000000000000 : ℝ)^3609 := by
    have hnat : (5123917077 : ℕ)^4633*1000000000000^3609 ≤ 423843972593^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123917077 10000000000 423843972593 1000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1982704811/10000000000 : ℝ)^4633 ≤ (31318828589/250000000000 : ℝ)^3609 := by
    have hnat : (1982704811 : ℕ)^4633*250000000000^3609 ≤ 31318828589^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982704811 10000000000 31318828589 250000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688388479/5000000000 : ℝ), (5123917077/10000000000 : ℝ), (-1982704811/10000000000 : ℝ)] ![(22544035649517/50000000000000 : ℝ), (423843972593/1000000000000 : ℝ), (31318828589/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688388479/5000000000 : ℝ)|^4633 ≤ (22544035649517/50000000000000 : ℝ)^3609
        have hw : |(2688388479/5000000000 : ℝ)|=(2688388479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5123917077/10000000000 : ℝ)|^4633 ≤ (423843972593/1000000000000 : ℝ)^3609
        have hw : |(5123917077/10000000000 : ℝ)|=(5123917077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1982704811/10000000000 : ℝ)|^4633 ≤ (31318828589/250000000000 : ℝ)^3609
        have hw : |(-1982704811/10000000000 : ℝ)|=(1982704811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s1_3 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4229187913/10000000000 : ℝ)*x 0 + (3766024801/10000000000 : ℝ)*x 1 + (592172841/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4229187913/10000000000 : ℝ)^4633 ≤ (6625870797239/20000000000000 : ℝ)^3609 := by
    have hnat : (4229187913 : ℕ)^4633*20000000000000^3609 ≤ 6625870797239^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229187913 10000000000 6625870797239 20000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3766024801/10000000000 : ℝ)^4633 ≤ (28546071111661/100000000000000 : ℝ)^3609 := by
    have hnat : (3766024801 : ℕ)^4633*100000000000000^3609 ≤ 28546071111661^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3766024801 10000000000 28546071111661 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (592172841/1250000000 : ℝ)^4633 ≤ (19162287442983/50000000000000 : ℝ)^3609 := by
    have hnat : (592172841 : ℕ)^4633*50000000000000^3609 ≤ 19162287442983^3609*1250000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592172841 1250000000 19162287442983 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4229187913/10000000000 : ℝ), (3766024801/10000000000 : ℝ), (592172841/1250000000 : ℝ)] ![(6625870797239/20000000000000 : ℝ), (28546071111661/100000000000000 : ℝ), (19162287442983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4229187913/10000000000 : ℝ)|^4633 ≤ (6625870797239/20000000000000 : ℝ)^3609
        have hw : |(4229187913/10000000000 : ℝ)|=(4229187913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3766024801/10000000000 : ℝ)|^4633 ≤ (28546071111661/100000000000000 : ℝ)^3609
        have hw : |(3766024801/10000000000 : ℝ)|=(3766024801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(592172841/1250000000 : ℝ)|^4633 ≤ (19162287442983/50000000000000 : ℝ)^3609
        have hw : |(592172841/1250000000 : ℝ)|=(592172841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s1_4 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1767340129/10000000000 : ℝ)*x 0 + (5128179543/10000000000 : ℝ)*x 1 + (5531646183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1767340129/10000000000 : ℝ)^4633 ≤ (1080832606129/10000000000000 : ℝ)^3609 := by
    have hnat : (1767340129 : ℕ)^4633*10000000000000^3609 ≤ 1080832606129^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767340129 10000000000 1080832606129 10000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128179543/10000000000 : ℝ)^4633 ≤ (8485933055991/20000000000000 : ℝ)^3609 := by
    have hnat : (5128179543 : ℕ)^4633*20000000000000^3609 ≤ 8485933055991^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128179543 10000000000 8485933055991 20000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5531646183/10000000000 : ℝ)^4633 ≤ (46762008643847/100000000000000 : ℝ)^3609 := by
    have hnat : (5531646183 : ℕ)^4633*100000000000000^3609 ≤ 46762008643847^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531646183 10000000000 46762008643847 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1767340129/10000000000 : ℝ), (5128179543/10000000000 : ℝ), (5531646183/10000000000 : ℝ)] ![(1080832606129/10000000000000 : ℝ), (8485933055991/20000000000000 : ℝ), (46762008643847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1767340129/10000000000 : ℝ)|^4633 ≤ (1080832606129/10000000000000 : ℝ)^3609
        have hw : |(-1767340129/10000000000 : ℝ)|=(1767340129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128179543/10000000000 : ℝ)|^4633 ≤ (8485933055991/20000000000000 : ℝ)^3609
        have hw : |(5128179543/10000000000 : ℝ)|=(5128179543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5531646183/10000000000 : ℝ)|^4633 ≤ (46762008643847/100000000000000 : ℝ)^3609
        have hw : |(5531646183/10000000000 : ℝ)|=(5531646183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s1_5 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633787777/5000000000 : ℝ)*x 0 + (-393743909/2500000000 : ℝ)*x 1 + (553164661/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633787777/5000000000 : ℝ)^4633 ≤ (21957959563039/50000000000000 : ℝ)^3609 := by
    have hnat : (2633787777 : ℕ)^4633*50000000000000^3609 ≤ 21957959563039^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633787777 5000000000 21957959563039 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393743909/2500000000 : ℝ)^4633 ≤ (9322067584257/100000000000000 : ℝ)^3609 := by
    have hnat : (393743909 : ℕ)^4633*100000000000000^3609 ≤ 9322067584257^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393743909 2500000000 9322067584257 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553164661/1000000000 : ℝ)^4633 ≤ (23381006638849/50000000000000 : ℝ)^3609 := by
    have hnat : (553164661 : ℕ)^4633*50000000000000^3609 ≤ 23381006638849^3609*1000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553164661 1000000000 23381006638849 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633787777/5000000000 : ℝ), (-393743909/2500000000 : ℝ), (553164661/1000000000 : ℝ)] ![(21957959563039/50000000000000 : ℝ), (9322067584257/100000000000000 : ℝ), (23381006638849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633787777/5000000000 : ℝ)|^4633 ≤ (21957959563039/50000000000000 : ℝ)^3609
        have hw : |(2633787777/5000000000 : ℝ)|=(2633787777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-393743909/2500000000 : ℝ)|^4633 ≤ (9322067584257/100000000000000 : ℝ)^3609
        have hw : |(-393743909/2500000000 : ℝ)|=(393743909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553164661/1000000000 : ℝ)|^4633 ≤ (23381006638849/50000000000000 : ℝ)^3609
        have hw : |(553164661/1000000000 : ℝ)|=(553164661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s1_6 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267575079/10000000000 : ℝ)*x 0 + (5531646783/10000000000 : ℝ)*x 1 + (-787488029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267575079/10000000000 : ℝ)^4633 ≤ (351327312339/800000000000 : ℝ)^3609 := by
    have hnat : (5267575079 : ℕ)^4633*800000000000^3609 ≤ 351327312339^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267575079 10000000000 351327312339 800000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5531646783/10000000000 : ℝ)^4633 ≤ (23381007577557/50000000000000 : ℝ)^3609 := by
    have hnat : (5531646783 : ℕ)^4633*50000000000000^3609 ≤ 23381007577557^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531646783 10000000000 23381007577557 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (787488029/5000000000 : ℝ)^4633 ≤ (29131471221/312500000000 : ℝ)^3609 := by
    have hnat : (787488029 : ℕ)^4633*312500000000^3609 ≤ 29131471221^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787488029 5000000000 29131471221 312500000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267575079/10000000000 : ℝ), (5531646783/10000000000 : ℝ), (-787488029/5000000000 : ℝ)] ![(351327312339/800000000000 : ℝ), (23381007577557/50000000000000 : ℝ), (29131471221/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267575079/10000000000 : ℝ)|^4633 ≤ (351327312339/800000000000 : ℝ)^3609
        have hw : |(5267575079/10000000000 : ℝ)|=(5267575079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5531646783/10000000000 : ℝ)|^4633 ≤ (23381007577557/50000000000000 : ℝ)^3609
        have hw : |(5531646783/10000000000 : ℝ)|=(5531646783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-787488029/5000000000 : ℝ)|^4633 ≤ (29131471221/312500000000 : ℝ)^3609
        have hw : |(-787488029/5000000000 : ℝ)|=(787488029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s1_7 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2114845363/5000000000 : ℝ)*x 0 + (4727334369/10000000000 : ℝ)*x 1 + (3776222359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114845363/5000000000 : ℝ)^4633 ≤ (33134410430473/100000000000000 : ℝ)^3609 := by
    have hnat : (2114845363 : ℕ)^4633*100000000000000^3609 ≤ 33134410430473^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114845363 5000000000 33134410430473 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4727334369/10000000000 : ℝ)^4633 ≤ (19110126111509/50000000000000 : ℝ)^3609 := by
    have hnat : (4727334369 : ℕ)^4633*50000000000000^3609 ≤ 19110126111509^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4727334369 10000000000 19110126111509 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3776222359/10000000000 : ℝ)^4633 ≤ (28645337326639/100000000000000 : ℝ)^3609 := by
    have hnat : (3776222359 : ℕ)^4633*100000000000000^3609 ≤ 28645337326639^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3776222359 10000000000 28645337326639 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114845363/5000000000 : ℝ), (4727334369/10000000000 : ℝ), (3776222359/10000000000 : ℝ)] ![(33134410430473/100000000000000 : ℝ), (19110126111509/50000000000000 : ℝ), (28645337326639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114845363/5000000000 : ℝ)|^4633 ≤ (33134410430473/100000000000000 : ℝ)^3609
        have hw : |(2114845363/5000000000 : ℝ)|=(2114845363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4727334369/10000000000 : ℝ)|^4633 ≤ (19110126111509/50000000000000 : ℝ)^3609
        have hw : |(4727334369/10000000000 : ℝ)|=(4727334369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3776222359/10000000000 : ℝ)|^4633 ≤ (28645337326639/100000000000000 : ℝ)^3609
        have hw : |(3776222359/10000000000 : ℝ)|=(3776222359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1568_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3521/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9047/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3521/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24779/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3521/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3521/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24779/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3521/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3521/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24779/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3521/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3521/100000 : ℝ) ^ (4631/1024 : ℝ) ≤ (13375926496851/50000000000000000000 : ℝ) := by
    have hpowers : (3521/100000 : ℝ)^4631 ≤ (13375926496851/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3521 : ℕ)^4631*50000000000000000000^1024 ≤ 13375926496851^1024*100000^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 100000 13375926496851 50000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/100000 : ℝ)) (X := (13375926496851/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24779/100000 : ℝ) ^ (4631/1024 : ℝ) ≤ (181872712530270801/100000000000000000000 : ℝ) := by
    have hpowers : (24779/100000 : ℝ)^4631 ≤ (181872712530270801/100000000000000000000 : ℝ)^1024 := by
      have hnat : (24779 : ℕ)^4631*100000000000000000000^1024 ≤ 181872712530270801^1024*100000^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24779 100000 181872712530270801 100000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24779/100000 : ℝ)) (X := (181872712530270801/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013375926496851/25000000000000000000 : ℝ) ≤ (10000001183065937/10000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (25000013375926496851/25000000000000000000 : ℝ)^1024 ≤ (10000001183065937/10000000000000000 : ℝ)^4631 := by
      have hnat : (25000013375926496851 : ℕ)^1024*10000000000000000^4631 ≤ 10000001183065937^4631*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013375926496851 25000000000000000000 10000001183065937 10000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001183065937/10000000000000000 : ℝ)) (X := (25000013375926496851/25000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100181899464383264503/100000000000000000000 : ℝ) ≤ (5002009644194093/5000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (100181899464383264503/100000000000000000000 : ℝ)^1024 ≤ (5002009644194093/5000000000000000 : ℝ)^4631 := by
      have hnat : (100181899464383264503 : ℕ)^1024*5000000000000000^4631 ≤ 5002009644194093^4631*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100181899464383264503 100000000000000000000 5002009644194093 5000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002009644194093/5000000000000000 : ℝ)) (X := (100181899464383264503/100000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50181872712530270801/50000000000000000000 : ℝ) ≤ (2001607478742087/2000000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (50181872712530270801/50000000000000000000 : ℝ)^1024 ≤ (2001607478742087/2000000000000000 : ℝ)^4631 := by
      have hnat : (50181872712530270801 : ℕ)^1024*2000000000000000^4631 ≤ 2001607478742087^4631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50181872712530270801 50000000000000000000 2001607478742087 2000000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001607478742087/2000000000000000 : ℝ)) (X := (50181872712530270801/50000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13375926496851/50000000000000000000 : ℝ) ≤ ((26568966206492051411/26572500000000000000 : ℝ)+2*(4018105322249/2125800000000000 : ℝ)*(3521/100000 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (26568966206492051411/26572500000000000000 : ℝ)+2*(4018105322249/2125800000000000 : ℝ)*(3521/100000 : ℝ)=(10000001183065937/10000000000000000 : ℝ) by norm_num, show 1+2*(13375926496851/50000000000000000000 : ℝ)=(25000013375926496851/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(181872712530270801/100000000000000000000 : ℝ)+(13375926496851/50000000000000000000 : ℝ) ≤ ((26568966206492051411/26572500000000000000 : ℝ)+(4018105322249/2125800000000000 : ℝ)*((24779/100000 : ℝ)+(3521/100000 : ℝ)))^(4631/1024 : ℝ) := by
    rw [show (26568966206492051411/26572500000000000000 : ℝ)+(4018105322249/2125800000000000 : ℝ)*((24779/100000 : ℝ)+(3521/100000 : ℝ))=(5002009644194093/5000000000000000 : ℝ) by norm_num, show 1+(181872712530270801/100000000000000000000 : ℝ)+(13375926496851/50000000000000000000 : ℝ)=(100181899464383264503/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(181872712530270801/100000000000000000000 : ℝ) ≤ ((26568966206492051411/26572500000000000000 : ℝ)+2*(4018105322249/2125800000000000 : ℝ)*(24779/100000 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (26568966206492051411/26572500000000000000 : ℝ)+2*(4018105322249/2125800000000000 : ℝ)*(24779/100000 : ℝ)=(2001607478742087/2000000000000000 : ℝ) by norm_num, show 1+2*(181872712530270801/100000000000000000000 : ℝ)=(50181872712530270801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26568966206492051411/26572500000000000000 : ℝ)*(X 1 0+X 2 0)+(4018105322249/2125800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (3521/100000 : ℝ)) (hi := (24779/100000 : ℝ)) (c := (26568966206492051411/26572500000000000000 : ℝ)) (alpha := (4018105322249/2125800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26568966206492051411/26572500000000000000 : ℝ)*(X 0 1+X 2 1)+(4018105322249/2125800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (3521/100000 : ℝ)) (hi := (24779/100000 : ℝ)) (c := (26568966206492051411/26572500000000000000 : ℝ)) (alpha := (4018105322249/2125800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26568966206492051411/26572500000000000000 : ℝ)*(X 0 2+X 1 2)+(4018105322249/2125800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (3521/100000 : ℝ)) (hi := (24779/100000 : ℝ)) (c := (26568966206492051411/26572500000000000000 : ℝ)) (alpha := (4018105322249/2125800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1767126329/10000000000 : ℝ)*X 0 0+(5535971941/10000000000 : ℝ)*X 0 1+(5123916859/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1344194263/2500000000 : ℝ)*X 1 0+(-1982705231/10000000000 : ℝ)*X 1 1+(256195833/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688388479/5000000000 : ℝ)*X 2 0+(5123917077/10000000000 : ℝ)*X 2 1+(-1982704811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4229187913/10000000000 : ℝ)*X 0 0+(3766024801/10000000000 : ℝ)*X 0 1+(592172841/1250000000 : ℝ)*X 0 2+(4229187913/10000000000 : ℝ)*X 1 0+(3766024801/10000000000 : ℝ)*X 1 1+(592172841/1250000000 : ℝ)*X 1 2+(4229187913/10000000000 : ℝ)*X 2 0+(3766024801/10000000000 : ℝ)*X 2 1+(592172841/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1767340129/10000000000 : ℝ)*X 0 0+(5128179543/10000000000 : ℝ)*X 0 1+(5531646183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2633787777/5000000000 : ℝ)*X 1 0+(-393743909/2500000000 : ℝ)*X 1 1+(553164661/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5267575079/10000000000 : ℝ)*X 2 0+(5531646783/10000000000 : ℝ)*X 2 1+(-787488029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2114845363/5000000000 : ℝ)*X 0 0+(4727334369/10000000000 : ℝ)*X 0 1+(3776222359/10000000000 : ℝ)*X 0 2+(2114845363/5000000000 : ℝ)*X 1 0+(4727334369/10000000000 : ℝ)*X 1 1+(3776222359/10000000000 : ℝ)*X 1 2+(2114845363/5000000000 : ℝ)*X 2 0+(4727334369/10000000000 : ℝ)*X 2 1+(3776222359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (247457676207182864241157639/73812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70337707/100000000000000 : ℝ)*(base1) + (22258459/2000000000000 : ℝ)*(base19) + (268321353/25000000000000 : ℝ)*(base23) + (54751563/25000000000000 : ℝ)*(upper5) + (1728187698391897/100000000000000 : ℝ)*(major0) + (1728187698391897/100000000000000 : ℝ)*(major1) + (1728187698391897/100000000000000 : ℝ)*(major2) + (2426867686388559/100000000000000 : ℝ)*(sp0) + (1213438872145287/50000000000000 : ℝ)*(sp1) + (151679870083027/6250000000000 : ℝ)*(sp2) + (514746027093477/50000000000000 : ℝ)*(sp3) + (11378562991/100000000000000 : ℝ)*(sp4) + (137400319/100000000000000 : ℝ)*(sp5) + (416589471/10000000000000 : ℝ)*(sp7) + (1029496290419371/100000000000000 : ℝ)*(f.failure) + (606719748653461/25000000000000 : ℝ)*(f.sum) + (395702106162127/106290000000000000000000000000 : ℝ)*base66 + (2491238481948923611/885750000000000000000000000000000 : ℝ)*base68 + (1114012964043923611/885750000000000000000000000000000 : ℝ)*base70 + (383546616131076389/885750000000000000000000000000000 : ℝ)*base71 + (737828672142787/106290000000000000000000000000 : ℝ)*base74 + (2295427993425923611/885750000000000000000000000000000 : ℝ)*base76 + (5062540653650423611/885750000000000000000000000000000 : ℝ)*base78 + (7646230081617923611/885750000000000000000000000000000 : ℝ)*base80 + (190578810748147/106290000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10403897/10000000000000000000000 : ℝ)*base89 + (10403897/10000000000000000000000 : ℝ)*base91 + (10403897/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182022369115603910087562391/55359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277212603/50000000000000 : ℝ)*(base19) + (47618609/10000000000000 : ℝ)*(base23) + (82554047/100000000000000 : ℝ)*(upper2) + (76413017/50000000000000 : ℝ)*(upper3) + (2541763/6250000000000 : ℝ)*(upper5) + (220619831170727/12500000000000 : ℝ)*(major0) + (220619831170727/12500000000000 : ℝ)*(major1) + (220619831170727/12500000000000 : ℝ)*(major2) + (1230859907/25000000000000 : ℝ)*(sp1) + (2185269151/50000000000000 : ℝ)*(sp2) + (309814515830559/12500000000000 : ℝ)*(sp4) + (1239255324389819/50000000000000 : ℝ)*(sp5) + (2478511279920079/100000000000000 : ℝ)*(sp6) + (65712566405419/6250000000000 : ℝ)*(sp7) + (65712566405419/6250000000000 : ℝ)*(f.failure) + (309814515830559/12500000000000 : ℝ)*(f.sum) + (2723476222693/13286250000000000000000000000 : ℝ)*base65 + (789742354554238901/110718750000000000000000000000000 : ℝ)*base68 + (1349912692014238901/110718750000000000000000000000000 : ℝ)*base70 + (783921553211113901/110718750000000000000000000000000 : ℝ)*base72 + (17517514361099/6643125000000000000000000000 : ℝ)*base73 + (1511150113989613901/110718750000000000000000000000000 : ℝ)*base76 + (529553025111332651/110718750000000000000000000000000 : ℝ)*base78 + (817798797477520151/110718750000000000000000000000000 : ℝ)*base80 + (27115913571137/13286250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7736633/625000000000000000000 : ℝ)*base89 + (7736633/625000000000000000000 : ℝ)*base91 + (7736633/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1568_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24779/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3521/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9047/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1568_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1568_s2_0 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892952789/5000000000 : ℝ)*x 0 + (2720976237/5000000000 : ℝ)*x 1 + (1301425297/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892952789/5000000000 : ℝ)^4633 ≤ (10954296293913/100000000000000 : ℝ)^3609 := by
    have hnat : (892952789 : ℕ)^4633*100000000000000^3609 ≤ 10954296293913^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892952789 5000000000 10954296293913 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720976237/5000000000 : ℝ)^4633 ≤ (11447722613393/25000000000000 : ℝ)^3609 := by
    have hnat : (2720976237 : ℕ)^4633*25000000000000^3609 ≤ 11447722613393^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720976237 5000000000 11447722613393 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301425297/2500000000 : ℝ)^4633 ≤ (21627406621799/50000000000000 : ℝ)^3609 := by
    have hnat : (1301425297 : ℕ)^4633*50000000000000^3609 ≤ 21627406621799^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301425297 2500000000 21627406621799 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892952789/5000000000 : ℝ), (2720976237/5000000000 : ℝ), (1301425297/2500000000 : ℝ)] ![(10954296293913/100000000000000 : ℝ), (11447722613393/25000000000000 : ℝ), (21627406621799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892952789/5000000000 : ℝ)|^4633 ≤ (10954296293913/100000000000000 : ℝ)^3609
        have hw : |(-892952789/5000000000 : ℝ)|=(892952789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720976237/5000000000 : ℝ)|^4633 ≤ (11447722613393/25000000000000 : ℝ)^3609
        have hw : |(2720976237/5000000000 : ℝ)|=(2720976237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301425297/2500000000 : ℝ)|^4633 ≤ (21627406621799/50000000000000 : ℝ)^3609
        have hw : |(1301425297/2500000000 : ℝ)|=(1301425297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s2_1 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070501187/2000000000 : ℝ)*x 0 + (-953586853/5000000000 : ℝ)*x 1 + (5205700981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070501187/2000000000 : ℝ)^4633 ≤ (8965392124923/20000000000000 : ℝ)^3609 := by
    have hnat : (1070501187 : ℕ)^4633*20000000000000^3609 ≤ 8965392124923^3609*2000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070501187 2000000000 8965392124923 20000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953586853/5000000000 : ℝ)^4633 ≤ (5959114166293/50000000000000 : ℝ)^3609 := by
    have hnat : (953586853 : ℕ)^4633*50000000000000^3609 ≤ 5959114166293^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953586853 5000000000 5959114166293 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5205700981/10000000000 : ℝ)^4633 ≤ (10813702758897/25000000000000 : ℝ)^3609 := by
    have hnat : (5205700981 : ℕ)^4633*25000000000000^3609 ≤ 10813702758897^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205700981 10000000000 10813702758897 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070501187/2000000000 : ℝ), (-953586853/5000000000 : ℝ), (5205700981/10000000000 : ℝ)] ![(8965392124923/20000000000000 : ℝ), (5959114166293/50000000000000 : ℝ), (10813702758897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070501187/2000000000 : ℝ)|^4633 ≤ (8965392124923/20000000000000 : ℝ)^3609
        have hw : |(1070501187/2000000000 : ℝ)|=(1070501187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-953586853/5000000000 : ℝ)|^4633 ≤ (5959114166293/50000000000000 : ℝ)^3609
        have hw : |(-953586853/5000000000 : ℝ)|=(953586853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5205700981/10000000000 : ℝ)|^4633 ≤ (10813702758897/25000000000000 : ℝ)^3609
        have hw : |(5205700981/10000000000 : ℝ)|=(5205700981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s2_2 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352505923/10000000000 : ℝ)*x 0 + (1041140181/2000000000 : ℝ)*x 1 + (-953586911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352505923/10000000000 : ℝ)^4633 ≤ (112067401239/250000000000 : ℝ)^3609 := by
    have hnat : (5352505923 : ℕ)^4633*250000000000^3609 ≤ 112067401239^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352505923 10000000000 112067401239 250000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1041140181/2000000000 : ℝ)^4633 ≤ (21627405112459/50000000000000 : ℝ)^3609 := by
    have hnat : (1041140181 : ℕ)^4633*50000000000000^3609 ≤ 21627405112459^3609*2000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041140181 2000000000 21627405112459 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953586911/5000000000 : ℝ)^4633 ≤ (186222332237/1562500000000 : ℝ)^3609 := by
    have hnat : (953586911 : ℕ)^4633*1562500000000^3609 ≤ 186222332237^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953586911 5000000000 186222332237 1562500000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352505923/10000000000 : ℝ), (1041140181/2000000000 : ℝ), (-953586911/5000000000 : ℝ)] ![(112067401239/250000000000 : ℝ), (21627405112459/50000000000000 : ℝ), (186222332237/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352505923/10000000000 : ℝ)|^4633 ≤ (112067401239/250000000000 : ℝ)^3609
        have hw : |(5352505923/10000000000 : ℝ)|=(5352505923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1041140181/2000000000 : ℝ)|^4633 ≤ (21627405112459/50000000000000 : ℝ)^3609
        have hw : |(1041140181/2000000000 : ℝ)|=(1041140181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-953586911/5000000000 : ℝ)|^4633 ≤ (186222332237/1562500000000 : ℝ)^3609
        have hw : |(-953586911/5000000000 : ℝ)|=(953586911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s2_3 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242793137/10000000000 : ℝ)*x 0 + (3971737079/10000000000 : ℝ)*x 1 + (1132165947/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242793137/10000000000 : ℝ)^4633 ≤ (33266232445503/100000000000000 : ℝ)^3609 := by
    have hnat : (4242793137 : ℕ)^4633*100000000000000^3609 ≤ 33266232445503^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242793137 10000000000 33266232445503 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3971737079/10000000000 : ℝ)^4633 ≤ (1910192764227/6250000000000 : ℝ)^3609 := by
    have hnat : (3971737079 : ℕ)^4633*6250000000000^3609 ≤ 1910192764227^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3971737079 10000000000 1910192764227 6250000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132165947/2500000000 : ℝ)^4633 ≤ (36170683315101/100000000000000 : ℝ)^3609 := by
    have hnat : (1132165947 : ℕ)^4633*100000000000000^3609 ≤ 36170683315101^3609*2500000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132165947 2500000000 36170683315101 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242793137/10000000000 : ℝ), (3971737079/10000000000 : ℝ), (1132165947/2500000000 : ℝ)] ![(33266232445503/100000000000000 : ℝ), (1910192764227/6250000000000 : ℝ), (36170683315101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242793137/10000000000 : ℝ)|^4633 ≤ (33266232445503/100000000000000 : ℝ)^3609
        have hw : |(4242793137/10000000000 : ℝ)|=(4242793137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3971737079/10000000000 : ℝ)|^4633 ≤ (1910192764227/6250000000000 : ℝ)^3609
        have hw : |(3971737079/10000000000 : ℝ)|=(3971737079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132165947/2500000000 : ℝ)|^4633 ≤ (36170683315101/100000000000000 : ℝ)^3609
        have hw : |(1132165947/2500000000 : ℝ)|=(1132165947/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s2_4 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-892972747/5000000000 : ℝ)*x 0 + (2603555251/5000000000 : ℝ)*x 1 + (5440531593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892972747/5000000000 : ℝ)^4633 ≤ (5477305298917/50000000000000 : ℝ)^3609 := by
    have hnat : (892972747 : ℕ)^4633*50000000000000^3609 ≤ 5477305298917^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892972747 5000000000 5477305298917 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603555251/5000000000 : ℝ)^4633 ≤ (8653969313873/20000000000000 : ℝ)^3609 := by
    have hnat : (2603555251 : ℕ)^4633*20000000000000^3609 ≤ 8653969313873^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603555251 5000000000 8653969313873 20000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440531593/10000000000 : ℝ)^4633 ≤ (45775542821433/100000000000000 : ℝ)^3609 := by
    have hnat : (5440531593 : ℕ)^4633*100000000000000^3609 ≤ 45775542821433^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440531593 10000000000 45775542821433 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892972747/5000000000 : ℝ), (2603555251/5000000000 : ℝ), (5440531593/10000000000 : ℝ)] ![(5477305298917/50000000000000 : ℝ), (8653969313873/20000000000000 : ℝ), (45775542821433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892972747/5000000000 : ℝ)|^4633 ≤ (5477305298917/50000000000000 : ℝ)^3609
        have hw : |(-892972747/5000000000 : ℝ)|=(892972747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603555251/5000000000 : ℝ)|^4633 ≤ (8653969313873/20000000000000 : ℝ)^3609
        have hw : |(2603555251/5000000000 : ℝ)|=(2603555251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440531593/10000000000 : ℝ)|^4633 ≤ (45775542821433/100000000000000 : ℝ)^3609
        have hw : |(5440531593/10000000000 : ℝ)|=(5440531593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s2_5 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645004489/5000000000 : ℝ)*x 0 + (-836171797/5000000000 : ℝ)*x 1 + (1088106489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645004489/5000000000 : ℝ)^4633 ≤ (2759759907847/6250000000000 : ℝ)^3609 := by
    have hnat : (2645004489 : ℕ)^4633*6250000000000^3609 ≤ 2759759907847^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645004489 5000000000 2759759907847 6250000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836171797/5000000000 : ℝ)^4633 ≤ (2517072359447/25000000000000 : ℝ)^3609 := by
    have hnat : (836171797 : ℕ)^4633*25000000000000^3609 ≤ 2517072359447^3609*5000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836171797 5000000000 2517072359447 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088106489/2000000000 : ℝ)^4633 ≤ (22887776011981/50000000000000 : ℝ)^3609 := by
    have hnat : (1088106489 : ℕ)^4633*50000000000000^3609 ≤ 22887776011981^3609*2000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088106489 2000000000 22887776011981 50000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645004489/5000000000 : ℝ), (-836171797/5000000000 : ℝ), (1088106489/2000000000 : ℝ)] ![(2759759907847/6250000000000 : ℝ), (2517072359447/25000000000000 : ℝ), (22887776011981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645004489/5000000000 : ℝ)|^4633 ≤ (2759759907847/6250000000000 : ℝ)^3609
        have hw : |(2645004489/5000000000 : ℝ)|=(2645004489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-836171797/5000000000 : ℝ)|^4633 ≤ (2517072359447/25000000000000 : ℝ)^3609
        have hw : |(-836171797/5000000000 : ℝ)|=(836171797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088106489/2000000000 : ℝ)|^4633 ≤ (22887776011981/50000000000000 : ℝ)^3609
        have hw : |(1088106489/2000000000 : ℝ)|=(1088106489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s2_6 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290009269/10000000000 : ℝ)*x 0 + (340033343/625000000 : ℝ)*x 1 + (-1672341733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290009269/10000000000 : ℝ)^4633 ≤ (44156161643747/100000000000000 : ℝ)^3609 := by
    have hnat : (5290009269 : ℕ)^4633*100000000000000^3609 ≤ 44156161643747^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290009269 10000000000 44156161643747 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (340033343/625000000 : ℝ)^4633 ≤ (91551126579/200000000000 : ℝ)^3609 := by
    have hnat : (340033343 : ℕ)^4633*200000000000^3609 ≤ 91551126579^3609*625000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340033343 625000000 91551126579 200000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1672341733/10000000000 : ℝ)^4633 ≤ (2517068763677/25000000000000 : ℝ)^3609 := by
    have hnat : (1672341733 : ℕ)^4633*25000000000000^3609 ≤ 2517068763677^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1672341733 10000000000 2517068763677 25000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290009269/10000000000 : ℝ), (340033343/625000000 : ℝ), (-1672341733/10000000000 : ℝ)] ![(44156161643747/100000000000000 : ℝ), (91551126579/200000000000 : ℝ), (2517068763677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290009269/10000000000 : ℝ)|^4633 ≤ (44156161643747/100000000000000 : ℝ)^3609
        have hw : |(5290009269/10000000000 : ℝ)|=(5290009269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(340033343/625000000 : ℝ)|^4633 ≤ (91551126579/200000000000 : ℝ)^3609
        have hw : |(340033343/625000000 : ℝ)|=(340033343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1672341733/10000000000 : ℝ)|^4633 ≤ (2517068763677/25000000000000 : ℝ)^3609
        have hw : |(-1672341733/10000000000 : ℝ)|=(1672341733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1568_s2_7 (p : ℝ) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4242887919/10000000000 : ℝ)*x 0 + (4525342327/10000000000 : ℝ)*x 1 + (3975087203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242887919/10000000000 : ℝ)^4633 ≤ (33267186458789/100000000000000 : ℝ)^3609 := by
    have hnat : (4242887919 : ℕ)^4633*100000000000000^3609 ≤ 33267186458789^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242887919 10000000000 33267186458789 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525342327/10000000000 : ℝ)^4633 ≤ (36136631049611/100000000000000 : ℝ)^3609 := by
    have hnat : (4525342327 : ℕ)^4633*100000000000000^3609 ≤ 36136631049611^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525342327 10000000000 36136631049611 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3975087203/10000000000 : ℝ)^4633 ≤ (30596182470853/100000000000000 : ℝ)^3609 := by
    have hnat : (3975087203 : ℕ)^4633*100000000000000^3609 ≤ 30596182470853^3609*10000000000^4633 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975087203 10000000000 30596182470853 100000000000000 4633 3609 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4633/1024 : ℝ)) 4633 3609 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242887919/10000000000 : ℝ), (4525342327/10000000000 : ℝ), (3975087203/10000000000 : ℝ)] ![(33267186458789/100000000000000 : ℝ), (36136631049611/100000000000000 : ℝ), (30596182470853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242887919/10000000000 : ℝ)|^4633 ≤ (33267186458789/100000000000000 : ℝ)^3609
        have hw : |(4242887919/10000000000 : ℝ)|=(4242887919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525342327/10000000000 : ℝ)|^4633 ≤ (36136631049611/100000000000000 : ℝ)^3609
        have hw : |(4525342327/10000000000 : ℝ)|=(4525342327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3975087203/10000000000 : ℝ)|^4633 ≤ (30596182470853/100000000000000 : ℝ)^3609
        have hw : |(3975087203/10000000000 : ℝ)|=(3975087203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1568_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9047/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1351/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15817/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9047/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17773/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9047/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9047/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17773/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9047/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9047/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17773/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9047/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9047/100000 : ℝ) ^ (4631/1024 : ℝ) ≤ (477279498757313/25000000000000000000 : ℝ) := by
    have hpowers : (9047/100000 : ℝ)^4631 ≤ (477279498757313/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9047 : ℕ)^4631*25000000000000000000^1024 ≤ 477279498757313^1024*100000^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9047 100000 477279498757313 25000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9047/100000 : ℝ)) (X := (477279498757313/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17773/100000 : ℝ) ^ (4631/1024 : ℝ) ≤ (4046432096757071/10000000000000000000 : ℝ) := by
    have hpowers : (17773/100000 : ℝ)^4631 ≤ (4046432096757071/10000000000000000000 : ℝ)^1024 := by
      have hnat : (17773 : ℕ)^4631*10000000000000000000^1024 ≤ 4046432096757071^1024*100000^4631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17773 100000 4046432096757071 10000000000000000000 4631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17773/100000 : ℝ)) (X := (4046432096757071/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500477279498757313/12500000000000000000 : ℝ) ≤ (625005276689047/625000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (12500477279498757313/12500000000000000000 : ℝ)^1024 ≤ (625005276689047/625000000000000 : ℝ)^4631 := by
      have hnat : (12500477279498757313 : ℕ)^1024*625000000000000^4631 ≤ 625005276689047^4631*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500477279498757313 12500000000000000000 625005276689047 625000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625005276689047/625000000000000 : ℝ)) (X := (12500477279498757313/12500000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021186719481299981/50000000000000000000 : ℝ) ≤ (312529275023643/312500000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (50021186719481299981/50000000000000000000 : ℝ)^1024 ≤ (312529275023643/312500000000000 : ℝ)^4631 := by
      have hnat : (50021186719481299981 : ℕ)^1024*312500000000000^4631 ≤ 312529275023643^4631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021186719481299981 50000000000000000000 312529275023643 312500000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312529275023643/312500000000000 : ℝ)) (X := (50021186719481299981/50000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5004046432096757071/5000000000000000000 : ℝ) ≤ (25004472936221/25000000000000 : ℝ) ^ (4631/1024 : ℝ) := by
    have hpowers : (5004046432096757071/5000000000000000000 : ℝ)^1024 ≤ (25004472936221/25000000000000 : ℝ)^4631 := by
      have hnat : (5004046432096757071 : ℕ)^1024*25000000000000^4631 ≤ 25004472936221^4631*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5004046432096757071 5000000000000000000 25004472936221 25000000000000 1024 4631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25004472936221/25000000000000 : ℝ)) (X := (5004046432096757071/5000000000000000000 : ℝ)) (by norm_num) 4631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(477279498757313/25000000000000000000 : ℝ) ≤ ((681604014530580957/681718750000000000 : ℝ)+2*(53273358239/54537500000000 : ℝ)*(9047/100000 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (681604014530580957/681718750000000000 : ℝ)+2*(53273358239/54537500000000 : ℝ)*(9047/100000 : ℝ)=(625005276689047/625000000000000 : ℝ) by norm_num, show 1+2*(477279498757313/25000000000000000000 : ℝ)=(12500477279498757313/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4046432096757071/10000000000000000000 : ℝ)+(477279498757313/25000000000000000000 : ℝ) ≤ ((681604014530580957/681718750000000000 : ℝ)+(53273358239/54537500000000 : ℝ)*((17773/100000 : ℝ)+(9047/100000 : ℝ)))^(4631/1024 : ℝ) := by
    rw [show (681604014530580957/681718750000000000 : ℝ)+(53273358239/54537500000000 : ℝ)*((17773/100000 : ℝ)+(9047/100000 : ℝ))=(312529275023643/312500000000000 : ℝ) by norm_num, show 1+(4046432096757071/10000000000000000000 : ℝ)+(477279498757313/25000000000000000000 : ℝ)=(50021186719481299981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4046432096757071/10000000000000000000 : ℝ) ≤ ((681604014530580957/681718750000000000 : ℝ)+2*(53273358239/54537500000000 : ℝ)*(17773/100000 : ℝ))^(4631/1024 : ℝ) := by
    rw [show (681604014530580957/681718750000000000 : ℝ)+2*(53273358239/54537500000000 : ℝ)*(17773/100000 : ℝ)=(25004472936221/25000000000000 : ℝ) by norm_num, show 1+2*(4046432096757071/10000000000000000000 : ℝ)=(5004046432096757071/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (681604014530580957/681718750000000000 : ℝ)*(X 1 0+X 2 0)+(53273358239/54537500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (9047/100000 : ℝ)) (hi := (17773/100000 : ℝ)) (c := (681604014530580957/681718750000000000 : ℝ)) (alpha := (53273358239/54537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (681604014530580957/681718750000000000 : ℝ)*(X 0 1+X 2 1)+(53273358239/54537500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (9047/100000 : ℝ)) (hi := (17773/100000 : ℝ)) (c := (681604014530580957/681718750000000000 : ℝ)) (alpha := (53273358239/54537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (681604014530580957/681718750000000000 : ℝ)*(X 0 2+X 1 2)+(53273358239/54537500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4631/1024 : ℝ)) (lo := (9047/100000 : ℝ)) (hi := (17773/100000 : ℝ)) (c := (681604014530580957/681718750000000000 : ℝ)) (alpha := (53273358239/54537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-892952789/5000000000 : ℝ)*X 0 0+(2720976237/5000000000 : ℝ)*X 0 1+(1301425297/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070501187/2000000000 : ℝ)*X 1 0+(-953586853/5000000000 : ℝ)*X 1 1+(5205700981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352505923/10000000000 : ℝ)*X 2 0+(1041140181/2000000000 : ℝ)*X 2 1+(-953586911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4242793137/10000000000 : ℝ)*X 0 0+(3971737079/10000000000 : ℝ)*X 0 1+(1132165947/2500000000 : ℝ)*X 0 2+(4242793137/10000000000 : ℝ)*X 1 0+(3971737079/10000000000 : ℝ)*X 1 1+(1132165947/2500000000 : ℝ)*X 1 2+(4242793137/10000000000 : ℝ)*X 2 0+(3971737079/10000000000 : ℝ)*X 2 1+(1132165947/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-892972747/5000000000 : ℝ)*X 0 0+(2603555251/5000000000 : ℝ)*X 0 1+(5440531593/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645004489/5000000000 : ℝ)*X 1 0+(-836171797/5000000000 : ℝ)*X 1 1+(1088106489/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290009269/10000000000 : ℝ)*X 2 0+(340033343/625000000 : ℝ)*X 2 1+(-1672341733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4242887919/10000000000 : ℝ)*X 0 0+(4525342327/10000000000 : ℝ)*X 0 1+(3975087203/10000000000 : ℝ)*X 0 2+(4242887919/10000000000 : ℝ)*X 1 0+(4525342327/10000000000 : ℝ)*X 1 1+(3975087203/10000000000 : ℝ)*X 1 2+(4242887919/10000000000 : ℝ)*X 2 0+(4525342327/10000000000 : ℝ)*X 2 1+(3975087203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1568_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (796773422139939747006759093/68171875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1054010171/50000000000000 : ℝ)*(base19) + (1879686779/100000000000000 : ℝ)*(base23) + (58568139/50000000000000 : ℝ)*(lower2) + (93279/24414062500 : ℝ)*(upper3) + (110031011/100000000000000 : ℝ)*(upper5) + (1507106333327373/50000000000000 : ℝ)*(major0) + (1507106333327373/50000000000000 : ℝ)*(major1) + (1507106333327373/50000000000000 : ℝ)*(major2) + (4232809471834227/100000000000000 : ℝ)*(sp0) + (4232830399909629/100000000000000 : ℝ)*(sp1) + (529103828530399/12500000000000 : ℝ)*(sp2) + (359115745081223/20000000000000 : ℝ)*(sp3) + (89984749/390625000000 : ℝ)*(sp4) + (13710382913/100000000000000 : ℝ)*(sp7) + (448898108947257/25000000000000 : ℝ)*(f.failure) + (4232832507929971/100000000000000 : ℝ)*(f.sum) + (8709697841387/5453750000000000000000000000 : ℝ)*base66 + (17141706337932043/17042968750000000000000000000000 : ℝ)*base67 + (225853875556318703/68171875000000000000000000000000 : ℝ)*base70 + (435428235448837547/68171875000000000000000000000000 : ℝ)*base71 + (13135604071661/10907500000000000000000000000 : ℝ)*base73 + (45271209396035961/34085937500000000000000000000000 : ℝ)*base75 + (47872577008057043/17042968750000000000000000000000 : ℝ)*base77 + (120945912571495289/34085937500000000000000000000000 : ℝ)*base80 + (17533847916673/21815000000000000000000000000 : ℝ)*base82 + (12373101/2500000000000000000000 : ℝ)*base90 + (12373101/2500000000000000000000 : ℝ)*base92 + (12373101/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40972218349762938567462201/3408593750000000000000000000000 : ℝ) := by norm_num
    linear_combination (6968551/25000000000000 : ℝ)*(base23) + (27172011/10000000000000 : ℝ)*(lower2) + (172910223/100000000000000 : ℝ)*(upper3) + (6840989/25000000000000 : ℝ)*(upper4) + (7014761/50000000000000 : ℝ)*(upper5) + (152536268543197/5000000000000 : ℝ)*(major0) + (152536268543197/5000000000000 : ℝ)*(major1) + (152536268543197/5000000000000 : ℝ)*(major2) + (1636030279/20000000000000 : ℝ)*(sp1) + (307581893/800000000000 : ℝ)*(sp2) + (2142053486508453/50000000000000 : ℝ)*(sp4) + (535512349108189/12500000000000 : ℝ)*(sp5) + (4284068497406077/100000000000000 : ℝ)*(sp6) + (181734336803529/10000000000000 : ℝ)*(sp7) + (181734336803529/10000000000000 : ℝ)*(f.failure) + (2142053486508453/50000000000000 : ℝ)*(f.sum) + (17186242690871/2181500000000000000000000000 : ℝ)*base66 + (53676853455014683/6817187500000000000000000000000 : ℝ)*base67 + (24277317190006721/3408593750000000000000000000000 : ℝ)*base70 + (53085950350055009/13634375000000000000000000000000 : ℝ)*base72 + (125960539359/109075000000000000000000000 : ℝ)*base74 + (58030229652626241/13634375000000000000000000000000 : ℝ)*base75 + (46531401633877183/6817187500000000000000000000000 : ℝ)*base77 + (36983897184382491/13634375000000000000000000000000 : ℝ)*base79 + (32259535672821/4363000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1326403/1000000000000000000000 : ℝ)*base89 + (1326403/1000000000000000000000 : ℝ)*base91 + (1326403/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1568_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17773/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9047/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15817/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1568_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1568_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15817/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1568_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1568_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1568_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4631/1024 : ℝ) ≤ p) (hpb : p ≤ (4633/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167867307/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1351/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15817/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1568_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
