-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1592_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:37:05.782056+00:00
-- url     : https://prove2.me/submissions/840d017d-57ce-497d-93e2-88ee1ab928b8

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
theorem support_rectangle_w1592_box_0 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1469808173/10000000000 : ℝ)*x 0 + (2711370787/5000000000 : ℝ)*x 1 + (216909671/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1469808173/10000000000 : ℝ)^4687 ≤ (4299683427499/50000000000000 : ℝ)^3663 := by
    have hnat : (1469808173 : ℕ)^4687*50000000000000^3663 ≤ 4299683427499^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1469808173 10000000000 4299683427499 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711370787/5000000000 : ℝ)^4687 ≤ (45700315481513/100000000000000 : ℝ)^3663 := by
    have hnat : (2711370787 : ℕ)^4687*100000000000000^3663 ≤ 45700315481513^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711370787 5000000000 45700315481513 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216909671/400000000 : ℝ)^4687 ≤ (4570031764899/10000000000000 : ℝ)^3663 := by
    have hnat : (216909671 : ℕ)^4687*10000000000000^3663 ≤ 4570031764899^3663*400000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216909671 400000000 4570031764899 10000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1469808173/10000000000 : ℝ), (2711370787/5000000000 : ℝ), (216909671/400000000 : ℝ)] ![(4299683427499/50000000000000 : ℝ), (45700315481513/100000000000000 : ℝ), (4570031764899/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1469808173/10000000000 : ℝ)|^4687 ≤ (4299683427499/50000000000000 : ℝ)^3663
        have hw : |(-1469808173/10000000000 : ℝ)|=(1469808173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711370787/5000000000 : ℝ)|^4687 ≤ (45700315481513/100000000000000 : ℝ)^3663
        have hw : |(2711370787/5000000000 : ℝ)|=(2711370787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216909671/400000000 : ℝ)|^4687 ≤ (4570031764899/10000000000000 : ℝ)^3663
        have hw : |(216909671/400000000 : ℝ)|=(216909671/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_1 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250825149/10000000000 : ℝ)*x 0 + (-855504317/5000000000 : ℝ)*x 1 + (5422741719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250825149/10000000000 : ℝ)^4687 ≤ (438547391701/1000000000000 : ℝ)^3663 := by
    have hnat : (5250825149 : ℕ)^4687*1000000000000^3663 ≤ 438547391701^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250825149 10000000000 438547391701 1000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (855504317/5000000000 : ℝ)^4687 ≤ (10444943763069/100000000000000 : ℝ)^3663 := by
    have hnat : (855504317 : ℕ)^4687*100000000000000^3663 ≤ 10444943763069^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855504317 5000000000 10444943763069 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422741719/10000000000 : ℝ)^4687 ≤ (11425079261279/25000000000000 : ℝ)^3663 := by
    have hnat : (5422741719 : ℕ)^4687*25000000000000^3663 ≤ 11425079261279^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422741719 10000000000 11425079261279 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250825149/10000000000 : ℝ), (-855504317/5000000000 : ℝ), (5422741719/10000000000 : ℝ)] ![(438547391701/1000000000000 : ℝ), (10444943763069/100000000000000 : ℝ), (11425079261279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250825149/10000000000 : ℝ)|^4687 ≤ (438547391701/1000000000000 : ℝ)^3663
        have hw : |(5250825149/10000000000 : ℝ)|=(5250825149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-855504317/5000000000 : ℝ)|^4687 ≤ (10444943763069/100000000000000 : ℝ)^3663
        have hw : |(-855504317/5000000000 : ℝ)|=(855504317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422741719/10000000000 : ℝ)|^4687 ≤ (11425079261279/25000000000000 : ℝ)^3663
        have hw : |(5422741719/10000000000 : ℝ)|=(5422741719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_2 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250825331/10000000000 : ℝ)*x 0 + (43381933/80000000 : ℝ)*x 1 + (-1711008517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250825331/10000000000 : ℝ)^4687 ≤ (8770948223019/20000000000000 : ℝ)^3663 := by
    have hnat : (5250825331 : ℕ)^4687*20000000000000^3663 ≤ 8770948223019^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250825331 10000000000 8770948223019 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43381933/80000000 : ℝ)^4687 ≤ (4570031603147/10000000000000 : ℝ)^3663 := by
    have hnat : (43381933 : ℕ)^4687*10000000000000^3663 ≤ 4570031603147^3663*80000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43381933 80000000 4570031603147 10000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1711008517/10000000000 : ℝ)^4687 ≤ (10444942849171/100000000000000 : ℝ)^3663 := by
    have hnat : (1711008517 : ℕ)^4687*100000000000000^3663 ≤ 10444942849171^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711008517 10000000000 10444942849171 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250825331/10000000000 : ℝ), (43381933/80000000 : ℝ), (-1711008517/10000000000 : ℝ)] ![(8770948223019/20000000000000 : ℝ), (4570031603147/10000000000000 : ℝ), (10444942849171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250825331/10000000000 : ℝ)|^4687 ≤ (8770948223019/20000000000000 : ℝ)^3663
        have hw : |(5250825331/10000000000 : ℝ)|=(5250825331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43381933/80000000 : ℝ)|^4687 ≤ (4570031603147/10000000000000 : ℝ)^3663
        have hw : |(43381933/80000000 : ℝ)|=(43381933/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1711008517/10000000000 : ℝ)|^4687 ≤ (10444942849171/100000000000000 : ℝ)^3663
        have hw : |(-1711008517/10000000000 : ℝ)|=(1711008517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_3 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1127291021/2500000000 : ℝ)*x 0 + (4099970113/10000000000 : ℝ)*x 1 + (2049985107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1127291021/2500000000 : ℝ)^4687 ≤ (721818143207/2000000000000 : ℝ)^3663 := by
    have hnat : (1127291021 : ℕ)^4687*2000000000000^3663 ≤ 721818143207^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127291021 2500000000 721818143207 2000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4099970113/10000000000 : ℝ)^4687 ≤ (31954545908803/100000000000000 : ℝ)^3663 := by
    have hnat : (4099970113 : ℕ)^4687*100000000000000^3663 ≤ 31954545908803^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4099970113 10000000000 31954545908803 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049985107/5000000000 : ℝ)^4687 ≤ (31954546916039/100000000000000 : ℝ)^3663 := by
    have hnat : (2049985107 : ℕ)^4687*100000000000000^3663 ≤ 31954546916039^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049985107 5000000000 31954546916039 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1127291021/2500000000 : ℝ), (4099970113/10000000000 : ℝ), (2049985107/5000000000 : ℝ)] ![(721818143207/2000000000000 : ℝ), (31954545908803/100000000000000 : ℝ), (31954546916039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1127291021/2500000000 : ℝ)|^4687 ≤ (721818143207/2000000000000 : ℝ)^3663
        have hw : |(1127291021/2500000000 : ℝ)|=(1127291021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4099970113/10000000000 : ℝ)|^4687 ≤ (31954545908803/100000000000000 : ℝ)^3663
        have hw : |(4099970113/10000000000 : ℝ)|=(4099970113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2049985107/5000000000 : ℝ)|^4687 ≤ (31954546916039/100000000000000 : ℝ)^3663
        have hw : |(2049985107/5000000000 : ℝ)|=(2049985107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_4 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2042328589/10000000000 : ℝ)*x 0 + (325807251/625000000 : ℝ)*x 1 + (5212916513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042328589/10000000000 : ℝ)^4687 ≤ (13099950671543/100000000000000 : ℝ)^3663 := by
    have hnat : (2042328589 : ℕ)^4687*100000000000000^3663 ≤ 13099950671543^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042328589 10000000000 13099950671543 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325807251/625000000 : ℝ)^4687 ≤ (5431252751541/12500000000000 : ℝ)^3663 := by
    have hnat : (325807251 : ℕ)^4687*12500000000000^3663 ≤ 5431252751541^3663*625000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325807251 625000000 5431252751541 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212916513/10000000000 : ℝ)^4687 ≤ (2715626707057/6250000000000 : ℝ)^3663 := by
    have hnat : (5212916513 : ℕ)^4687*6250000000000^3663 ≤ 2715626707057^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212916513 10000000000 2715626707057 6250000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2042328589/10000000000 : ℝ), (325807251/625000000 : ℝ), (5212916513/10000000000 : ℝ)] ![(13099950671543/100000000000000 : ℝ), (5431252751541/12500000000000 : ℝ), (2715626707057/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2042328589/10000000000 : ℝ)|^4687 ≤ (13099950671543/100000000000000 : ℝ)^3663
        have hw : |(-2042328589/10000000000 : ℝ)|=(2042328589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325807251/625000000 : ℝ)|^4687 ≤ (5431252751541/12500000000000 : ℝ)^3663
        have hw : |(325807251/625000000 : ℝ)|=(325807251/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212916513/10000000000 : ℝ)|^4687 ≤ (2715626707057/6250000000000 : ℝ)^3663
        have hw : |(5212916513/10000000000 : ℝ)|=(5212916513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_5 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1349003843/2500000000 : ℝ)*x 0 + (-359813233/2000000000 : ℝ)*x 1 + (1303229171/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1349003843/2500000000 : ℝ)^4687 ≤ (5676539149771/12500000000000 : ℝ)^3663 := by
    have hnat : (1349003843 : ℕ)^4687*12500000000000^3663 ≤ 5676539149771^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349003843 2500000000 5676539149771 12500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359813233/2000000000 : ℝ)^4687 ≤ (11137657653871/100000000000000 : ℝ)^3663 := by
    have hnat : (359813233 : ℕ)^4687*100000000000000^3663 ≤ 11137657653871^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359813233 2000000000 11137657653871 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303229171/2500000000 : ℝ)^4687 ≤ (21725014568327/50000000000000 : ℝ)^3663 := by
    have hnat : (1303229171 : ℕ)^4687*50000000000000^3663 ≤ 21725014568327^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303229171 2500000000 21725014568327 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1349003843/2500000000 : ℝ), (-359813233/2000000000 : ℝ), (1303229171/2500000000 : ℝ)] ![(5676539149771/12500000000000 : ℝ), (11137657653871/100000000000000 : ℝ), (21725014568327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1349003843/2500000000 : ℝ)|^4687 ≤ (5676539149771/12500000000000 : ℝ)^3663
        have hw : |(1349003843/2500000000 : ℝ)|=(1349003843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-359813233/2000000000 : ℝ)|^4687 ≤ (11137657653871/100000000000000 : ℝ)^3663
        have hw : |(-359813233/2000000000 : ℝ)|=(359813233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303229171/2500000000 : ℝ)|^4687 ≤ (21725014568327/50000000000000 : ℝ)^3663
        have hw : |(1303229171/2500000000 : ℝ)|=(1303229171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_6 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698008193/5000000000 : ℝ)*x 0 + (5212915521/10000000000 : ℝ)*x 1 + (-1799066351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698008193/5000000000 : ℝ)^4687 ≤ (45412324117509/100000000000000 : ℝ)^3663 := by
    have hnat : (2698008193 : ℕ)^4687*100000000000000^3663 ≤ 45412324117509^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698008193 5000000000 45412324117509 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5212915521/10000000000 : ℝ)^4687 ≤ (1738000669323/4000000000000 : ℝ)^3663 := by
    have hnat : (5212915521 : ℕ)^4687*4000000000000^3663 ≤ 1738000669323^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212915521 10000000000 1738000669323 4000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1799066351/10000000000 : ℝ)^4687 ≤ (11137659127261/100000000000000 : ℝ)^3663 := by
    have hnat : (1799066351 : ℕ)^4687*100000000000000^3663 ≤ 11137659127261^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799066351 10000000000 11137659127261 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698008193/5000000000 : ℝ), (5212915521/10000000000 : ℝ), (-1799066351/10000000000 : ℝ)] ![(45412324117509/100000000000000 : ℝ), (1738000669323/4000000000000 : ℝ), (11137659127261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698008193/5000000000 : ℝ)|^4687 ≤ (45412324117509/100000000000000 : ℝ)^3663
        have hw : |(2698008193/5000000000 : ℝ)|=(2698008193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5212915521/10000000000 : ℝ)|^4687 ≤ (1738000669323/4000000000000 : ℝ)^3663
        have hw : |(5212915521/10000000000 : ℝ)|=(5212915521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1799066351/10000000000 : ℝ)|^4687 ≤ (11137659127261/100000000000000 : ℝ)^3663
        have hw : |(-1799066351/10000000000 : ℝ)|=(1799066351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_7 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1970272871/5000000000 : ℝ)*x 0 + (4383925727/10000000000 : ℝ)*x 1 + (547990801/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1970272871/5000000000 : ℝ)^4687 ≤ (1518669390713/5000000000000 : ℝ)^3663 := by
    have hnat : (1970272871 : ℕ)^4687*5000000000000^3663 ≤ 1518669390713^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970272871 5000000000 1518669390713 5000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4383925727/10000000000 : ℝ)^4687 ≤ (34813302628529/100000000000000 : ℝ)^3663 := by
    have hnat : (4383925727 : ℕ)^4687*100000000000000^3663 ≤ 34813302628529^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383925727 10000000000 34813302628529 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547990801/1250000000 : ℝ)^4687 ≤ (8703327387057/25000000000000 : ℝ)^3663 := by
    have hnat : (547990801 : ℕ)^4687*25000000000000^3663 ≤ 8703327387057^3663*1250000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547990801 1250000000 8703327387057 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1970272871/5000000000 : ℝ), (4383925727/10000000000 : ℝ), (547990801/1250000000 : ℝ)] ![(1518669390713/5000000000000 : ℝ), (34813302628529/100000000000000 : ℝ), (8703327387057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1970272871/5000000000 : ℝ)|^4687 ≤ (1518669390713/5000000000000 : ℝ)^3663
        have hw : |(1970272871/5000000000 : ℝ)|=(1970272871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4383925727/10000000000 : ℝ)|^4687 ≤ (34813302628529/100000000000000 : ℝ)^3663
        have hw : |(4383925727/10000000000 : ℝ)|=(4383925727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547990801/1250000000 : ℝ)|^4687 ≤ (8703327387057/25000000000000 : ℝ)^3663
        have hw : |(547990801/1250000000 : ℝ)|=(547990801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_8 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-60025787/312500000 : ℝ)*x 0 + (1012702857/2000000000 : ℝ)*x 1 + (5452901611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (60025787/312500000 : ℝ)^4687 ≤ (2422229167713/20000000000000 : ℝ)^3663 := by
    have hnat : (60025787 : ℕ)^4687*20000000000000^3663 ≤ 2422229167713^3663*312500000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60025787 312500000 2422229167713 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1012702857/2000000000 : ℝ)^4687 ≤ (20931528233371/50000000000000 : ℝ)^3663 := by
    have hnat : (1012702857 : ℕ)^4687*50000000000000^3663 ≤ 20931528233371^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012702857 2000000000 20931528233371 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5452901611/10000000000 : ℝ)^4687 ≤ (23012898838109/50000000000000 : ℝ)^3663 := by
    have hnat : (5452901611 : ℕ)^4687*50000000000000^3663 ≤ 23012898838109^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452901611 10000000000 23012898838109 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-60025787/312500000 : ℝ), (1012702857/2000000000 : ℝ), (5452901611/10000000000 : ℝ)] ![(2422229167713/20000000000000 : ℝ), (20931528233371/50000000000000 : ℝ), (23012898838109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-60025787/312500000 : ℝ)|^4687 ≤ (2422229167713/20000000000000 : ℝ)^3663
        have hw : |(-60025787/312500000 : ℝ)|=(60025787/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1012702857/2000000000 : ℝ)|^4687 ≤ (20931528233371/50000000000000 : ℝ)^3663
        have hw : |(1012702857/2000000000 : ℝ)|=(1012702857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5452901611/10000000000 : ℝ)|^4687 ≤ (23012898838109/50000000000000 : ℝ)^3663
        have hw : |(5452901611/10000000000 : ℝ)|=(5452901611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_9 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261497419/500000000 : ℝ)*x 0 + (-212234003/1250000000 : ℝ)*x 1 + (2726450887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261497419/500000000 : ℝ)^4687 ≤ (43631757766393/100000000000000 : ℝ)^3663 := by
    have hnat : (261497419 : ℕ)^4687*100000000000000^3663 ≤ 43631757766393^3663*500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261497419 500000000 43631757766393 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212234003/1250000000 : ℝ)^4687 ≤ (2068488554327/20000000000000 : ℝ)^3663 := by
    have hnat : (212234003 : ℕ)^4687*20000000000000^3663 ≤ 2068488554327^3663*1250000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212234003 1250000000 2068488554327 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2726450887/5000000000 : ℝ)^4687 ≤ (920515988733/2000000000000 : ℝ)^3663 := by
    have hnat : (2726450887 : ℕ)^4687*2000000000000^3663 ≤ 920515988733^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726450887 5000000000 920515988733 2000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261497419/500000000 : ℝ), (-212234003/1250000000 : ℝ), (2726450887/5000000000 : ℝ)] ![(43631757766393/100000000000000 : ℝ), (2068488554327/20000000000000 : ℝ), (920515988733/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261497419/500000000 : ℝ)|^4687 ≤ (43631757766393/100000000000000 : ℝ)^3663
        have hw : |(261497419/500000000 : ℝ)|=(261497419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212234003/1250000000 : ℝ)|^4687 ≤ (2068488554327/20000000000000 : ℝ)^3663
        have hw : |(-212234003/1250000000 : ℝ)|=(212234003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2726450887/5000000000 : ℝ)|^4687 ≤ (920515988733/2000000000000 : ℝ)^3663
        have hw : |(2726450887/5000000000 : ℝ)|=(2726450887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_10 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045989671/2000000000 : ℝ)*x 0 + (2726450959/5000000000 : ℝ)*x 1 + (-84893593/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045989671/2000000000 : ℝ)^4687 ≤ (43631757499521/100000000000000 : ℝ)^3663 := by
    have hnat : (1045989671 : ℕ)^4687*100000000000000^3663 ≤ 43631757499521^3663*2000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045989671 2000000000 43631757499521 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726450959/5000000000 : ℝ)^4687 ≤ (46025800991879/100000000000000 : ℝ)^3663 := by
    have hnat : (2726450959 : ℕ)^4687*100000000000000^3663 ≤ 46025800991879^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726450959 5000000000 46025800991879 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84893593/500000000 : ℝ)^4687 ≤ (10342441493373/100000000000000 : ℝ)^3663 := by
    have hnat : (84893593 : ℕ)^4687*100000000000000^3663 ≤ 10342441493373^3663*500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84893593 500000000 10342441493373 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045989671/2000000000 : ℝ), (2726450959/5000000000 : ℝ), (-84893593/500000000 : ℝ)] ![(43631757499521/100000000000000 : ℝ), (46025800991879/100000000000000 : ℝ), (10342441493373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045989671/2000000000 : ℝ)|^4687 ≤ (43631757499521/100000000000000 : ℝ)^3663
        have hw : |(1045989671/2000000000 : ℝ)|=(1045989671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726450959/5000000000 : ℝ)|^4687 ≤ (46025800991879/100000000000000 : ℝ)^3663
        have hw : |(2726450959/5000000000 : ℝ)|=(2726450959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-84893593/500000000 : ℝ)|^4687 ≤ (10342441493373/100000000000000 : ℝ)^3663
        have hw : |(-84893593/500000000 : ℝ)|=(84893593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_11 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (114712241/250000000 : ℝ)*x 0 + (1014770437/2500000000 : ℝ)*x 1 + (4059081361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (114712241/250000000 : ℝ)^4687 ≤ (18452651035217/50000000000000 : ℝ)^3663 := by
    have hnat : (114712241 : ℕ)^4687*50000000000000^3663 ≤ 18452651035217^3663*250000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114712241 250000000 18452651035217 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1014770437/2500000000 : ℝ)^4687 ≤ (15773675440167/50000000000000 : ℝ)^3663 := by
    have hnat : (1014770437 : ℕ)^4687*50000000000000^3663 ≤ 15773675440167^3663*2500000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014770437 2500000000 15773675440167 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4059081361/10000000000 : ℝ)^4687 ≤ (15773673515861/50000000000000 : ℝ)^3663 := by
    have hnat : (4059081361 : ℕ)^4687*50000000000000^3663 ≤ 15773673515861^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4059081361 10000000000 15773673515861 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(114712241/250000000 : ℝ), (1014770437/2500000000 : ℝ), (4059081361/10000000000 : ℝ)] ![(18452651035217/50000000000000 : ℝ), (15773675440167/50000000000000 : ℝ), (15773673515861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(114712241/250000000 : ℝ)|^4687 ≤ (18452651035217/50000000000000 : ℝ)^3663
        have hw : |(114712241/250000000 : ℝ)|=(114712241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1014770437/2500000000 : ℝ)|^4687 ≤ (15773675440167/50000000000000 : ℝ)^3663
        have hw : |(1014770437/2500000000 : ℝ)|=(1014770437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4059081361/10000000000 : ℝ)|^4687 ≤ (15773673515861/50000000000000 : ℝ)^3663
        have hw : |(4059081361/10000000000 : ℝ)|=(4059081361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_12 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1590376613/10000000000 : ℝ)*x 0 + (86967021/156250000 : ℝ)*x 1 + (5193051067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1590376613/10000000000 : ℝ)^4687 ≤ (4756061747277/50000000000000 : ℝ)^3663 := by
    have hnat : (1590376613 : ℕ)^4687*50000000000000^3663 ≤ 4756061747277^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1590376613 10000000000 4756061747277 50000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86967021/156250000 : ℝ)^4687 ≤ (47249604345273/100000000000000 : ℝ)^3663 := by
    have hnat : (86967021 : ℕ)^4687*100000000000000^3663 ≤ 47249604345273^3663*156250000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86967021 156250000 47249604345273 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193051067/10000000000 : ℝ)^4687 ≤ (10809568034371/25000000000000 : ℝ)^3663 := by
    have hnat : (5193051067 : ℕ)^4687*25000000000000^3663 ≤ 10809568034371^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193051067 10000000000 10809568034371 25000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1590376613/10000000000 : ℝ), (86967021/156250000 : ℝ), (5193051067/10000000000 : ℝ)] ![(4756061747277/50000000000000 : ℝ), (47249604345273/100000000000000 : ℝ), (10809568034371/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1590376613/10000000000 : ℝ)|^4687 ≤ (4756061747277/50000000000000 : ℝ)^3663
        have hw : |(-1590376613/10000000000 : ℝ)|=(1590376613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86967021/156250000 : ℝ)|^4687 ≤ (47249604345273/100000000000000 : ℝ)^3663
        have hw : |(86967021/156250000 : ℝ)|=(86967021/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193051067/10000000000 : ℝ)|^4687 ≤ (10809568034371/25000000000000 : ℝ)^3663
        have hw : |(5193051067/10000000000 : ℝ)|=(5193051067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_13 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2704883353/5000000000 : ℝ)*x 0 + (-112943271/625000000 : ℝ)*x 1 + (2596525693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704883353/5000000000 : ℝ)^4687 ≤ (45560448268869/100000000000000 : ℝ)^3663 := by
    have hnat : (2704883353 : ℕ)^4687*100000000000000^3663 ≤ 45560448268869^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704883353 5000000000 45560448268869 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112943271/625000000 : ℝ)^4687 ≤ (11201276181937/100000000000000 : ℝ)^3663 := by
    have hnat : (112943271 : ℕ)^4687*100000000000000^3663 ≤ 11201276181937^3663*625000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112943271 625000000 11201276181937 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596525693/5000000000 : ℝ)^4687 ≤ (1080956888401/2500000000000 : ℝ)^3663 := by
    have hnat : (2596525693 : ℕ)^4687*2500000000000^3663 ≤ 1080956888401^3663*5000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596525693 5000000000 1080956888401 2500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704883353/5000000000 : ℝ), (-112943271/625000000 : ℝ), (2596525693/5000000000 : ℝ)] ![(45560448268869/100000000000000 : ℝ), (11201276181937/100000000000000 : ℝ), (1080956888401/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704883353/5000000000 : ℝ)|^4687 ≤ (45560448268869/100000000000000 : ℝ)^3663
        have hw : |(2704883353/5000000000 : ℝ)|=(2704883353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-112943271/625000000 : ℝ)|^4687 ≤ (11201276181937/100000000000000 : ℝ)^3663
        have hw : |(-112943271/625000000 : ℝ)|=(112943271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2596525693/5000000000 : ℝ)|^4687 ≤ (1080956888401/2500000000000 : ℝ)^3663
        have hw : |(2596525693/5000000000 : ℝ)|=(2596525693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_14 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409767041/10000000000 : ℝ)*x 0 + (649131371/1250000000 : ℝ)*x 1 + (-1807092441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409767041/10000000000 : ℝ)^4687 ≤ (11123157197/24414062500 : ℝ)^3663 := by
    have hnat : (5409767041 : ℕ)^4687*24414062500^3663 ≤ 11123157197^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409767041 10000000000 11123157197 24414062500 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649131371/1250000000 : ℝ)^4687 ≤ (1080956777069/2500000000000 : ℝ)^3663 := by
    have hnat : (649131371 : ℕ)^4687*2500000000000^3663 ≤ 1080956777069^3663*1250000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649131371 1250000000 1080956777069 2500000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1807092441/10000000000 : ℝ)^4687 ≤ (448051080589/4000000000000 : ℝ)^3663 := by
    have hnat : (1807092441 : ℕ)^4687*4000000000000^3663 ≤ 448051080589^3663*10000000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807092441 10000000000 448051080589 4000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409767041/10000000000 : ℝ), (649131371/1250000000 : ℝ), (-1807092441/10000000000 : ℝ)] ![(11123157197/24414062500 : ℝ), (1080956777069/2500000000000 : ℝ), (448051080589/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409767041/10000000000 : ℝ)|^4687 ≤ (11123157197/24414062500 : ℝ)^3663
        have hw : |(5409767041/10000000000 : ℝ)|=(5409767041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649131371/1250000000 : ℝ)|^4687 ≤ (1080956777069/2500000000000 : ℝ)^3663
        have hw : |(649131371/1250000000 : ℝ)|=(649131371/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1807092441/10000000000 : ℝ)|^4687 ≤ (448051080589/4000000000000 : ℝ)^3663
        have hw : |(-1807092441/10000000000 : ℝ)|=(1807092441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1592_box_15 (p : ℝ) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (242818291/625000000 : ℝ)*x 0 + (176430507/400000000 : ℝ)*x 1 + (275672621/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242818291/625000000 : ℝ)^4687 ≤ (932110977057/3125000000000 : ℝ)^3663 := by
    have hnat : (242818291 : ℕ)^4687*3125000000000^3663 ≤ 932110977057^3663*625000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242818291 625000000 932110977057 3125000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (176430507/400000000 : ℝ)^4687 ≤ (35086228121779/100000000000000 : ℝ)^3663 := by
    have hnat : (176430507 : ℕ)^4687*100000000000000^3663 ≤ 35086228121779^3663*400000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176430507 400000000 35086228121779 100000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275672621/625000000 : ℝ)^4687 ≤ (7017244119983/20000000000000 : ℝ)^3663 := by
    have hnat : (275672621 : ℕ)^4687*20000000000000^3663 ≤ 7017244119983^3663*625000000^4687 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275672621 625000000 7017244119983 20000000000000 4687 3663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4687/1024 : ℝ)) 4687 3663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(242818291/625000000 : ℝ), (176430507/400000000 : ℝ), (275672621/625000000 : ℝ)] ![(932110977057/3125000000000 : ℝ), (35086228121779/100000000000000 : ℝ), (7017244119983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(242818291/625000000 : ℝ)|^4687 ≤ (932110977057/3125000000000 : ℝ)^3663
        have hw : |(242818291/625000000 : ℝ)|=(242818291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(176430507/400000000 : ℝ)|^4687 ≤ (35086228121779/100000000000000 : ℝ)^3663
        have hw : |(176430507/400000000 : ℝ)|=(176430507/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275672621/625000000 : ℝ)|^4687 ≤ (7017244119983/20000000000000 : ℝ)^3663
        have hw : |(275672621/625000000 : ℝ)|=(275672621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1592_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(32433/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(57999/100000 : ℝ) ∧ (40033/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (43819/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1637/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1637/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10311/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1637/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1637/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10311/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1637/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1637/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10311/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10311/100000 : ℝ) ^ (4683/1024 : ℝ) ≤ (3073162549345201/100000000000000000000 : ℝ) := by
    have hpowers : (10311/100000 : ℝ)^4683 ≤ (3073162549345201/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10311 : ℕ)^4683*100000000000000000000^1024 ≤ 3073162549345201^1024*100000^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10311 100000 3073162549345201 100000000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10311/100000 : ℝ)) (X := (3073162549345201/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1637/10000 : ℝ) ^ (4683/1024 : ℝ) ≤ (5089607116699749/20000000000000000000 : ℝ) := by
    have hpowers : (1637/10000 : ℝ)^4683 ≤ (5089607116699749/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1637 : ℕ)^4683*20000000000000000000^1024 ≤ 5089607116699749^1024*10000^4683 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1637 10000 5089607116699749 20000000000000000000 4683 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1637/10000 : ℝ)) (X := (5089607116699749/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50003073162549345201/50000000000000000000 : ℝ) ≤ (2000026878863039/2000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (50003073162549345201/50000000000000000000 : ℝ)^1024 ≤ (2000026878863039/2000000000000000 : ℝ)^4683 := by
      have hnat : (50003073162549345201 : ℕ)^1024*2000000000000000^4683 ≤ 2000026878863039^4683*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003073162549345201 50000000000000000000 2000026878863039 2000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000026878863039/2000000000000000 : ℝ)) (X := (50003073162549345201/50000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014260599066421973/50000000000000000000 : ℝ) ≤ (10000623584310117/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (50014260599066421973/50000000000000000000 : ℝ)^1024 ≤ (10000623584310117/10000000000000000 : ℝ)^4683 := by
      have hnat : (50014260599066421973 : ℕ)^1024*10000000000000000^4683 ≤ 10000623584310117^4683*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014260599066421973 50000000000000000000 10000623584310117 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000623584310117/10000000000000000 : ℝ)) (X := (50014260599066421973/50000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005089607116699749/10000000000000000000 : ℝ) ≤ (10001112774305039/10000000000000000 : ℝ) ^ (4683/1024 : ℝ) := by
    have hpowers : (10005089607116699749/10000000000000000000 : ℝ)^1024 ≤ (10001112774305039/10000000000000000 : ℝ)^4683 := by
      have hnat : (10005089607116699749 : ℕ)^1024*10000000000000000^4683 ≤ 10001112774305039^4683*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005089607116699749 10000000000000000000 10001112774305039 10000000000000000 1024 4683 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001112774305039/10000000000000000 : ℝ)) (X := (10005089607116699749/10000000000000000000 : ℝ)) (by norm_num) 4683 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3073162549345201/100000000000000000000 : ℝ) ≤ ((60580726219080485021/60590000000000000000 : ℝ)+2*(244594997461/302950000000000 : ℝ)*(10311/100000 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (60580726219080485021/60590000000000000000 : ℝ)+2*(244594997461/302950000000000 : ℝ)*(10311/100000 : ℝ)=(2000026878863039/2000000000000000 : ℝ) by norm_num, show 1+2*(3073162549345201/100000000000000000000 : ℝ)=(50003073162549345201/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5089607116699749/20000000000000000000 : ℝ)+(3073162549345201/100000000000000000000 : ℝ) ≤ ((60580726219080485021/60590000000000000000 : ℝ)+(244594997461/302950000000000 : ℝ)*((1637/10000 : ℝ)+(10311/100000 : ℝ)))^(4683/1024 : ℝ) := by
    rw [show (60580726219080485021/60590000000000000000 : ℝ)+(244594997461/302950000000000 : ℝ)*((1637/10000 : ℝ)+(10311/100000 : ℝ))=(10000623584310117/10000000000000000 : ℝ) by norm_num, show 1+(5089607116699749/20000000000000000000 : ℝ)+(3073162549345201/100000000000000000000 : ℝ)=(50014260599066421973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5089607116699749/20000000000000000000 : ℝ) ≤ ((60580726219080485021/60590000000000000000 : ℝ)+2*(244594997461/302950000000000 : ℝ)*(1637/10000 : ℝ))^(4683/1024 : ℝ) := by
    rw [show (60580726219080485021/60590000000000000000 : ℝ)+2*(244594997461/302950000000000 : ℝ)*(1637/10000 : ℝ)=(10001112774305039/10000000000000000 : ℝ) by norm_num, show 1+2*(5089607116699749/20000000000000000000 : ℝ)=(10005089607116699749/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (60580726219080485021/60590000000000000000 : ℝ)*(X 1 0+X 2 0)+(244594997461/302950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10311/100000 : ℝ)) (hi := (1637/10000 : ℝ)) (c := (60580726219080485021/60590000000000000000 : ℝ)) (alpha := (244594997461/302950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (60580726219080485021/60590000000000000000 : ℝ)*(X 0 1+X 2 1)+(244594997461/302950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10311/100000 : ℝ)) (hi := (1637/10000 : ℝ)) (c := (60580726219080485021/60590000000000000000 : ℝ)) (alpha := (244594997461/302950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (60580726219080485021/60590000000000000000 : ℝ)*(X 0 2+X 1 2)+(244594997461/302950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4683/1024 : ℝ)) (lo := (10311/100000 : ℝ)) (hi := (1637/10000 : ℝ)) (c := (60580726219080485021/60590000000000000000 : ℝ)) (alpha := (244594997461/302950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1469808173/10000000000 : ℝ)*X 0 0+(2711370787/5000000000 : ℝ)*X 0 1+(216909671/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250825149/10000000000 : ℝ)*X 1 0+(-855504317/5000000000 : ℝ)*X 1 1+(5422741719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5250825331/10000000000 : ℝ)*X 2 0+(43381933/80000000 : ℝ)*X 2 1+(-1711008517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1127291021/2500000000 : ℝ)*X 0 0+(4099970113/10000000000 : ℝ)*X 0 1+(2049985107/5000000000 : ℝ)*X 0 2+(1127291021/2500000000 : ℝ)*X 1 0+(4099970113/10000000000 : ℝ)*X 1 1+(2049985107/5000000000 : ℝ)*X 1 2+(1127291021/2500000000 : ℝ)*X 2 0+(4099970113/10000000000 : ℝ)*X 2 1+(2049985107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2042328589/10000000000 : ℝ)*X 0 0+(325807251/625000000 : ℝ)*X 0 1+(5212916513/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1349003843/2500000000 : ℝ)*X 1 0+(-359813233/2000000000 : ℝ)*X 1 1+(1303229171/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2698008193/5000000000 : ℝ)*X 2 0+(5212915521/10000000000 : ℝ)*X 2 1+(-1799066351/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1970272871/5000000000 : ℝ)*X 0 0+(4383925727/10000000000 : ℝ)*X 0 1+(547990801/1250000000 : ℝ)*X 0 2+(1970272871/5000000000 : ℝ)*X 1 0+(4383925727/10000000000 : ℝ)*X 1 1+(547990801/1250000000 : ℝ)*X 1 2+(1970272871/5000000000 : ℝ)*X 2 0+(4383925727/10000000000 : ℝ)*X 2 1+(547990801/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-60025787/312500000 : ℝ)*X 0 0+(1012702857/2000000000 : ℝ)*X 0 1+(5452901611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((261497419/500000000 : ℝ)*X 1 0+(-212234003/1250000000 : ℝ)*X 1 1+(2726450887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1045989671/2000000000 : ℝ)*X 2 0+(2726450959/5000000000 : ℝ)*X 2 1+(-84893593/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((114712241/250000000 : ℝ)*X 0 0+(1014770437/2500000000 : ℝ)*X 0 1+(4059081361/10000000000 : ℝ)*X 0 2+(114712241/250000000 : ℝ)*X 1 0+(1014770437/2500000000 : ℝ)*X 1 1+(4059081361/10000000000 : ℝ)*X 1 2+(114712241/250000000 : ℝ)*X 2 0+(1014770437/2500000000 : ℝ)*X 2 1+(4059081361/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1590376613/10000000000 : ℝ)*X 0 0+(86967021/156250000 : ℝ)*X 0 1+(5193051067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2704883353/5000000000 : ℝ)*X 1 0+(-112943271/625000000 : ℝ)*X 1 1+(2596525693/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5409767041/10000000000 : ℝ)*X 2 0+(649131371/1250000000 : ℝ)*X 2 1+(-1807092441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((242818291/625000000 : ℝ)*X 0 0+(176430507/400000000 : ℝ)*X 0 1+(275672621/625000000 : ℝ)*X 0 2+(242818291/625000000 : ℝ)*X 1 0+(176430507/400000000 : ℝ)*X 1 1+(275672621/625000000 : ℝ)*X 1 2+(242818291/625000000 : ℝ)*X 2 0+(176430507/400000000 : ℝ)*X 2 1+(275672621/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1592_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-32433/50000 : ℝ) ≤ (-672957373030478490874941238377/1037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1916219/10000000000000 : ℝ)*(lower2) + (17680343/25000000000000 : ℝ)*(lower3) + (41237659/50000000000000 : ℝ)*(upper5) + (41154729675111/2500000000000 : ℝ)*(major0) + (41154729675111/2500000000000 : ℝ)*(major1) + (41154729675111/2500000000000 : ℝ)*(major2) + (60998711/625000000000 : ℝ)*(sp2) + (862641961/100000000000000 : ℝ)*(sp3) + (1172712581399867/50000000000000 : ℝ)*(sp4) + (1172684686487813/50000000000000 : ℝ)*(sp5) + (2345415578998807/100000000000000 : ℝ)*(sp6) + (242143323248249/25000000000000 : ℝ)*(sp7) + (175992833/100000000000000 : ℝ)*(sp12) + (55965816941/100000000000000 : ℝ)*(sp13) + (242143538908739/25000000000000 : ℝ)*(f.failure) + (2345425338792567/100000000000000 : ℝ)*(f.sum) + (93828458651/83000000000000000000000000 : ℝ)*base66 + (13694195507955653/2075000000000000000000000000000 : ℝ)*base68 + (23243900350505653/2075000000000000000000000000000 : ℝ)*base70 + (13338768743430653/2075000000000000000000000000000 : ℝ)*base72 + (37374614069/16600000000000000000000000 : ℝ)*base74 + (18486888268780653/2075000000000000000000000000000 : ℝ)*base76 + (12509384694730653/2075000000000000000000000000000 : ℝ)*base78 + (17499397221280653/2075000000000000000000000000000 : ℝ)*base80 + (382348829303/83000000000000000000000000 : ℝ)*base82 + (1761877/2500000000000000000000 : ℝ)*base90 + (1761877/2500000000000000000000 : ℝ)*base92 + (1761877/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (57999/100000 : ℝ) ≤ (878581987653340637444300267053047/1514750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1844519/5000000000000 : ℝ)*(lower3) + (28316769/100000000000000 : ℝ)*(upper4) + (11247907/100000000000000 : ℝ)*(upper5) + (864235859930031/50000000000000 : ℝ)*(major0) + (864235859930031/50000000000000 : ℝ)*(major1) + (864235859930031/50000000000000 : ℝ)*(major2) + (30257780978927/1250000000000 : ℝ)*(sp0) + (605155341228473/25000000000000 : ℝ)*(sp1) + (2420622448910051/100000000000000 : ℝ)*(sp2) + (1016986449773739/100000000000000 : ℝ)*(sp3) + (1127007319/100000000000000 : ℝ)*(sp5) + (43011161/100000000000000 : ℝ)*(sp6) + (1783769/312500000000 : ℝ)*(sp7) + (13607051/100000000000000 : ℝ)*(sp12) + (1016987020579819/100000000000000 : ℝ)*(f.failure) + (605155622980303/25000000000000 : ℝ)*(f.sum) + (185339541365271/30295000000000000000000000000 : ℝ)*base66 + (11806649203857265651/3029500000000000000000000000000000 : ℝ)*base67 + (31779103124873265651/3029500000000000000000000000000000 : ℝ)*base69 + (4222871425992234349/3029500000000000000000000000000000 : ℝ)*base72 + (23526567594629/7573750000000000000000000000 : ℝ)*base74 + (21248672831626765651/3029500000000000000000000000000000 : ℝ)*base75 + (6206007728296734349/3029500000000000000000000000000000 : ℝ)*base78 + (14343399901883265651/3029500000000000000000000000000000 : ℝ)*base79 + (17606032013413/3786875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10289683/10000000000000000000000 : ℝ)*base89 + (10289683/10000000000000000000000 : ℝ)*base91 + (10289683/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40033/50000 : ℝ) ≤ (194053820969396948841934479/242360000000000000000000000 : ℝ) := by norm_num
    linear_combination (340101/100000000000000 : ℝ)*(upper1) + (13353621/50000000000000 : ℝ)*(upper3) + (1998689/4000000000000 : ℝ)*(upper4) + (8171669/100000000000000 : ℝ)*(lower5) + (91909113339129/5000000000000 : ℝ)*(major0) + (91909113339129/5000000000000 : ℝ)*(major1) + (91909113339129/5000000000000 : ℝ)*(major2) + (513709183/10000000000000 : ℝ)*(sp1) + (32146493233/100000000000000 : ℝ)*(sp2) + (4078376701/50000000000000 : ℝ)*(sp3) + (32101715715987/1250000000000 : ℝ)*(sp8) + (256813212018713/10000000000000 : ℝ)*(sp9) + (2568105110785727/100000000000000 : ℝ)*(sp10) + (1081529646439133/100000000000000 : ℝ)*(sp11) + (216307560638507/20000000000000 : ℝ)*(f.failure) + (32101715715987/1250000000000 : ℝ)*(f.sum) + (751450926403/151475000000000000000000000 : ℝ)*base65 + (138373305066986709/302950000000000000000000000000000 : ℝ)*base67 + (1275042977001463291/302950000000000000000000000000000 : ℝ)*base70 + (1079391915095386709/302950000000000000000000000000000 : ℝ)*base71 + (4460182672561/3029500000000000000000000000 : ℝ)*base73 + (1511000395500036709/302950000000000000000000000000000 : ℝ)*base75 + (983949681111713291/302950000000000000000000000000000 : ℝ)*base78 + (293422666245463291/302950000000000000000000000000000 : ℝ)*base80 + (1540575593157/378687500000000000000000000 : ℝ)*base81 + (6114899/2000000000000000000000 : ℝ)*base89 + (6114899/2000000000000000000000 : ℝ)*base91 + (6114899/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-43819/50000 : ℝ) ≤ (-663726349621894936710468528636387/757375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48822637/100000000000000 : ℝ)*(lower0) + (17108083/50000000000000 : ℝ)*(lower2) + (3572543/12500000000000 : ℝ)*(upper3) + (939667395214149/50000000000000 : ℝ)*(major0) + (939667395214149/50000000000000 : ℝ)*(major1) + (939667395214149/50000000000000 : ℝ)*(major2) + (884794751/100000000000000 : ℝ)*(sp0) + (10115009783/25000000000000 : ℝ)*(sp6) + (34550217/625000000000 : ℝ)*(sp7) + (1410684099/100000000000000 : ℝ)*(sp8) + (1341064063373819/50000000000000 : ℝ)*(sp12) + (335266302778311/12500000000000 : ℝ)*(sp13) + (670522490546839/25000000000000 : ℝ)*(sp14) + (110574533107937/10000000000000 : ℝ)*(sp15) + (110575085911409/10000000000000 : ℝ)*(f.failure) + (335266302778311/12500000000000 : ℝ)*(f.sum) + (205981370523291/30295000000000000000000000000 : ℝ)*base65 + (18570611749665062129/3029500000000000000000000000000000 : ℝ)*base67 + (20667860713189562129/3029500000000000000000000000000000 : ℝ)*base69 + (17772582262323562129/3029500000000000000000000000000000 : ℝ)*base71 + (20211967911367/15147500000000000000000000000 : ℝ)*base74 + (16544480644003562129/3029500000000000000000000000000000 : ℝ)*base75 + (41841226562733562129/3029500000000000000000000000000000 : ℝ)*base77 + (1449616692595437871/3029500000000000000000000000000000 : ℝ)*base80 + (19680343832729/7573750000000000000000000000 : ℝ)*base81 + (9409687/1000000000000000000000 : ℝ)*base90 + (9409687/1000000000000000000000 : ℝ)*base92 + (9409687/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1592_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57999/100000 : ℝ) else (40033/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43819/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1592_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1592_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57999/100000 : ℝ) else (40033/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43819/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1592_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4683/1024 : ℝ) ≤ p) (hpb : p ≤ (4687/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169960057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1637/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10311/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(32433/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(57999/100000 : ℝ) else (40033/50000 : ℝ) ≤ X j i ∧ X j i ≤ (43819/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1592_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
