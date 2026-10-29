-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1479_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:34.652082+00:00
-- url     : https://prove2.me/submissions/7748fad8-3171-405c-8b47-b087867bdc87

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
theorem support_rectangle_w1479_s0_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53793779/312500000 : ℝ)*x 0 + (2969346601/5000000000 : ℝ)*x 1 + (4840950333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53793779/312500000 : ℝ)^4455 ≤ (5090928643719/50000000000000 : ℝ)^3431 := by
    have hnat : (53793779 : ℕ)^4455*50000000000000^3431 ≤ 5090928643719^3431*312500000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53793779 312500000 5090928643719 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2969346601/5000000000 : ℝ)^4455 ≤ (50833234586609/100000000000000 : ℝ)^3431 := by
    have hnat : (2969346601 : ℕ)^4455*100000000000000^3431 ≤ 50833234586609^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2969346601 5000000000 50833234586609 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4840950333/10000000000 : ℝ)^4455 ≤ (19492454058299/50000000000000 : ℝ)^3431 := by
    have hnat : (4840950333 : ℕ)^4455*50000000000000^3431 ≤ 19492454058299^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840950333 10000000000 19492454058299 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53793779/312500000 : ℝ), (2969346601/5000000000 : ℝ), (4840950333/10000000000 : ℝ)] ![(5090928643719/50000000000000 : ℝ), (50833234586609/100000000000000 : ℝ), (19492454058299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53793779/312500000 : ℝ)|^4455 ≤ (5090928643719/50000000000000 : ℝ)^3431
        have hw : |(-53793779/312500000 : ℝ)|=(53793779/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2969346601/5000000000 : ℝ)|^4455 ≤ (50833234586609/100000000000000 : ℝ)^3431
        have hw : |(2969346601/5000000000 : ℝ)|=(2969346601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4840950333/10000000000 : ℝ)|^4455 ≤ (19492454058299/50000000000000 : ℝ)^3431
        have hw : |(4840950333/10000000000 : ℝ)|=(4840950333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s0_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5485195351/10000000000 : ℝ)*x 0 + (-467875459/2000000000 : ℝ)*x 1 + (2420475163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5485195351/10000000000 : ℝ)^4455 ≤ (4585140089667/10000000000000 : ℝ)^3431 := by
    have hnat : (5485195351 : ℕ)^4455*10000000000000^3431 ≤ 4585140089667^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5485195351 10000000000 4585140089667 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467875459/2000000000 : ℝ)^4455 ≤ (7581845521333/50000000000000 : ℝ)^3431 := by
    have hnat : (467875459 : ℕ)^4455*50000000000000^3431 ≤ 7581845521333^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467875459 2000000000 7581845521333 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2420475163/5000000000 : ℝ)^4455 ≤ (38984908043401/100000000000000 : ℝ)^3431 := by
    have hnat : (2420475163 : ℕ)^4455*100000000000000^3431 ≤ 38984908043401^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420475163 5000000000 38984908043401 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5485195351/10000000000 : ℝ), (-467875459/2000000000 : ℝ), (2420475163/5000000000 : ℝ)] ![(4585140089667/10000000000000 : ℝ), (7581845521333/50000000000000 : ℝ), (38984908043401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5485195351/10000000000 : ℝ)|^4455 ≤ (4585140089667/10000000000000 : ℝ)^3431
        have hw : |(5485195351/10000000000 : ℝ)|=(5485195351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-467875459/2000000000 : ℝ)|^4455 ≤ (7581845521333/50000000000000 : ℝ)^3431
        have hw : |(-467875459/2000000000 : ℝ)|=(467875459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2420475163/5000000000 : ℝ)|^4455 ≤ (38984908043401/100000000000000 : ℝ)^3431
        have hw : |(2420475163/5000000000 : ℝ)|=(2420475163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s0_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1097039107/2000000000 : ℝ)*x 0 + (4840950159/10000000000 : ℝ)*x 1 + (-467875453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097039107/2000000000 : ℝ)^4455 ≤ (9170280578759/20000000000000 : ℝ)^3431 := by
    have hnat : (1097039107 : ℕ)^4455*20000000000000^3431 ≤ 9170280578759^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097039107 2000000000 9170280578759 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4840950159/10000000000 : ℝ)^4455 ≤ (38984906297139/100000000000000 : ℝ)^3431 := by
    have hnat : (4840950159 : ℕ)^4455*100000000000000^3431 ≤ 38984906297139^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4840950159 10000000000 38984906297139 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467875453/2000000000 : ℝ)^4455 ≤ (15163690790171/100000000000000 : ℝ)^3431 := by
    have hnat : (467875453 : ℕ)^4455*100000000000000^3431 ≤ 15163690790171^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467875453 2000000000 15163690790171 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097039107/2000000000 : ℝ), (4840950159/10000000000 : ℝ), (-467875453/2000000000 : ℝ)] ![(9170280578759/20000000000000 : ℝ), (38984906297139/100000000000000 : ℝ), (15163690790171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097039107/2000000000 : ℝ)|^4455 ≤ (9170280578759/20000000000000 : ℝ)^3431
        have hw : |(1097039107/2000000000 : ℝ)|=(1097039107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4840950159/10000000000 : ℝ)|^4455 ≤ (38984906297139/100000000000000 : ℝ)^3431
        have hw : |(4840950159/10000000000 : ℝ)|=(4840950159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467875453/2000000000 : ℝ)|^4455 ≤ (15163690790171/100000000000000 : ℝ)^3431
        have hw : |(-467875453/2000000000 : ℝ)|=(467875453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s0_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4154164723/10000000000 : ℝ)*x 0 + (386437741/1250000000 : ℝ)*x 1 + (5522955297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154164723/10000000000 : ℝ)^4455 ≤ (31960838938233/100000000000000 : ℝ)^3431 := by
    have hnat : (4154164723 : ℕ)^4455*100000000000000^3431 ≤ 31960838938233^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154164723 10000000000 31960838938233 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386437741/1250000000 : ℝ)^4455 ≤ (21777495530597/100000000000000 : ℝ)^3431 := by
    have hnat : (386437741 : ℕ)^4455*100000000000000^3431 ≤ 21777495530597^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386437741 1250000000 21777495530597 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5522955297/10000000000 : ℝ)^4455 ≤ (23130832756363/50000000000000 : ℝ)^3431 := by
    have hnat : (5522955297 : ℕ)^4455*50000000000000^3431 ≤ 23130832756363^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522955297 10000000000 23130832756363 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154164723/10000000000 : ℝ), (386437741/1250000000 : ℝ), (5522955297/10000000000 : ℝ)] ![(31960838938233/100000000000000 : ℝ), (21777495530597/100000000000000 : ℝ), (23130832756363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154164723/10000000000 : ℝ)|^4455 ≤ (31960838938233/100000000000000 : ℝ)^3431
        have hw : |(4154164723/10000000000 : ℝ)|=(4154164723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386437741/1250000000 : ℝ)|^4455 ≤ (21777495530597/100000000000000 : ℝ)^3431
        have hw : |(386437741/1250000000 : ℝ)|=(386437741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5522955297/10000000000 : ℝ)|^4455 ≤ (23130832756363/50000000000000 : ℝ)^3431
        have hw : |(5522955297/10000000000 : ℝ)|=(5522955297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s0_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-862606847/5000000000 : ℝ)*x 0 + (4869117061/10000000000 : ℝ)*x 1 + (2954756639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862606847/5000000000 : ℝ)^4455 ≤ (319098429013/3125000000000 : ℝ)^3431 := by
    have hnat : (862606847 : ℕ)^4455*3125000000000^3431 ≤ 319098429013^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862606847 5000000000 319098429013 3125000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4869117061/10000000000 : ℝ)^4455 ≤ (9819923331331/25000000000000 : ℝ)^3431 := by
    have hnat : (4869117061 : ℕ)^4455*25000000000000^3431 ≤ 9819923331331^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4869117061 10000000000 9819923331331 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2954756639/5000000000 : ℝ)^4455 ≤ (25254578469007/50000000000000 : ℝ)^3431 := by
    have hnat : (2954756639 : ℕ)^4455*50000000000000^3431 ≤ 25254578469007^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2954756639 5000000000 25254578469007 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-862606847/5000000000 : ℝ), (4869117061/10000000000 : ℝ), (2954756639/5000000000 : ℝ)] ![(319098429013/3125000000000 : ℝ), (9819923331331/25000000000000 : ℝ), (25254578469007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-862606847/5000000000 : ℝ)|^4455 ≤ (319098429013/3125000000000 : ℝ)^3431
        have hw : |(-862606847/5000000000 : ℝ)|=(862606847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4869117061/10000000000 : ℝ)|^4455 ≤ (9819923331331/25000000000000 : ℝ)^3431
        have hw : |(4869117061/10000000000 : ℝ)|=(4869117061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2954756639/5000000000 : ℝ)|^4455 ≤ (25254578469007/50000000000000 : ℝ)^3431
        have hw : |(2954756639/5000000000 : ℝ)|=(2954756639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s0_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185467889/10000000000 : ℝ)*x 0 + (-79425889/625000000 : ℝ)*x 1 + (5909513271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185467889/10000000000 : ℝ)^4455 ≤ (42625051059267/100000000000000 : ℝ)^3431 := by
    have hnat : (5185467889 : ℕ)^4455*100000000000000^3431 ≤ 42625051059267^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185467889 10000000000 42625051059267 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79425889/625000000 : ℝ)^4455 ≤ (214556002237/3125000000000 : ℝ)^3431 := by
    have hnat : (79425889 : ℕ)^4455*3125000000000^3431 ≤ 214556002237^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79425889 625000000 214556002237 3125000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5909513271/10000000000 : ℝ)^4455 ≤ (6313644607541/12500000000000 : ℝ)^3431 := by
    have hnat : (5909513271 : ℕ)^4455*12500000000000^3431 ≤ 6313644607541^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5909513271 10000000000 6313644607541 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185467889/10000000000 : ℝ), (-79425889/625000000 : ℝ), (5909513271/10000000000 : ℝ)] ![(42625051059267/100000000000000 : ℝ), (214556002237/3125000000000 : ℝ), (6313644607541/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185467889/10000000000 : ℝ)|^4455 ≤ (42625051059267/100000000000000 : ℝ)^3431
        have hw : |(5185467889/10000000000 : ℝ)|=(5185467889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79425889/625000000 : ℝ)|^4455 ≤ (214556002237/3125000000000 : ℝ)^3431
        have hw : |(-79425889/625000000 : ℝ)|=(79425889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5909513271/10000000000 : ℝ)|^4455 ≤ (6313644607541/12500000000000 : ℝ)^3431
        have hw : |(5909513271/10000000000 : ℝ)|=(5909513271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s0_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185467783/10000000000 : ℝ)*x 0 + (1477378313/2500000000 : ℝ)*x 1 + (-635407207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185467783/10000000000 : ℝ)^4455 ≤ (10656262481971/25000000000000 : ℝ)^3431 := by
    have hnat : (5185467783 : ℕ)^4455*25000000000000^3431 ≤ 10656262481971^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185467783 10000000000 10656262481971 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477378313/2500000000 : ℝ)^4455 ≤ (25254578324733/50000000000000 : ℝ)^3431 := by
    have hnat : (1477378313 : ℕ)^4455*50000000000000^3431 ≤ 25254578324733^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477378313 2500000000 25254578324733 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635407207/5000000000 : ℝ)^4455 ≤ (3432896702229/50000000000000 : ℝ)^3431 := by
    have hnat : (635407207 : ℕ)^4455*50000000000000^3431 ≤ 3432896702229^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635407207 5000000000 3432896702229 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185467783/10000000000 : ℝ), (1477378313/2500000000 : ℝ), (-635407207/5000000000 : ℝ)] ![(10656262481971/25000000000000 : ℝ), (25254578324733/50000000000000 : ℝ), (3432896702229/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185467783/10000000000 : ℝ)|^4455 ≤ (10656262481971/25000000000000 : ℝ)^3431
        have hw : |(5185467783/10000000000 : ℝ)|=(5185467783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1477378313/2500000000 : ℝ)|^4455 ≤ (25254578324733/50000000000000 : ℝ)^3431
        have hw : |(1477378313/2500000000 : ℝ)|=(1477378313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-635407207/5000000000 : ℝ)|^4455 ≤ (3432896702229/50000000000000 : ℝ)^3431
        have hw : |(-635407207/5000000000 : ℝ)|=(635407207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s0_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166504377/400000000 : ℝ)*x 0 + (1365141813/2500000000 : ℝ)*x 1 + (394516791/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166504377/400000000 : ℝ)^4455 ≤ (1001413322051/3125000000000 : ℝ)^3431 := by
    have hnat : (166504377 : ℕ)^4455*3125000000000^3431 ≤ 1001413322051^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166504377 400000000 1001413322051 3125000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365141813/2500000000 : ℝ)^4455 ≤ (45584268229131/100000000000000 : ℝ)^3431 := by
    have hnat : (1365141813 : ℕ)^4455*100000000000000^3431 ≤ 45584268229131^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365141813 2500000000 45584268229131 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394516791/1250000000 : ℝ)^4455 ≤ (22370505442151/100000000000000 : ℝ)^3431 := by
    have hnat : (394516791 : ℕ)^4455*100000000000000^3431 ≤ 22370505442151^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394516791 1250000000 22370505442151 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166504377/400000000 : ℝ), (1365141813/2500000000 : ℝ), (394516791/1250000000 : ℝ)] ![(1001413322051/3125000000000 : ℝ), (45584268229131/100000000000000 : ℝ), (22370505442151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166504377/400000000 : ℝ)|^4455 ≤ (1001413322051/3125000000000 : ℝ)^3431
        have hw : |(166504377/400000000 : ℝ)|=(166504377/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365141813/2500000000 : ℝ)|^4455 ≤ (45584268229131/100000000000000 : ℝ)^3431
        have hw : |(1365141813/2500000000 : ℝ)|=(1365141813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(394516791/1250000000 : ℝ)|^4455 ≤ (22370505442151/100000000000000 : ℝ)^3431
        have hw : |(394516791/1250000000 : ℝ)|=(394516791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (299/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12959/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4453/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4453 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4453*1^1024 ≤ 0^1024*1^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4453/1024 : ℝ) ≤ (464991516545493849/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4453 ≤ (464991516545493849/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4453*25000000000000000000^1024 ≤ 464991516545493849^1024*5^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 464991516545493849 25000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (464991516545493849/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4453 := by
      have hnat : (1 : ℕ)^1024*1^4453 ≤ 1^4453*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25464991516545493849/25000000000000000000 : ℝ) ≤ (2008493661104101/2000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (25464991516545493849/25000000000000000000 : ℝ)^1024 ≤ (2008493661104101/2000000000000000 : ℝ)^4453 := by
      have hnat : (25464991516545493849 : ℕ)^1024*2000000000000000^4453 ≤ 2008493661104101^4453*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25464991516545493849 25000000000000000000 2008493661104101 2000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2008493661104101/2000000000000000 : ℝ)) (X := (25464991516545493849/25000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12964991516545493849/12500000000000000000 : ℝ) ≤ (1008493661104101/1000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (12964991516545493849/12500000000000000000 : ℝ)^1024 ≤ (1008493661104101/1000000000000000 : ℝ)^4453 := by
      have hnat : (12964991516545493849 : ℕ)^1024*1000000000000000^4453 ≤ 1008493661104101^4453*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12964991516545493849 12500000000000000000 1008493661104101 1000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1008493661104101/1000000000000000 : ℝ)) (X := (12964991516545493849/12500000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8493661104101/800000000000000 : ℝ)*(0 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8493661104101/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(464991516545493849/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8493661104101/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8493661104101/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2008493661104101/2000000000000000 : ℝ) by norm_num, show 1+(464991516545493849/25000000000000000000 : ℝ)+(0 : ℝ)=(25464991516545493849/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(464991516545493849/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8493661104101/800000000000000 : ℝ)*(2/5 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8493661104101/800000000000000 : ℝ)*(2/5 : ℝ)=(1008493661104101/1000000000000000 : ℝ) by norm_num, show 1+2*(464991516545493849/25000000000000000000 : ℝ)=(12964991516545493849/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8493661104101/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8493661104101/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8493661104101/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8493661104101/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8493661104101/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8493661104101/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53793779/312500000 : ℝ)*X 0 0+(2969346601/5000000000 : ℝ)*X 0 1+(4840950333/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5485195351/10000000000 : ℝ)*X 1 0+(-467875459/2000000000 : ℝ)*X 1 1+(2420475163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1097039107/2000000000 : ℝ)*X 2 0+(4840950159/10000000000 : ℝ)*X 2 1+(-467875453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4154164723/10000000000 : ℝ)*X 0 0+(386437741/1250000000 : ℝ)*X 0 1+(5522955297/10000000000 : ℝ)*X 0 2+(4154164723/10000000000 : ℝ)*X 1 0+(386437741/1250000000 : ℝ)*X 1 1+(5522955297/10000000000 : ℝ)*X 1 2+(4154164723/10000000000 : ℝ)*X 2 0+(386437741/1250000000 : ℝ)*X 2 1+(5522955297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-862606847/5000000000 : ℝ)*X 0 0+(4869117061/10000000000 : ℝ)*X 0 1+(2954756639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5185467889/10000000000 : ℝ)*X 1 0+(-79425889/625000000 : ℝ)*X 1 1+(5909513271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185467783/10000000000 : ℝ)*X 2 0+(1477378313/2500000000 : ℝ)*X 2 1+(-635407207/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((166504377/400000000 : ℝ)*X 0 0+(1365141813/2500000000 : ℝ)*X 0 1+(394516791/1250000000 : ℝ)*X 0 2+(166504377/400000000 : ℝ)*X 1 0+(1365141813/2500000000 : ℝ)*X 1 1+(394516791/1250000000 : ℝ)*X 1 2+(166504377/400000000 : ℝ)*X 2 0+(1365141813/2500000000 : ℝ)*X 2 1+(394516791/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135923796443553346606611/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57581619/50000000000000 : ℝ)*(base1) + (772936751/50000000000000 : ℝ)*(base19) + (1576431797/100000000000000 : ℝ)*(base23) + (177744339/100000000000000 : ℝ)*(upper3) + (195133747/100000000000000 : ℝ)*(upper5) + (330562900663837/50000000000000 : ℝ)*(major0) + (330562900663837/50000000000000 : ℝ)*(major1) + (330562900663837/50000000000000 : ℝ)*(major2) + (910964985769769/100000000000000 : ℝ)*(sp0) + (910968597158507/100000000000000 : ℝ)*(sp1) + (227742141650053/25000000000000 : ℝ)*(sp2) + (82255768138351/20000000000000 : ℝ)*(sp3) + (5272425477/100000000000000 : ℝ)*(sp4) + (1138614339/50000000000000 : ℝ)*(sp7) + (41128123308367/10000000000000 : ℝ)*(f.failure) + (910970143032009/100000000000000 : ℝ)*(f.sum) + (20945163804463/20000000000000000000000000000 : ℝ)*base66 + (9062065855537/40000000000000000000000000000 : ℝ)*base67 + (40471211015537/40000000000000000000000000000 : ℝ)*base69 + (120257264215537/40000000000000000000000000000 : ℝ)*base71 + (105967895524463/20000000000000000000000000000 : ℝ)*base74 + (39012947055537/40000000000000000000000000000 : ℝ)*base75 + (176819165695537/40000000000000000000000000000 : ℝ)*base77 + (53404345064463/40000000000000000000000000000 : ℝ)*base80 + (94367825684463/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1622709/200000000000000000000 : ℝ)*base90 + (1622709/200000000000000000000 : ℝ)*base92 + (1622709/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57979625169245143880781/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (679141561/100000000000000 : ℝ)*(base19) + (65687411/10000000000000 : ℝ)*(base23) + (69998979/100000000000000 : ℝ)*(base32) + (95131487/100000000000000 : ℝ)*(upper3) + (28947917/50000000000000 : ℝ)*(upper5) + (348779542396227/50000000000000 : ℝ)*(major0) + (348779542396227/50000000000000 : ℝ)*(major1) + (348779542396227/50000000000000 : ℝ)*(major2) + (1703200053/100000000000000 : ℝ)*(sp1) + (414470163/25000000000000 : ℝ)*(sp2) + (961171976814337/100000000000000 : ℝ)*(sp4) + (961169594472723/100000000000000 : ℝ)*(sp5) + (120146207757447/12500000000000 : ℝ)*(sp6) + (433946026138879/100000000000000 : ℝ)*(sp7) + (216973048068929/50000000000000 : ℝ)*(f.failure) + (961171976814337/100000000000000 : ℝ)*(f.sum) + (8968037313073/20000000000000000000000000000 : ℝ)*base66 + (36539725973073/40000000000000000000000000000 : ℝ)*base68 + (139024163293073/40000000000000000000000000000 : ℝ)*base70 + (33928839626927/40000000000000000000000000000 : ℝ)*base71 + (25520398206927/20000000000000000000000000000 : ℝ)*base73 + (298516464293073/40000000000000000000000000000 : ℝ)*base76 + (331930499493073/40000000000000000000000000000 : ℝ)*base78 + (323412576493073/40000000000000000000000000000 : ℝ)*base80 + (22407375266927/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1917317/1000000000000000000000 : ℝ)*base89 + (1917317/1000000000000000000000 : ℝ)*base91 + (1917317/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1479_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (299/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12959/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1479_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1479_s1_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117755301/625000000 : ℝ)*x 0 + (2796730081/5000000000 : ℝ)*x 1 + (1270441307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117755301/625000000 : ℝ)^4455 ≤ (5724273417607/50000000000000 : ℝ)^3431 := by
    have hnat : (117755301 : ℕ)^4455*50000000000000^3431 ≤ 5724273417607^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117755301 625000000 5724273417607 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796730081/5000000000 : ℝ)^4455 ≤ (23514973092221/50000000000000 : ℝ)^3431 := by
    have hnat : (2796730081 : ℕ)^4455*50000000000000^3431 ≤ 23514973092221^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796730081 5000000000 23514973092221 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1270441307/2500000000 : ℝ)^4455 ≤ (162193386561/390625000000 : ℝ)^3431 := by
    have hnat : (1270441307 : ℕ)^4455*390625000000^3431 ≤ 162193386561^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270441307 2500000000 162193386561 390625000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117755301/625000000 : ℝ), (2796730081/5000000000 : ℝ), (1270441307/2500000000 : ℝ)] ![(5724273417607/50000000000000 : ℝ), (23514973092221/50000000000000 : ℝ), (162193386561/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117755301/625000000 : ℝ)|^4455 ≤ (5724273417607/50000000000000 : ℝ)^3431
        have hw : |(-117755301/625000000 : ℝ)|=(117755301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796730081/5000000000 : ℝ)|^4455 ≤ (23514973092221/50000000000000 : ℝ)^3431
        have hw : |(2796730081/5000000000 : ℝ)|=(2796730081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1270441307/2500000000 : ℝ)|^4455 ≤ (162193386561/390625000000 : ℝ)^3431
        have hw : |(1270441307/2500000000 : ℝ)|=(1270441307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s1_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392751521/10000000000 : ℝ)*x 0 + (-2154690219/10000000000 : ℝ)*x 1 + (5081765611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392751521/10000000000 : ℝ)^4455 ≤ (11212638604989/25000000000000 : ℝ)^3431 := by
    have hnat : (5392751521 : ℕ)^4455*25000000000000^3431 ≤ 11212638604989^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392751521 10000000000 11212638604989 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154690219/10000000000 : ℝ)^4455 ≤ (3406983635021/25000000000000 : ℝ)^3431 := by
    have hnat : (2154690219 : ℕ)^4455*25000000000000^3431 ≤ 3406983635021^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154690219 10000000000 3406983635021 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5081765611/10000000000 : ℝ)^4455 ≤ (20760755511483/50000000000000 : ℝ)^3431 := by
    have hnat : (5081765611 : ℕ)^4455*50000000000000^3431 ≤ 20760755511483^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5081765611 10000000000 20760755511483 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392751521/10000000000 : ℝ), (-2154690219/10000000000 : ℝ), (5081765611/10000000000 : ℝ)] ![(11212638604989/25000000000000 : ℝ), (3406983635021/25000000000000 : ℝ), (20760755511483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392751521/10000000000 : ℝ)|^4455 ≤ (11212638604989/25000000000000 : ℝ)^3431
        have hw : |(5392751521/10000000000 : ℝ)|=(5392751521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2154690219/10000000000 : ℝ)|^4455 ≤ (3406983635021/25000000000000 : ℝ)^3431
        have hw : |(-2154690219/10000000000 : ℝ)|=(2154690219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5081765611/10000000000 : ℝ)|^4455 ≤ (20760755511483/50000000000000 : ℝ)^3431
        have hw : |(5081765611/10000000000 : ℝ)|=(5081765611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s1_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392752011/10000000000 : ℝ)*x 0 + (635220663/1250000000 : ℝ)*x 1 + (-2154689971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392752011/10000000000 : ℝ)^4455 ≤ (44850559711477/100000000000000 : ℝ)^3431 := by
    have hnat : (5392752011 : ℕ)^4455*100000000000000^3431 ≤ 44850559711477^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392752011 10000000000 44850559711477 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635220663/1250000000 : ℝ)^4455 ≤ (259509423537/625000000000 : ℝ)^3431 := by
    have hnat : (635220663 : ℕ)^4455*625000000000^3431 ≤ 259509423537^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635220663 1250000000 259509423537 625000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154689971/10000000000 : ℝ)^4455 ≤ (13627932503399/100000000000000 : ℝ)^3431 := by
    have hnat : (2154689971 : ℕ)^4455*100000000000000^3431 ≤ 13627932503399^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154689971 10000000000 13627932503399 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392752011/10000000000 : ℝ), (635220663/1250000000 : ℝ), (-2154689971/10000000000 : ℝ)] ![(44850559711477/100000000000000 : ℝ), (259509423537/625000000000 : ℝ), (13627932503399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392752011/10000000000 : ℝ)|^4455 ≤ (44850559711477/100000000000000 : ℝ)^3431
        have hw : |(5392752011/10000000000 : ℝ)|=(5392752011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635220663/1250000000 : ℝ)|^4455 ≤ (259509423537/625000000000 : ℝ)^3431
        have hw : |(635220663/1250000000 : ℝ)|=(635220663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2154689971/10000000000 : ℝ)|^4455 ≤ (13627932503399/100000000000000 : ℝ)^3431
        have hw : |(-2154689971/10000000000 : ℝ)|=(2154689971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s1_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261629453/10000000000 : ℝ)*x 0 + (232976673/625000000 : ℝ)*x 1 + (2430504527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261629453/10000000000 : ℝ)^4455 ≤ (33038521176603/100000000000000 : ℝ)^3431 := by
    have hnat : (4261629453 : ℕ)^4455*100000000000000^3431 ≤ 33038521176603^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261629453 10000000000 33038521176603 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232976673/625000000 : ℝ)^4455 ≤ (347083674329/1250000000000 : ℝ)^3431 := by
    have hnat : (232976673 : ℕ)^4455*1250000000000^3431 ≤ 347083674329^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232976673 625000000 347083674329 1250000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2430504527/5000000000 : ℝ)^4455 ≤ (4899348107201/12500000000000 : ℝ)^3431 := by
    have hnat : (2430504527 : ℕ)^4455*12500000000000^3431 ≤ 4899348107201^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430504527 5000000000 4899348107201 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261629453/10000000000 : ℝ), (232976673/625000000 : ℝ), (2430504527/5000000000 : ℝ)] ![(33038521176603/100000000000000 : ℝ), (347083674329/1250000000000 : ℝ), (4899348107201/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261629453/10000000000 : ℝ)|^4455 ≤ (33038521176603/100000000000000 : ℝ)^3431
        have hw : |(4261629453/10000000000 : ℝ)|=(4261629453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(232976673/625000000 : ℝ)|^4455 ≤ (347083674329/1250000000000 : ℝ)^3431
        have hw : |(232976673/625000000 : ℝ)|=(232976673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2430504527/5000000000 : ℝ)|^4455 ≤ (4899348107201/12500000000000 : ℝ)^3431
        have hw : |(2430504527/5000000000 : ℝ)|=(2430504527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s1_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1884456473/10000000000 : ℝ)*x 0 + (2543880493/5000000000 : ℝ)*x 1 + (5587363029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1884456473/10000000000 : ℝ)^4455 ≤ (11451479294603/100000000000000 : ℝ)^3431 := by
    have hnat : (1884456473 : ℕ)^4455*100000000000000^3431 ≤ 11451479294603^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884456473 10000000000 11451479294603 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2543880493/5000000000 : ℝ)^4455 ≤ (41585128771483/100000000000000 : ℝ)^3431 := by
    have hnat : (2543880493 : ℕ)^4455*100000000000000^3431 ≤ 41585128771483^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2543880493 5000000000 41585128771483 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5587363029/10000000000 : ℝ)^4455 ≤ (46963391914611/100000000000000 : ℝ)^3431 := by
    have hnat : (5587363029 : ℕ)^4455*100000000000000^3431 ≤ 46963391914611^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587363029 10000000000 46963391914611 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1884456473/10000000000 : ℝ), (2543880493/5000000000 : ℝ), (5587363029/10000000000 : ℝ)] ![(11451479294603/100000000000000 : ℝ), (41585128771483/100000000000000 : ℝ), (46963391914611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1884456473/10000000000 : ℝ)|^4455 ≤ (11451479294603/100000000000000 : ℝ)^3431
        have hw : |(-1884456473/10000000000 : ℝ)|=(1884456473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2543880493/5000000000 : ℝ)|^4455 ≤ (41585128771483/100000000000000 : ℝ)^3431
        have hw : |(2543880493/5000000000 : ℝ)|=(2543880493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5587363029/10000000000 : ℝ)|^4455 ≤ (46963391914611/100000000000000 : ℝ)^3431
        have hw : |(5587363029/10000000000 : ℝ)|=(5587363029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s1_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2629268209/5000000000 : ℝ)*x 0 + (-412273111/2500000000 : ℝ)*x 1 + (1117472613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2629268209/5000000000 : ℝ)^4455 ≤ (43406577354619/100000000000000 : ℝ)^3431 := by
    have hnat : (2629268209 : ℕ)^4455*100000000000000^3431 ≤ 43406577354619^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629268209 5000000000 43406577354619 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412273111/2500000000 : ℝ)^4455 ≤ (9630030322573/100000000000000 : ℝ)^3431 := by
    have hnat : (412273111 : ℕ)^4455*100000000000000^3431 ≤ 9630030322573^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412273111 2500000000 9630030322573 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117472613/2000000000 : ℝ)^4455 ≤ (46963392307511/100000000000000 : ℝ)^3431 := by
    have hnat : (1117472613 : ℕ)^4455*100000000000000^3431 ≤ 46963392307511^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117472613 2000000000 46963392307511 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2629268209/5000000000 : ℝ), (-412273111/2500000000 : ℝ), (1117472613/2000000000 : ℝ)] ![(43406577354619/100000000000000 : ℝ), (9630030322573/100000000000000 : ℝ), (46963392307511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2629268209/5000000000 : ℝ)|^4455 ≤ (43406577354619/100000000000000 : ℝ)^3431
        have hw : |(2629268209/5000000000 : ℝ)|=(2629268209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412273111/2500000000 : ℝ)|^4455 ≤ (9630030322573/100000000000000 : ℝ)^3431
        have hw : |(-412273111/2500000000 : ℝ)|=(412273111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1117472613/2000000000 : ℝ)|^4455 ≤ (46963392307511/100000000000000 : ℝ)^3431
        have hw : |(1117472613/2000000000 : ℝ)|=(1117472613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s1_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051707289/2000000000 : ℝ)*x 0 + (2793681517/5000000000 : ℝ)*x 1 + (-32981849/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051707289/2000000000 : ℝ)^4455 ≤ (5425822205501/12500000000000 : ℝ)^3431 := by
    have hnat : (1051707289 : ℕ)^4455*12500000000000^3431 ≤ 5425822205501^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051707289 2000000000 5425822205501 12500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2793681517/5000000000 : ℝ)^4455 ≤ (46963391969181/100000000000000 : ℝ)^3431 := by
    have hnat : (2793681517 : ℕ)^4455*100000000000000^3431 ≤ 46963391969181^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2793681517 5000000000 46963391969181 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32981849/200000000 : ℝ)^4455 ≤ (2407507592017/25000000000000 : ℝ)^3431 := by
    have hnat : (32981849 : ℕ)^4455*25000000000000^3431 ≤ 2407507592017^3431*200000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32981849 200000000 2407507592017 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051707289/2000000000 : ℝ), (2793681517/5000000000 : ℝ), (-32981849/200000000 : ℝ)] ![(5425822205501/12500000000000 : ℝ), (46963391969181/100000000000000 : ℝ), (2407507592017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051707289/2000000000 : ℝ)|^4455 ≤ (5425822205501/12500000000000 : ℝ)^3431
        have hw : |(1051707289/2000000000 : ℝ)|=(1051707289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2793681517/5000000000 : ℝ)|^4455 ≤ (46963391969181/100000000000000 : ℝ)^3431
        have hw : |(2793681517/5000000000 : ℝ)|=(2793681517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-32981849/200000000 : ℝ)|^4455 ≤ (2407507592017/25000000000000 : ℝ)^3431
        have hw : |(-32981849/200000000 : ℝ)|=(32981849/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s1_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065613199/2500000000 : ℝ)*x 0 + (969545837/2000000000 : ℝ)*x 1 + (1870565773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065613199/2500000000 : ℝ)^4455 ≤ (3304680947203/10000000000000 : ℝ)^3431 := by
    have hnat : (1065613199 : ℕ)^4455*10000000000000^3431 ≤ 3304680947203^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065613199 2500000000 3304680947203 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969545837/2000000000 : ℝ)^4455 ≤ (7811161411381/20000000000000 : ℝ)^3431 := by
    have hnat : (969545837 : ℕ)^4455*20000000000000^3431 ≤ 7811161411381^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969545837 2000000000 7811161411381 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870565773/5000000000 : ℝ)^4455 ≤ (27897383454691/100000000000000 : ℝ)^3431 := by
    have hnat : (1870565773 : ℕ)^4455*100000000000000^3431 ≤ 27897383454691^3431*5000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870565773 5000000000 27897383454691 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065613199/2500000000 : ℝ), (969545837/2000000000 : ℝ), (1870565773/5000000000 : ℝ)] ![(3304680947203/10000000000000 : ℝ), (7811161411381/20000000000000 : ℝ), (27897383454691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065613199/2500000000 : ℝ)|^4455 ≤ (3304680947203/10000000000000 : ℝ)^3431
        have hw : |(1065613199/2500000000 : ℝ)|=(1065613199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(969545837/2000000000 : ℝ)|^4455 ≤ (7811161411381/20000000000000 : ℝ)^3431
        have hw : |(969545837/2000000000 : ℝ)|=(969545837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870565773/5000000000 : ℝ)|^4455 ≤ (27897383454691/100000000000000 : ℝ)^3431
        have hw : |(1870565773/5000000000 : ℝ)|=(1870565773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (299/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (7891/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4677/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12959/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (299/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12959/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (299/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12959/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (299/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12959/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (299/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12959/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (299/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12959/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (299/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (299/12500 : ℝ) ^ (4453/1024 : ℝ) ≤ (4454486575287/50000000000000000000 : ℝ) := by
    have hpowers : (299/12500 : ℝ)^4453 ≤ (4454486575287/50000000000000000000 : ℝ)^1024 := by
      have hnat : (299 : ℕ)^4453*50000000000000000000^1024 ≤ 4454486575287^1024*12500^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        299 12500 4454486575287 50000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (299/12500 : ℝ)) (X := (4454486575287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12959/50000 : ℝ) ^ (4453/1024 : ℝ) ≤ (281817643284065339/100000000000000000000 : ℝ) := by
    have hpowers : (12959/50000 : ℝ)^4453 ≤ (281817643284065339/100000000000000000000 : ℝ)^1024 := by
      have hnat : (12959 : ℕ)^4453*100000000000000000000^1024 ≤ 281817643284065339^1024*50000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12959 50000 281817643284065339 100000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12959/50000 : ℝ)) (X := (281817643284065339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000004454486575287/25000000000000000000 : ℝ) ≤ (1250000051217089/1250000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (25000004454486575287/25000000000000000000 : ℝ)^1024 ≤ (1250000051217089/1250000000000000 : ℝ)^4453 := by
      have hnat : (25000004454486575287 : ℕ)^1024*1250000000000000^4453 ≤ 1250000051217089^4453*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000004454486575287 25000000000000000000 1250000051217089 1250000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000051217089/1250000000000000 : ℝ)) (X := (25000004454486575287/25000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100281826552257215913/100000000000000000000 : ℝ) ≤ (2501618446900851/2500000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (100281826552257215913/100000000000000000000 : ℝ)^1024 ≤ (2501618446900851/2500000000000000 : ℝ)^4453 := by
      have hnat : (100281826552257215913 : ℕ)^1024*2500000000000000^4453 ≤ 2501618446900851^4453*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100281826552257215913 100000000000000000000 2501618446900851 2500000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501618446900851/2500000000000000 : ℝ)) (X := (100281826552257215913/100000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50281817643284065339/50000000000000000000 : ℝ) ≤ (625809197841881/625000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (50281817643284065339/50000000000000000000 : ℝ)^1024 ≤ (625809197841881/625000000000000 : ℝ)^4453 := by
      have hnat : (50281817643284065339 : ℕ)^1024*625000000000000^4453 ≤ 625809197841881^4453*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50281817643284065339 50000000000000000000 625809197841881 625000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625809197841881/625000000000000 : ℝ)) (X := (50281817643284065339/50000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4454486575287/50000000000000000000 : ℝ) ≤ ((14701815062484476999/14703750000000000000 : ℝ)+2*(1618344466673/588150000000000 : ℝ)*(299/12500 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (14701815062484476999/14703750000000000000 : ℝ)+2*(1618344466673/588150000000000 : ℝ)*(299/12500 : ℝ)=(1250000051217089/1250000000000000 : ℝ) by norm_num, show 1+2*(4454486575287/50000000000000000000 : ℝ)=(25000004454486575287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(281817643284065339/100000000000000000000 : ℝ)+(4454486575287/50000000000000000000 : ℝ) ≤ ((14701815062484476999/14703750000000000000 : ℝ)+(1618344466673/588150000000000 : ℝ)*((12959/50000 : ℝ)+(299/12500 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (14701815062484476999/14703750000000000000 : ℝ)+(1618344466673/588150000000000 : ℝ)*((12959/50000 : ℝ)+(299/12500 : ℝ))=(2501618446900851/2500000000000000 : ℝ) by norm_num, show 1+(281817643284065339/100000000000000000000 : ℝ)+(4454486575287/50000000000000000000 : ℝ)=(100281826552257215913/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(281817643284065339/100000000000000000000 : ℝ) ≤ ((14701815062484476999/14703750000000000000 : ℝ)+2*(1618344466673/588150000000000 : ℝ)*(12959/50000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (14701815062484476999/14703750000000000000 : ℝ)+2*(1618344466673/588150000000000 : ℝ)*(12959/50000 : ℝ)=(625809197841881/625000000000000 : ℝ) by norm_num, show 1+2*(281817643284065339/100000000000000000000 : ℝ)=(50281817643284065339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14701815062484476999/14703750000000000000 : ℝ)*(X 1 0+X 2 0)+(1618344466673/588150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (299/12500 : ℝ)) (hi := (12959/50000 : ℝ)) (c := (14701815062484476999/14703750000000000000 : ℝ)) (alpha := (1618344466673/588150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14701815062484476999/14703750000000000000 : ℝ)*(X 0 1+X 2 1)+(1618344466673/588150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (299/12500 : ℝ)) (hi := (12959/50000 : ℝ)) (c := (14701815062484476999/14703750000000000000 : ℝ)) (alpha := (1618344466673/588150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14701815062484476999/14703750000000000000 : ℝ)*(X 0 2+X 1 2)+(1618344466673/588150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (299/12500 : ℝ)) (hi := (12959/50000 : ℝ)) (c := (14701815062484476999/14703750000000000000 : ℝ)) (alpha := (1618344466673/588150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-117755301/625000000 : ℝ)*X 0 0+(2796730081/5000000000 : ℝ)*X 0 1+(1270441307/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5392751521/10000000000 : ℝ)*X 1 0+(-2154690219/10000000000 : ℝ)*X 1 1+(5081765611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5392752011/10000000000 : ℝ)*X 2 0+(635220663/1250000000 : ℝ)*X 2 1+(-2154689971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261629453/10000000000 : ℝ)*X 0 0+(232976673/625000000 : ℝ)*X 0 1+(2430504527/5000000000 : ℝ)*X 0 2+(4261629453/10000000000 : ℝ)*X 1 0+(232976673/625000000 : ℝ)*X 1 1+(2430504527/5000000000 : ℝ)*X 1 2+(4261629453/10000000000 : ℝ)*X 2 0+(232976673/625000000 : ℝ)*X 2 1+(2430504527/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1884456473/10000000000 : ℝ)*X 0 0+(2543880493/5000000000 : ℝ)*X 0 1+(5587363029/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2629268209/5000000000 : ℝ)*X 1 0+(-412273111/2500000000 : ℝ)*X 1 1+(1117472613/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051707289/2000000000 : ℝ)*X 2 0+(2793681517/5000000000 : ℝ)*X 2 1+(-32981849/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1065613199/2500000000 : ℝ)*X 0 0+(969545837/2000000000 : ℝ)*X 0 1+(1870565773/5000000000 : ℝ)*X 0 2+(1065613199/2500000000 : ℝ)*X 1 0+(969545837/2000000000 : ℝ)*X 1 1+(1870565773/5000000000 : ℝ)*X 1 2+(1065613199/2500000000 : ℝ)*X 2 0+(969545837/2000000000 : ℝ)*X 2 1+(1870565773/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (103958427243289135872402831/20421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4608019/25000000000000 : ℝ)*(base1) + (194771607/20000000000000 : ℝ)*(base19) + (575715723/50000000000000 : ℝ)*(base23) + (61906649/100000000000000 : ℝ)*(upper3) + (215879189/100000000000000 : ℝ)*(upper5) + (354578519158581/25000000000000 : ℝ)*(major0) + (354578519158581/25000000000000 : ℝ)*(major1) + (354578519158581/25000000000000 : ℝ)*(major2) + (488574067969189/25000000000000 : ℝ)*(sp0) + (1954304823590237/100000000000000 : ℝ)*(sp1) + (977152323008413/50000000000000 : ℝ)*(sp2) + (882318755629139/100000000000000 : ℝ)*(sp3) + (1193000449/12500000000000 : ℝ)*(sp4) + (1706037199/50000000000000 : ℝ)*(sp7) + (882322186135613/100000000000000 : ℝ)*(f.failure) + (122144112340517/6250000000000 : ℝ)*(f.sum) + (12830837475253/19605000000000000000000000000 : ℝ)*base65 + (838839184869246973/122531250000000000000000000000000 : ℝ)*base67 + (1196401327898496973/122531250000000000000000000000000 : ℝ)*base69 + (190784430406559473/122531250000000000000000000000000 : ℝ)*base71 + (2531417068573/19605000000000000000000000000 : ℝ)*base73 + (1635590176598778223/122531250000000000000000000000000 : ℝ)*base75 + (890580419660028223/122531250000000000000000000000000 : ℝ)*base77 + (1220432262515496973/122531250000000000000000000000000 : ℝ)*base79 + (44047352429/612656250000000000000000000 : ℝ)*base81 + (1956751/2000000000000000000000 : ℝ)*base90 + (1956751/2000000000000000000000 : ℝ)*base92 + (1956751/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (164957580929379262670495477/30632812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (103198387/10000000000000 : ℝ)*(base19) + (1107047611/100000000000000 : ℝ)*(base23) + (145527937/100000000000000 : ℝ)*(upper3) + (5057213/20000000000000 : ℝ)*(lower4) + (106823689/100000000000000 : ℝ)*(upper5) + (90789487491233/6250000000000 : ℝ)*(major0) + (90789487491233/6250000000000 : ℝ)*(major1) + (90789487491233/6250000000000 : ℝ)*(major2) + (6270894117/100000000000000 : ℝ)*(sp1) + (3462603187/50000000000000 : ℝ)*(sp2) + (1000796222322833/50000000000000 : ℝ)*(sp4) + (2001585141767679/100000000000000 : ℝ)*(sp5) + (1000792206195841/50000000000000 : ℝ)*(sp6) + (225917743893477/25000000000000 : ℝ)*(sp7) + (225917743893477/25000000000000 : ℝ)*(f.failure) + (1000796222322833/50000000000000 : ℝ)*(f.sum) + (85081467335681/29407500000000000000000000000 : ℝ)*base66 + (532627589182812733/91898437500000000000000000000000 : ℝ)*base68 + (192805701606324277/22974609375000000000000000000000 : ℝ)*base70 + (949369574472391091/183796875000000000000000000000000 : ℝ)*base72 + (4217945198873/58815000000000000000000000000 : ℝ)*base73 + (350446664052507929/45949218750000000000000000000000 : ℝ)*base76 + (382035799114906483/91898437500000000000000000000000 : ℝ)*base78 + (1074823243235187733/91898437500000000000000000000000 : ℝ)*base80 + (82348774339511/29407500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3035321/500000000000000000000 : ℝ)*base89 + (3035321/500000000000000000000 : ℝ)*base91 + (3035321/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1479_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12959/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (299/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7891/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4677/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1479_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1479_s2_0 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-478164397/2500000000 : ℝ)*x 0 + (546928497/1000000000 : ℝ)*x 1 + (207499919/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478164397/2500000000 : ℝ)^4455 ≤ (11674494346281/100000000000000 : ℝ)^3431 := by
    have hnat : (478164397 : ℕ)^4455*100000000000000^3431 ≤ 11674494346281^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478164397 2500000000 11674494346281 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546928497/1000000000 : ℝ)^4455 ≤ (9135757068489/20000000000000 : ℝ)^3431 := by
    have hnat : (546928497 : ℕ)^4455*20000000000000^3431 ≤ 9135757068489^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546928497 1000000000 9135757068489 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207499919/400000000 : ℝ)^4455 ≤ (42646720303213/100000000000000 : ℝ)^3431 := by
    have hnat : (207499919 : ℕ)^4455*100000000000000^3431 ≤ 42646720303213^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207499919 400000000 42646720303213 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-478164397/2500000000 : ℝ), (546928497/1000000000 : ℝ), (207499919/400000000 : ℝ)] ![(11674494346281/100000000000000 : ℝ), (9135757068489/20000000000000 : ℝ), (42646720303213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-478164397/2500000000 : ℝ)|^4455 ≤ (11674494346281/100000000000000 : ℝ)^3431
        have hw : |(-478164397/2500000000 : ℝ)|=(478164397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546928497/1000000000 : ℝ)|^4455 ≤ (9135757068489/20000000000000 : ℝ)^3431
        have hw : |(546928497/1000000000 : ℝ)|=(546928497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207499919/400000000 : ℝ)|^4455 ≤ (42646720303213/100000000000000 : ℝ)^3431
        have hw : |(207499919/400000000 : ℝ)|=(207499919/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s2_1 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361542653/10000000000 : ℝ)*x 0 + (-257253349/1250000000 : ℝ)*x 1 + (207499903/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361542653/10000000000 : ℝ)^4455 ≤ (1780552825741/4000000000000 : ℝ)^3431 := by
    have hnat : (5361542653 : ℕ)^4455*4000000000000^3431 ≤ 1780552825741^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361542653 10000000000 1780552825741 4000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257253349/1250000000 : ℝ)^4455 ≤ (12839463309891/100000000000000 : ℝ)^3431 := by
    have hnat : (257253349 : ℕ)^4455*100000000000000^3431 ≤ 12839463309891^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257253349 1250000000 12839463309891 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207499903/400000000 : ℝ)^4455 ≤ (21323358016671/50000000000000 : ℝ)^3431 := by
    have hnat : (207499903 : ℕ)^4455*50000000000000^3431 ≤ 21323358016671^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207499903 400000000 21323358016671 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361542653/10000000000 : ℝ), (-257253349/1250000000 : ℝ), (207499903/400000000 : ℝ)] ![(1780552825741/4000000000000 : ℝ), (12839463309891/100000000000000 : ℝ), (21323358016671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361542653/10000000000 : ℝ)|^4455 ≤ (1780552825741/4000000000000 : ℝ)^3431
        have hw : |(5361542653/10000000000 : ℝ)|=(5361542653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-257253349/1250000000 : ℝ)|^4455 ≤ (12839463309891/100000000000000 : ℝ)^3431
        have hw : |(-257253349/1250000000 : ℝ)|=(257253349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207499903/400000000 : ℝ)|^4455 ≤ (21323358016671/50000000000000 : ℝ)^3431
        have hw : |(207499903/400000000 : ℝ)|=(207499903/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s2_2 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335096411/625000000 : ℝ)*x 0 + (5187497467/10000000000 : ℝ)*x 1 + (-514506759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335096411/625000000 : ℝ)^4455 ≤ (139105686917/312500000000 : ℝ)^3431 := by
    have hnat : (335096411 : ℕ)^4455*312500000000^3431 ≤ 139105686917^3431*625000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335096411 625000000 139105686917 312500000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5187497467/10000000000 : ℝ)^4455 ≤ (21323357440239/50000000000000 : ℝ)^3431 := by
    have hnat : (5187497467 : ℕ)^4455*50000000000000^3431 ≤ 21323357440239^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5187497467 10000000000 21323357440239 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514506759/2500000000 : ℝ)^4455 ≤ (12839465286463/100000000000000 : ℝ)^3431 := by
    have hnat : (514506759 : ℕ)^4455*100000000000000^3431 ≤ 12839465286463^3431*2500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514506759 2500000000 12839465286463 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335096411/625000000 : ℝ), (5187497467/10000000000 : ℝ), (-514506759/2500000000 : ℝ)] ![(139105686917/312500000000 : ℝ), (21323357440239/50000000000000 : ℝ), (12839465286463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335096411/625000000 : ℝ)|^4455 ≤ (139105686917/312500000000 : ℝ)^3431
        have hw : |(335096411/625000000 : ℝ)|=(335096411/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5187497467/10000000000 : ℝ)|^4455 ≤ (21323357440239/50000000000000 : ℝ)^3431
        have hw : |(5187497467/10000000000 : ℝ)|=(5187497467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-514506759/2500000000 : ℝ)|^4455 ≤ (12839465286463/100000000000000 : ℝ)^3431
        have hw : |(-514506759/2500000000 : ℝ)|=(514506759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s2_3 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282017759/10000000000 : ℝ)*x 0 + (3979857579/10000000000 : ℝ)*x 1 + (4604004721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282017759/10000000000 : ℝ)^4455 ≤ (6648780660661/20000000000000 : ℝ)^3431 := by
    have hnat : (4282017759 : ℕ)^4455*20000000000000^3431 ≤ 6648780660661^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282017759 10000000000 6648780660661 20000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3979857579/10000000000 : ℝ)^4455 ≤ (15115269497457/50000000000000 : ℝ)^3431 := by
    have hnat : (3979857579 : ℕ)^4455*50000000000000^3431 ≤ 15115269497457^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3979857579 10000000000 15115269497457 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4604004721/10000000000 : ℝ)^4455 ≤ (18262778848179/50000000000000 : ℝ)^3431 := by
    have hnat : (4604004721 : ℕ)^4455*50000000000000^3431 ≤ 18262778848179^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4604004721 10000000000 18262778848179 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282017759/10000000000 : ℝ), (3979857579/10000000000 : ℝ), (4604004721/10000000000 : ℝ)] ![(6648780660661/20000000000000 : ℝ), (15115269497457/50000000000000 : ℝ), (18262778848179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282017759/10000000000 : ℝ)|^4455 ≤ (6648780660661/20000000000000 : ℝ)^3431
        have hw : |(4282017759/10000000000 : ℝ)|=(4282017759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3979857579/10000000000 : ℝ)|^4455 ≤ (15115269497457/50000000000000 : ℝ)^3431
        have hw : |(3979857579/10000000000 : ℝ)|=(3979857579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4604004721/10000000000 : ℝ)|^4455 ≤ (18262778848179/50000000000000 : ℝ)^3431
        have hw : |(4604004721/10000000000 : ℝ)|=(4604004721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s2_4 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95635987/500000000 : ℝ)*x 0 + (648665669/1250000000 : ℝ)*x 1 + (1093488121/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95635987/500000000 : ℝ)^4455 ≤ (5837493467837/50000000000000 : ℝ)^3431 := by
    have hnat : (95635987 : ℕ)^4455*50000000000000^3431 ≤ 5837493467837^3431*500000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95635987 500000000 5837493467837 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648665669/1250000000 : ℝ)^4455 ≤ (42666227985321/100000000000000 : ℝ)^3431 := by
    have hnat : (648665669 : ℕ)^4455*100000000000000^3431 ≤ 42666227985321^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648665669 1250000000 42666227985321 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093488121/2000000000 : ℝ)^4455 ≤ (2282939253297/5000000000000 : ℝ)^3431 := by
    have hnat : (1093488121 : ℕ)^4455*5000000000000^3431 ≤ 2282939253297^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093488121 2000000000 2282939253297 5000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95635987/500000000 : ℝ), (648665669/1250000000 : ℝ), (1093488121/2000000000 : ℝ)] ![(5837493467837/50000000000000 : ℝ), (42666227985321/100000000000000 : ℝ), (2282939253297/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95635987/500000000 : ℝ)|^4455 ≤ (5837493467837/50000000000000 : ℝ)^3431
        have hw : |(-95635987/500000000 : ℝ)|=(95635987/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648665669/1250000000 : ℝ)|^4455 ≤ (42666227985321/100000000000000 : ℝ)^3431
        have hw : |(648665669/1250000000 : ℝ)|=(648665669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093488121/2000000000 : ℝ)|^4455 ≤ (2282939253297/5000000000000 : ℝ)^3431
        have hw : |(1093488121/2000000000 : ℝ)|=(1093488121/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s2_5 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057586181/2000000000 : ℝ)*x 0 + (-222260579/1250000000 : ℝ)*x 1 + (5467440631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057586181/2000000000 : ℝ)^4455 ≤ (21860946376869/50000000000000 : ℝ)^3431 := by
    have hnat : (1057586181 : ℕ)^4455*50000000000000^3431 ≤ 21860946376869^3431*2000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057586181 2000000000 21860946376869 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222260579/1250000000 : ℝ)^4455 ≤ (5309660938883/50000000000000 : ℝ)^3431 := by
    have hnat : (222260579 : ℕ)^4455*50000000000000^3431 ≤ 5309660938883^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222260579 1250000000 5309660938883 50000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467440631/10000000000 : ℝ)^4455 ≤ (4565878534787/10000000000000 : ℝ)^3431 := by
    have hnat : (5467440631 : ℕ)^4455*10000000000000^3431 ≤ 4565878534787^3431*10000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467440631 10000000000 4565878534787 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057586181/2000000000 : ℝ), (-222260579/1250000000 : ℝ), (5467440631/10000000000 : ℝ)] ![(21860946376869/50000000000000 : ℝ), (5309660938883/50000000000000 : ℝ), (4565878534787/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057586181/2000000000 : ℝ)|^4455 ≤ (21860946376869/50000000000000 : ℝ)^3431
        have hw : |(1057586181/2000000000 : ℝ)|=(1057586181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222260579/1250000000 : ℝ)|^4455 ≤ (5309660938883/50000000000000 : ℝ)^3431
        have hw : |(-222260579/1250000000 : ℝ)|=(222260579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467440631/10000000000 : ℝ)|^4455 ≤ (4565878534787/10000000000000 : ℝ)^3431
        have hw : |(5467440631/10000000000 : ℝ)|=(5467440631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s2_6 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211517249/400000000 : ℝ)*x 0 + (218697627/400000000 : ℝ)*x 1 + (-55565129/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211517249/400000000 : ℝ)^4455 ≤ (1093047404731/2500000000000 : ℝ)^3431 := by
    have hnat : (211517249 : ℕ)^4455*2500000000000^3431 ≤ 1093047404731^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211517249 400000000 1093047404731 2500000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218697627/400000000 : ℝ)^4455 ≤ (45658785824981/100000000000000 : ℝ)^3431 := by
    have hnat : (218697627 : ℕ)^4455*100000000000000^3431 ≤ 45658785824981^3431*400000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218697627 400000000 45658785824981 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55565129/312500000 : ℝ)^4455 ≤ (530965898467/5000000000000 : ℝ)^3431 := by
    have hnat : (55565129 : ℕ)^4455*5000000000000^3431 ≤ 530965898467^3431*312500000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55565129 312500000 530965898467 5000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211517249/400000000 : ℝ), (218697627/400000000 : ℝ), (-55565129/312500000 : ℝ)] ![(1093047404731/2500000000000 : ℝ), (45658785824981/100000000000000 : ℝ), (530965898467/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211517249/400000000 : ℝ)|^4455 ≤ (1093047404731/2500000000000 : ℝ)^3431
        have hw : |(211517249/400000000 : ℝ)|=(211517249/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218697627/400000000 : ℝ)|^4455 ≤ (45658785824981/100000000000000 : ℝ)^3431
        have hw : |(218697627/400000000 : ℝ)|=(218697627/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55565129/312500000 : ℝ)|^4455 ≤ (530965898467/5000000000000 : ℝ)^3431
        have hw : |(-55565129/312500000 : ℝ)|=(55565129/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1479_s2_7 (p : ℝ) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428215549/1000000000 : ℝ)*x 0 + (574994563/1250000000 : ℝ)*x 1 + (497992967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428215549/1000000000 : ℝ)^4455 ≤ (33245291734369/100000000000000 : ℝ)^3431 := by
    have hnat : (428215549 : ℕ)^4455*100000000000000^3431 ≤ 33245291734369^3431*1000000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428215549 1000000000 33245291734369 100000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574994563/1250000000 : ℝ)^4455 ≤ (3648386165071/10000000000000 : ℝ)^3431 := by
    have hnat : (574994563 : ℕ)^4455*10000000000000^3431 ≤ 3648386165071^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574994563 1250000000 3648386165071 10000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497992967/1250000000 : ℝ)^4455 ≤ (7567711648211/25000000000000 : ℝ)^3431 := by
    have hnat : (497992967 : ℕ)^4455*25000000000000^3431 ≤ 7567711648211^3431*1250000000^4455 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497992967 1250000000 7567711648211 25000000000000 4455 3431 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4455/1024 : ℝ)) 4455 3431 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428215549/1000000000 : ℝ), (574994563/1250000000 : ℝ), (497992967/1250000000 : ℝ)] ![(33245291734369/100000000000000 : ℝ), (3648386165071/10000000000000 : ℝ), (7567711648211/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428215549/1000000000 : ℝ)|^4455 ≤ (33245291734369/100000000000000 : ℝ)^3431
        have hw : |(428215549/1000000000 : ℝ)|=(428215549/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574994563/1250000000 : ℝ)|^4455 ≤ (3648386165071/10000000000000 : ℝ)^3431
        have hw : |(574994563/1250000000 : ℝ)|=(574994563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(497992967/1250000000 : ℝ)|^4455 ≤ (7567711648211/25000000000000 : ℝ)^3431
        have hw : |(497992967/1250000000 : ℝ)|=(497992967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1479_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (407/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2017/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7891/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7891/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7891/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7891/100000 : ℝ) ^ (4453/1024 : ℝ) ≤ (799838344173847/50000000000000000000 : ℝ) := by
    have hpowers : (7891/100000 : ℝ)^4453 ≤ (799838344173847/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7891 : ℕ)^4453*50000000000000000000^1024 ≤ 799838344173847^1024*100000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7891 100000 799838344173847 50000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7891/100000 : ℝ)) (X := (799838344173847/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4677/25000 : ℝ) ^ (4453/1024 : ℝ) ≤ (34141633876837903/50000000000000000000 : ℝ) := by
    have hpowers : (4677/25000 : ℝ)^4453 ≤ (34141633876837903/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4677 : ℕ)^4453*50000000000000000000^1024 ≤ 34141633876837903^1024*25000^4453 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4677 25000 34141633876837903 50000000000000000000 4453 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4677/25000 : ℝ)) (X := (34141633876837903/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000799838344173847/25000000000000000000 : ℝ) ≤ (1250009196321307/1250000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (25000799838344173847/25000000000000000000 : ℝ)^1024 ≤ (1250009196321307/1250000000000000 : ℝ)^4453 := by
      have hnat : (25000799838344173847 : ℕ)^1024*1250000000000000^4453 ≤ 1250009196321307^4453*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000799838344173847 25000000000000000000 1250009196321307 1250000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250009196321307/1250000000000000 : ℝ)) (X := (25000799838344173847/25000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (200139765888884047/200000000000000000 : ℝ) ≤ (10001606577335953/10000000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (200139765888884047/200000000000000000 : ℝ)^1024 ≤ (10001606577335953/10000000000000000 : ℝ)^4453 := by
      have hnat : (200139765888884047 : ℕ)^1024*10000000000000000^4453 ≤ 10001606577335953^4453*200000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200139765888884047 200000000000000000 10001606577335953 10000000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001606577335953/10000000000000000 : ℝ)) (X := (200139765888884047/200000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25034141633876837903/25000000000000000000 : ℝ) ≤ (200062791682029/200000000000000 : ℝ) ^ (4453/1024 : ℝ) := by
    have hpowers : (25034141633876837903/25000000000000000000 : ℝ)^1024 ≤ (200062791682029/200000000000000 : ℝ)^4453 := by
      have hnat : (25034141633876837903 : ℕ)^1024*200000000000000^4453 ≤ 200062791682029^4453*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25034141633876837903 25000000000000000000 200062791682029 200000000000000 1024 4453 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200062791682029/200000000000000 : ℝ)) (X := (25034141633876837903/25000000000000000000 : ℝ)) (by norm_num) 4453 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(799838344173847/50000000000000000000 : ℝ) ≤ ((54073300950043774449/54085000000000000000 : ℝ)+2*(1533006765497/1081700000000000 : ℝ)*(7891/100000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (54073300950043774449/54085000000000000000 : ℝ)+2*(1533006765497/1081700000000000 : ℝ)*(7891/100000 : ℝ)=(1250009196321307/1250000000000000 : ℝ) by norm_num, show 1+2*(799838344173847/50000000000000000000 : ℝ)=(25000799838344173847/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34141633876837903/50000000000000000000 : ℝ)+(799838344173847/50000000000000000000 : ℝ) ≤ ((54073300950043774449/54085000000000000000 : ℝ)+(1533006765497/1081700000000000 : ℝ)*((4677/25000 : ℝ)+(7891/100000 : ℝ)))^(4453/1024 : ℝ) := by
    rw [show (54073300950043774449/54085000000000000000 : ℝ)+(1533006765497/1081700000000000 : ℝ)*((4677/25000 : ℝ)+(7891/100000 : ℝ))=(10001606577335953/10000000000000000 : ℝ) by norm_num, show 1+(34141633876837903/50000000000000000000 : ℝ)+(799838344173847/50000000000000000000 : ℝ)=(200139765888884047/200000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34141633876837903/50000000000000000000 : ℝ) ≤ ((54073300950043774449/54085000000000000000 : ℝ)+2*(1533006765497/1081700000000000 : ℝ)*(4677/25000 : ℝ))^(4453/1024 : ℝ) := by
    rw [show (54073300950043774449/54085000000000000000 : ℝ)+2*(1533006765497/1081700000000000 : ℝ)*(4677/25000 : ℝ)=(200062791682029/200000000000000 : ℝ) by norm_num, show 1+2*(34141633876837903/50000000000000000000 : ℝ)=(25034141633876837903/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (54073300950043774449/54085000000000000000 : ℝ)*(X 1 0+X 2 0)+(1533006765497/1081700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (7891/100000 : ℝ)) (hi := (4677/25000 : ℝ)) (c := (54073300950043774449/54085000000000000000 : ℝ)) (alpha := (1533006765497/1081700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (54073300950043774449/54085000000000000000 : ℝ)*(X 0 1+X 2 1)+(1533006765497/1081700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (7891/100000 : ℝ)) (hi := (4677/25000 : ℝ)) (c := (54073300950043774449/54085000000000000000 : ℝ)) (alpha := (1533006765497/1081700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (54073300950043774449/54085000000000000000 : ℝ)*(X 0 2+X 1 2)+(1533006765497/1081700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4453/1024 : ℝ)) (lo := (7891/100000 : ℝ)) (hi := (4677/25000 : ℝ)) (c := (54073300950043774449/54085000000000000000 : ℝ)) (alpha := (1533006765497/1081700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-478164397/2500000000 : ℝ)*X 0 0+(546928497/1000000000 : ℝ)*X 0 1+(207499919/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361542653/10000000000 : ℝ)*X 1 0+(-257253349/1250000000 : ℝ)*X 1 1+(207499903/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335096411/625000000 : ℝ)*X 2 0+(5187497467/10000000000 : ℝ)*X 2 1+(-514506759/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282017759/10000000000 : ℝ)*X 0 0+(3979857579/10000000000 : ℝ)*X 0 1+(4604004721/10000000000 : ℝ)*X 0 2+(4282017759/10000000000 : ℝ)*X 1 0+(3979857579/10000000000 : ℝ)*X 1 1+(4604004721/10000000000 : ℝ)*X 1 2+(4282017759/10000000000 : ℝ)*X 2 0+(3979857579/10000000000 : ℝ)*X 2 1+(4604004721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-95635987/500000000 : ℝ)*X 0 0+(648665669/1250000000 : ℝ)*X 0 1+(1093488121/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057586181/2000000000 : ℝ)*X 1 0+(-222260579/1250000000 : ℝ)*X 1 1+(5467440631/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211517249/400000000 : ℝ)*X 2 0+(218697627/400000000 : ℝ)*X 2 1+(-55565129/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((428215549/1000000000 : ℝ)*X 0 0+(574994563/1250000000 : ℝ)*X 0 1+(497992967/1250000000 : ℝ)*X 0 2+(428215549/1000000000 : ℝ)*X 1 0+(574994563/1250000000 : ℝ)*X 1 1+(497992967/1250000000 : ℝ)*X 1 2+(428215549/1000000000 : ℝ)*X 2 0+(574994563/1250000000 : ℝ)*X 2 1+(497992967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1479_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (265679611678546512467799/27042500000000000000000000000 : ℝ) := by norm_num
    linear_combination (292140149/12500000000000 : ℝ)*(base19) + (2211835029/100000000000000 : ℝ)*(base23) + (19923373/50000000000000 : ℝ)*(lower2) + (185421361/50000000000000 : ℝ)*(upper3) + (11515629/10000000000000 : ℝ)*(upper5) + (1287760060318269/50000000000000 : ℝ)*(major0) + (1287760060318269/50000000000000 : ℝ)*(major1) + (1287760060318269/50000000000000 : ℝ)*(major2) + (887201740935517/25000000000000 : ℝ)*(sp0) + (887206621563023/25000000000000 : ℝ)*(sp1) + (1774413305769127/50000000000000 : ℝ)*(sp2) + (400549364561171/25000000000000 : ℝ)*(sp3) + (10929815607/50000000000000 : ℝ)*(sp4) + (6816085533/50000000000000 : ℝ)*(sp7) + (6408844361663/400000000000 : ℝ)*(f.failure) + (3548828823373283/100000000000000 : ℝ)*(f.sum) + (88149380546733/27042500000000000000000000000 : ℝ)*base65 + (2204162778125758781/2704250000000000000000000000000000 : ℝ)*base67 + (14028160787057258781/2704250000000000000000000000000000 : ℝ)*base69 + (6376008678356241219/2704250000000000000000000000000000 : ℝ)*base72 + (73178204595837/27042500000000000000000000000 : ℝ)*base74 + (18875314674495241219/2704250000000000000000000000000000 : ℝ)*base76 + (14432594111574758781/2704250000000000000000000000000000 : ℝ)*base77 + (8474237189026741219/2704250000000000000000000000000000 : ℝ)*base80 + (82938820702637/27042500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (20101/8000000000000000000 : ℝ)*base90 + (20101/8000000000000000000 : ℝ)*base92 + (20101/8000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15559383787037316760549857177/1352125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (90542821/6250000000000 : ℝ)*(base19) + (940317649/50000000000000 : ℝ)*(base23) + (20653573/10000000000000 : ℝ)*(upper3) + (6109709/10000000000000 : ℝ)*(lower4) + (28938723/10000000000000 : ℝ)*(upper5) + (2609488560709109/100000000000000 : ℝ)*(major0) + (2609488560709109/100000000000000 : ℝ)*(major1) + (2609488560709109/100000000000000 : ℝ)*(major2) + (1025739983/6250000000000 : ℝ)*(sp1) + (734709039/3125000000000 : ℝ)*(sp2) + (71912682886517/2000000000000 : ℝ)*(sp4) + (1797808141900493/50000000000000 : ℝ)*(sp5) + (449451094125163/12500000000000 : ℝ)*(sp6) + (1623342593513829/100000000000000 : ℝ)*(sp7) + (1623342593513829/100000000000000 : ℝ)*(f.failure) + (71912682886517/2000000000000 : ℝ)*(f.sum) + (34373956134323/54085000000000000000000000000 : ℝ)*base65 + (9691482082868405941/5408500000000000000000000000000000 : ℝ)*base67 + (25064486859955405941/5408500000000000000000000000000000 : ℝ)*base69 + (13685016218950405941/5408500000000000000000000000000000 : ℝ)*base71 + (197739760462693/54085000000000000000000000000 : ℝ)*base73 + (5340923877830594059/5408500000000000000000000000000000 : ℝ)*base76 + (5388650164311405941/5408500000000000000000000000000000 : ℝ)*base77 + (15706676157032405941/5408500000000000000000000000000000 : ℝ)*base79 + (254298650765333/54085000000000000000000000000 : ℝ)*base81 + (8054983/2000000000000000000000 : ℝ)*base90 + (8054983/2000000000000000000000 : ℝ)*base92 + (8054983/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1479_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7891/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (407/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1479_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1479_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (407/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1479_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1479_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1479_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4453/1024 : ℝ) ≤ p) (hpb : p ≤ (4455/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32149573/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (407/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2017/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1479_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
