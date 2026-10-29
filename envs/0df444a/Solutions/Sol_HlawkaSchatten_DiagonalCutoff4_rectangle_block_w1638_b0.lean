-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1638_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:38.102991+00:00
-- url     : https://prove2.me/submissions/19aa57b3-cef0-4f41-9d67-5c3ec4f38fdc

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
theorem support_rectangle_w1638_s0_0 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1513948881/10000000000 : ℝ)*x 0 + (580036329/1000000000 : ℝ)*x 1 + (491328723/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1513948881/10000000000 : ℝ)^4871 ≤ (9159505606683/100000000000000 : ℝ)^3847 := by
    have hnat : (1513948881 : ℕ)^4871*100000000000000^3847 ≤ 9159505606683^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513948881 10000000000 9159505606683 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (580036329/1000000000 : ℝ)^4871 ≤ (25087729756679/50000000000000 : ℝ)^3847 := by
    have hnat : (580036329 : ℕ)^4871*50000000000000^3847 ≤ 25087729756679^3847*1000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580036329 1000000000 25087729756679 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491328723/1000000000 : ℝ)^4871 ≤ (40665034873349/100000000000000 : ℝ)^3847 := by
    have hnat : (491328723 : ℕ)^4871*100000000000000^3847 ≤ 40665034873349^3847*1000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491328723 1000000000 40665034873349 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1513948881/10000000000 : ℝ), (580036329/1000000000 : ℝ), (491328723/1000000000 : ℝ)] ![(9159505606683/100000000000000 : ℝ), (25087729756679/50000000000000 : ℝ), (40665034873349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1513948881/10000000000 : ℝ)|^4871 ≤ (9159505606683/100000000000000 : ℝ)^3847
        have hw : |(-1513948881/10000000000 : ℝ)|=(1513948881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(580036329/1000000000 : ℝ)|^4871 ≤ (25087729756679/50000000000000 : ℝ)^3847
        have hw : |(580036329/1000000000 : ℝ)|=(580036329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(491328723/1000000000 : ℝ)|^4871 ≤ (40665034873349/100000000000000 : ℝ)^3847
        have hw : |(491328723/1000000000 : ℝ)|=(491328723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s0_1 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (680290453/1250000000 : ℝ)*x 0 + (-1001053761/5000000000 : ℝ)*x 1 + (1228322209/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (680290453/1250000000 : ℝ)^4871 ≤ (925731539277/2000000000000 : ℝ)^3847 := by
    have hnat : (680290453 : ℕ)^4871*2000000000000^3847 ≤ 925731539277^3847*1250000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680290453 1250000000 925731539277 2000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001053761/5000000000 : ℝ)^4871 ≤ (6524185656771/50000000000000 : ℝ)^3847 := by
    have hnat : (1001053761 : ℕ)^4871*50000000000000^3847 ≤ 6524185656771^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001053761 5000000000 6524185656771 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1228322209/2500000000 : ℝ)^4871 ≤ (10166262925899/25000000000000 : ℝ)^3847 := by
    have hnat : (1228322209 : ℕ)^4871*25000000000000^3847 ≤ 10166262925899^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1228322209 2500000000 10166262925899 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(680290453/1250000000 : ℝ), (-1001053761/5000000000 : ℝ), (1228322209/2500000000 : ℝ)] ![(925731539277/2000000000000 : ℝ), (6524185656771/50000000000000 : ℝ), (10166262925899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(680290453/1250000000 : ℝ)|^4871 ≤ (925731539277/2000000000000 : ℝ)^3847
        have hw : |(680290453/1250000000 : ℝ)|=(680290453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1001053761/5000000000 : ℝ)|^4871 ≤ (6524185656771/50000000000000 : ℝ)^3847
        have hw : |(-1001053761/5000000000 : ℝ)|=(1001053761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1228322209/2500000000 : ℝ)|^4871 ≤ (10166262925899/25000000000000 : ℝ)^3847
        have hw : |(1228322209/2500000000 : ℝ)|=(1228322209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s0_2 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5442325287/10000000000 : ℝ)*x 0 + (4913287337/10000000000 : ℝ)*x 1 + (-250263407/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5442325287/10000000000 : ℝ)^4871 ≤ (23143297436169/50000000000000 : ℝ)^3847 := by
    have hnat : (5442325287 : ℕ)^4871*50000000000000^3847 ≤ 23143297436169^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442325287 10000000000 23143297436169 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4913287337/10000000000 : ℝ)^4871 ≤ (20332517997333/50000000000000 : ℝ)^3847 := by
    have hnat : (4913287337 : ℕ)^4871*50000000000000^3847 ≤ 20332517997333^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4913287337 10000000000 20332517997333 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250263407/1250000000 : ℝ)^4871 ≤ (6524184559241/50000000000000 : ℝ)^3847 := by
    have hnat : (250263407 : ℕ)^4871*50000000000000^3847 ≤ 6524184559241^3847*1250000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250263407 1250000000 6524184559241 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5442325287/10000000000 : ℝ), (4913287337/10000000000 : ℝ), (-250263407/1250000000 : ℝ)] ![(23143297436169/50000000000000 : ℝ), (20332517997333/50000000000000 : ℝ), (6524184559241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5442325287/10000000000 : ℝ)|^4871 ≤ (23143297436169/50000000000000 : ℝ)^3847
        have hw : |(5442325287/10000000000 : ℝ)|=(5442325287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4913287337/10000000000 : ℝ)|^4871 ≤ (20332517997333/50000000000000 : ℝ)^3847
        have hw : |(4913287337/10000000000 : ℝ)|=(4913287337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250263407/1250000000 : ℝ)|^4871 ≤ (6524184559241/50000000000000 : ℝ)^3847
        have hw : |(-250263407/1250000000 : ℝ)|=(250263407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s0_3 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1024067541/2500000000 : ℝ)*x 0 + (3079762173/10000000000 : ℝ)*x 1 + (83440439/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024067541/2500000000 : ℝ)^4871 ≤ (32300826090089/100000000000000 : ℝ)^3847 := by
    have hnat : (1024067541 : ℕ)^4871*100000000000000^3847 ≤ 32300826090089^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024067541 2500000000 32300826090089 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3079762173/10000000000 : ℝ)^4871 ≤ (4501942488503/20000000000000 : ℝ)^3847 := by
    have hnat : (3079762173 : ℕ)^4871*20000000000000^3847 ≤ 4501942488503^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3079762173 10000000000 4501942488503 20000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83440439/156250000 : ℝ)^4871 ≤ (22594730725687/50000000000000 : ℝ)^3847 := by
    have hnat : (83440439 : ℕ)^4871*50000000000000^3847 ≤ 22594730725687^3847*156250000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83440439 156250000 22594730725687 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1024067541/2500000000 : ℝ), (3079762173/10000000000 : ℝ), (83440439/156250000 : ℝ)] ![(32300826090089/100000000000000 : ℝ), (4501942488503/20000000000000 : ℝ), (22594730725687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1024067541/2500000000 : ℝ)|^4871 ≤ (32300826090089/100000000000000 : ℝ)^3847
        have hw : |(1024067541/2500000000 : ℝ)|=(1024067541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3079762173/10000000000 : ℝ)|^4871 ≤ (4501942488503/20000000000000 : ℝ)^3847
        have hw : |(3079762173/10000000000 : ℝ)|=(3079762173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83440439/156250000 : ℝ)|^4871 ≤ (22594730725687/50000000000000 : ℝ)^3847
        have hw : |(83440439/156250000 : ℝ)|=(83440439/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s0_4 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-379096181/2500000000 : ℝ)*x 0 + (4935432601/10000000000 : ℝ)*x 1 + (5777446257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379096181/2500000000 : ℝ)^4871 ≤ (367126774439/4000000000000 : ℝ)^3847 := by
    have hnat : (379096181 : ℕ)^4871*4000000000000^3847 ≤ 367126774439^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379096181 2500000000 367126774439 4000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4935432601/10000000000 : ℝ)^4871 ≤ (8179449737893/20000000000000 : ℝ)^3847 := by
    have hnat : (4935432601 : ℕ)^4871*20000000000000^3847 ≤ 8179449737893^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4935432601 10000000000 8179449737893 20000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5777446257/10000000000 : ℝ)^4871 ≤ (49924581935909/100000000000000 : ℝ)^3847 := by
    have hnat : (5777446257 : ℕ)^4871*100000000000000^3847 ≤ 49924581935909^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5777446257 10000000000 49924581935909 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379096181/2500000000 : ℝ), (4935432601/10000000000 : ℝ), (5777446257/10000000000 : ℝ)] ![(367126774439/4000000000000 : ℝ), (8179449737893/20000000000000 : ℝ), (49924581935909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379096181/2500000000 : ℝ)|^4871 ≤ (367126774439/4000000000000 : ℝ)^3847
        have hw : |(-379096181/2500000000 : ℝ)|=(379096181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4935432601/10000000000 : ℝ)|^4871 ≤ (8179449737893/20000000000000 : ℝ)^3847
        have hw : |(4935432601/10000000000 : ℝ)|=(4935432601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5777446257/10000000000 : ℝ)|^4871 ≤ (49924581935909/100000000000000 : ℝ)^3847
        have hw : |(5777446257/10000000000 : ℝ)|=(5777446257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s0_5 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5200174929/10000000000 : ℝ)*x 0 + (-113794919/1000000000 : ℝ)*x 1 + (2888723083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5200174929/10000000000 : ℝ)^4871 ≤ (43694543152367/100000000000000 : ℝ)^3847 := by
    have hnat : (5200174929 : ℕ)^4871*100000000000000^3847 ≤ 43694543152367^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200174929 10000000000 43694543152367 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113794919/1000000000 : ℝ)^4871 ≤ (6380875890461/100000000000000 : ℝ)^3847 := by
    have hnat : (113794919 : ℕ)^4871*100000000000000^3847 ≤ 6380875890461^3847*1000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113794919 1000000000 6380875890461 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2888723083/5000000000 : ℝ)^4871 ≤ (24962290470119/50000000000000 : ℝ)^3847 := by
    have hnat : (2888723083 : ℕ)^4871*50000000000000^3847 ≤ 24962290470119^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888723083 5000000000 24962290470119 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5200174929/10000000000 : ℝ), (-113794919/1000000000 : ℝ), (2888723083/5000000000 : ℝ)] ![(43694543152367/100000000000000 : ℝ), (6380875890461/100000000000000 : ℝ), (24962290470119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5200174929/10000000000 : ℝ)|^4871 ≤ (43694543152367/100000000000000 : ℝ)^3847
        have hw : |(5200174929/10000000000 : ℝ)|=(5200174929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113794919/1000000000 : ℝ)|^4871 ≤ (6380875890461/100000000000000 : ℝ)^3847
        have hw : |(-113794919/1000000000 : ℝ)|=(113794919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2888723083/5000000000 : ℝ)|^4871 ≤ (24962290470119/50000000000000 : ℝ)^3847
        have hw : |(2888723083/5000000000 : ℝ)|=(2888723083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s0_6 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (325010939/625000000 : ℝ)*x 0 + (288872303/500000000 : ℝ)*x 1 + (-1137949211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325010939/625000000 : ℝ)^4871 ≤ (21847272081541/50000000000000 : ℝ)^3847 := by
    have hnat : (325010939 : ℕ)^4871*50000000000000^3847 ≤ 21847272081541^3847*625000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325010939 625000000 21847272081541 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288872303/500000000 : ℝ)^4871 ≤ (24962289890223/50000000000000 : ℝ)^3847 := by
    have hnat : (288872303 : ℕ)^4871*50000000000000^3847 ≤ 24962289890223^3847*500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288872303 500000000 24962289890223 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137949211/10000000000 : ℝ)^4871 ≤ (6380876039559/100000000000000 : ℝ)^3847 := by
    have hnat : (1137949211 : ℕ)^4871*100000000000000^3847 ≤ 6380876039559^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137949211 10000000000 6380876039559 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(325010939/625000000 : ℝ), (288872303/500000000 : ℝ), (-1137949211/10000000000 : ℝ)] ![(21847272081541/50000000000000 : ℝ), (24962289890223/50000000000000 : ℝ), (6380876039559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(325010939/625000000 : ℝ)|^4871 ≤ (21847272081541/50000000000000 : ℝ)^3847
        have hw : |(325010939/625000000 : ℝ)|=(325010939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(288872303/500000000 : ℝ)|^4871 ≤ (24962289890223/50000000000000 : ℝ)^3847
        have hw : |(288872303/500000000 : ℝ)|=(288872303/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1137949211/10000000000 : ℝ)|^4871 ≤ (6380876039559/100000000000000 : ℝ)^3847
        have hw : |(-1137949211/10000000000 : ℝ)|=(1137949211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s0_7 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1025619647/2500000000 : ℝ)*x 0 + (1056751749/2000000000 : ℝ)*x 1 + (627631387/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025619647/2500000000 : ℝ)^4871 ≤ (8090706459103/25000000000000 : ℝ)^3847 := by
    have hnat : (1025619647 : ℕ)^4871*25000000000000^3847 ≤ 8090706459103^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025619647 2500000000 8090706459103 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056751749/2000000000 : ℝ)^4871 ≤ (22292847611009/50000000000000 : ℝ)^3847 := by
    have hnat : (1056751749 : ℕ)^4871*50000000000000^3847 ≤ 22292847611009^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056751749 2000000000 22292847611009 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627631387/2000000000 : ℝ)^4871 ≤ (23051478931503/100000000000000 : ℝ)^3847 := by
    have hnat : (627631387 : ℕ)^4871*100000000000000^3847 ≤ 23051478931503^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627631387 2000000000 23051478931503 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1025619647/2500000000 : ℝ), (1056751749/2000000000 : ℝ), (627631387/2000000000 : ℝ)] ![(8090706459103/25000000000000 : ℝ), (22292847611009/50000000000000 : ℝ), (23051478931503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1025619647/2500000000 : ℝ)|^4871 ≤ (8090706459103/25000000000000 : ℝ)^3847
        have hw : |(1025619647/2500000000 : ℝ)|=(1025619647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056751749/2000000000 : ℝ)|^4871 ≤ (22292847611009/50000000000000 : ℝ)^3847
        have hw : |(1056751749/2000000000 : ℝ)|=(1056751749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627631387/2000000000 : ℝ)|^4871 ≤ (23051478931503/100000000000000 : ℝ)^3847
        have hw : |(627631387/2000000000 : ℝ)|=(627631387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1638_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4607/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4723/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4867/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4867 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4867*1^1024 ≤ 0^1024*1^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4867/1024 : ℝ) ≤ (1284159943478857661/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4867 ≤ (1284159943478857661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4867*100000000000000000000^1024 ≤ 1284159943478857661^1024*5^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1284159943478857661 100000000000000000000 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1284159943478857661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4867 := by
      have hnat : (1 : ℕ)^1024*1^4867 ≤ 1^4867*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101284159943478857661/100000000000000000000 : ℝ) ≤ (10026882342362359/10000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (101284159943478857661/100000000000000000000 : ℝ)^1024 ≤ (10026882342362359/10000000000000000 : ℝ)^4867 := by
      have hnat : (101284159943478857661 : ℕ)^1024*10000000000000000^4867 ≤ 10026882342362359^4867*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101284159943478857661 100000000000000000000 10026882342362359 10000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026882342362359/10000000000000000 : ℝ)) (X := (101284159943478857661/100000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51284159943478857661/50000000000000000000 : ℝ) ≤ (5026882342362359/5000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (51284159943478857661/50000000000000000000 : ℝ)^1024 ≤ (5026882342362359/5000000000000000 : ℝ)^4867 := by
      have hnat : (51284159943478857661 : ℕ)^1024*5000000000000000^4867 ≤ 5026882342362359^4867*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51284159943478857661 50000000000000000000 5026882342362359 5000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026882342362359/5000000000000000 : ℝ)) (X := (51284159943478857661/50000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(26882342362359/4000000000000000 : ℝ)*(0 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26882342362359/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1284159943478857661/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(26882342362359/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4867/1024 : ℝ) := by
    rw [show (1 : ℝ)+(26882342362359/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10026882342362359/10000000000000000 : ℝ) by norm_num, show 1+(1284159943478857661/100000000000000000000 : ℝ)+(0 : ℝ)=(101284159943478857661/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1284159943478857661/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(26882342362359/4000000000000000 : ℝ)*(2/5 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(26882342362359/4000000000000000 : ℝ)*(2/5 : ℝ)=(5026882342362359/5000000000000000 : ℝ) by norm_num, show 1+2*(1284159943478857661/100000000000000000000 : ℝ)=(51284159943478857661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(26882342362359/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26882342362359/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(26882342362359/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26882342362359/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(26882342362359/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (26882342362359/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1513948881/10000000000 : ℝ)*X 0 0+(580036329/1000000000 : ℝ)*X 0 1+(491328723/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((680290453/1250000000 : ℝ)*X 1 0+(-1001053761/5000000000 : ℝ)*X 1 1+(1228322209/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5442325287/10000000000 : ℝ)*X 2 0+(4913287337/10000000000 : ℝ)*X 2 1+(-250263407/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1024067541/2500000000 : ℝ)*X 0 0+(3079762173/10000000000 : ℝ)*X 0 1+(83440439/156250000 : ℝ)*X 0 2+(1024067541/2500000000 : ℝ)*X 1 0+(3079762173/10000000000 : ℝ)*X 1 1+(83440439/156250000 : ℝ)*X 1 2+(1024067541/2500000000 : ℝ)*X 2 0+(3079762173/10000000000 : ℝ)*X 2 1+(83440439/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-379096181/2500000000 : ℝ)*X 0 0+(4935432601/10000000000 : ℝ)*X 0 1+(5777446257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5200174929/10000000000 : ℝ)*X 1 0+(-113794919/1000000000 : ℝ)*X 1 1+(2888723083/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((325010939/625000000 : ℝ)*X 2 0+(288872303/500000000 : ℝ)*X 2 1+(-1137949211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1025619647/2500000000 : ℝ)*X 0 0+(1056751749/2000000000 : ℝ)*X 0 1+(627631387/2000000000 : ℝ)*X 0 2+(1025619647/2500000000 : ℝ)*X 1 0+(1056751749/2000000000 : ℝ)*X 1 1+(627631387/2000000000 : ℝ)*X 1 2+(1025619647/2500000000 : ℝ)*X 2 0+(1056751749/2000000000 : ℝ)*X 2 1+(627631387/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49644329395249036890591/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1694312199/100000000000000 : ℝ)*(base19) + (201369747/10000000000000 : ℝ)*(base23) + (87200949/50000000000000 : ℝ)*(upper3) + (3413163/25000000000000 : ℝ)*(upper4) + (8229613/2500000000000 : ℝ)*(upper5) + (98107386773317/12500000000000 : ℝ)*(major0) + (98107386773317/12500000000000 : ℝ)*(major1) + (98107386773317/12500000000000 : ℝ)*(major2) + (225461354309077/20000000000000 : ℝ)*(sp0) + (112731512738407/10000000000000 : ℝ)*(sp1) + (1127314807998799/100000000000000 : ℝ)*(sp2) + (221198910857143/50000000000000 : ℝ)*(sp3) + (10050150883/100000000000000 : ℝ)*(sp4) + (321400031/10000000000000 : ℝ)*(sp7) + (110600258928649/25000000000000 : ℝ)*(f.failure) + (281829205424067/25000000000000 : ℝ)*(f.sum) + (90208463699803/25000000000000000000000000000 : ℝ)*base65 + (224543818324803/50000000000000000000000000000 : ℝ)*base67 + (524206317024803/50000000000000000000000000000 : ℝ)*base69 + (270782463174803/50000000000000000000000000000 : ℝ)*base71 + (36088709174803/25000000000000000000000000000 : ℝ)*base73 + (11420615074803/50000000000000000000000000000 : ℝ)*base75 + (261729431524803/50000000000000000000000000000 : ℝ)*base77 + (14848928175197/50000000000000000000000000000 : ℝ)*base80 + (178337112324803/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (7747591/625000000000000000000 : ℝ)*base90 + (7747591/625000000000000000000 : ℝ)*base92 + (7747591/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (640947813781418070384477/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1231458267/100000000000000 : ℝ)*(base19) + (631788013/50000000000000 : ℝ)*(base23) + (8219399/10000000000000 : ℝ)*(base32) + (97620501/50000000000000 : ℝ)*(upper3) + (67168589/50000000000000 : ℝ)*(upper5) + (826849252466201/100000000000000 : ℝ)*(major0) + (826849252466201/100000000000000 : ℝ)*(major1) + (826849252466201/100000000000000 : ℝ)*(major2) + (3632920173/100000000000000 : ℝ)*(sp1) + (1928348601/50000000000000 : ℝ)*(sp2) + (593814344630551/50000000000000 : ℝ)*(sp4) + (593811912441331/50000000000000 : ℝ)*(sp5) + (593811784493937/50000000000000 : ℝ)*(sp6) + (466069519828037/100000000000000 : ℝ)*(sp7) + (466069602022027/100000000000000 : ℝ)*(f.failure) + (593814344630551/50000000000000 : ℝ)*(f.sum) + (35876039471841/200000000000000000000000000000 : ℝ)*base66 + (895770804671841/400000000000000000000000000000 : ℝ)*base68 + (161164418528159/400000000000000000000000000000 : ℝ)*base69 + (963869259728159/400000000000000000000000000000 : ℝ)*base71 + (800632553671841/200000000000000000000000000000 : ℝ)*base74 + (478657496128159/400000000000000000000000000000 : ℝ)*base75 + (298993940271841/400000000000000000000000000000 : ℝ)*base78 + (1245420710528159/400000000000000000000000000000 : ℝ)*base79 + (315607151671841/200000000000000000000000000000 : ℝ)*base82 + (3812507/2500000000000000000000 : ℝ)*base89 + (3812507/2500000000000000000000 : ℝ)*base91 + (3812507/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1638_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4607/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4723/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1638_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1638_s1_0 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1624873181/10000000000 : ℝ)*x 0 + (2752794369/5000000000 : ℝ)*x 1 + (1027215033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624873181/10000000000 : ℝ)^4871 ≤ (626086411651/6250000000000 : ℝ)^3847 := by
    have hnat : (1624873181 : ℕ)^4871*6250000000000^3847 ≤ 626086411651^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624873181 10000000000 626086411651 6250000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752794369/5000000000 : ℝ)^4871 ≤ (1174222908483/2500000000000 : ℝ)^3847 := by
    have hnat : (2752794369 : ℕ)^4871*2500000000000^3847 ≤ 1174222908483^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752794369 5000000000 1174222908483 2500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027215033/2000000000 : ℝ)^4871 ≤ (1075342526461/2500000000000 : ℝ)^3847 := by
    have hnat : (1027215033 : ℕ)^4871*2500000000000^3847 ≤ 1075342526461^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027215033 2000000000 1075342526461 2500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1624873181/10000000000 : ℝ), (2752794369/5000000000 : ℝ), (1027215033/2000000000 : ℝ)] ![(626086411651/6250000000000 : ℝ), (1174222908483/2500000000000 : ℝ), (1075342526461/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1624873181/10000000000 : ℝ)|^4871 ≤ (626086411651/6250000000000 : ℝ)^3847
        have hw : |(-1624873181/10000000000 : ℝ)|=(1624873181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752794369/5000000000 : ℝ)|^4871 ≤ (1174222908483/2500000000000 : ℝ)^3847
        have hw : |(2752794369/5000000000 : ℝ)|=(2752794369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027215033/2000000000 : ℝ)|^4871 ≤ (1075342526461/2500000000000 : ℝ)^3847
        have hw : |(1027215033/2000000000 : ℝ)|=(1027215033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s1_1 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363919677/10000000000 : ℝ)*x 0 + (-908644937/5000000000 : ℝ)*x 1 + (5136074953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363919677/10000000000 : ℝ)^4871 ≤ (22721943211693/50000000000000 : ℝ)^3847 := by
    have hnat : (5363919677 : ℕ)^4871*50000000000000^3847 ≤ 22721943211693^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363919677 10000000000 22721943211693 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (908644937/5000000000 : ℝ)^4871 ≤ (11542414747739/100000000000000 : ℝ)^3847 := by
    have hnat : (908644937 : ℕ)^4871*100000000000000^3847 ≤ 11542414747739^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908644937 5000000000 11542414747739 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136074953/10000000000 : ℝ)^4871 ≤ (43013698810383/100000000000000 : ℝ)^3847 := by
    have hnat : (5136074953 : ℕ)^4871*100000000000000^3847 ≤ 43013698810383^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136074953 10000000000 43013698810383 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363919677/10000000000 : ℝ), (-908644937/5000000000 : ℝ), (5136074953/10000000000 : ℝ)] ![(22721943211693/50000000000000 : ℝ), (11542414747739/100000000000000 : ℝ), (43013698810383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363919677/10000000000 : ℝ)|^4871 ≤ (22721943211693/50000000000000 : ℝ)^3847
        have hw : |(5363919677/10000000000 : ℝ)|=(5363919677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-908644937/5000000000 : ℝ)|^4871 ≤ (11542414747739/100000000000000 : ℝ)^3847
        have hw : |(-908644937/5000000000 : ℝ)|=(908644937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136074953/10000000000 : ℝ)|^4871 ≤ (43013698810383/100000000000000 : ℝ)^3847
        have hw : |(5136074953/10000000000 : ℝ)|=(5136074953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s1_2 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681960357/5000000000 : ℝ)*x 0 + (5136073731/10000000000 : ℝ)*x 1 + (-1817290103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681960357/5000000000 : ℝ)^4871 ≤ (11360974386891/25000000000000 : ℝ)^3847 := by
    have hnat : (2681960357 : ℕ)^4871*25000000000000^3847 ≤ 11360974386891^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681960357 5000000000 11360974386891 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136073731/10000000000 : ℝ)^4871 ≤ (21506842926123/50000000000000 : ℝ)^3847 := by
    have hnat : (5136073731 : ℕ)^4871*50000000000000^3847 ≤ 21506842926123^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136073731 10000000000 21506842926123 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1817290103/10000000000 : ℝ)^4871 ≤ (180350259209/1562500000000 : ℝ)^3847 := by
    have hnat : (1817290103 : ℕ)^4871*1562500000000^3847 ≤ 180350259209^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1817290103 10000000000 180350259209 1562500000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681960357/5000000000 : ℝ), (5136073731/10000000000 : ℝ), (-1817290103/10000000000 : ℝ)] ![(11360974386891/25000000000000 : ℝ), (21506842926123/50000000000000 : ℝ), (180350259209/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681960357/5000000000 : ℝ)|^4871 ≤ (11360974386891/25000000000000 : ℝ)^3847
        have hw : |(2681960357/5000000000 : ℝ)|=(2681960357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136073731/10000000000 : ℝ)|^4871 ≤ (21506842926123/50000000000000 : ℝ)^3847
        have hw : |(5136073731/10000000000 : ℝ)|=(5136073731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1817290103/10000000000 : ℝ)|^4871 ≤ (180350259209/1562500000000 : ℝ)^3847
        have hw : |(-1817290103/10000000000 : ℝ)|=(1817290103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s1_3 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261352373/625000000 : ℝ)*x 0 + (746071751/2000000000 : ℝ)*x 1 + (4671947519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261352373/625000000 : ℝ)^4871 ≤ (4144440327157/12500000000000 : ℝ)^3847 := by
    have hnat : (261352373 : ℕ)^4871*12500000000000^3847 ≤ 4144440327157^3847*625000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261352373 625000000 4144440327157 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (746071751/2000000000 : ℝ)^4871 ≤ (14345925235829/50000000000000 : ℝ)^3847 := by
    have hnat : (746071751 : ℕ)^4871*50000000000000^3847 ≤ 14345925235829^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746071751 2000000000 14345925235829 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4671947519/10000000000 : ℝ)^4871 ≤ (38152626894927/100000000000000 : ℝ)^3847 := by
    have hnat : (4671947519 : ℕ)^4871*100000000000000^3847 ≤ 38152626894927^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671947519 10000000000 38152626894927 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261352373/625000000 : ℝ), (746071751/2000000000 : ℝ), (4671947519/10000000000 : ℝ)] ![(4144440327157/12500000000000 : ℝ), (14345925235829/50000000000000 : ℝ), (38152626894927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261352373/625000000 : ℝ)|^4871 ≤ (4144440327157/12500000000000 : ℝ)^3847
        have hw : |(261352373/625000000 : ℝ)|=(261352373/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(746071751/2000000000 : ℝ)|^4871 ≤ (14345925235829/50000000000000 : ℝ)^3847
        have hw : |(746071751/2000000000 : ℝ)|=(746071751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4671947519/10000000000 : ℝ)|^4871 ≤ (38152626894927/100000000000000 : ℝ)^3847
        have hw : |(4671947519/10000000000 : ℝ)|=(4671947519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s1_4 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-812523359/5000000000 : ℝ)*x 0 + (80310909/156250000 : ℝ)*x 1 + (85964213/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (812523359/5000000000 : ℝ)^4871 ≤ (1252342155289/12500000000000 : ℝ)^3847 := by
    have hnat : (812523359 : ℕ)^4871*12500000000000^3847 ≤ 1252342155289^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812523359 5000000000 1252342155289 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80310909/156250000 : ℝ)^4871 ≤ (21527122218947/50000000000000 : ℝ)^3847 := by
    have hnat : (80310909 : ℕ)^4871*50000000000000^3847 ≤ 21527122218947^3847*156250000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80310909 156250000 21527122218947 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85964213/156250000 : ℝ)^4871 ≤ (5865877288343/12500000000000 : ℝ)^3847 := by
    have hnat : (85964213 : ℕ)^4871*12500000000000^3847 ≤ 5865877288343^3847*156250000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85964213 156250000 5865877288343 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-812523359/5000000000 : ℝ), (80310909/156250000 : ℝ), (85964213/156250000 : ℝ)] ![(1252342155289/12500000000000 : ℝ), (21527122218947/50000000000000 : ℝ), (5865877288343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-812523359/5000000000 : ℝ)|^4871 ≤ (1252342155289/12500000000000 : ℝ)^3847
        have hw : |(-812523359/5000000000 : ℝ)|=(812523359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(80310909/156250000 : ℝ)|^4871 ≤ (21527122218947/50000000000000 : ℝ)^3847
        have hw : |(80310909/156250000 : ℝ)|=(80310909/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85964213/156250000 : ℝ)|^4871 ≤ (5865877288343/12500000000000 : ℝ)^3847
        have hw : |(85964213/156250000 : ℝ)|=(85964213/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s1_5 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105305011/200000000 : ℝ)*x 0 + (-1451654831/10000000000 : ℝ)*x 1 + (687713703/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105305011/200000000 : ℝ)^4871 ≤ (44388039275099/100000000000000 : ℝ)^3847 := by
    have hnat : (105305011 : ℕ)^4871*100000000000000^3847 ≤ 44388039275099^3847*200000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105305011 200000000 44388039275099 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1451654831/10000000000 : ℝ)^4871 ≤ (1736988497731/20000000000000 : ℝ)^3847 := by
    have hnat : (1451654831 : ℕ)^4871*20000000000000^3847 ≤ 1736988497731^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1451654831 10000000000 1736988497731 20000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687713703/1250000000 : ℝ)^4871 ≤ (5865877277543/12500000000000 : ℝ)^3847 := by
    have hnat : (687713703 : ℕ)^4871*12500000000000^3847 ≤ 5865877277543^3847*1250000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687713703 1250000000 5865877277543 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105305011/200000000 : ℝ), (-1451654831/10000000000 : ℝ), (687713703/1250000000 : ℝ)] ![(44388039275099/100000000000000 : ℝ), (1736988497731/20000000000000 : ℝ), (5865877277543/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105305011/200000000 : ℝ)|^4871 ≤ (44388039275099/100000000000000 : ℝ)^3847
        have hw : |(105305011/200000000 : ℝ)|=(105305011/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1451654831/10000000000 : ℝ)|^4871 ≤ (1736988497731/20000000000000 : ℝ)^3847
        have hw : |(-1451654831/10000000000 : ℝ)|=(1451654831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687713703/1250000000 : ℝ)|^4871 ≤ (5865877277543/12500000000000 : ℝ)^3847
        have hw : |(687713703/1250000000 : ℝ)|=(687713703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s1_6 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316312607/2500000000 : ℝ)*x 0 + (1375427453/2500000000 : ℝ)*x 1 + (-290330947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316312607/2500000000 : ℝ)^4871 ≤ (5548504746603/12500000000000 : ℝ)^3847 := by
    have hnat : (1316312607 : ℕ)^4871*12500000000000^3847 ≤ 5548504746603^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316312607 2500000000 5548504746603 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375427453/2500000000 : ℝ)^4871 ≤ (11731755062683/25000000000000 : ℝ)^3847 := by
    have hnat : (1375427453 : ℕ)^4871*25000000000000^3847 ≤ 11731755062683^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375427453 2500000000 11731755062683 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290330947/2000000000 : ℝ)^4871 ≤ (8684941761427/100000000000000 : ℝ)^3847 := by
    have hnat : (290330947 : ℕ)^4871*100000000000000^3847 ≤ 8684941761427^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290330947 2000000000 8684941761427 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316312607/2500000000 : ℝ), (1375427453/2500000000 : ℝ), (-290330947/2000000000 : ℝ)] ![(5548504746603/12500000000000 : ℝ), (11731755062683/25000000000000 : ℝ), (8684941761427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316312607/2500000000 : ℝ)|^4871 ≤ (5548504746603/12500000000000 : ℝ)^3847
        have hw : |(1316312607/2500000000 : ℝ)|=(1316312607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375427453/2500000000 : ℝ)|^4871 ≤ (11731755062683/25000000000000 : ℝ)^3847
        have hw : |(1375427453/2500000000 : ℝ)|=(1375427453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-290330947/2000000000 : ℝ)|^4871 ≤ (8684941761427/100000000000000 : ℝ)^3847
        have hw : |(-290330947/2000000000 : ℝ)|=(290330947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s1_7 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2091038541/5000000000 : ℝ)*x 0 + (2331102277/5000000000 : ℝ)*x 1 + (3740244229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091038541/5000000000 : ℝ)^4871 ≤ (33159931095927/100000000000000 : ℝ)^3847 := by
    have hnat : (2091038541 : ℕ)^4871*100000000000000^3847 ≤ 33159931095927^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091038541 5000000000 33159931095927 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2331102277/5000000000 : ℝ)^4871 ≤ (7610382434557/20000000000000 : ℝ)^3847 := by
    have hnat : (2331102277 : ℕ)^4871*20000000000000^3847 ≤ 7610382434557^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2331102277 5000000000 7610382434557 20000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3740244229/10000000000 : ℝ)^4871 ≤ (5757631343127/20000000000000 : ℝ)^3847 := by
    have hnat : (3740244229 : ℕ)^4871*20000000000000^3847 ≤ 5757631343127^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3740244229 10000000000 5757631343127 20000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091038541/5000000000 : ℝ), (2331102277/5000000000 : ℝ), (3740244229/10000000000 : ℝ)] ![(33159931095927/100000000000000 : ℝ), (7610382434557/20000000000000 : ℝ), (5757631343127/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091038541/5000000000 : ℝ)|^4871 ≤ (33159931095927/100000000000000 : ℝ)^3847
        have hw : |(2091038541/5000000000 : ℝ)|=(2091038541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2331102277/5000000000 : ℝ)|^4871 ≤ (7610382434557/20000000000000 : ℝ)^3847
        have hw : |(2331102277/5000000000 : ℝ)|=(2331102277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3740244229/10000000000 : ℝ)|^4871 ≤ (5757631343127/20000000000000 : ℝ)^3847
        have hw : |(3740244229/10000000000 : ℝ)|=(3740244229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1638_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4723/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4607/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9587/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2179/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4723/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4607/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4723/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4607/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4723/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4607/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4723/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4607/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4723/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4607/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4723/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4607/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4607/100000 : ℝ) ^ (4867/1024 : ℝ) ≤ (8878727700197/20000000000000000000 : ℝ) := by
    have hpowers : (4607/100000 : ℝ)^4867 ≤ (8878727700197/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4607 : ℕ)^4867*20000000000000000000^1024 ≤ 8878727700197^1024*100000^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4607 100000 8878727700197 20000000000000000000 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4607/100000 : ℝ)) (X := (8878727700197/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4723/20000 : ℝ) ^ (4867/1024 : ℝ) ≤ (104907466415504883/100000000000000000000 : ℝ) := by
    have hpowers : (4723/20000 : ℝ)^4867 ≤ (104907466415504883/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4723 : ℕ)^4867*100000000000000000000^1024 ≤ 104907466415504883^1024*20000^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4723 20000 104907466415504883 100000000000000000000 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4723/20000 : ℝ)) (X := (104907466415504883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000008878727700197/10000000000000000000 : ℝ) ≤ (5000000934026503/5000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (10000008878727700197/10000000000000000000 : ℝ)^1024 ≤ (5000000934026503/5000000000000000 : ℝ)^4867 := by
      have hnat : (10000008878727700197 : ℕ)^1024*5000000000000000^4867 ≤ 5000000934026503^4867*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000008878727700197 10000000000000000000 5000000934026503 5000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000934026503/5000000000000000 : ℝ)) (X := (10000008878727700197/10000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25026237965013501467/25000000000000000000 : ℝ) ≤ (2000441447305853/2000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (25026237965013501467/25000000000000000000 : ℝ)^1024 ≤ (2000441447305853/2000000000000000 : ℝ)^4867 := by
      have hnat : (25026237965013501467 : ℕ)^1024*2000000000000000^4867 ≤ 2000441447305853^4867*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25026237965013501467 25000000000000000000 2000441447305853 2000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000441447305853/2000000000000000 : ℝ)) (X := (25026237965013501467/25000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50104907466415504883/50000000000000000000 : ℝ) ≤ (2501103151251381/2500000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (50104907466415504883/50000000000000000000 : ℝ)^1024 ≤ (2501103151251381/2500000000000000 : ℝ)^4867 := by
      have hnat : (50104907466415504883 : ℕ)^1024*2500000000000000^4867 ≤ 2501103151251381^4867*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50104907466415504883 50000000000000000000 2501103151251381 2500000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501103151251381/2500000000000000 : ℝ)) (X := (50104907466415504883/50000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8878727700197/20000000000000000000 : ℝ) ≤ ((95029857621405643811/95040000000000000000 : ℝ)+2*(2205368476259/1900800000000000 : ℝ)*(4607/100000 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (95029857621405643811/95040000000000000000 : ℝ)+2*(2205368476259/1900800000000000 : ℝ)*(4607/100000 : ℝ)=(5000000934026503/5000000000000000 : ℝ) by norm_num, show 1+2*(8878727700197/20000000000000000000 : ℝ)=(10000008878727700197/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(104907466415504883/100000000000000000000 : ℝ)+(8878727700197/20000000000000000000 : ℝ) ≤ ((95029857621405643811/95040000000000000000 : ℝ)+(2205368476259/1900800000000000 : ℝ)*((4723/20000 : ℝ)+(4607/100000 : ℝ)))^(4867/1024 : ℝ) := by
    rw [show (95029857621405643811/95040000000000000000 : ℝ)+(2205368476259/1900800000000000 : ℝ)*((4723/20000 : ℝ)+(4607/100000 : ℝ))=(2000441447305853/2000000000000000 : ℝ) by norm_num, show 1+(104907466415504883/100000000000000000000 : ℝ)+(8878727700197/20000000000000000000 : ℝ)=(25026237965013501467/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(104907466415504883/100000000000000000000 : ℝ) ≤ ((95029857621405643811/95040000000000000000 : ℝ)+2*(2205368476259/1900800000000000 : ℝ)*(4723/20000 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (95029857621405643811/95040000000000000000 : ℝ)+2*(2205368476259/1900800000000000 : ℝ)*(4723/20000 : ℝ)=(2501103151251381/2500000000000000 : ℝ) by norm_num, show 1+2*(104907466415504883/100000000000000000000 : ℝ)=(50104907466415504883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (95029857621405643811/95040000000000000000 : ℝ)*(X 1 0+X 2 0)+(2205368476259/1900800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (4607/100000 : ℝ)) (hi := (4723/20000 : ℝ)) (c := (95029857621405643811/95040000000000000000 : ℝ)) (alpha := (2205368476259/1900800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (95029857621405643811/95040000000000000000 : ℝ)*(X 0 1+X 2 1)+(2205368476259/1900800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (4607/100000 : ℝ)) (hi := (4723/20000 : ℝ)) (c := (95029857621405643811/95040000000000000000 : ℝ)) (alpha := (2205368476259/1900800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (95029857621405643811/95040000000000000000 : ℝ)*(X 0 2+X 1 2)+(2205368476259/1900800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (4607/100000 : ℝ)) (hi := (4723/20000 : ℝ)) (c := (95029857621405643811/95040000000000000000 : ℝ)) (alpha := (2205368476259/1900800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1624873181/10000000000 : ℝ)*X 0 0+(2752794369/5000000000 : ℝ)*X 0 1+(1027215033/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363919677/10000000000 : ℝ)*X 1 0+(-908644937/5000000000 : ℝ)*X 1 1+(5136074953/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681960357/5000000000 : ℝ)*X 2 0+(5136073731/10000000000 : ℝ)*X 2 1+(-1817290103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((261352373/625000000 : ℝ)*X 0 0+(746071751/2000000000 : ℝ)*X 0 1+(4671947519/10000000000 : ℝ)*X 0 2+(261352373/625000000 : ℝ)*X 1 0+(746071751/2000000000 : ℝ)*X 1 1+(4671947519/10000000000 : ℝ)*X 1 2+(261352373/625000000 : ℝ)*X 2 0+(746071751/2000000000 : ℝ)*X 2 1+(4671947519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-812523359/5000000000 : ℝ)*X 0 0+(80310909/156250000 : ℝ)*X 0 1+(85964213/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((105305011/200000000 : ℝ)*X 1 0+(-1451654831/10000000000 : ℝ)*X 1 1+(687713703/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316312607/2500000000 : ℝ)*X 2 0+(1375427453/2500000000 : ℝ)*X 2 1+(-290330947/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2091038541/5000000000 : ℝ)*X 0 0+(2331102277/5000000000 : ℝ)*X 0 1+(3740244229/10000000000 : ℝ)*X 0 2+(2091038541/5000000000 : ℝ)*X 1 0+(2331102277/5000000000 : ℝ)*X 1 1+(3740244229/10000000000 : ℝ)*X 1 2+(2091038541/5000000000 : ℝ)*X 2 0+(2331102277/5000000000 : ℝ)*X 2 1+(3740244229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2707536310747444668865399739/264000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (588428187/100000000000000 : ℝ)*(base1) + (1275635969/100000000000000 : ℝ)*(base19) + (449708631/25000000000000 : ℝ)*(base23) + (7812379/5000000000000 : ℝ)*(upper3) + (12474817/12500000000000 : ℝ)*(upper5) + (942076069123049/50000000000000 : ℝ)*(major0) + (942076069123049/50000000000000 : ℝ)*(major1) + (942076069123049/50000000000000 : ℝ)*(major2) + (84570712565453/3125000000000 : ℝ)*(sp0) + (676565949827427/25000000000000 : ℝ)*(sp1) + (1353131638055577/50000000000000 : ℝ)*(sp2) + (531018009091893/50000000000000 : ℝ)*(sp3) + (357659921/12500000000000 : ℝ)*(sp4) + (225307389/10000000000000 : ℝ)*(sp7) + (53101942984293/5000000000000 : ℝ)*(f.failure) + (2706265074945677/100000000000000 : ℝ)*(f.sum) + (157590781632869/47520000000000000000000000000 : ℝ)*base66 + (26249451020801050087/1584000000000000000000000000000000 : ℝ)*base68 + (24943303397537050087/1584000000000000000000000000000000 : ℝ)*base70 + (24554317324193050087/1584000000000000000000000000000000 : ℝ)*base72 + (218834313855269/47520000000000000000000000000 : ℝ)*base74 + (9564689821409050087/1584000000000000000000000000000000 : ℝ)*base76 + (22255489233953050087/1584000000000000000000000000000000 : ℝ)*base78 + (15631070205473050087/1584000000000000000000000000000000 : ℝ)*base80 + (254823784678949/47520000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (149387/125000000000000000000 : ℝ)*base90 + (149387/125000000000000000000 : ℝ)*base92 + (149387/125000000000000000000 : ℝ)*base94 + (3/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (387990890299536179457/40000000000000000000000000 : ℝ) := by norm_num
    linear_combination (889320169/50000000000000 : ℝ)*(base19) + (1747690473/100000000000000 : ℝ)*(base23) + (230015969/100000000000000 : ℝ)*(upper3) + (60103/625000000000 : ℝ)*(lower4) + (232356689/100000000000000 : ℝ)*(upper5) + (240532242584139/12500000000000 : ℝ)*(major0) + (240532242584139/12500000000000 : ℝ)*(major1) + (240532242584139/12500000000000 : ℝ)*(major2) + (3106144197/20000000000000 : ℝ)*(sp1) + (8160871503/50000000000000 : ℝ)*(sp2) + (1381935142857223/50000000000000 : ℝ)*(sp4) + (2763852976353123/100000000000000 : ℝ)*(sp5) + (1381926108140483/50000000000000 : ℝ)*(sp6) + (1084645272306033/100000000000000 : ℝ)*(sp7) + (1084645272306033/100000000000000 : ℝ)*(f.failure) + (1381935142857223/50000000000000 : ℝ)*(f.sum) + (319895763461/120000000000000000000000000 : ℝ)*base66 + (3366795750275543/4000000000000000000000000000000 : ℝ)*base68 + (4315793645724457/4000000000000000000000000000000 : ℝ)*base69 + (7426397442275543/4000000000000000000000000000000 : ℝ)*base72 + (111987807581/120000000000000000000000000 : ℝ)*base74 + (14731408694275543/4000000000000000000000000000000 : ℝ)*base76 + (8735641609724457/4000000000000000000000000000000 : ℝ)*base77 + (19879751121724457/4000000000000000000000000000000 : ℝ)*base79 + (249148857581/120000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1369953/2500000000000000000000 : ℝ)*base89 + (1369953/2500000000000000000000 : ℝ)*base91 + (1369953/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1638_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4723/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4607/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9587/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2179/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1638_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1638_s2_0 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-327076049/2000000000 : ℝ)*x 0 + (5455480003/10000000000 : ℝ)*x 1 + (323704229/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327076049/2000000000 : ℝ)^4871 ≤ (10099471616119/100000000000000 : ℝ)^3847 := by
    have hnat : (327076049 : ℕ)^4871*100000000000000^3847 ≤ 10099471616119^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327076049 2000000000 10099471616119 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5455480003/10000000000 : ℝ)^4871 ≤ (9285660143321/20000000000000 : ℝ)^3847 := by
    have hnat : (5455480003 : ℕ)^4871*20000000000000^3847 ≤ 9285660143321^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455480003 10000000000 9285660143321 20000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323704229/625000000 : ℝ)^4871 ≤ (43472227654439/100000000000000 : ℝ)^3847 := by
    have hnat : (323704229 : ℕ)^4871*100000000000000^3847 ≤ 43472227654439^3847*625000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323704229 625000000 43472227654439 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-327076049/2000000000 : ℝ), (5455480003/10000000000 : ℝ), (323704229/625000000 : ℝ)] ![(10099471616119/100000000000000 : ℝ), (9285660143321/20000000000000 : ℝ), (43472227654439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-327076049/2000000000 : ℝ)|^4871 ≤ (10099471616119/100000000000000 : ℝ)^3847
        have hw : |(-327076049/2000000000 : ℝ)|=(327076049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5455480003/10000000000 : ℝ)|^4871 ≤ (9285660143321/20000000000000 : ℝ)^3847
        have hw : |(5455480003/10000000000 : ℝ)|=(5455480003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323704229/625000000 : ℝ)|^4871 ≤ (43472227654439/100000000000000 : ℝ)^3847
        have hw : |(323704229/625000000 : ℝ)|=(323704229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s2_1 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070142573/2000000000 : ℝ)*x 0 + (-1777768387/10000000000 : ℝ)*x 1 + (12948171/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070142573/2000000000 : ℝ)^4871 ≤ (45302259860431/100000000000000 : ℝ)^3847 := by
    have hnat : (1070142573 : ℕ)^4871*100000000000000^3847 ≤ 45302259860431^3847*2000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070142573 2000000000 45302259860431 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1777768387/10000000000 : ℝ)^4871 ≤ (5612752324483/50000000000000 : ℝ)^3847 := by
    have hnat : (1777768387 : ℕ)^4871*50000000000000^3847 ≤ 5612752324483^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777768387 10000000000 5612752324483 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12948171/25000000 : ℝ)^4871 ≤ (4347223547643/10000000000000 : ℝ)^3847 := by
    have hnat : (12948171 : ℕ)^4871*10000000000000^3847 ≤ 4347223547643^3847*25000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12948171 25000000 4347223547643 10000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070142573/2000000000 : ℝ), (-1777768387/10000000000 : ℝ), (12948171/25000000 : ℝ)] ![(45302259860431/100000000000000 : ℝ), (5612752324483/50000000000000 : ℝ), (4347223547643/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070142573/2000000000 : ℝ)|^4871 ≤ (45302259860431/100000000000000 : ℝ)^3847
        have hw : |(1070142573/2000000000 : ℝ)|=(1070142573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1777768387/10000000000 : ℝ)|^4871 ≤ (5612752324483/50000000000000 : ℝ)^3847
        have hw : |(-1777768387/10000000000 : ℝ)|=(1777768387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12948171/25000000 : ℝ)|^4871 ≤ (4347223547643/10000000000000 : ℝ)^3847
        have hw : |(12948171/25000000 : ℝ)|=(12948171/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s2_2 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350715387/10000000000 : ℝ)*x 0 + (647408387/1250000000 : ℝ)*x 1 + (-1777766739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350715387/10000000000 : ℝ)^4871 ≤ (5662785862107/12500000000000 : ℝ)^3847 := by
    have hnat : (5350715387 : ℕ)^4871*12500000000000^3847 ≤ 5662785862107^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350715387 10000000000 5662785862107 12500000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647408387/1250000000 : ℝ)^4871 ≤ (43472221617903/100000000000000 : ℝ)^3847 := by
    have hnat : (647408387 : ℕ)^4871*100000000000000^3847 ≤ 43472221617903^3847*1250000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647408387 1250000000 43472221617903 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1777766739/10000000000 : ℝ)^4871 ≤ (35079660853/312500000000 : ℝ)^3847 := by
    have hnat : (1777766739 : ℕ)^4871*312500000000^3847 ≤ 35079660853^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777766739 10000000000 35079660853 312500000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350715387/10000000000 : ℝ), (647408387/1250000000 : ℝ), (-1777766739/10000000000 : ℝ)] ![(5662785862107/12500000000000 : ℝ), (43472221617903/100000000000000 : ℝ), (35079660853/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350715387/10000000000 : ℝ)|^4871 ≤ (5662785862107/12500000000000 : ℝ)^3847
        have hw : |(5350715387/10000000000 : ℝ)|=(5350715387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647408387/1250000000 : ℝ)|^4871 ≤ (43472221617903/100000000000000 : ℝ)^3847
        have hw : |(647408387/1250000000 : ℝ)|=(647408387/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1777766739/10000000000 : ℝ)|^4871 ≤ (35079660853/312500000000 : ℝ)^3847
        have hw : |(-1777766739/10000000000 : ℝ)|=(1777766739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s2_3 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523680963/1250000000 : ℝ)*x 0 + (3848436597/10000000000 : ℝ)*x 1 + (284517249/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523680963/1250000000 : ℝ)^4871 ≤ (16616973366557/50000000000000 : ℝ)^3847 := by
    have hnat : (523680963 : ℕ)^4871*50000000000000^3847 ≤ 16616973366557^3847*1250000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523680963 1250000000 16616973366557 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3848436597/10000000000 : ℝ)^4871 ≤ (7461647560303/25000000000000 : ℝ)^3847 := by
    have hnat : (3848436597 : ℕ)^4871*25000000000000^3847 ≤ 7461647560303^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848436597 10000000000 7461647560303 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284517249/625000000 : ℝ)^4871 ≤ (36919463014567/100000000000000 : ℝ)^3847 := by
    have hnat : (284517249 : ℕ)^4871*100000000000000^3847 ≤ 36919463014567^3847*625000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284517249 625000000 36919463014567 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523680963/1250000000 : ℝ), (3848436597/10000000000 : ℝ), (284517249/625000000 : ℝ)] ![(16616973366557/50000000000000 : ℝ), (7461647560303/25000000000000 : ℝ), (36919463014567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523680963/1250000000 : ℝ)|^4871 ≤ (16616973366557/50000000000000 : ℝ)^3847
        have hw : |(523680963/1250000000 : ℝ)|=(523680963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3848436597/10000000000 : ℝ)|^4871 ≤ (7461647560303/25000000000000 : ℝ)^3847
        have hw : |(3848436597/10000000000 : ℝ)|=(3848436597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(284517249/625000000 : ℝ)|^4871 ≤ (36919463014567/100000000000000 : ℝ)^3847
        have hw : |(284517249/625000000 : ℝ)|=(284517249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s2_4 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1635451547/10000000000 : ℝ)*x 0 + (207256437/400000000 : ℝ)*x 1 + (5453314207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1635451547/10000000000 : ℝ)^4871 ≤ (10100029161319/100000000000000 : ℝ)^3847 := by
    have hnat : (1635451547 : ℕ)^4871*100000000000000^3847 ≤ 10100029161319^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635451547 10000000000 10100029161319 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207256437/400000000 : ℝ)^4871 ≤ (21747503427013/50000000000000 : ℝ)^3847 := by
    have hnat : (207256437 : ℕ)^4871*50000000000000^3847 ≤ 21747503427013^3847*400000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207256437 400000000 21747503427013 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453314207/10000000000 : ℝ)^4871 ≤ (46404963967253/100000000000000 : ℝ)^3847 := by
    have hnat : (5453314207 : ℕ)^4871*100000000000000^3847 ≤ 46404963967253^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453314207 10000000000 46404963967253 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1635451547/10000000000 : ℝ), (207256437/400000000 : ℝ), (5453314207/10000000000 : ℝ)] ![(10100029161319/100000000000000 : ℝ), (21747503427013/50000000000000 : ℝ), (46404963967253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1635451547/10000000000 : ℝ)|^4871 ≤ (10100029161319/100000000000000 : ℝ)^3847
        have hw : |(-1635451547/10000000000 : ℝ)|=(1635451547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207256437/400000000 : ℝ)|^4871 ≤ (21747503427013/50000000000000 : ℝ)^3847
        have hw : |(207256437/400000000 : ℝ)|=(207256437/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453314207/10000000000 : ℝ)|^4871 ≤ (46404963967253/100000000000000 : ℝ)^3847
        have hw : |(5453314207/10000000000 : ℝ)|=(5453314207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s2_5 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277029723/10000000000 : ℝ)*x 0 + (-751860229/5000000000 : ℝ)*x 1 + (5453314439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277029723/10000000000 : ℝ)^4871 ≤ (44513812119229/100000000000000 : ℝ)^3847 := by
    have hnat : (5277029723 : ℕ)^4871*100000000000000^3847 ≤ 44513812119229^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277029723 10000000000 44513812119229 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (751860229/5000000000 : ℝ)^4871 ≤ (9081221407413/100000000000000 : ℝ)^3847 := by
    have hnat : (751860229 : ℕ)^4871*100000000000000^3847 ≤ 9081221407413^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751860229 5000000000 9081221407413 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5453314439/10000000000 : ℝ)^4871 ≤ (46404966466953/100000000000000 : ℝ)^3847 := by
    have hnat : (5453314439 : ℕ)^4871*100000000000000^3847 ≤ 46404966466953^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453314439 10000000000 46404966466953 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277029723/10000000000 : ℝ), (-751860229/5000000000 : ℝ), (5453314439/10000000000 : ℝ)] ![(44513812119229/100000000000000 : ℝ), (9081221407413/100000000000000 : ℝ), (46404966466953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277029723/10000000000 : ℝ)|^4871 ≤ (44513812119229/100000000000000 : ℝ)^3847
        have hw : |(5277029723/10000000000 : ℝ)|=(5277029723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-751860229/5000000000 : ℝ)|^4871 ≤ (9081221407413/100000000000000 : ℝ)^3847
        have hw : |(-751860229/5000000000 : ℝ)|=(751860229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5453314439/10000000000 : ℝ)|^4871 ≤ (46404966466953/100000000000000 : ℝ)^3847
        have hw : |(5453314439/10000000000 : ℝ)|=(5453314439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s2_6 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277030631/10000000000 : ℝ)*x 0 + (5453313583/10000000000 : ℝ)*x 1 + (-751860197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277030631/10000000000 : ℝ)^4871 ≤ (22256910908669/50000000000000 : ℝ)^3847 := by
    have hnat : (5277030631 : ℕ)^4871*50000000000000^3847 ≤ 22256910908669^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277030631 10000000000 22256910908669 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453313583/10000000000 : ℝ)^4871 ≤ (46404957243923/100000000000000 : ℝ)^3847 := by
    have hnat : (5453313583 : ℕ)^4871*100000000000000^3847 ≤ 46404957243923^3847*10000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453313583 10000000000 46404957243923 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (751860197/5000000000 : ℝ)^4871 ≤ (4540610459013/50000000000000 : ℝ)^3847 := by
    have hnat : (751860197 : ℕ)^4871*50000000000000^3847 ≤ 4540610459013^3847*5000000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      751860197 5000000000 4540610459013 50000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277030631/10000000000 : ℝ), (5453313583/10000000000 : ℝ), (-751860197/5000000000 : ℝ)] ![(22256910908669/50000000000000 : ℝ), (46404957243923/100000000000000 : ℝ), (4540610459013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277030631/10000000000 : ℝ)|^4871 ≤ (22256910908669/50000000000000 : ℝ)^3847
        have hw : |(5277030631/10000000000 : ℝ)|=(5277030631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453313583/10000000000 : ℝ)|^4871 ≤ (46404957243923/100000000000000 : ℝ)^3847
        have hw : |(5453313583/10000000000 : ℝ)|=(5453313583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-751860197/5000000000 : ℝ)|^4871 ≤ (4540610459013/50000000000000 : ℝ)^3847
        have hw : |(-751860197/5000000000 : ℝ)|=(751860197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1638_s2_7 (p : ℝ) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523703923/1250000000 : ℝ)*x 0 + (227340849/500000000 : ℝ)*x 1 + (963488839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523703923/1250000000 : ℝ)^4871 ≤ (8308947921727/25000000000000 : ℝ)^3847 := by
    have hnat : (523703923 : ℕ)^4871*25000000000000^3847 ≤ 8308947921727^3847*1250000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523703923 1250000000 8308947921727 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227340849/500000000 : ℝ)^4871 ≤ (36863414151339/100000000000000 : ℝ)^3847 := by
    have hnat : (227340849 : ℕ)^4871*100000000000000^3847 ≤ 36863414151339^3847*500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227340849 500000000 36863414151339 100000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (963488839/2500000000 : ℝ)^4871 ≤ (7475198537641/25000000000000 : ℝ)^3847 := by
    have hnat : (963488839 : ℕ)^4871*25000000000000^3847 ≤ 7475198537641^3847*2500000000^4871 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963488839 2500000000 7475198537641 25000000000000 4871 3847 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4871/1024 : ℝ)) 4871 3847 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523703923/1250000000 : ℝ), (227340849/500000000 : ℝ), (963488839/2500000000 : ℝ)] ![(8308947921727/25000000000000 : ℝ), (36863414151339/100000000000000 : ℝ), (7475198537641/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523703923/1250000000 : ℝ)|^4871 ≤ (8308947921727/25000000000000 : ℝ)^3847
        have hw : |(523703923/1250000000 : ℝ)|=(523703923/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227340849/500000000 : ℝ)|^4871 ≤ (36863414151339/100000000000000 : ℝ)^3847
        have hw : |(227340849/500000000 : ℝ)|=(227340849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(963488839/2500000000 : ℝ)|^4871 ≤ (7475198537641/25000000000000 : ℝ)^3847
        have hw : |(963488839/2500000000 : ℝ)|=(963488839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1638_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2179/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9587/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (263/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8193/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2179/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9587/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2179/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9587/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2179/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9587/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2179/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9587/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2179/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9587/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2179/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9587/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9587/100000 : ℝ) ^ (4867/1024 : ℝ) ≤ (722735867179423/50000000000000000000 : ℝ) := by
    have hpowers : (9587/100000 : ℝ)^4867 ≤ (722735867179423/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9587 : ℕ)^4867*50000000000000000000^1024 ≤ 722735867179423^1024*100000^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9587 100000 722735867179423 50000000000000000000 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9587/100000 : ℝ)) (X := (722735867179423/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2179/12500 : ℝ) ^ (4867/1024 : ℝ) ≤ (12392150255943243/50000000000000000000 : ℝ) := by
    have hpowers : (2179/12500 : ℝ)^4867 ≤ (12392150255943243/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2179 : ℕ)^4867*50000000000000000000^1024 ≤ 12392150255943243^1024*12500^4867 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2179 12500 12392150255943243 50000000000000000000 4867 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2179/12500 : ℝ)) (X := (12392150255943243/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000722735867179423/25000000000000000000 : ℝ) ≤ (5000030411879237/5000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (25000722735867179423/25000000000000000000 : ℝ)^1024 ≤ (5000030411879237/5000000000000000 : ℝ)^4867 := by
      have hnat : (25000722735867179423 : ℕ)^1024*5000000000000000^4867 ≤ 5000030411879237^4867*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000722735867179423 25000000000000000000 5000030411879237 5000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000030411879237/5000000000000000 : ℝ)) (X := (25000722735867179423/25000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006557443061561333/25000000000000000000 : ℝ) ≤ (10000551808214217/10000000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (25006557443061561333/25000000000000000000 : ℝ)^1024 ≤ (10000551808214217/10000000000000000 : ℝ)^4867 := by
      have hnat : (25006557443061561333 : ℕ)^1024*10000000000000000^4867 ≤ 10000551808214217^4867*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006557443061561333 25000000000000000000 10000551808214217 10000000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000551808214217/10000000000000000 : ℝ)) (X := (25006557443061561333/25000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012392150255943243/25000000000000000000 : ℝ) ≤ (250026069816749/250000000000000 : ℝ) ^ (4867/1024 : ℝ) := by
    have hpowers : (25012392150255943243/25000000000000000000 : ℝ)^1024 ≤ (250026069816749/250000000000000 : ℝ)^4867 := by
      have hnat : (25012392150255943243 : ℕ)^1024*250000000000000^4867 ≤ 250026069816749^4867*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012392150255943243 25000000000000000000 250026069816749 250000000000000 1024 4867 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250026069816749/250000000000000 : ℝ)) (X := (25012392150255943243/25000000000000000000 : ℝ)) (by norm_num) 4867 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(722735867179423/50000000000000000000 : ℝ) ≤ ((9805132878303851531/9806250000000000000 : ℝ)+2*(490984455743/784500000000000 : ℝ)*(9587/100000 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (9805132878303851531/9806250000000000000 : ℝ)+2*(490984455743/784500000000000 : ℝ)*(9587/100000 : ℝ)=(5000030411879237/5000000000000000 : ℝ) by norm_num, show 1+2*(722735867179423/50000000000000000000 : ℝ)=(25000722735867179423/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12392150255943243/50000000000000000000 : ℝ)+(722735867179423/50000000000000000000 : ℝ) ≤ ((9805132878303851531/9806250000000000000 : ℝ)+(490984455743/784500000000000 : ℝ)*((2179/12500 : ℝ)+(9587/100000 : ℝ)))^(4867/1024 : ℝ) := by
    rw [show (9805132878303851531/9806250000000000000 : ℝ)+(490984455743/784500000000000 : ℝ)*((2179/12500 : ℝ)+(9587/100000 : ℝ))=(10000551808214217/10000000000000000 : ℝ) by norm_num, show 1+(12392150255943243/50000000000000000000 : ℝ)+(722735867179423/50000000000000000000 : ℝ)=(25006557443061561333/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12392150255943243/50000000000000000000 : ℝ) ≤ ((9805132878303851531/9806250000000000000 : ℝ)+2*(490984455743/784500000000000 : ℝ)*(2179/12500 : ℝ))^(4867/1024 : ℝ) := by
    rw [show (9805132878303851531/9806250000000000000 : ℝ)+2*(490984455743/784500000000000 : ℝ)*(2179/12500 : ℝ)=(250026069816749/250000000000000 : ℝ) by norm_num, show 1+2*(12392150255943243/50000000000000000000 : ℝ)=(25012392150255943243/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9805132878303851531/9806250000000000000 : ℝ)*(X 1 0+X 2 0)+(490984455743/784500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (9587/100000 : ℝ)) (hi := (2179/12500 : ℝ)) (c := (9805132878303851531/9806250000000000000 : ℝ)) (alpha := (490984455743/784500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9805132878303851531/9806250000000000000 : ℝ)*(X 0 1+X 2 1)+(490984455743/784500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (9587/100000 : ℝ)) (hi := (2179/12500 : ℝ)) (c := (9805132878303851531/9806250000000000000 : ℝ)) (alpha := (490984455743/784500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9805132878303851531/9806250000000000000 : ℝ)*(X 0 2+X 1 2)+(490984455743/784500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4867/1024 : ℝ)) (lo := (9587/100000 : ℝ)) (hi := (2179/12500 : ℝ)) (c := (9805132878303851531/9806250000000000000 : ℝ)) (alpha := (490984455743/784500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-327076049/2000000000 : ℝ)*X 0 0+(5455480003/10000000000 : ℝ)*X 0 1+(323704229/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070142573/2000000000 : ℝ)*X 1 0+(-1777768387/10000000000 : ℝ)*X 1 1+(12948171/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350715387/10000000000 : ℝ)*X 2 0+(647408387/1250000000 : ℝ)*X 2 1+(-1777766739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((523680963/1250000000 : ℝ)*X 0 0+(3848436597/10000000000 : ℝ)*X 0 1+(284517249/625000000 : ℝ)*X 0 2+(523680963/1250000000 : ℝ)*X 1 0+(3848436597/10000000000 : ℝ)*X 1 1+(284517249/625000000 : ℝ)*X 1 2+(523680963/1250000000 : ℝ)*X 2 0+(3848436597/10000000000 : ℝ)*X 2 1+(284517249/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1635451547/10000000000 : ℝ)*X 0 0+(207256437/400000000 : ℝ)*X 0 1+(5453314207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277029723/10000000000 : ℝ)*X 1 0+(-751860229/5000000000 : ℝ)*X 1 1+(5453314439/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277030631/10000000000 : ℝ)*X 2 0+(5453313583/10000000000 : ℝ)*X 2 1+(-751860197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((523703923/1250000000 : ℝ)*X 0 0+(227340849/500000000 : ℝ)*X 0 1+(963488839/2500000000 : ℝ)*X 0 2+(523703923/1250000000 : ℝ)*X 1 0+(227340849/500000000 : ℝ)*X 1 1+(963488839/2500000000 : ℝ)*X 1 2+(523703923/1250000000 : ℝ)*X 2 0+(227340849/500000000 : ℝ)*X 2 1+(963488839/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1638_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (294251264221914901350010131/40859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13081699/10000000000000 : ℝ)*(base19) + (953300683/50000000000000 : ℝ)*(base23) + (16692363/20000000000000 : ℝ)*(upper4) + (501481691/100000000000000 : ℝ)*(upper5) + (157538552143747/6250000000000 : ℝ)*(major0) + (157538552143747/6250000000000 : ℝ)*(major1) + (157538552143747/6250000000000 : ℝ)*(major2) + (1810205262319099/50000000000000 : ℝ)*(sp0) + (3620422418305631/100000000000000 : ℝ)*(sp1) + (362043700431439/10000000000000 : ℝ)*(sp2) + (1420786808735127/100000000000000 : ℝ)*(sp3) + (14193138779/50000000000000 : ℝ)*(sp4) + (3272358627/20000000000000 : ℝ)*(sp5) + (7708896999/100000000000000 : ℝ)*(sp7) + (710397258816063/50000000000000 : ℝ)*(f.failure) + (905109727728939/25000000000000 : ℝ)*(f.sum) + (1894566060077/1225781250000000000000000000 : ℝ)*base66 + (408329501866531187/40859375000000000000000000000000 : ℝ)*base68 + (24273877940480453/10214843750000000000000000000000 : ℝ)*base70 + (61180388874789031/20429687500000000000000000000000 : ℝ)*base72 + (7185111444091/9806250000000000000000000000 : ℝ)*base74 + (183702705457312437/40859375000000000000000000000000 : ℝ)*base76 + (3352498662477543/2553710937500000000000000000000 : ℝ)*base77 + (124922163507781187/40859375000000000000000000000000 : ℝ)*base80 + (6043727972057/19612500000000000000000000000 : ℝ)*base82 + (847183/1250000000000000000000 : ℝ)*base89 + (847183/1250000000000000000000 : ℝ)*base91 + (847183/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (191632036671820993603120453/40859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (884557/390625000000 : ℝ)*(base19) + (131540197/10000000000000 : ℝ)*(base23) + (188087761/100000000000000 : ℝ)*(lower4) + (5780497/12500000000000 : ℝ)*(lower5) + (320067094525469/12500000000000 : ℝ)*(major0) + (320067094525469/12500000000000 : ℝ)*(major1) + (320067094525469/12500000000000 : ℝ)*(major2) + (1717618113/25000000000000 : ℝ)*(sp1) + (1751362557/12500000000000 : ℝ)*(sp2) + (1481858547/50000000000000 : ℝ)*(sp3) + (3677777200979081/100000000000000 : ℝ)*(sp4) + (3677770104060037/100000000000000 : ℝ)*(sp5) + (1838880937338327/50000000000000 : ℝ)*(sp6) + (1443293191376711/100000000000000 : ℝ)*(sp7) + (288659231018761/20000000000000 : ℝ)*(f.failure) + (3677777200979081/100000000000000 : ℝ)*(f.sum) + (121987106794811/39225000000000000000000000000 : ℝ)*base65 + (65224764992393389/5107421875000000000000000000000 : ℝ)*base68 + (68162339922052403/10214843750000000000000000000000 : ℝ)*base70 + (20750516029396153/10214843750000000000000000000000 : ℝ)*base72 + (48328490200141/9806250000000000000000000000 : ℝ)*base74 + (3801747008492533/638427734375000000000000000000 : ℝ)*base76 + (70092685332024763/40859375000000000000000000000000 : ℝ)*base77 + (5552294860931013/40859375000000000000000000000000 : ℝ)*base79 + (6650478352433/4903125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3393401/500000000000000000000 : ℝ)*base89 + (3393401/500000000000000000000 : ℝ)*base91 + (3393401/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1638_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2179/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9587/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (263/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1638_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1638_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (263/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1638_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1638_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1638_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4867/1024 : ℝ) ≤ p) (hpb : p ≤ (4871/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44352241/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (263/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1638_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
