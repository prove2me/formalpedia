-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:09:41.438503+00:00
-- url     : https://prove2.me/submissions/30e9821e-6aef-40be-99e4-3083156e76e6

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
theorem support_rectangle_w1122_s0_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-47453921/250000000 : ℝ)*x 0 + (605896431/1000000000 : ℝ)*x 1 + (238896881/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (47453921/250000000 : ℝ)^8315 ≤ (2757004239109/25000000000000 : ℝ)^6267 := by
    have hnat : (47453921 : ℕ)^8315*25000000000000^6267 ≤ 2757004239109^6267*250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47453921 250000000 2757004239109 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605896431/1000000000 : ℝ)^8315 ≤ (51438479212091/100000000000000 : ℝ)^6267 := by
    have hnat : (605896431 : ℕ)^8315*100000000000000^6267 ≤ 51438479212091^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605896431 1000000000 51438479212091 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238896881/500000000 : ℝ)^8315 ≤ (9383375954623/25000000000000 : ℝ)^6267 := by
    have hnat : (238896881 : ℕ)^8315*25000000000000^6267 ≤ 9383375954623^6267*500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238896881 500000000 9383375954623 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-47453921/250000000 : ℝ), (605896431/1000000000 : ℝ), (238896881/500000000 : ℝ)] ![(2757004239109/25000000000000 : ℝ), (51438479212091/100000000000000 : ℝ), (9383375954623/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-47453921/250000000 : ℝ)|^8315 ≤ (2757004239109/25000000000000 : ℝ)^6267
        have hw : |(-47453921/250000000 : ℝ)|=(47453921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605896431/1000000000 : ℝ)|^8315 ≤ (51438479212091/100000000000000 : ℝ)^6267
        have hw : |(605896431/1000000000 : ℝ)|=(605896431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238896881/500000000 : ℝ)|^8315 ≤ (9383375954623/25000000000000 : ℝ)^6267
        have hw : |(238896881/500000000 : ℝ)|=(238896881/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s0_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1103584031/2000000000 : ℝ)*x 0 + (-658472933/2500000000 : ℝ)*x 1 + (2388968827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103584031/2000000000 : ℝ)^8315 ≤ (11358733654643/25000000000000 : ℝ)^6267 := by
    have hnat : (1103584031 : ℕ)^8315*25000000000000^6267 ≤ 11358733654643^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103584031 2000000000 11358733654643 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658472933/2500000000 : ℝ)^8315 ≤ (4257890298807/25000000000000 : ℝ)^6267 := by
    have hnat : (658472933 : ℕ)^8315*25000000000000^6267 ≤ 4257890298807^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658472933 2500000000 4257890298807 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2388968827/5000000000 : ℝ)^8315 ≤ (586461002701/1562500000000 : ℝ)^6267 := by
    have hnat : (2388968827 : ℕ)^8315*1562500000000^6267 ≤ 586461002701^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2388968827 5000000000 586461002701 1562500000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103584031/2000000000 : ℝ), (-658472933/2500000000 : ℝ), (2388968827/5000000000 : ℝ)] ![(11358733654643/25000000000000 : ℝ), (4257890298807/25000000000000 : ℝ), (586461002701/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103584031/2000000000 : ℝ)|^8315 ≤ (11358733654643/25000000000000 : ℝ)^6267
        have hw : |(1103584031/2000000000 : ℝ)|=(1103584031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-658472933/2500000000 : ℝ)|^8315 ≤ (4257890298807/25000000000000 : ℝ)^6267
        have hw : |(-658472933/2500000000 : ℝ)|=(658472933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2388968827/5000000000 : ℝ)|^8315 ≤ (586461002701/1562500000000 : ℝ)^6267
        have hw : |(2388968827/5000000000 : ℝ)|=(2388968827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s0_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5517920307/10000000000 : ℝ)*x 0 + (1194484377/2500000000 : ℝ)*x 1 + (-658472929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517920307/10000000000 : ℝ)^8315 ≤ (9086987255831/20000000000000 : ℝ)^6267 := by
    have hnat : (5517920307 : ℕ)^8315*20000000000000^6267 ≤ 9086987255831^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517920307 10000000000 9086987255831 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1194484377/2500000000 : ℝ)^8315 ≤ (37533502651147/100000000000000 : ℝ)^6267 := by
    have hnat : (1194484377 : ℕ)^8315*100000000000000^6267 ≤ 37533502651147^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194484377 2500000000 37533502651147 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658472929/2500000000 : ℝ)^8315 ≤ (17031561057957/100000000000000 : ℝ)^6267 := by
    have hnat : (658472929 : ℕ)^8315*100000000000000^6267 ≤ 17031561057957^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658472929 2500000000 17031561057957 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517920307/10000000000 : ℝ), (1194484377/2500000000 : ℝ), (-658472929/2500000000 : ℝ)] ![(9086987255831/20000000000000 : ℝ), (37533502651147/100000000000000 : ℝ), (17031561057957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517920307/10000000000 : ℝ)|^8315 ≤ (9086987255831/20000000000000 : ℝ)^6267
        have hw : |(5517920307/10000000000 : ℝ)|=(5517920307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1194484377/2500000000 : ℝ)|^8315 ≤ (37533502651147/100000000000000 : ℝ)^6267
        have hw : |(1194484377/2500000000 : ℝ)|=(1194484377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-658472929/2500000000 : ℝ)|^8315 ≤ (17031561057957/100000000000000 : ℝ)^6267
        have hw : |(-658472929/2500000000 : ℝ)|=(658472929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s0_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1050653327/2500000000 : ℝ)*x 0 + (3122023021/10000000000 : ℝ)*x 1 + (2830299471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050653327/2500000000 : ℝ)^8315 ≤ (31658397058301/100000000000000 : ℝ)^6267 := by
    have hnat : (1050653327 : ℕ)^8315*100000000000000^6267 ≤ 31658397058301^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050653327 2500000000 31658397058301 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122023021/10000000000 : ℝ)^8315 ≤ (21341370438629/100000000000000 : ℝ)^6267 := by
    have hnat : (3122023021 : ℕ)^8315*100000000000000^6267 ≤ 21341370438629^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122023021 10000000000 21341370438629 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2830299471/5000000000 : ℝ)^8315 ≤ (9400046496317/20000000000000 : ℝ)^6267 := by
    have hnat : (2830299471 : ℕ)^8315*20000000000000^6267 ≤ 9400046496317^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830299471 5000000000 9400046496317 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050653327/2500000000 : ℝ), (3122023021/10000000000 : ℝ), (2830299471/5000000000 : ℝ)] ![(31658397058301/100000000000000 : ℝ), (21341370438629/100000000000000 : ℝ), (9400046496317/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050653327/2500000000 : ℝ)|^8315 ≤ (31658397058301/100000000000000 : ℝ)^6267
        have hw : |(1050653327/2500000000 : ℝ)|=(1050653327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122023021/10000000000 : ℝ)|^8315 ≤ (21341370438629/100000000000000 : ℝ)^6267
        have hw : |(3122023021/10000000000 : ℝ)|=(3122023021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2830299471/5000000000 : ℝ)|^8315 ≤ (9400046496317/20000000000000 : ℝ)^6267
        have hw : |(2830299471/5000000000 : ℝ)|=(2830299471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s0_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-190336283/1000000000 : ℝ)*x 0 + (2405497373/5000000000 : ℝ)*x 1 + (6024745669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190336283/1000000000 : ℝ)^8315 ≤ (11068165119547/100000000000000 : ℝ)^6267 := by
    have hnat : (190336283 : ℕ)^8315*100000000000000^6267 ≤ 11068165119547^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190336283 1000000000 11068165119547 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2405497373/5000000000 : ℝ)^8315 ≤ (1893921899159/5000000000000 : ℝ)^6267 := by
    have hnat : (2405497373 : ℕ)^8315*5000000000000^6267 ≤ 1893921899159^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405497373 5000000000 1893921899159 5000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6024745669/10000000000 : ℝ)^8315 ≤ (25526698444427/50000000000000 : ℝ)^6267 := by
    have hnat : (6024745669 : ℕ)^8315*50000000000000^6267 ≤ 25526698444427^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024745669 10000000000 25526698444427 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190336283/1000000000 : ℝ), (2405497373/5000000000 : ℝ), (6024745669/10000000000 : ℝ)] ![(11068165119547/100000000000000 : ℝ), (1893921899159/5000000000000 : ℝ), (25526698444427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190336283/1000000000 : ℝ)|^8315 ≤ (11068165119547/100000000000000 : ℝ)^6267
        have hw : |(-190336283/1000000000 : ℝ)|=(190336283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2405497373/5000000000 : ℝ)|^8315 ≤ (1893921899159/5000000000000 : ℝ)^6267
        have hw : |(2405497373/5000000000 : ℝ)|=(2405497373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6024745669/10000000000 : ℝ)|^8315 ≤ (25526698444427/50000000000000 : ℝ)^6267
        have hw : |(6024745669/10000000000 : ℝ)|=(6024745669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s0_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169932861/10000000000 : ℝ)*x 0 + (-1387084449/10000000000 : ℝ)*x 1 + (3012374667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169932861/10000000000 : ℝ)^8315 ≤ (41672956383191/100000000000000 : ℝ)^6267 := by
    have hnat : (5169932861 : ℕ)^8315*100000000000000^6267 ≤ 41672956383191^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169932861 10000000000 41672956383191 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387084449/10000000000 : ℝ)^8315 ≤ (1818401375379/25000000000000 : ℝ)^6267 := by
    have hnat : (1387084449 : ℕ)^8315*25000000000000^6267 ≤ 1818401375379^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387084449 10000000000 1818401375379 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3012374667/5000000000 : ℝ)^8315 ≤ (6381679761881/12500000000000 : ℝ)^6267 := by
    have hnat : (3012374667 : ℕ)^8315*12500000000000^6267 ≤ 6381679761881^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3012374667 5000000000 6381679761881 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169932861/10000000000 : ℝ), (-1387084449/10000000000 : ℝ), (3012374667/5000000000 : ℝ)] ![(41672956383191/100000000000000 : ℝ), (1818401375379/25000000000000 : ℝ), (6381679761881/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169932861/10000000000 : ℝ)|^8315 ≤ (41672956383191/100000000000000 : ℝ)^6267
        have hw : |(5169932861/10000000000 : ℝ)|=(5169932861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1387084449/10000000000 : ℝ)|^8315 ≤ (1818401375379/25000000000000 : ℝ)^6267
        have hw : |(-1387084449/10000000000 : ℝ)|=(1387084449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3012374667/5000000000 : ℝ)|^8315 ≤ (6381679761881/12500000000000 : ℝ)^6267
        have hw : |(3012374667/5000000000 : ℝ)|=(3012374667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s0_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169937523/10000000000 : ℝ)*x 0 + (6024745993/10000000000 : ℝ)*x 1 + (-693541341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169937523/10000000000 : ℝ)^8315 ≤ (1666920249691/4000000000000 : ℝ)^6267 := by
    have hnat : (5169937523 : ℕ)^8315*4000000000000^6267 ≤ 1666920249691^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169937523 10000000000 1666920249691 4000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6024745993/10000000000 : ℝ)^8315 ≤ (51053400531639/100000000000000 : ℝ)^6267 := by
    have hnat : (6024745993 : ℕ)^8315*100000000000000^6267 ≤ 51053400531639^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024745993 10000000000 51053400531639 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693541341/5000000000 : ℝ)^8315 ≤ (1818398301931/25000000000000 : ℝ)^6267 := by
    have hnat : (693541341 : ℕ)^8315*25000000000000^6267 ≤ 1818398301931^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693541341 5000000000 1818398301931 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169937523/10000000000 : ℝ), (6024745993/10000000000 : ℝ), (-693541341/5000000000 : ℝ)] ![(1666920249691/4000000000000 : ℝ), (51053400531639/100000000000000 : ℝ), (1818398301931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169937523/10000000000 : ℝ)|^8315 ≤ (1666920249691/4000000000000 : ℝ)^6267
        have hw : |(5169937523/10000000000 : ℝ)|=(5169937523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6024745993/10000000000 : ℝ)|^8315 ≤ (51053400531639/100000000000000 : ℝ)^6267
        have hw : |(6024745993/10000000000 : ℝ)|=(6024745993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-693541341/5000000000 : ℝ)|^8315 ≤ (1818398301931/25000000000000 : ℝ)^6267
        have hw : |(-693541341/5000000000 : ℝ)|=(693541341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s0_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1053231563/2500000000 : ℝ)*x 0 + (5595094453/10000000000 : ℝ)*x 1 + (1594914171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053231563/2500000000 : ℝ)^8315 ≤ (31761513688887/100000000000000 : ℝ)^6267 := by
    have hnat : (1053231563 : ℕ)^8315*100000000000000^6267 ≤ 31761513688887^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053231563 2500000000 31761513688887 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5595094453/10000000000 : ℝ)^8315 ≤ (46279976045619/100000000000000 : ℝ)^6267 := by
    have hnat : (5595094453 : ℕ)^8315*100000000000000^6267 ≤ 46279976045619^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5595094453 10000000000 46279976045619 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594914171/5000000000 : ℝ)^8315 ≤ (5489627564393/25000000000000 : ℝ)^6267 := by
    have hnat : (1594914171 : ℕ)^8315*25000000000000^6267 ≤ 5489627564393^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594914171 5000000000 5489627564393 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053231563/2500000000 : ℝ), (5595094453/10000000000 : ℝ), (1594914171/5000000000 : ℝ)] ![(31761513688887/100000000000000 : ℝ), (46279976045619/100000000000000 : ℝ), (5489627564393/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053231563/2500000000 : ℝ)|^8315 ≤ (31761513688887/100000000000000 : ℝ)^6267
        have hw : |(1053231563/2500000000 : ℝ)|=(1053231563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5595094453/10000000000 : ℝ)|^8315 ≤ (46279976045619/100000000000000 : ℝ)^6267
        have hw : |(5595094453/10000000000 : ℝ)|=(5595094453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594914171/5000000000 : ℝ)|^8315 ≤ (5489627564393/25000000000000 : ℝ)^6267
        have hw : |(1594914171/5000000000 : ℝ)|=(1594914171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (331/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6973/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4157/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4157 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4157*1^1024 ≤ 0^1024*1^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4157/1024 : ℝ) ≤ (1212005411647598443/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4157 ≤ (1212005411647598443/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4157*50000000000000000000^1024 ≤ 1212005411647598443^1024*5^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1212005411647598443 50000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1212005411647598443/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4157 := by
      have hnat : (1 : ℕ)^1024*1^4157 ≤ 1^4157*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51212005411647598443/50000000000000000000 : ℝ) ≤ (1005917319098569/1000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (51212005411647598443/50000000000000000000 : ℝ)^1024 ≤ (1005917319098569/1000000000000000 : ℝ)^4157 := by
      have hnat : (51212005411647598443 : ℕ)^1024*1000000000000000^4157 ≤ 1005917319098569^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51212005411647598443 50000000000000000000 1005917319098569 1000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005917319098569/1000000000000000 : ℝ)) (X := (51212005411647598443/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26212005411647598443/25000000000000000000 : ℝ) ≤ (505917319098569/500000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (26212005411647598443/25000000000000000000 : ℝ)^1024 ≤ (505917319098569/500000000000000 : ℝ)^4157 := by
      have hnat : (26212005411647598443 : ℕ)^1024*500000000000000^4157 ≤ 505917319098569^4157*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26212005411647598443 25000000000000000000 505917319098569 500000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505917319098569/500000000000000 : ℝ)) (X := (26212005411647598443/25000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5917319098569/400000000000000 : ℝ)*(0 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5917319098569/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1212005411647598443/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5917319098569/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5917319098569/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1005917319098569/1000000000000000 : ℝ) by norm_num, show 1+(1212005411647598443/50000000000000000000 : ℝ)+(0 : ℝ)=(51212005411647598443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1212005411647598443/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5917319098569/400000000000000 : ℝ)*(2/5 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5917319098569/400000000000000 : ℝ)*(2/5 : ℝ)=(505917319098569/500000000000000 : ℝ) by norm_num, show 1+2*(1212005411647598443/50000000000000000000 : ℝ)=(26212005411647598443/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5917319098569/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5917319098569/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5917319098569/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5917319098569/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5917319098569/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5917319098569/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-47453921/250000000 : ℝ)*X 0 0+(605896431/1000000000 : ℝ)*X 0 1+(238896881/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1103584031/2000000000 : ℝ)*X 1 0+(-658472933/2500000000 : ℝ)*X 1 1+(2388968827/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5517920307/10000000000 : ℝ)*X 2 0+(1194484377/2500000000 : ℝ)*X 2 1+(-658472929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1050653327/2500000000 : ℝ)*X 0 0+(3122023021/10000000000 : ℝ)*X 0 1+(2830299471/5000000000 : ℝ)*X 0 2+(1050653327/2500000000 : ℝ)*X 1 0+(3122023021/10000000000 : ℝ)*X 1 1+(2830299471/5000000000 : ℝ)*X 1 2+(1050653327/2500000000 : ℝ)*X 2 0+(3122023021/10000000000 : ℝ)*X 2 1+(2830299471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-190336283/1000000000 : ℝ)*X 0 0+(2405497373/5000000000 : ℝ)*X 0 1+(6024745669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5169932861/10000000000 : ℝ)*X 1 0+(-1387084449/10000000000 : ℝ)*X 1 1+(3012374667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169937523/10000000000 : ℝ)*X 2 0+(6024745993/10000000000 : ℝ)*X 2 1+(-693541341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1053231563/2500000000 : ℝ)*X 0 0+(5595094453/10000000000 : ℝ)*X 0 1+(1594914171/5000000000 : ℝ)*X 0 2+(1053231563/2500000000 : ℝ)*X 1 0+(5595094453/10000000000 : ℝ)*X 1 1+(1594914171/5000000000 : ℝ)*X 1 2+(1053231563/2500000000 : ℝ)*X 2 0+(5595094453/10000000000 : ℝ)*X 2 1+(1594914171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18671087107708472864313/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44921053/100000000000000 : ℝ)*(base1) + (28670247/3125000000000 : ℝ)*(base19) + (871291087/100000000000000 : ℝ)*(base23) + (67660469/100000000000000 : ℝ)*(base24) + (107146609/50000000000000 : ℝ)*(upper3) + (587276590178141/100000000000000 : ℝ)*(major0) + (587276590178141/100000000000000 : ℝ)*(major1) + (587276590178141/100000000000000 : ℝ)*(major2) + (156125374620721/20000000000000 : ℝ)*(sp0) + (390313941866153/50000000000000 : ℝ)*(sp1) + (390313931114327/50000000000000 : ℝ)*(sp2) + (78784516334769/20000000000000 : ℝ)*(sp3) + (1972997659/100000000000000 : ℝ)*(sp4) + (1628107253/100000000000000 : ℝ)*(sp7) + (49240531837769/12500000000000 : ℝ)*(f.failure) + (78062880118021/10000000000000 : ℝ)*(f.sum) + (43925011260229/20000000000000000000000000000 : ℝ)*base65 + (77357627460229/40000000000000000000000000000 : ℝ)*base67 + (132311428700229/40000000000000000000000000000 : ℝ)*base69 + (271346750340229/40000000000000000000000000000 : ℝ)*base71 + (15776060940229/20000000000000000000000000000 : ℝ)*base73 + (236345782580229/40000000000000000000000000000 : ℝ)*base75 + (260072776420229/40000000000000000000000000000 : ℝ)*base77 + (98464944740229/40000000000000000000000000000 : ℝ)*base79 + (85914876859771/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6634777/1250000000000000000000 : ℝ)*base89 + (6634777/1250000000000000000000 : ℝ)*base91 + (6634777/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26917522081007505128391/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95840923/50000000000000 : ℝ)*(base19) + (1539893799/100000000000000 : ℝ)*(base23) + (551925359/100000000000000 : ℝ)*(base39) + (200398229/100000000000000 : ℝ)*(upper3) + (255422383/100000000000000 : ℝ)*(upper5) + (619822184694711/100000000000000 : ℝ)*(major0) + (619822184694711/100000000000000 : ℝ)*(major1) + (77477704096169/12500000000000 : ℝ)*(major2) + (712839857/50000000000000 : ℝ)*(sp1) + (1226424049/50000000000000 : ℝ)*(sp2) + (823888955744589/100000000000000 : ℝ)*(sp4) + (205971834595757/25000000000000 : ℝ)*(sp5) + (823885514928051/100000000000000 : ℝ)*(sp6) + (415754682269321/100000000000000 : ℝ)*(sp7) + (415754682269321/100000000000000 : ℝ)*(f.failure) + (205972376917487/25000000000000 : ℝ)*(f.sum) + (55295191345847/40000000000000000000000000000 : ℝ)*base65 + (20585437247161/5000000000000000000000000000 : ℝ)*base67 + (45489749048559/40000000000000000000000000000 : ℝ)*base69 + (24004797932161/5000000000000000000000000000 : ℝ)*base71 + (73245904505847/40000000000000000000000000000 : ℝ)*base73 + (309628978368559/40000000000000000000000000000 : ℝ)*base75 + (22491035928559/40000000000000000000000000000 : ℝ)*base77 + (168107548368559/40000000000000000000000000000 : ℝ)*base79 + (34398445328559/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (40876807/10000000000000000000000 : ℝ)*base90 + (40876807/10000000000000000000000 : ℝ)*base92 + (40876807/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1122_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (331/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6973/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1122_s1_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104264767/10000000000 : ℝ)*x 0 + (2853444269/5000000000 : ℝ)*x 1 + (2499027393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104264767/10000000000 : ℝ)^8315 ≤ (1264432337613/10000000000000 : ℝ)^6267 := by
    have hnat : (2104264767 : ℕ)^8315*10000000000000^6267 ≤ 1264432337613^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104264767 10000000000 1264432337613 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2853444269/5000000000 : ℝ)^8315 ≤ (11877714470091/25000000000000 : ℝ)^6267 := by
    have hnat : (2853444269 : ℕ)^8315*25000000000000^6267 ≤ 11877714470091^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2853444269 5000000000 11877714470091 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2499027393/5000000000 : ℝ)^8315 ≤ (19922409363047/50000000000000 : ℝ)^6267 := by
    have hnat : (2499027393 : ℕ)^8315*50000000000000^6267 ≤ 19922409363047^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499027393 5000000000 19922409363047 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104264767/10000000000 : ℝ), (2853444269/5000000000 : ℝ), (2499027393/5000000000 : ℝ)] ![(1264432337613/10000000000000 : ℝ), (11877714470091/25000000000000 : ℝ), (19922409363047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104264767/10000000000 : ℝ)|^8315 ≤ (1264432337613/10000000000000 : ℝ)^6267
        have hw : |(-2104264767/10000000000 : ℝ)|=(2104264767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2853444269/5000000000 : ℝ)|^8315 ≤ (11877714470091/25000000000000 : ℝ)^6267
        have hw : |(2853444269/5000000000 : ℝ)|=(2853444269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2499027393/5000000000 : ℝ)|^8315 ≤ (19922409363047/50000000000000 : ℝ)^6267
        have hw : |(2499027393/5000000000 : ℝ)|=(2499027393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s1_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2710111377/5000000000 : ℝ)*x 0 + (-2487182811/10000000000 : ℝ)*x 1 + (1249513633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710111377/5000000000 : ℝ)^8315 ≤ (22185350727983/50000000000000 : ℝ)^6267 := by
    have hnat : (2710111377 : ℕ)^8315*50000000000000^6267 ≤ 22185350727983^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710111377 5000000000 22185350727983 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2487182811/10000000000 : ℝ)^8315 ≤ (3946120622421/25000000000000 : ℝ)^6267 := by
    have hnat : (2487182811 : ℕ)^8315*25000000000000^6267 ≤ 3946120622421^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487182811 10000000000 3946120622421 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249513633/2500000000 : ℝ)^8315 ≤ (39844816039469/100000000000000 : ℝ)^6267 := by
    have hnat : (1249513633 : ℕ)^8315*100000000000000^6267 ≤ 39844816039469^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249513633 2500000000 39844816039469 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710111377/5000000000 : ℝ), (-2487182811/10000000000 : ℝ), (1249513633/2500000000 : ℝ)] ![(22185350727983/50000000000000 : ℝ), (3946120622421/25000000000000 : ℝ), (39844816039469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710111377/5000000000 : ℝ)|^8315 ≤ (22185350727983/50000000000000 : ℝ)^6267
        have hw : |(2710111377/5000000000 : ℝ)|=(2710111377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2487182811/10000000000 : ℝ)|^8315 ≤ (3946120622421/25000000000000 : ℝ)^6267
        have hw : |(-2487182811/10000000000 : ℝ)|=(2487182811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1249513633/2500000000 : ℝ)|^8315 ≤ (39844816039469/100000000000000 : ℝ)^6267
        have hw : |(1249513633/2500000000 : ℝ)|=(1249513633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s1_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2710112151/5000000000 : ℝ)*x 0 + (999610623/2000000000 : ℝ)*x 1 + (-2487182593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710112151/5000000000 : ℝ)^8315 ≤ (5546339783657/12500000000000 : ℝ)^6267 := by
    have hnat : (2710112151 : ℕ)^8315*12500000000000^6267 ≤ 5546339783657^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710112151 5000000000 5546339783657 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999610623/2000000000 : ℝ)^8315 ≤ (7968960210297/20000000000000 : ℝ)^6267 := by
    have hnat : (999610623 : ℕ)^8315*20000000000000^6267 ≤ 7968960210297^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999610623 2000000000 7968960210297 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2487182593/10000000000 : ℝ)^8315 ≤ (3946120163517/25000000000000 : ℝ)^6267 := by
    have hnat : (2487182593 : ℕ)^8315*25000000000000^6267 ≤ 3946120163517^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487182593 10000000000 3946120163517 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710112151/5000000000 : ℝ), (999610623/2000000000 : ℝ), (-2487182593/10000000000 : ℝ)] ![(5546339783657/12500000000000 : ℝ), (7968960210297/20000000000000 : ℝ), (3946120163517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710112151/5000000000 : ℝ)|^8315 ≤ (5546339783657/12500000000000 : ℝ)^6267
        have hw : |(2710112151/5000000000 : ℝ)|=(2710112151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(999610623/2000000000 : ℝ)|^8315 ≤ (7968960210297/20000000000000 : ℝ)^6267
        have hw : |(999610623/2000000000 : ℝ)|=(999610623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2487182593/10000000000 : ℝ)|^8315 ≤ (3946120163517/25000000000000 : ℝ)^6267
        have hw : |(-2487182593/10000000000 : ℝ)|=(2487182593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s1_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4319127173/10000000000 : ℝ)*x 0 + (3673266071/10000000000 : ℝ)*x 1 + (1269485177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319127173/10000000000 : ℝ)^8315 ≤ (16414083590919/50000000000000 : ℝ)^6267 := by
    have hnat : (4319127173 : ℕ)^8315*50000000000000^6267 ≤ 16414083590919^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319127173 10000000000 16414083590919 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3673266071/10000000000 : ℝ)^8315 ≤ (26479840593317/100000000000000 : ℝ)^6267 := by
    have hnat : (3673266071 : ℕ)^8315*100000000000000^6267 ≤ 26479840593317^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3673266071 10000000000 26479840593317 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269485177/2500000000 : ℝ)^8315 ≤ (5086499026613/12500000000000 : ℝ)^6267 := by
    have hnat : (1269485177 : ℕ)^8315*12500000000000^6267 ≤ 5086499026613^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269485177 2500000000 5086499026613 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319127173/10000000000 : ℝ), (3673266071/10000000000 : ℝ), (1269485177/2500000000 : ℝ)] ![(16414083590919/50000000000000 : ℝ), (26479840593317/100000000000000 : ℝ), (5086499026613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319127173/10000000000 : ℝ)|^8315 ≤ (16414083590919/50000000000000 : ℝ)^6267
        have hw : |(4319127173/10000000000 : ℝ)|=(4319127173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3673266071/10000000000 : ℝ)|^8315 ≤ (26479840593317/100000000000000 : ℝ)^6267
        have hw : |(3673266071/10000000000 : ℝ)|=(3673266071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269485177/2500000000 : ℝ)|^8315 ≤ (5086499026613/12500000000000 : ℝ)^6267
        have hw : |(1269485177/2500000000 : ℝ)|=(1269485177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s1_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2105099311/10000000000 : ℝ)*x 0 + (1251951877/2500000000 : ℝ)*x 1 + (227877651/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105099311/10000000000 : ℝ)^8315 ≤ (1581372157369/12500000000000 : ℝ)^6267 := by
    have hnat : (2105099311 : ℕ)^8315*12500000000000^6267 ≤ 1581372157369^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105099311 10000000000 1581372157369 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1251951877/2500000000 : ℝ)^8315 ≤ (39948008730769/100000000000000 : ℝ)^6267 := by
    have hnat : (1251951877 : ℕ)^8315*100000000000000^6267 ≤ 39948008730769^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1251951877 2500000000 39948008730769 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (227877651/400000000 : ℝ)^8315 ≤ (47401013994799/100000000000000 : ℝ)^6267 := by
    have hnat : (227877651 : ℕ)^8315*100000000000000^6267 ≤ 47401013994799^6267*400000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227877651 400000000 47401013994799 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2105099311/10000000000 : ℝ), (1251951877/2500000000 : ℝ), (227877651/400000000 : ℝ)] ![(1581372157369/12500000000000 : ℝ), (39948008730769/100000000000000 : ℝ), (47401013994799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2105099311/10000000000 : ℝ)|^8315 ≤ (1581372157369/12500000000000 : ℝ)^6267
        have hw : |(-2105099311/10000000000 : ℝ)|=(2105099311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1251951877/2500000000 : ℝ)|^8315 ≤ (39948008730769/100000000000000 : ℝ)^6267
        have hw : |(1251951877/2500000000 : ℝ)|=(1251951877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(227877651/400000000 : ℝ)|^8315 ≤ (47401013994799/100000000000000 : ℝ)^6267
        have hw : |(227877651/400000000 : ℝ)|=(227877651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s1_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1047734737/2000000000 : ℝ)*x 0 + (-1788295691/10000000000 : ℝ)*x 1 + (1424235261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047734737/2000000000 : ℝ)^8315 ≤ (42409717013869/100000000000000 : ℝ)^6267 := by
    have hnat : (1047734737 : ℕ)^8315*100000000000000^6267 ≤ 42409717013869^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047734737 2000000000 42409717013869 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1788295691/10000000000 : ℝ)^8315 ≤ (2037854304523/20000000000000 : ℝ)^6267 := by
    have hnat : (1788295691 : ℕ)^8315*20000000000000^6267 ≤ 2037854304523^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788295691 10000000000 2037854304523 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1424235261/2500000000 : ℝ)^8315 ≤ (1185025286117/2500000000000 : ℝ)^6267 := by
    have hnat : (1424235261 : ℕ)^8315*2500000000000^6267 ≤ 1185025286117^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424235261 2500000000 1185025286117 2500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047734737/2000000000 : ℝ), (-1788295691/10000000000 : ℝ), (1424235261/2500000000 : ℝ)] ![(42409717013869/100000000000000 : ℝ), (2037854304523/20000000000000 : ℝ), (1185025286117/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047734737/2000000000 : ℝ)|^8315 ≤ (42409717013869/100000000000000 : ℝ)^6267
        have hw : |(1047734737/2000000000 : ℝ)|=(1047734737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1788295691/10000000000 : ℝ)|^8315 ≤ (2037854304523/20000000000000 : ℝ)^6267
        have hw : |(-1788295691/10000000000 : ℝ)|=(1788295691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1424235261/2500000000 : ℝ)|^8315 ≤ (1185025286117/2500000000000 : ℝ)^6267
        have hw : |(1424235261/2500000000 : ℝ)|=(1424235261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s1_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5238673721/10000000000 : ℝ)*x 0 + (5696941203/10000000000 : ℝ)*x 1 + (-1788295409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5238673721/10000000000 : ℝ)^8315 ≤ (42409717400547/100000000000000 : ℝ)^6267 := by
    have hnat : (5238673721 : ℕ)^8315*100000000000000^6267 ≤ 42409717400547^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238673721 10000000000 42409717400547 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5696941203/10000000000 : ℝ)^8315 ≤ (47401013199957/100000000000000 : ℝ)^6267 := by
    have hnat : (5696941203 : ℕ)^8315*100000000000000^6267 ≤ 47401013199957^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696941203 10000000000 47401013199957 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1788295409/10000000000 : ℝ)^8315 ≤ (1018926939077/10000000000000 : ℝ)^6267 := by
    have hnat : (1788295409 : ℕ)^8315*10000000000000^6267 ≤ 1018926939077^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788295409 10000000000 1018926939077 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5238673721/10000000000 : ℝ), (5696941203/10000000000 : ℝ), (-1788295409/10000000000 : ℝ)] ![(42409717400547/100000000000000 : ℝ), (47401013199957/100000000000000 : ℝ), (1018926939077/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5238673721/10000000000 : ℝ)|^8315 ≤ (42409717400547/100000000000000 : ℝ)^6267
        have hw : |(5238673721/10000000000 : ℝ)|=(5238673721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5696941203/10000000000 : ℝ)|^8315 ≤ (47401013199957/100000000000000 : ℝ)^6267
        have hw : |(5696941203/10000000000 : ℝ)|=(5696941203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1788295409/10000000000 : ℝ)|^8315 ≤ (1018926939077/10000000000000 : ℝ)^6267
        have hw : |(-1788295409/10000000000 : ℝ)|=(1788295409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s1_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1080194653/2500000000 : ℝ)*x 0 + (5058614783/10000000000 : ℝ)*x 1 + (1846488653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080194653/2500000000 : ℝ)^8315 ≤ (1642241105703/5000000000000 : ℝ)^6267 := by
    have hnat : (1080194653 : ℕ)^8315*5000000000000^6267 ≤ 1642241105703^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080194653 2500000000 1642241105703 5000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5058614783/10000000000 : ℝ)^8315 ≤ (40486642646553/100000000000000 : ℝ)^6267 := by
    have hnat : (5058614783 : ℕ)^8315*100000000000000^6267 ≤ 40486642646553^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5058614783 10000000000 40486642646553 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846488653/5000000000 : ℝ)^8315 ≤ (6667133805733/25000000000000 : ℝ)^6267 := by
    have hnat : (1846488653 : ℕ)^8315*25000000000000^6267 ≤ 6667133805733^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846488653 5000000000 6667133805733 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080194653/2500000000 : ℝ), (5058614783/10000000000 : ℝ), (1846488653/5000000000 : ℝ)] ![(1642241105703/5000000000000 : ℝ), (40486642646553/100000000000000 : ℝ), (6667133805733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080194653/2500000000 : ℝ)|^8315 ≤ (1642241105703/5000000000000 : ℝ)^6267
        have hw : |(1080194653/2500000000 : ℝ)|=(1080194653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5058614783/10000000000 : ℝ)|^8315 ≤ (40486642646553/100000000000000 : ℝ)^6267
        have hw : |(5058614783/10000000000 : ℝ)|=(5058614783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1846488653/5000000000 : ℝ)|^8315 ≤ (6667133805733/25000000000000 : ℝ)^6267
        have hw : |(1846488653/5000000000 : ℝ)|=(1846488653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6973/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5537/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1283/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6973/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6973/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (331/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6973/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6973/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (331/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6973/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6973/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (331/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (331/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (8542153153/100000000000000000000 : ℝ) := by
    have hpowers : (331/100000 : ℝ)^4157 ≤ (8542153153/100000000000000000000 : ℝ)^1024 := by
      have hnat : (331 : ℕ)^4157*100000000000000000000^1024 ≤ 8542153153^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        331 100000 8542153153 100000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (331/100000 : ℝ)) (X := (8542153153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6973/25000 : ℝ) ^ (4157/1024 : ℝ) ≤ (140225076191324713/25000000000000000000 : ℝ) := by
    have hpowers : (6973/25000 : ℝ)^4157 ≤ (140225076191324713/25000000000000000000 : ℝ)^1024 := by
      have hnat : (6973 : ℕ)^4157*25000000000000000000^1024 ≤ 140225076191324713^1024*25000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6973 25000 140225076191324713 25000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6973/25000 : ℝ)) (X := (140225076191324713/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000008542153153/50000000000000000000 : ℝ) ≤ (10000000000420841/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (50000000008542153153/50000000000000000000 : ℝ)^1024 ≤ (10000000000420841/10000000000000000 : ℝ)^4157 := by
      have hnat : (50000000008542153153 : ℕ)^1024*10000000000000000^4157 ≤ 10000000000420841^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000008542153153 50000000000000000000 10000000000420841 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000420841/10000000000000000 : ℝ)) (X := (50000000008542153153/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20112180062661490401/20000000000000000000 : ℝ) ≤ (5006893816184403/5000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (20112180062661490401/20000000000000000000 : ℝ)^1024 ≤ (5006893816184403/5000000000000000 : ℝ)^4157 := by
      have hnat : (20112180062661490401 : ℕ)^1024*5000000000000000^4157 ≤ 5006893816184403^4157*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20112180062661490401 20000000000000000000 5006893816184403 5000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006893816184403/5000000000000000 : ℝ)) (X := (20112180062661490401/20000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12640225076191324713/12500000000000000000 : ℝ) ≤ (10027575264316771/10000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (12640225076191324713/12500000000000000000 : ℝ)^1024 ≤ (10027575264316771/10000000000000000 : ℝ)^4157 := by
      have hnat : (12640225076191324713 : ℕ)^1024*10000000000000000^4157 ≤ 10027575264316771^4157*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12640225076191324713 12500000000000000000 10027575264316771 10000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027575264316771/10000000000000000 : ℝ)) (X := (12640225076191324713/12500000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8542153153/100000000000000000000 : ℝ) ≤ ((275600872599249245971/275610000000000000000 : ℝ)+2*(2757526389593/551220000000000 : ℝ)*(331/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (275600872599249245971/275610000000000000000 : ℝ)+2*(2757526389593/551220000000000 : ℝ)*(331/100000 : ℝ)=(10000000000420841/10000000000000000 : ℝ) by norm_num, show 1+2*(8542153153/100000000000000000000 : ℝ)=(50000000008542153153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(140225076191324713/25000000000000000000 : ℝ)+(8542153153/100000000000000000000 : ℝ) ≤ ((275600872599249245971/275610000000000000000 : ℝ)+(2757526389593/551220000000000 : ℝ)*((6973/25000 : ℝ)+(331/100000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (275600872599249245971/275610000000000000000 : ℝ)+(2757526389593/551220000000000 : ℝ)*((6973/25000 : ℝ)+(331/100000 : ℝ))=(5006893816184403/5000000000000000 : ℝ) by norm_num, show 1+(140225076191324713/25000000000000000000 : ℝ)+(8542153153/100000000000000000000 : ℝ)=(20112180062661490401/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(140225076191324713/25000000000000000000 : ℝ) ≤ ((275600872599249245971/275610000000000000000 : ℝ)+2*(2757526389593/551220000000000 : ℝ)*(6973/25000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (275600872599249245971/275610000000000000000 : ℝ)+2*(2757526389593/551220000000000 : ℝ)*(6973/25000 : ℝ)=(10027575264316771/10000000000000000 : ℝ) by norm_num, show 1+2*(140225076191324713/25000000000000000000 : ℝ)=(12640225076191324713/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (275600872599249245971/275610000000000000000 : ℝ)*(X 1 0+X 2 0)+(2757526389593/551220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (331/100000 : ℝ)) (hi := (6973/25000 : ℝ)) (c := (275600872599249245971/275610000000000000000 : ℝ)) (alpha := (2757526389593/551220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (275600872599249245971/275610000000000000000 : ℝ)*(X 0 1+X 2 1)+(2757526389593/551220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (331/100000 : ℝ)) (hi := (6973/25000 : ℝ)) (c := (275600872599249245971/275610000000000000000 : ℝ)) (alpha := (2757526389593/551220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (275600872599249245971/275610000000000000000 : ℝ)*(X 0 2+X 1 2)+(2757526389593/551220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (331/100000 : ℝ)) (hi := (6973/25000 : ℝ)) (c := (275600872599249245971/275610000000000000000 : ℝ)) (alpha := (2757526389593/551220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2104264767/10000000000 : ℝ)*X 0 0+(2853444269/5000000000 : ℝ)*X 0 1+(2499027393/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2710111377/5000000000 : ℝ)*X 1 0+(-2487182811/10000000000 : ℝ)*X 1 1+(1249513633/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710112151/5000000000 : ℝ)*X 2 0+(999610623/2000000000 : ℝ)*X 2 1+(-2487182593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319127173/10000000000 : ℝ)*X 0 0+(3673266071/10000000000 : ℝ)*X 0 1+(1269485177/2500000000 : ℝ)*X 0 2+(4319127173/10000000000 : ℝ)*X 1 0+(3673266071/10000000000 : ℝ)*X 1 1+(1269485177/2500000000 : ℝ)*X 1 2+(4319127173/10000000000 : ℝ)*X 2 0+(3673266071/10000000000 : ℝ)*X 2 1+(1269485177/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2105099311/10000000000 : ℝ)*X 0 0+(1251951877/2500000000 : ℝ)*X 0 1+(227877651/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1047734737/2000000000 : ℝ)*X 1 0+(-1788295691/10000000000 : ℝ)*X 1 1+(1424235261/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5238673721/10000000000 : ℝ)*X 2 0+(5696941203/10000000000 : ℝ)*X 2 1+(-1788295409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080194653/2500000000 : ℝ)*X 0 0+(5058614783/10000000000 : ℝ)*X 0 1+(1846488653/5000000000 : ℝ)*X 0 2+(1080194653/2500000000 : ℝ)*X 1 0+(5058614783/10000000000 : ℝ)*X 1 1+(1846488653/5000000000 : ℝ)*X 1 2+(1080194653/2500000000 : ℝ)*X 2 0+(5058614783/10000000000 : ℝ)*X 2 1+(1846488653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1193506180716405716929184469/287093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (313912881/100000000000000 : ℝ)*(base1) + (296387467/50000000000000 : ℝ)*(base19) + (1017004073/100000000000000 : ℝ)*(base23) + (506607/25000000000000 : ℝ)*(upper3) + (42339451/50000000000000 : ℝ)*(upper5) + (66333726504639/6250000000000 : ℝ)*(major0) + (66333726504639/6250000000000 : ℝ)*(major1) + (66333726504639/6250000000000 : ℝ)*(major2) + (352692112442943/25000000000000 : ℝ)*(sp0) + (176346124866801/12500000000000 : ℝ)*(sp1) + (352692302787149/25000000000000 : ℝ)*(sp2) + (44494285469347/6250000000000 : ℝ)*(sp3) + (2092293779/100000000000000 : ℝ)*(sp4) + (318221663/50000000000000 : ℝ)*(sp5) + (22247152544451/3125000000000 : ℝ)*(f.failure) + (1410770228152669/100000000000000 : ℝ)*(f.sum) + (19801231660317/9187000000000000000000000000 : ℝ)*base66 + (6022666571489730177/574187500000000000000000000000000 : ℝ)*base68 + (2790748628811667677/574187500000000000000000000000000 : ℝ)*base70 + (998268401304894823/574187500000000000000000000000000 : ℝ)*base71 + (40205901049581/4593500000000000000000000000 : ℝ)*base74 + (1526406191274519823/574187500000000000000000000000000 : ℝ)*base75 + (2140920340404480177/574187500000000000000000000000000 : ℝ)*base78 + (2121082302381230177/574187500000000000000000000000000 : ℝ)*base80 + (8131399189653/2296750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (929517/312500000000000000000 : ℝ)*base90 + (929517/312500000000000000000 : ℝ)*base92 + (929517/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7756524118512818306090563717/4593500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26551977/100000000000000 : ℝ)*(base1) + (16115051/4000000000000 : ℝ)*(base19) + (4322299/1000000000000 : ℝ)*(base23) + (28609387/100000000000000 : ℝ)*(upper3) + (33744229/100000000000000 : ℝ)*(upper5) + (1091678017217491/100000000000000 : ℝ)*(major0) + (1091678017217491/100000000000000 : ℝ)*(major1) + (1091678017217491/100000000000000 : ℝ)*(major2) + (1375098779/100000000000000 : ℝ)*(sp1) + (483587661/25000000000000 : ℝ)*(sp2) + (725548603955067/50000000000000 : ℝ)*(sp4) + (725547701691551/50000000000000 : ℝ)*(sp5) + (362773703694403/25000000000000 : ℝ)*(sp6) + (732258770238607/100000000000000 : ℝ)*(sp7) + (91532349598823/12500000000000 : ℝ)*(f.failure) + (362774295339539/25000000000000 : ℝ)*(f.sum) + (35398628891753/27561000000000000000000000000 : ℝ)*base65 + (36434104200810978761/27561000000000000000000000000000000 : ℝ)*base67 + (103048483393731978761/27561000000000000000000000000000000 : ℝ)*base69 + (284616820057923978761/27561000000000000000000000000000000 : ℝ)*base71 + (93969128241667/27561000000000000000000000000 : ℝ)*base74 + (221751669060705978761/27561000000000000000000000000000000 : ℝ)*base75 + (276701397211179978761/27561000000000000000000000000000000 : ℝ)*base77 + (124719780790146978761/27561000000000000000000000000000000 : ℝ)*base79 + (130418647535899/27561000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (12136041/1250000000000000000000 : ℝ)*base90 + (12136041/1250000000000000000000 : ℝ)*base92 + (12136041/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1122_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6973/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (331/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5537/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1283/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1122_s2_0 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2158582727/10000000000 : ℝ)*x 0 + (5514648667/10000000000 : ℝ)*x 1 + (1031155019/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158582727/10000000000 : ℝ)^8315 ≤ (13079192597543/100000000000000 : ℝ)^6267 := by
    have hnat : (2158582727 : ℕ)^8315*100000000000000^6267 ≤ 13079192597543^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158582727 10000000000 13079192597543 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514648667/10000000000 : ℝ)^8315 ≤ (45399197436379/100000000000000 : ℝ)^6267 := by
    have hnat : (5514648667 : ℕ)^8315*100000000000000^6267 ≤ 45399197436379^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514648667 10000000000 45399197436379 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031155019/2000000000 : ℝ)^8315 ≤ (41521609944359/100000000000000 : ℝ)^6267 := by
    have hnat : (1031155019 : ℕ)^8315*100000000000000^6267 ≤ 41521609944359^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031155019 2000000000 41521609944359 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2158582727/10000000000 : ℝ), (5514648667/10000000000 : ℝ), (1031155019/2000000000 : ℝ)] ![(13079192597543/100000000000000 : ℝ), (45399197436379/100000000000000 : ℝ), (41521609944359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2158582727/10000000000 : ℝ)|^8315 ≤ (13079192597543/100000000000000 : ℝ)^6267
        have hw : |(-2158582727/10000000000 : ℝ)|=(2158582727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514648667/10000000000 : ℝ)|^8315 ≤ (45399197436379/100000000000000 : ℝ)^6267
        have hw : |(5514648667/10000000000 : ℝ)|=(5514648667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031155019/2000000000 : ℝ)|^8315 ≤ (41521609944359/100000000000000 : ℝ)^6267
        have hw : |(1031155019/2000000000 : ℝ)|=(1031155019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s2_1 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5374726221/10000000000 : ℝ)*x 0 + (-1172654229/5000000000 : ℝ)*x 1 + (161118019/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374726221/10000000000 : ℝ)^8315 ≤ (43877229084309/100000000000000 : ℝ)^6267 := by
    have hnat : (5374726221 : ℕ)^8315*100000000000000^6267 ≤ 43877229084309^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374726221 10000000000 43877229084309 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1172654229/5000000000 : ℝ)^8315 ≤ (7300572391763/50000000000000 : ℝ)^6267 := by
    have hnat : (1172654229 : ℕ)^8315*50000000000000^6267 ≤ 7300572391763^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1172654229 5000000000 7300572391763 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161118019/312500000 : ℝ)^8315 ≤ (1297550815971/3125000000000 : ℝ)^6267 := by
    have hnat : (161118019 : ℕ)^8315*3125000000000^6267 ≤ 1297550815971^6267*312500000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161118019 312500000 1297550815971 3125000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374726221/10000000000 : ℝ), (-1172654229/5000000000 : ℝ), (161118019/312500000 : ℝ)] ![(43877229084309/100000000000000 : ℝ), (7300572391763/50000000000000 : ℝ), (1297550815971/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374726221/10000000000 : ℝ)|^8315 ≤ (43877229084309/100000000000000 : ℝ)^6267
        have hw : |(5374726221/10000000000 : ℝ)|=(5374726221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1172654229/5000000000 : ℝ)|^8315 ≤ (7300572391763/50000000000000 : ℝ)^6267
        have hw : |(-1172654229/5000000000 : ℝ)|=(1172654229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161118019/312500000 : ℝ)|^8315 ≤ (1297550815971/3125000000000 : ℝ)^6267
        have hw : |(161118019/312500000 : ℝ)|=(161118019/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s2_2 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5248756/9765625 : ℝ)*x 0 + (257788833/500000000 : ℝ)*x 1 + (-2345308493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5248756/9765625 : ℝ)^8315 ≤ (43877228250289/100000000000000 : ℝ)^6267 := by
    have hnat : (5248756 : ℕ)^8315*100000000000000^6267 ≤ 43877228250289^6267*9765625^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5248756 9765625 43877228250289 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257788833/500000000 : ℝ)^8315 ≤ (20760813333351/50000000000000 : ℝ)^6267 := by
    have hnat : (257788833 : ℕ)^8315*50000000000000^6267 ≤ 20760813333351^6267*500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257788833 500000000 20760813333351 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2345308493/10000000000 : ℝ)^8315 ≤ (1825143134079/12500000000000 : ℝ)^6267 := by
    have hnat : (2345308493 : ℕ)^8315*12500000000000^6267 ≤ 1825143134079^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345308493 10000000000 1825143134079 12500000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5248756/9765625 : ℝ), (257788833/500000000 : ℝ), (-2345308493/10000000000 : ℝ)] ![(43877228250289/100000000000000 : ℝ), (20760813333351/50000000000000 : ℝ), (1825143134079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5248756/9765625 : ℝ)|^8315 ≤ (43877228250289/100000000000000 : ℝ)^6267
        have hw : |(5248756/9765625 : ℝ)|=(5248756/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257788833/500000000 : ℝ)|^8315 ≤ (20760813333351/50000000000000 : ℝ)^6267
        have hw : |(257788833/500000000 : ℝ)|=(257788833/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2345308493/10000000000 : ℝ)|^8315 ≤ (1825143134079/12500000000000 : ℝ)^6267
        have hw : |(-2345308493/10000000000 : ℝ)|=(2345308493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s2_3 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356338739/10000000000 : ℝ)*x 0 + (4015203513/10000000000 : ℝ)*x 1 + (4726369769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356338739/10000000000 : ℝ)^8315 ≤ (16601976730147/50000000000000 : ℝ)^6267 := by
    have hnat : (4356338739 : ℕ)^8315*50000000000000^6267 ≤ 16601976730147^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356338739 10000000000 16601976730147 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4015203513/10000000000 : ℝ)^8315 ≤ (29799069972411/100000000000000 : ℝ)^6267 := by
    have hnat : (4015203513 : ℕ)^8315*100000000000000^6267 ≤ 29799069972411^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015203513 10000000000 29799069972411 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4726369769/10000000000 : ℝ)^8315 ≤ (3699697655151/10000000000000 : ℝ)^6267 := by
    have hnat : (4726369769 : ℕ)^8315*10000000000000^6267 ≤ 3699697655151^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4726369769 10000000000 3699697655151 10000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356338739/10000000000 : ℝ), (4015203513/10000000000 : ℝ), (4726369769/10000000000 : ℝ)] ![(16601976730147/50000000000000 : ℝ), (29799069972411/100000000000000 : ℝ), (3699697655151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356338739/10000000000 : ℝ)|^8315 ≤ (16601976730147/50000000000000 : ℝ)^6267
        have hw : |(4356338739/10000000000 : ℝ)|=(4356338739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4015203513/10000000000 : ℝ)|^8315 ≤ (29799069972411/100000000000000 : ℝ)^6267
        have hw : |(4015203513/10000000000 : ℝ)|=(4015203513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4726369769/10000000000 : ℝ)|^8315 ≤ (3699697655151/10000000000000 : ℝ)^6267
        have hw : |(4726369769/10000000000 : ℝ)|=(4726369769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s2_4 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-269836377/1250000000 : ℝ)*x 0 + (1289571173/2500000000 : ℝ)*x 1 + (2756056783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269836377/1250000000 : ℝ)^8315 ≤ (13080063165543/100000000000000 : ℝ)^6267 := by
    have hnat : (269836377 : ℕ)^8315*100000000000000^6267 ≤ 13080063165543^6267*1250000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269836377 1250000000 13080063165543 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1289571173/2500000000 : ℝ)^8315 ≤ (20774213815173/50000000000000 : ℝ)^6267 := by
    have hnat : (1289571173 : ℕ)^8315*50000000000000^6267 ≤ 20774213815173^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289571173 2500000000 20774213815173 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2756056783/5000000000 : ℝ)^8315 ≤ (45371509185217/100000000000000 : ℝ)^6267 := by
    have hnat : (2756056783 : ℕ)^8315*100000000000000^6267 ≤ 45371509185217^6267*5000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756056783 5000000000 45371509185217 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269836377/1250000000 : ℝ), (1289571173/2500000000 : ℝ), (2756056783/5000000000 : ℝ)] ![(13080063165543/100000000000000 : ℝ), (20774213815173/50000000000000 : ℝ), (45371509185217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269836377/1250000000 : ℝ)|^8315 ≤ (13080063165543/100000000000000 : ℝ)^6267
        have hw : |(-269836377/1250000000 : ℝ)|=(269836377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1289571173/2500000000 : ℝ)|^8315 ≤ (20774213815173/50000000000000 : ℝ)^6267
        have hw : |(1289571173/2500000000 : ℝ)|=(1289571173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2756056783/5000000000 : ℝ)|^8315 ≤ (45371509185217/100000000000000 : ℝ)^6267
        have hw : |(2756056783/5000000000 : ℝ)|=(2756056783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s2_5 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528379281/1000000000 : ℝ)*x 0 + (-397793977/2000000000 : ℝ)*x 1 + (5512114083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528379281/1000000000 : ℝ)^8315 ≤ (1715800972489/4000000000000 : ℝ)^6267 := by
    have hnat : (528379281 : ℕ)^8315*4000000000000^6267 ≤ 1715800972489^6267*1000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528379281 1000000000 1715800972489 4000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397793977/2000000000 : ℝ)^8315 ≤ (5866730419799/50000000000000 : ℝ)^6267 := by
    have hnat : (397793977 : ℕ)^8315*50000000000000^6267 ≤ 5866730419799^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397793977 2000000000 5866730419799 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5512114083/10000000000 : ℝ)^8315 ≤ (22685757415721/50000000000000 : ℝ)^6267 := by
    have hnat : (5512114083 : ℕ)^8315*50000000000000^6267 ≤ 22685757415721^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512114083 10000000000 22685757415721 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528379281/1000000000 : ℝ), (-397793977/2000000000 : ℝ), (5512114083/10000000000 : ℝ)] ![(1715800972489/4000000000000 : ℝ), (5866730419799/50000000000000 : ℝ), (22685757415721/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528379281/1000000000 : ℝ)|^8315 ≤ (1715800972489/4000000000000 : ℝ)^6267
        have hw : |(528379281/1000000000 : ℝ)|=(528379281/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-397793977/2000000000 : ℝ)|^8315 ≤ (5866730419799/50000000000000 : ℝ)^6267
        have hw : |(-397793977/2000000000 : ℝ)|=(397793977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5512114083/10000000000 : ℝ)|^8315 ≤ (22685757415721/50000000000000 : ℝ)^6267
        have hw : |(5512114083/10000000000 : ℝ)|=(5512114083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s2_6 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (105675833/200000000 : ℝ)*x 0 + (5512113981/10000000000 : ℝ)*x 1 + (-1988971623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105675833/200000000 : ℝ)^8315 ≤ (8579002363529/20000000000000 : ℝ)^6267 := by
    have hnat : (105675833 : ℕ)^8315*20000000000000^6267 ≤ 8579002363529^6267*200000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105675833 200000000 8579002363529 20000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5512113981/10000000000 : ℝ)^8315 ≤ (22685756858743/50000000000000 : ℝ)^6267 := by
    have hnat : (5512113981 : ℕ)^8315*50000000000000^6267 ≤ 22685756858743^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512113981 10000000000 22685756858743 50000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988971623/10000000000 : ℝ)^8315 ≤ (11733474443087/100000000000000 : ℝ)^6267 := by
    have hnat : (1988971623 : ℕ)^8315*100000000000000^6267 ≤ 11733474443087^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988971623 10000000000 11733474443087 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105675833/200000000 : ℝ), (5512113981/10000000000 : ℝ), (-1988971623/10000000000 : ℝ)] ![(8579002363529/20000000000000 : ℝ), (22685756858743/50000000000000 : ℝ), (11733474443087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105675833/200000000 : ℝ)|^8315 ≤ (8579002363529/20000000000000 : ℝ)^6267
        have hw : |(105675833/200000000 : ℝ)|=(105675833/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5512113981/10000000000 : ℝ)|^8315 ≤ (22685756858743/50000000000000 : ℝ)^6267
        have hw : |(5512113981/10000000000 : ℝ)|=(5512113981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1988971623/10000000000 : ℝ)|^8315 ≤ (11733474443087/100000000000000 : ℝ)^6267
        have hw : |(-1988971623/10000000000 : ℝ)|=(1988971623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1122_s2_7 (p : ℝ) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871310593/2000000000 : ℝ)*x 0 + (1180349429/2500000000 : ℝ)*x 1 + (4020225771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871310593/2000000000 : ℝ)^8315 ≤ (8301529974719/25000000000000 : ℝ)^6267 := by
    have hnat : (871310593 : ℕ)^8315*25000000000000^6267 ≤ 8301529974719^6267*2000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871310593 2000000000 8301529974719 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1180349429/2500000000 : ℝ)^8315 ≤ (36945346545899/100000000000000 : ℝ)^6267 := by
    have hnat : (1180349429 : ℕ)^8315*100000000000000^6267 ≤ 36945346545899^6267*2500000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180349429 2500000000 36945346545899 100000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020225771/10000000000 : ℝ)^8315 ≤ (7462133385407/25000000000000 : ℝ)^6267 := by
    have hnat : (4020225771 : ℕ)^8315*25000000000000^6267 ≤ 7462133385407^6267*10000000000^8315 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020225771 10000000000 7462133385407 25000000000000 8315 6267 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8315/2048 : ℝ)) 8315 6267 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871310593/2000000000 : ℝ), (1180349429/2500000000 : ℝ), (4020225771/10000000000 : ℝ)] ![(8301529974719/25000000000000 : ℝ), (36945346545899/100000000000000 : ℝ), (7462133385407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871310593/2000000000 : ℝ)|^8315 ≤ (8301529974719/25000000000000 : ℝ)^6267
        have hw : |(871310593/2000000000 : ℝ)|=(871310593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1180349429/2500000000 : ℝ)|^8315 ≤ (36945346545899/100000000000000 : ℝ)^6267
        have hw : |(1180349429/2500000000 : ℝ)|=(1180349429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020225771/10000000000 : ℝ)|^8315 ≤ (7462133385407/25000000000000 : ℝ)^6267
        have hw : |(4020225771/10000000000 : ℝ)|=(4020225771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1122_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1283/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8979/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16563/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1283/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5537/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1283/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5537/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1283/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5537/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1283/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5537/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1283/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5537/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1283/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5537/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5537/100000 : ℝ) ^ (4157/1024 : ℝ) ≤ (98888224118253/12500000000000000000 : ℝ) := by
    have hpowers : (5537/100000 : ℝ)^4157 ≤ (98888224118253/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5537 : ℕ)^4157*12500000000000000000^1024 ≤ 98888224118253^1024*100000^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5537 100000 98888224118253 12500000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5537/100000 : ℝ)) (X := (98888224118253/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1283/6250 : ℝ) ^ (4157/1024 : ℝ) ≤ (161593106693947661/100000000000000000000 : ℝ) := by
    have hpowers : (1283/6250 : ℝ)^4157 ≤ (161593106693947661/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1283 : ℕ)^4157*100000000000000000000^1024 ≤ 161593106693947661^1024*6250^4157 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1283 6250 161593106693947661 100000000000000000000 4157 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1283/6250 : ℝ)) (X := (161593106693947661/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250098888224118253/6250000000000000000 : ℝ) ≤ (5000019487310609/5000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (6250098888224118253/6250000000000000000 : ℝ)^1024 ≤ (5000019487310609/5000000000000000 : ℝ)^4157 := by
      have hnat : (6250098888224118253 : ℕ)^1024*5000000000000000^4157 ≤ 5000019487310609^4157*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250098888224118253 6250000000000000000 5000019487310609 5000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000019487310609/5000000000000000 : ℝ)) (X := (6250098888224118253/6250000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20032476842497378737/20000000000000000000 : ℝ) ≤ (5001998794554229/5000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (20032476842497378737/20000000000000000000 : ℝ)^1024 ≤ (5001998794554229/5000000000000000 : ℝ)^4157 := by
      have hnat : (20032476842497378737 : ℕ)^1024*5000000000000000^4157 ≤ 5001998794554229^4157*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20032476842497378737 20000000000000000000 5001998794554229 5000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001998794554229/5000000000000000 : ℝ)) (X := (20032476842497378737/20000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50161593106693947661/50000000000000000000 : ℝ) ≤ (5003978101797849/5000000000000000 : ℝ) ^ (4157/1024 : ℝ) := by
    have hpowers : (50161593106693947661/50000000000000000000 : ℝ)^1024 ≤ (5003978101797849/5000000000000000 : ℝ)^4157 := by
      have hnat : (50161593106693947661 : ℕ)^1024*5000000000000000^4157 ≤ 5003978101797849^4157*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50161593106693947661 50000000000000000000 5003978101797849 5000000000000000 1024 4157 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003978101797849/5000000000000000 : ℝ)) (X := (50161593106693947661/50000000000000000000 : ℝ)) (by norm_num) 4157 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(98888224118253/12500000000000000000 : ℝ) ≤ ((74933373285857491639/74955000000000000000 : ℝ)+2*(98965362181/37477500000000 : ℝ)*(5537/100000 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (74933373285857491639/74955000000000000000 : ℝ)+2*(98965362181/37477500000000 : ℝ)*(5537/100000 : ℝ)=(5000019487310609/5000000000000000 : ℝ) by norm_num, show 1+2*(98888224118253/12500000000000000000 : ℝ)=(6250098888224118253/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(161593106693947661/100000000000000000000 : ℝ)+(98888224118253/12500000000000000000 : ℝ) ≤ ((74933373285857491639/74955000000000000000 : ℝ)+(98965362181/37477500000000 : ℝ)*((1283/6250 : ℝ)+(5537/100000 : ℝ)))^(4157/1024 : ℝ) := by
    rw [show (74933373285857491639/74955000000000000000 : ℝ)+(98965362181/37477500000000 : ℝ)*((1283/6250 : ℝ)+(5537/100000 : ℝ))=(5001998794554229/5000000000000000 : ℝ) by norm_num, show 1+(161593106693947661/100000000000000000000 : ℝ)+(98888224118253/12500000000000000000 : ℝ)=(20032476842497378737/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(161593106693947661/100000000000000000000 : ℝ) ≤ ((74933373285857491639/74955000000000000000 : ℝ)+2*(98965362181/37477500000000 : ℝ)*(1283/6250 : ℝ))^(4157/1024 : ℝ) := by
    rw [show (74933373285857491639/74955000000000000000 : ℝ)+2*(98965362181/37477500000000 : ℝ)*(1283/6250 : ℝ)=(5003978101797849/5000000000000000 : ℝ) by norm_num, show 1+2*(161593106693947661/100000000000000000000 : ℝ)=(50161593106693947661/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74933373285857491639/74955000000000000000 : ℝ)*(X 1 0+X 2 0)+(98965362181/37477500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5537/100000 : ℝ)) (hi := (1283/6250 : ℝ)) (c := (74933373285857491639/74955000000000000000 : ℝ)) (alpha := (98965362181/37477500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74933373285857491639/74955000000000000000 : ℝ)*(X 0 1+X 2 1)+(98965362181/37477500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5537/100000 : ℝ)) (hi := (1283/6250 : ℝ)) (c := (74933373285857491639/74955000000000000000 : ℝ)) (alpha := (98965362181/37477500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74933373285857491639/74955000000000000000 : ℝ)*(X 0 2+X 1 2)+(98965362181/37477500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4157/1024 : ℝ)) (lo := (5537/100000 : ℝ)) (hi := (1283/6250 : ℝ)) (c := (74933373285857491639/74955000000000000000 : ℝ)) (alpha := (98965362181/37477500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2158582727/10000000000 : ℝ)*X 0 0+(5514648667/10000000000 : ℝ)*X 0 1+(1031155019/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374726221/10000000000 : ℝ)*X 1 0+(-1172654229/5000000000 : ℝ)*X 1 1+(161118019/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5248756/9765625 : ℝ)*X 2 0+(257788833/500000000 : ℝ)*X 2 1+(-2345308493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356338739/10000000000 : ℝ)*X 0 0+(4015203513/10000000000 : ℝ)*X 0 1+(4726369769/10000000000 : ℝ)*X 0 2+(4356338739/10000000000 : ℝ)*X 1 0+(4015203513/10000000000 : ℝ)*X 1 1+(4726369769/10000000000 : ℝ)*X 1 2+(4356338739/10000000000 : ℝ)*X 2 0+(4015203513/10000000000 : ℝ)*X 2 1+(4726369769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-269836377/1250000000 : ℝ)*X 0 0+(1289571173/2500000000 : ℝ)*X 0 1+(2756056783/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528379281/1000000000 : ℝ)*X 1 0+(-397793977/2000000000 : ℝ)*X 1 1+(5512114083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((105675833/200000000 : ℝ)*X 2 0+(5512113981/10000000000 : ℝ)*X 2 1+(-1988971623/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871310593/2000000000 : ℝ)*X 0 0+(1180349429/2500000000 : ℝ)*X 0 1+(4020225771/10000000000 : ℝ)*X 0 2+(871310593/2000000000 : ℝ)*X 1 0+(1180349429/2500000000 : ℝ)*X 1 1+(4020225771/10000000000 : ℝ)*X 1 2+(871310593/2000000000 : ℝ)*X 2 0+(1180349429/2500000000 : ℝ)*X 2 1+(4020225771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1122_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1021047185017905460275763739/156156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (485889201/100000000000000 : ℝ)*(base19) + (49489129/20000000000000 : ℝ)*(base23) + (5640847/20000000000000 : ℝ)*(upper2) + (22773611/12500000000000 : ℝ)*(upper3) + (1079239/800000000000 : ℝ)*(upper4) + (262042114932967/12500000000000 : ℝ)*(major0) + (262042114932967/12500000000000 : ℝ)*(major1) + (262042114932967/12500000000000 : ℝ)*(major2) + (87078500983567/3125000000000 : ℝ)*(sp0) + (1393262434828989/50000000000000 : ℝ)*(sp1) + (1393262554050767/50000000000000 : ℝ)*(sp2) + (703071880263611/50000000000000 : ℝ)*(sp3) + (2664814607/20000000000000 : ℝ)*(sp4) + (2252449447/50000000000000 : ℝ)*(sp7) + (351537066356529/25000000000000 : ℝ)*(f.failure) + (2786525355547179/100000000000000 : ℝ)*(f.sum) + (7386048654287/936937500000000000000000000 : ℝ)*base66 + (2034729795996804029/312312500000000000000000000000000 : ℝ)*base68 + (1285424094329804029/312312500000000000000000000000000 : ℝ)*base70 + (2428965502562804029/312312500000000000000000000000000 : ℝ)*base72 + (5891098366339/7495500000000000000000000000 : ℝ)*base74 + (2398206690804679029/312312500000000000000000000000000 : ℝ)*base76 + (2222172077483179029/312312500000000000000000000000000 : ℝ)*base78 + (199066284089554029/312312500000000000000000000000000 : ℝ)*base80 + (8383769091149/7495500000000000000000000000 : ℝ)*base81 + (16589857/2500000000000000000000 : ℝ)*base89 + (16589857/2500000000000000000000 : ℝ)*base91 + (16589857/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6064533330466534275443477841/624625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1799687711/100000000000000 : ℝ)*(base19) + (327186293/25000000000000 : ℝ)*(base23) + (97814789/50000000000000 : ℝ)*(upper2) + (120581051/100000000000000 : ℝ)*(upper3) + (269936063/100000000000000 : ℝ)*(upper5) + (1063100688819681/50000000000000 : ℝ)*(major0) + (1063100688819681/50000000000000 : ℝ)*(major1) + (1063100688819681/50000000000000 : ℝ)*(major2) + (2338272021/10000000000000 : ℝ)*(sp1) + (1879049861/20000000000000 : ℝ)*(sp2) + (1413111074786461/50000000000000 : ℝ)*(sp4) + (565239393433/20000000000 : ℝ)*(sp5) + (706552861394611/25000000000000 : ℝ)*(sp6) + (713090141034919/50000000000000 : ℝ)*(sp7) + (713090141034919/50000000000000 : ℝ)*(f.failure) + (1413111074786461/50000000000000 : ℝ)*(f.sum) + (11450433281073/2498500000000000000000000000 : ℝ)*base65 + (3456215816389950947/1249250000000000000000000000000000 : ℝ)*base68 + (1857993972701450947/1249250000000000000000000000000000 : ℝ)*base70 + (2054917958146049053/1249250000000000000000000000000000 : ℝ)*base71 + (2246782176031/1249250000000000000000000000 : ℝ)*base74 + (9698714304419549053/1249250000000000000000000000000000 : ℝ)*base75 + (6138408755228549053/1249250000000000000000000000000000 : ℝ)*base77 + (2147249036240049053/1249250000000000000000000000000000 : ℝ)*base79 + (443163079249/999400000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4380727/5000000000000000000000 : ℝ)*base89 + (4380727/5000000000000000000000 : ℝ)*base91 + (4380727/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1122_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1283/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5537/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16563/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1122_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1122_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16563/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1122_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1122_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1122_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4157/1024 : ℝ) ≤ p) (hpb : p ≤ (8315/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149083633/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8979/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16563/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1122_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
