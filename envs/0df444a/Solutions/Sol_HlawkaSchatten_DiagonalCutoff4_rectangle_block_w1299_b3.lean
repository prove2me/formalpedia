-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1299_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:36:04.075002+00:00
-- url     : https://prove2.me/submissions/e06475ac-c348-45ea-9749-ba19f3e17741

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
theorem support_rectangle_w1299_box_0 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29858751/156250000 : ℝ)*x 0 + (1078344609/2000000000 : ℝ)*x 1 + (539172323/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29858751/156250000 : ℝ)^4259 ≤ (2829310020931/25000000000000 : ℝ)^3235 := by
    have hnat : (29858751 : ℕ)^4259*25000000000000^3235 ≤ 2829310020931^3235*156250000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29858751 156250000 2829310020931 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078344609/2000000000 : ℝ)^4259 ≤ (11085344737297/25000000000000 : ℝ)^3235 := by
    have hnat : (1078344609 : ℕ)^4259*25000000000000^3235 ≤ 11085344737297^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078344609 2000000000 11085344737297 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539172323/1000000000 : ℝ)^4259 ≤ (22170690476107/50000000000000 : ℝ)^3235 := by
    have hnat : (539172323 : ℕ)^4259*50000000000000^3235 ≤ 22170690476107^3235*1000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539172323 1000000000 22170690476107 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29858751/156250000 : ℝ), (1078344609/2000000000 : ℝ), (539172323/1000000000 : ℝ)] ![(2829310020931/25000000000000 : ℝ), (11085344737297/25000000000000 : ℝ), (22170690476107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29858751/156250000 : ℝ)|^4259 ≤ (2829310020931/25000000000000 : ℝ)^3235
        have hw : |(-29858751/156250000 : ℝ)|=(29858751/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078344609/2000000000 : ℝ)|^4259 ≤ (11085344737297/25000000000000 : ℝ)^3235
        have hw : |(1078344609/2000000000 : ℝ)|=(1078344609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539172323/1000000000 : ℝ)|^4259 ≤ (22170690476107/50000000000000 : ℝ)^3235
        have hw : |(539172323/1000000000 : ℝ)|=(539172323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_1 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528449491/1000000000 : ℝ)*x 0 + (-128602463/625000000 : ℝ)*x 1 + (5391723551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528449491/1000000000 : ℝ)^4259 ≤ (4318407262013/10000000000000 : ℝ)^3235 := by
    have hnat : (528449491 : ℕ)^4259*10000000000000^3235 ≤ 4318407262013^3235*1000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528449491 1000000000 4318407262013 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (128602463/625000000 : ℝ)^4259 ≤ (249490858561/2000000000000 : ℝ)^3235 := by
    have hnat : (128602463 : ℕ)^4259*2000000000000^3235 ≤ 249490858561^3235*625000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128602463 625000000 249490858561 2000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391723551/10000000000 : ℝ)^4259 ≤ (5542673053467/12500000000000 : ℝ)^3235 := by
    have hnat : (5391723551 : ℕ)^4259*12500000000000^3235 ≤ 5542673053467^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391723551 10000000000 5542673053467 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528449491/1000000000 : ℝ), (-128602463/625000000 : ℝ), (5391723551/10000000000 : ℝ)] ![(4318407262013/10000000000000 : ℝ), (249490858561/2000000000000 : ℝ), (5542673053467/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528449491/1000000000 : ℝ)|^4259 ≤ (4318407262013/10000000000000 : ℝ)^3235
        have hw : |(528449491/1000000000 : ℝ)|=(528449491/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-128602463/625000000 : ℝ)|^4259 ≤ (249490858561/2000000000000 : ℝ)^3235
        have hw : |(-128602463/625000000 : ℝ)|=(128602463/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391723551/10000000000 : ℝ)|^4259 ≤ (5542673053467/12500000000000 : ℝ)^3235
        have hw : |(5391723551/10000000000 : ℝ)|=(5391723551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_2 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642247673/5000000000 : ℝ)*x 0 + (5391723127/10000000000 : ℝ)*x 1 + (-2057639397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642247673/5000000000 : ℝ)^4259 ≤ (8636815462171/20000000000000 : ℝ)^3235 := by
    have hnat : (2642247673 : ℕ)^4259*20000000000000^3235 ≤ 8636815462171^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642247673 5000000000 8636815462171 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391723127/10000000000 : ℝ)^4259 ≤ (5542672479627/12500000000000 : ℝ)^3235 := by
    have hnat : (5391723127 : ℕ)^4259*12500000000000^3235 ≤ 5542672479627^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391723127 10000000000 5542672479627 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2057639397/10000000000 : ℝ)^4259 ≤ (12474542840253/100000000000000 : ℝ)^3235 := by
    have hnat : (2057639397 : ℕ)^4259*100000000000000^3235 ≤ 12474542840253^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057639397 10000000000 12474542840253 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642247673/5000000000 : ℝ), (5391723127/10000000000 : ℝ), (-2057639397/10000000000 : ℝ)] ![(8636815462171/20000000000000 : ℝ), (5542672479627/12500000000000 : ℝ), (12474542840253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642247673/5000000000 : ℝ)|^4259 ≤ (8636815462171/20000000000000 : ℝ)^3235
        have hw : |(2642247673/5000000000 : ℝ)|=(2642247673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391723127/10000000000 : ℝ)|^4259 ≤ (5542672479627/12500000000000 : ℝ)^3235
        have hw : |(5391723127/10000000000 : ℝ)|=(5391723127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2057639397/10000000000 : ℝ)|^4259 ≤ (12474542840253/100000000000000 : ℝ)^3235
        have hw : |(-2057639397/10000000000 : ℝ)|=(2057639397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_3 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4487233463/10000000000 : ℝ)*x 0 + (2133680341/5000000000 : ℝ)*x 1 + (2133680389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4487233463/10000000000 : ℝ)^4259 ≤ (34819035341771/100000000000000 : ℝ)^3235 := by
    have hnat : (4487233463 : ℕ)^4259*100000000000000^3235 ≤ 34819035341771^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487233463 10000000000 34819035341771 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2133680341/5000000000 : ℝ)^4259 ≤ (4073810229881/12500000000000 : ℝ)^3235 := by
    have hnat : (2133680341 : ℕ)^4259*12500000000000^3235 ≤ 4073810229881^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133680341 5000000000 4073810229881 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133680389/5000000000 : ℝ)^4259 ≤ (32590482804289/100000000000000 : ℝ)^3235 := by
    have hnat : (2133680389 : ℕ)^4259*100000000000000^3235 ≤ 32590482804289^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133680389 5000000000 32590482804289 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4487233463/10000000000 : ℝ), (2133680341/5000000000 : ℝ), (2133680389/5000000000 : ℝ)] ![(34819035341771/100000000000000 : ℝ), (4073810229881/12500000000000 : ℝ), (32590482804289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4487233463/10000000000 : ℝ)|^4259 ≤ (34819035341771/100000000000000 : ℝ)^3235
        have hw : |(4487233463/10000000000 : ℝ)|=(4487233463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2133680341/5000000000 : ℝ)|^4259 ≤ (4073810229881/12500000000000 : ℝ)^3235
        have hw : |(2133680341/5000000000 : ℝ)|=(2133680341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2133680389/5000000000 : ℝ)|^4259 ≤ (32590482804289/100000000000000 : ℝ)^3235
        have hw : |(2133680389/5000000000 : ℝ)|=(2133680389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_4 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-563806797/2500000000 : ℝ)*x 0 + (5263884349/10000000000 : ℝ)*x 1 + (5263883501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563806797/2500000000 : ℝ)^4259 ≤ (2815013817419/20000000000000 : ℝ)^3235 := by
    have hnat : (563806797 : ℕ)^4259*20000000000000^3235 ≤ 2815013817419^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563806797 2500000000 2815013817419 20000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263884349/10000000000 : ℝ)^4259 ≤ (42962470006109/100000000000000 : ℝ)^3235 := by
    have hnat : (5263884349 : ℕ)^4259*100000000000000^3235 ≤ 42962470006109^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263884349 10000000000 42962470006109 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263883501/10000000000 : ℝ)^4259 ≤ (42962460894143/100000000000000 : ℝ)^3235 := by
    have hnat : (5263883501 : ℕ)^4259*100000000000000^3235 ≤ 42962460894143^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263883501 10000000000 42962460894143 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-563806797/2500000000 : ℝ), (5263884349/10000000000 : ℝ), (5263883501/10000000000 : ℝ)] ![(2815013817419/20000000000000 : ℝ), (42962470006109/100000000000000 : ℝ), (42962460894143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-563806797/2500000000 : ℝ)|^4259 ≤ (2815013817419/20000000000000 : ℝ)^3235
        have hw : |(-563806797/2500000000 : ℝ)|=(563806797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263884349/10000000000 : ℝ)|^4259 ≤ (42962470006109/100000000000000 : ℝ)^3235
        have hw : |(5263884349/10000000000 : ℝ)|=(5263884349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263883501/10000000000 : ℝ)|^4259 ≤ (42962460894143/100000000000000 : ℝ)^3235
        have hw : |(5263883501/10000000000 : ℝ)|=(5263883501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_5 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537445199/1000000000 : ℝ)*x 0 + (-2108622537/10000000000 : ℝ)*x 1 + (5263884093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537445199/1000000000 : ℝ)^4259 ≤ (4415447716473/10000000000000 : ℝ)^3235 := by
    have hnat : (537445199 : ℕ)^4259*10000000000000^3235 ≤ 4415447716473^3235*1000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537445199 1000000000 4415447716473 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108622537/10000000000 : ℝ)^4259 ≤ (1288305556371/10000000000000 : ℝ)^3235 := by
    have hnat : (2108622537 : ℕ)^4259*10000000000000^3235 ≤ 1288305556371^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108622537 10000000000 1288305556371 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263884093/10000000000 : ℝ)^4259 ≤ (42962467255327/100000000000000 : ℝ)^3235 := by
    have hnat : (5263884093 : ℕ)^4259*100000000000000^3235 ≤ 42962467255327^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263884093 10000000000 42962467255327 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537445199/1000000000 : ℝ), (-2108622537/10000000000 : ℝ), (5263884093/10000000000 : ℝ)] ![(4415447716473/10000000000000 : ℝ), (1288305556371/10000000000000 : ℝ), (42962467255327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537445199/1000000000 : ℝ)|^4259 ≤ (4415447716473/10000000000000 : ℝ)^3235
        have hw : |(537445199/1000000000 : ℝ)|=(537445199/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108622537/10000000000 : ℝ)|^4259 ≤ (1288305556371/10000000000000 : ℝ)^3235
        have hw : |(-2108622537/10000000000 : ℝ)|=(2108622537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263884093/10000000000 : ℝ)|^4259 ≤ (42962467255327/100000000000000 : ℝ)^3235
        have hw : |(5263884093/10000000000 : ℝ)|=(5263884093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_6 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374452869/10000000000 : ℝ)*x 0 + (164496359/312500000 : ℝ)*x 1 + (-2108622163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374452869/10000000000 : ℝ)^4259 ≤ (44154486672153/100000000000000 : ℝ)^3235 := by
    have hnat : (5374452869 : ℕ)^4259*100000000000000^3235 ≤ 44154486672153^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374452869 10000000000 44154486672153 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164496359/312500000 : ℝ)^4259 ≤ (21481230377227/50000000000000 : ℝ)^3235 := by
    have hnat : (164496359 : ℕ)^4259*50000000000000^3235 ≤ 21481230377227^3235*312500000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164496359 312500000 21481230377227 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108622163/10000000000 : ℝ)^4259 ≤ (12883052555383/100000000000000 : ℝ)^3235 := by
    have hnat : (2108622163 : ℕ)^4259*100000000000000^3235 ≤ 12883052555383^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108622163 10000000000 12883052555383 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374452869/10000000000 : ℝ), (164496359/312500000 : ℝ), (-2108622163/10000000000 : ℝ)] ![(44154486672153/100000000000000 : ℝ), (21481230377227/50000000000000 : ℝ), (12883052555383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374452869/10000000000 : ℝ)|^4259 ≤ (44154486672153/100000000000000 : ℝ)^3235
        have hw : |(5374452869/10000000000 : ℝ)|=(5374452869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164496359/312500000 : ℝ)|^4259 ≤ (21481230377227/50000000000000 : ℝ)^3235
        have hw : |(164496359/312500000 : ℝ)|=(164496359/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108622163/10000000000 : ℝ)|^4259 ≤ (12883052555383/100000000000000 : ℝ)^3235
        have hw : |(-2108622163/10000000000 : ℝ)|=(2108622163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_7 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (837578337/2000000000 : ℝ)*x 0 + (4416976887/10000000000 : ℝ)*x 1 + (1104244039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837578337/2000000000 : ℝ)^4259 ≤ (15896908993313/50000000000000 : ℝ)^3235 := by
    have hnat : (837578337 : ℕ)^4259*50000000000000^3235 ≤ 15896908993313^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837578337 2000000000 15896908993313 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4416976887/10000000000 : ℝ)^4259 ≤ (34103094716499/100000000000000 : ℝ)^3235 := by
    have hnat : (4416976887 : ℕ)^4259*100000000000000^3235 ≤ 34103094716499^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416976887 10000000000 34103094716499 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1104244039/2500000000 : ℝ)^4259 ≤ (4262885910747/12500000000000 : ℝ)^3235 := by
    have hnat : (1104244039 : ℕ)^4259*12500000000000^3235 ≤ 4262885910747^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104244039 2500000000 4262885910747 12500000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837578337/2000000000 : ℝ), (4416976887/10000000000 : ℝ), (1104244039/2500000000 : ℝ)] ![(15896908993313/50000000000000 : ℝ), (34103094716499/100000000000000 : ℝ), (4262885910747/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837578337/2000000000 : ℝ)|^4259 ≤ (15896908993313/50000000000000 : ℝ)^3235
        have hw : |(837578337/2000000000 : ℝ)|=(837578337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4416976887/10000000000 : ℝ)|^4259 ≤ (34103094716499/100000000000000 : ℝ)^3235
        have hw : |(4416976887/10000000000 : ℝ)|=(4416976887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1104244039/2500000000 : ℝ)|^4259 ≤ (4262885910747/12500000000000 : ℝ)^3235
        have hw : |(1104244039/2500000000 : ℝ)|=(1104244039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_8 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-136440743/625000000 : ℝ)*x 0 + (2588042077/5000000000 : ℝ)*x 1 + (42232489/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136440743/625000000 : ℝ)^4259 ≤ (1348505757877/10000000000000 : ℝ)^3235 := by
    have hnat : (136440743 : ℕ)^4259*10000000000000^3235 ≤ 1348505757877^3235*625000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136440743 625000000 1348505757877 10000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588042077/5000000000 : ℝ)^4259 ≤ (10505383906921/25000000000000 : ℝ)^3235 := by
    have hnat : (2588042077 : ℕ)^4259*25000000000000^3235 ≤ 10505383906921^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588042077 5000000000 10505383906921 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42232489/78125000 : ℝ)^4259 ≤ (44493406781643/100000000000000 : ℝ)^3235 := by
    have hnat : (42232489 : ℕ)^4259*100000000000000^3235 ≤ 44493406781643^3235*78125000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42232489 78125000 44493406781643 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-136440743/625000000 : ℝ), (2588042077/5000000000 : ℝ), (42232489/78125000 : ℝ)] ![(1348505757877/10000000000000 : ℝ), (10505383906921/25000000000000 : ℝ), (44493406781643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-136440743/625000000 : ℝ)|^4259 ≤ (1348505757877/10000000000000 : ℝ)^3235
        have hw : |(-136440743/625000000 : ℝ)|=(136440743/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588042077/5000000000 : ℝ)|^4259 ≤ (10505383906921/25000000000000 : ℝ)^3235
        have hw : |(2588042077/5000000000 : ℝ)|=(2588042077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42232489/78125000 : ℝ)|^4259 ≤ (44493406781643/100000000000000 : ℝ)^3235
        have hw : |(42232489/78125000 : ℝ)|=(42232489/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_9 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5274613127/10000000000 : ℝ)*x 0 + (-2051906303/10000000000 : ℝ)*x 1 + (67571981/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274613127/10000000000 : ℝ)^4259 ≤ (10769447627067/25000000000000 : ℝ)^3235 := by
    have hnat : (5274613127 : ℕ)^4259*25000000000000^3235 ≤ 10769447627067^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274613127 10000000000 10769447627067 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2051906303/10000000000 : ℝ)^4259 ≤ (6214401949257/50000000000000 : ℝ)^3235 := by
    have hnat : (2051906303 : ℕ)^4259*50000000000000^3235 ≤ 6214401949257^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051906303 10000000000 6214401949257 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67571981/125000000 : ℝ)^4259 ≤ (22246702784001/50000000000000 : ℝ)^3235 := by
    have hnat : (67571981 : ℕ)^4259*50000000000000^3235 ≤ 22246702784001^3235*125000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67571981 125000000 22246702784001 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274613127/10000000000 : ℝ), (-2051906303/10000000000 : ℝ), (67571981/125000000 : ℝ)] ![(10769447627067/25000000000000 : ℝ), (6214401949257/50000000000000 : ℝ), (22246702784001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274613127/10000000000 : ℝ)|^4259 ≤ (10769447627067/25000000000000 : ℝ)^3235
        have hw : |(5274613127/10000000000 : ℝ)|=(5274613127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2051906303/10000000000 : ℝ)|^4259 ≤ (6214401949257/50000000000000 : ℝ)^3235
        have hw : |(-2051906303/10000000000 : ℝ)|=(2051906303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67571981/125000000 : ℝ)|^4259 ≤ (22246702784001/50000000000000 : ℝ)^3235
        have hw : |(67571981/125000000 : ℝ)|=(67571981/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_10 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054922607/2000000000 : ℝ)*x 0 + (5405758463/10000000000 : ℝ)*x 1 + (-512976613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054922607/2000000000 : ℝ)^4259 ≤ (10769447379767/25000000000000 : ℝ)^3235 := by
    have hnat : (1054922607 : ℕ)^4259*25000000000000^3235 ≤ 10769447379767^3235*2000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054922607 2000000000 10769447379767 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405758463/10000000000 : ℝ)^4259 ≤ (11123351345947/25000000000000 : ℝ)^3235 := by
    have hnat : (5405758463 : ℕ)^4259*25000000000000^3235 ≤ 11123351345947^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405758463 10000000000 11123351345947 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512976613/2500000000 : ℝ)^4259 ≤ (12428805086719/100000000000000 : ℝ)^3235 := by
    have hnat : (512976613 : ℕ)^4259*100000000000000^3235 ≤ 12428805086719^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512976613 2500000000 12428805086719 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054922607/2000000000 : ℝ), (5405758463/10000000000 : ℝ), (-512976613/2500000000 : ℝ)] ![(10769447379767/25000000000000 : ℝ), (11123351345947/25000000000000 : ℝ), (12428805086719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054922607/2000000000 : ℝ)|^4259 ≤ (10769447379767/25000000000000 : ℝ)^3235
        have hw : |(1054922607/2000000000 : ℝ)|=(1054922607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405758463/10000000000 : ℝ)|^4259 ≤ (11123351345947/25000000000000 : ℝ)^3235
        have hw : |(5405758463/10000000000 : ℝ)|=(5405758463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-512976613/2500000000 : ℝ)|^4259 ≤ (12428805086719/100000000000000 : ℝ)^3235
        have hw : |(-512976613/2500000000 : ℝ)|=(512976613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_11 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (564942291/1250000000 : ℝ)*x 0 + (1062730197/2500000000 : ℝ)*x 1 + (1062730137/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564942291/1250000000 : ℝ)^4259 ≤ (17574715035273/50000000000000 : ℝ)^3235 := by
    have hnat : (564942291 : ℕ)^4259*50000000000000^3235 ≤ 17574715035273^3235*1250000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564942291 1250000000 17574715035273 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062730197/2500000000 : ℝ)^4259 ≤ (32425286160063/100000000000000 : ℝ)^3235 := by
    have hnat : (1062730197 : ℕ)^4259*100000000000000^3235 ≤ 32425286160063^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062730197 2500000000 32425286160063 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1062730137/2500000000 : ℝ)^4259 ≤ (16212641874953/50000000000000 : ℝ)^3235 := by
    have hnat : (1062730137 : ℕ)^4259*50000000000000^3235 ≤ 16212641874953^3235*2500000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062730137 2500000000 16212641874953 50000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(564942291/1250000000 : ℝ), (1062730197/2500000000 : ℝ), (1062730137/2500000000 : ℝ)] ![(17574715035273/50000000000000 : ℝ), (32425286160063/100000000000000 : ℝ), (16212641874953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(564942291/1250000000 : ℝ)|^4259 ≤ (17574715035273/50000000000000 : ℝ)^3235
        have hw : |(564942291/1250000000 : ℝ)|=(564942291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062730197/2500000000 : ℝ)|^4259 ≤ (32425286160063/100000000000000 : ℝ)^3235
        have hw : |(1062730197/2500000000 : ℝ)|=(1062730197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1062730137/2500000000 : ℝ)|^4259 ≤ (16212641874953/50000000000000 : ℝ)^3235
        have hw : |(1062730137/2500000000 : ℝ)|=(1062730137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_12 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983559233/10000000000 : ℝ)*x 0 + (5477216751/10000000000 : ℝ)*x 1 + (328303389/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983559233/10000000000 : ℝ)^4259 ≤ (29716658703/250000000000 : ℝ)^3235 := by
    have hnat : (1983559233 : ℕ)^4259*250000000000^3235 ≤ 29716658703^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983559233 10000000000 29716658703 250000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5477216751/10000000000 : ℝ)^4259 ≤ (45269348552363/100000000000000 : ℝ)^3235 := by
    have hnat : (5477216751 : ℕ)^4259*100000000000000^3235 ≤ 45269348552363^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477216751 10000000000 45269348552363 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328303389/625000000 : ℝ)^4259 ≤ (42843987953581/100000000000000 : ℝ)^3235 := by
    have hnat : (328303389 : ℕ)^4259*100000000000000^3235 ≤ 42843987953581^3235*625000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328303389 625000000 42843987953581 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983559233/10000000000 : ℝ), (5477216751/10000000000 : ℝ), (328303389/625000000 : ℝ)] ![(29716658703/250000000000 : ℝ), (45269348552363/100000000000000 : ℝ), (42843987953581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983559233/10000000000 : ℝ)|^4259 ≤ (29716658703/250000000000 : ℝ)^3235
        have hw : |(-1983559233/10000000000 : ℝ)|=(1983559233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5477216751/10000000000 : ℝ)|^4259 ≤ (45269348552363/100000000000000 : ℝ)^3235
        have hw : |(5477216751/10000000000 : ℝ)|=(5477216751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328303389/625000000 : ℝ)|^4259 ≤ (42843987953581/100000000000000 : ℝ)^3235
        have hw : |(328303389/625000000 : ℝ)|=(328303389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_13 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382210373/10000000000 : ℝ)*x 0 + (-2112915711/10000000000 : ℝ)*x 1 + (5252854237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382210373/10000000000 : ℝ)^4259 ≤ (2211920619973/5000000000000 : ℝ)^3235 := by
    have hnat : (5382210373 : ℕ)^4259*5000000000000^3235 ≤ 2211920619973^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382210373 10000000000 2211920619973 5000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112915711/10000000000 : ℝ)^4259 ≤ (3229399873327/25000000000000 : ℝ)^3235 := by
    have hnat : (2112915711 : ℕ)^4259*25000000000000^3235 ≤ 3229399873327^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112915711 10000000000 3229399873327 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252854237/10000000000 : ℝ)^4259 ≤ (42843988093177/100000000000000 : ℝ)^3235 := by
    have hnat : (5252854237 : ℕ)^4259*100000000000000^3235 ≤ 42843988093177^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252854237 10000000000 42843988093177 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382210373/10000000000 : ℝ), (-2112915711/10000000000 : ℝ), (5252854237/10000000000 : ℝ)] ![(2211920619973/5000000000000 : ℝ), (3229399873327/25000000000000 : ℝ), (42843988093177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382210373/10000000000 : ℝ)|^4259 ≤ (2211920619973/5000000000000 : ℝ)^3235
        have hw : |(5382210373/10000000000 : ℝ)|=(5382210373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2112915711/10000000000 : ℝ)|^4259 ≤ (3229399873327/25000000000000 : ℝ)^3235
        have hw : |(-2112915711/10000000000 : ℝ)|=(2112915711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252854237/10000000000 : ℝ)|^4259 ≤ (42843988093177/100000000000000 : ℝ)^3235
        have hw : |(5252854237/10000000000 : ℝ)|=(5252854237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_14 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336388157/625000000 : ℝ)*x 0 + (525285399/1000000000 : ℝ)*x 1 + (-1056457927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336388157/625000000 : ℝ)^4259 ≤ (11059603475899/25000000000000 : ℝ)^3235 := by
    have hnat : (336388157 : ℕ)^4259*25000000000000^3235 ≤ 11059603475899^3235*625000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336388157 625000000 11059603475899 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525285399/1000000000 : ℝ)^4259 ≤ (42843985440863/100000000000000 : ℝ)^3235 := by
    have hnat : (525285399 : ℕ)^4259*100000000000000^3235 ≤ 42843985440863^3235*1000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525285399 1000000000 42843985440863 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056457927/5000000000 : ℝ)^4259 ≤ (3229400161073/25000000000000 : ℝ)^3235 := by
    have hnat : (1056457927 : ℕ)^4259*25000000000000^3235 ≤ 3229400161073^3235*5000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056457927 5000000000 3229400161073 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336388157/625000000 : ℝ), (525285399/1000000000 : ℝ), (-1056457927/5000000000 : ℝ)] ![(11059603475899/25000000000000 : ℝ), (42843985440863/100000000000000 : ℝ), (3229400161073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336388157/625000000 : ℝ)|^4259 ≤ (11059603475899/25000000000000 : ℝ)^3235
        have hw : |(336388157/625000000 : ℝ)|=(336388157/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525285399/1000000000 : ℝ)|^4259 ≤ (42843985440863/100000000000000 : ℝ)^3235
        have hw : |(525285399/1000000000 : ℝ)|=(525285399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056457927/5000000000 : ℝ)|^4259 ≤ (3229400161073/25000000000000 : ℝ)^3235
        have hw : |(-1056457927/5000000000 : ℝ)|=(1056457927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1299_box_15 (p : ℝ) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4161617109/10000000000 : ℝ)*x 0 + (4429875157/10000000000 : ℝ)*x 1 + (4429875627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4161617109/10000000000 : ℝ)^4259 ≤ (31531466070531/100000000000000 : ℝ)^3235 := by
    have hnat : (4161617109 : ℕ)^4259*100000000000000^3235 ≤ 31531466070531^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161617109 10000000000 31531466070531 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4429875157/10000000000 : ℝ)^4259 ≤ (8558566141611/25000000000000 : ℝ)^3235 := by
    have hnat : (4429875157 : ℕ)^4259*25000000000000^3235 ≤ 8558566141611^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429875157 10000000000 8558566141611 25000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4429875627/10000000000 : ℝ)^4259 ≤ (34234269348347/100000000000000 : ℝ)^3235 := by
    have hnat : (4429875627 : ℕ)^4259*100000000000000^3235 ≤ 34234269348347^3235*10000000000^4259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4429875627 10000000000 34234269348347 100000000000000 4259 3235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4259/1024 : ℝ)) 4259 3235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4161617109/10000000000 : ℝ), (4429875157/10000000000 : ℝ), (4429875627/10000000000 : ℝ)] ![(31531466070531/100000000000000 : ℝ), (8558566141611/25000000000000 : ℝ), (34234269348347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4161617109/10000000000 : ℝ)|^4259 ≤ (31531466070531/100000000000000 : ℝ)^3235
        have hw : |(4161617109/10000000000 : ℝ)|=(4161617109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4429875157/10000000000 : ℝ)|^4259 ≤ (8558566141611/25000000000000 : ℝ)^3235
        have hw : |(4429875157/10000000000 : ℝ)|=(4429875157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4429875627/10000000000 : ℝ)|^4259 ≤ (34234269348347/100000000000000 : ℝ)^3235
        have hw : |(4429875627/10000000000 : ℝ)|=(4429875627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1299_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62841/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29429/50000 : ℝ) ∧ (79699/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84183/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5523/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14677/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5523/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14677/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5523/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5523/50000 : ℝ) ^ (2129/512 : ℝ) ≤ (2101271636704811/20000000000000000000 : ℝ) := by
    have hpowers : (5523/50000 : ℝ)^2129 ≤ (2101271636704811/20000000000000000000 : ℝ)^512 := by
      have hnat : (5523 : ℕ)^2129*20000000000000000000^512 ≤ 2101271636704811^512*50000^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5523 50000 2101271636704811 20000000000000000000 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5523/50000 : ℝ)) (X := (2101271636704811/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14677/100000 : ℝ) ^ (2129/512 : ℝ) ≤ (3425378698318319/10000000000000000000 : ℝ) := by
    have hpowers : (14677/100000 : ℝ)^2129 ≤ (3425378698318319/10000000000000000000 : ℝ)^512 := by
      have hnat : (14677 : ℕ)^2129*10000000000000000000^512 ≤ 3425378698318319^512*100000^2129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14677 100000 3425378698318319 10000000000000000000 2129 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14677/100000 : ℝ)) (X := (3425378698318319/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002101271636704811/10000000000000000000 : ℝ) ≤ (10000505291328739/10000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (10002101271636704811/10000000000000000000 : ℝ)^512 ≤ (10000505291328739/10000000000000000 : ℝ)^2129 := by
      have hnat : (10002101271636704811 : ℕ)^512*10000000000000000^2129 ≤ 10000505291328739^2129*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002101271636704811 10000000000000000000 10000505291328739 10000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000505291328739/10000000000000000 : ℝ)) (X := (10002101271636704811/10000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008952029033341449/20000000000000000000 : ℝ) ≤ (5000538123529843/5000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (20008952029033341449/20000000000000000000 : ℝ)^512 ≤ (5000538123529843/5000000000000000 : ℝ)^2129 := by
      have hnat : (20008952029033341449 : ℕ)^512*5000000000000000^2129 ≤ 5000538123529843^2129*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008952029033341449 20000000000000000000 5000538123529843 5000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000538123529843/5000000000000000 : ℝ)) (X := (20008952029033341449/20000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003425378698318319/5000000000000000000 : ℝ) ≤ (10001647202790633/10000000000000000 : ℝ) ^ (2129/512 : ℝ) := by
    have hpowers : (5003425378698318319/5000000000000000000 : ℝ)^512 ≤ (10001647202790633/10000000000000000 : ℝ)^2129 := by
      have hnat : (5003425378698318319 : ℕ)^512*10000000000000000^2129 ≤ 10001647202790633^2129*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003425378698318319 5000000000000000000 10001647202790633 10000000000000000 512 2129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001647202790633/10000000000000000 : ℝ)) (X := (5003425378698318319/5000000000000000000 : ℝ)) (by norm_num) 2129 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2101271636704811/20000000000000000000 : ℝ) ≤ ((7259844231761314037/7262000000000000000 : ℝ)+2*(570955730947/363100000000000 : ℝ)*(5523/50000 : ℝ))^(2129/512 : ℝ) := by
    rw [show (7259844231761314037/7262000000000000000 : ℝ)+2*(570955730947/363100000000000 : ℝ)*(5523/50000 : ℝ)=(10000505291328739/10000000000000000 : ℝ) by norm_num, show 1+2*(2101271636704811/20000000000000000000 : ℝ)=(10002101271636704811/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3425378698318319/10000000000000000000 : ℝ)+(2101271636704811/20000000000000000000 : ℝ) ≤ ((7259844231761314037/7262000000000000000 : ℝ)+(570955730947/363100000000000 : ℝ)*((14677/100000 : ℝ)+(5523/50000 : ℝ)))^(2129/512 : ℝ) := by
    rw [show (7259844231761314037/7262000000000000000 : ℝ)+(570955730947/363100000000000 : ℝ)*((14677/100000 : ℝ)+(5523/50000 : ℝ))=(5000538123529843/5000000000000000 : ℝ) by norm_num, show 1+(3425378698318319/10000000000000000000 : ℝ)+(2101271636704811/20000000000000000000 : ℝ)=(20008952029033341449/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3425378698318319/10000000000000000000 : ℝ) ≤ ((7259844231761314037/7262000000000000000 : ℝ)+2*(570955730947/363100000000000 : ℝ)*(14677/100000 : ℝ))^(2129/512 : ℝ) := by
    rw [show (7259844231761314037/7262000000000000000 : ℝ)+2*(570955730947/363100000000000 : ℝ)*(14677/100000 : ℝ)=(10001647202790633/10000000000000000 : ℝ) by norm_num, show 1+2*(3425378698318319/10000000000000000000 : ℝ)=(5003425378698318319/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7259844231761314037/7262000000000000000 : ℝ)*(X 1 0+X 2 0)+(570955730947/363100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (7259844231761314037/7262000000000000000 : ℝ)) (alpha := (570955730947/363100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7259844231761314037/7262000000000000000 : ℝ)*(X 0 1+X 2 1)+(570955730947/363100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (7259844231761314037/7262000000000000000 : ℝ)) (alpha := (570955730947/363100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7259844231761314037/7262000000000000000 : ℝ)*(X 0 2+X 1 2)+(570955730947/363100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2129/512 : ℝ)) (lo := (5523/50000 : ℝ)) (hi := (14677/100000 : ℝ)) (c := (7259844231761314037/7262000000000000000 : ℝ)) (alpha := (570955730947/363100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-29858751/156250000 : ℝ)*X 0 0+(1078344609/2000000000 : ℝ)*X 0 1+(539172323/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528449491/1000000000 : ℝ)*X 1 0+(-128602463/625000000 : ℝ)*X 1 1+(5391723551/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642247673/5000000000 : ℝ)*X 2 0+(5391723127/10000000000 : ℝ)*X 2 1+(-2057639397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4487233463/10000000000 : ℝ)*X 0 0+(2133680341/5000000000 : ℝ)*X 0 1+(2133680389/5000000000 : ℝ)*X 0 2+(4487233463/10000000000 : ℝ)*X 1 0+(2133680341/5000000000 : ℝ)*X 1 1+(2133680389/5000000000 : ℝ)*X 1 2+(4487233463/10000000000 : ℝ)*X 2 0+(2133680341/5000000000 : ℝ)*X 2 1+(2133680389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-563806797/2500000000 : ℝ)*X 0 0+(5263884349/10000000000 : ℝ)*X 0 1+(5263883501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((537445199/1000000000 : ℝ)*X 1 0+(-2108622537/10000000000 : ℝ)*X 1 1+(5263884093/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5374452869/10000000000 : ℝ)*X 2 0+(164496359/312500000 : ℝ)*X 2 1+(-2108622163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((837578337/2000000000 : ℝ)*X 0 0+(4416976887/10000000000 : ℝ)*X 0 1+(1104244039/2500000000 : ℝ)*X 0 2+(837578337/2000000000 : ℝ)*X 1 0+(4416976887/10000000000 : ℝ)*X 1 1+(1104244039/2500000000 : ℝ)*X 1 2+(837578337/2000000000 : ℝ)*X 2 0+(4416976887/10000000000 : ℝ)*X 2 1+(1104244039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-136440743/625000000 : ℝ)*X 0 0+(2588042077/5000000000 : ℝ)*X 0 1+(42232489/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274613127/10000000000 : ℝ)*X 1 0+(-2051906303/10000000000 : ℝ)*X 1 1+(67571981/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1054922607/2000000000 : ℝ)*X 2 0+(5405758463/10000000000 : ℝ)*X 2 1+(-512976613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((564942291/1250000000 : ℝ)*X 0 0+(1062730197/2500000000 : ℝ)*X 0 1+(1062730137/2500000000 : ℝ)*X 0 2+(564942291/1250000000 : ℝ)*X 1 0+(1062730197/2500000000 : ℝ)*X 1 1+(1062730137/2500000000 : ℝ)*X 1 2+(564942291/1250000000 : ℝ)*X 2 0+(1062730197/2500000000 : ℝ)*X 2 1+(1062730137/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1983559233/10000000000 : ℝ)*X 0 0+(5477216751/10000000000 : ℝ)*X 0 1+(328303389/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5382210373/10000000000 : ℝ)*X 1 0+(-2112915711/10000000000 : ℝ)*X 1 1+(5252854237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((336388157/625000000 : ℝ)*X 2 0+(525285399/1000000000 : ℝ)*X 2 1+(-1056457927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4161617109/10000000000 : ℝ)*X 0 0+(4429875157/10000000000 : ℝ)*X 0 1+(4429875627/10000000000 : ℝ)*X 0 2+(4161617109/10000000000 : ℝ)*X 1 0+(4429875157/10000000000 : ℝ)*X 1 1+(4429875627/10000000000 : ℝ)*X 1 2+(4161617109/10000000000 : ℝ)*X 2 0+(4429875157/10000000000 : ℝ)*X 2 1+(4429875627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1299_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62841/100000 : ℝ) ≤ (-57041635737125969055791304555279/90775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2407929/100000000000000 : ℝ)*(lower1) + (214257183/50000000000000 : ℝ)*(lower2) + (101327903/100000000000000 : ℝ)*(lower3) + (32103331/25000000000000 : ℝ)*(lower4) + (71870397/100000000000000 : ℝ)*(lower5) + (1436057456456511/50000000000000 : ℝ)*(major0) + (1436057456456511/50000000000000 : ℝ)*(major1) + (1436057456456511/50000000000000 : ℝ)*(major2) + (463460683/10000000000000 : ℝ)*(sp2) + (1944202389510087/50000000000000 : ℝ)*(sp4) + (1944213988265967/50000000000000 : ℝ)*(sp5) + (243026458870319/6250000000000 : ℝ)*(sp6) + (938374005660019/50000000000000 : ℝ)*(sp7) + (289968897/1250000000000 : ℝ)*(sp8) + (938374005660019/50000000000000 : ℝ)*(f.failure) + (1944213988265967/50000000000000 : ℝ)*(f.sum) + (15190554411243/2269375000000000000000000000 : ℝ)*base65 + (57809459260515093/363100000000000000000000000000000 : ℝ)*base68 + (1586475982534484907/363100000000000000000000000000000 : ℝ)*base69 + (1579366653716315093/363100000000000000000000000000000 : ℝ)*base72 + (21250949785053/9077500000000000000000000000 : ℝ)*base74 + (2111092871726315093/363100000000000000000000000000000 : ℝ)*base76 + (9155770548753915093/363100000000000000000000000000000 : ℝ)*base78 + (894004212248115093/363100000000000000000000000000000 : ℝ)*base80 + (23579056542901/4538750000000000000000000000 : ℝ)*base81 + (3909901/500000000000000000000 : ℝ)*base89 + (3909901/500000000000000000000 : ℝ)*base91 + (3909901/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (29429/50000 : ℝ) ≤ (26715504820834080122907078539499/45387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1548127/100000000000000 : ℝ)*(upper0) + (10258249/100000000000000 : ℝ)*(lower1) + (19501923/50000000000000 : ℝ)*(lower3) + (62527583/100000000000000 : ℝ)*(upper4) + (16921687/50000000000000 : ℝ)*(upper5) + (734846137481991/25000000000000 : ℝ)*(major0) + (734846137481991/25000000000000 : ℝ)*(major1) + (734846137481991/25000000000000 : ℝ)*(major2) + (393844426503417/10000000000000 : ℝ)*(sp0) + (196921606359031/5000000000000 : ℝ)*(sp1) + (393844426503417/10000000000000 : ℝ)*(sp2) + (1920703635933289/100000000000000 : ℝ)*(sp3) + (12137853551/100000000000000 : ℝ)*(sp5) + (35549161/4000000000000 : ℝ)*(sp11) + (960352262331157/50000000000000 : ℝ)*(f.failure) + (393844426503417/10000000000000 : ℝ)*(f.sum) + (58434401081223/18155000000000000000000000000 : ℝ)*base65 + (11349032658147667/181550000000000000000000000000000 : ℝ)*base67 + (4147135631612552333/181550000000000000000000000000000 : ℝ)*base70 + (1064226789552197667/181550000000000000000000000000000 : ℝ)*base71 + (382130247626503/18155000000000000000000000000 : ℝ)*base73 + (2166360612064797667/181550000000000000000000000000000 : ℝ)*base75 + (818260647350697667/181550000000000000000000000000000 : ℝ)*base77 + (7321858840451147667/181550000000000000000000000000000 : ℝ)*base79 + (1671861967589/567343750000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1573397/500000000000000000000 : ℝ)*base90 + (1573397/500000000000000000000 : ℝ)*base92 + (1573397/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79699/100000 : ℝ) ≤ (28939583083510150660252532137533/36310000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39707909/100000000000000 : ℝ)*(upper1) + (4782261/10000000000000 : ℝ)*(upper2) + (71677293/100000000000000 : ℝ)*(lower5) + (325314027426401/10000000000000 : ℝ)*(major0) + (325314027426401/10000000000000 : ℝ)*(major1) + (325314027426401/10000000000000 : ℝ)*(major2) + (61396957/781250000000 : ℝ)*(sp1) + (8040139249/25000000000000 : ℝ)*(sp3) + (1276475097/100000000000000 : ℝ)*(sp4) + (2176993839057331/50000000000000 : ℝ)*(sp8) + (87079624500929/2000000000000 : ℝ)*(sp9) + (4353989083856947/100000000000000 : ℝ)*(sp10) + (425138433285217/20000000000000 : ℝ)*(sp11) + (32316797/25000000000000 : ℝ)*(sp12) + (53143108174577/2500000000000 : ℝ)*(f.failure) + (4353989083856947/100000000000000 : ℝ)*(f.sum) + (36189564051399/1815500000000000000000000000 : ℝ)*base66 + (1211648408300789163/72620000000000000000000000000000 : ℝ)*base68 + (812360035181589163/72620000000000000000000000000000 : ℝ)*base70 + (595467148908929163/72620000000000000000000000000000 : ℝ)*base72 + (1338653620523/181550000000000000000000000 : ℝ)*base74 + (674152169861049163/72620000000000000000000000000000 : ℝ)*base76 + (4197432194002629163/72620000000000000000000000000000 : ℝ)*base78 + (550697730437429163/72620000000000000000000000000000 : ℝ)*base80 + (366495760021/72620000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (131217/25000000000000000000 : ℝ)*base90 + (131217/25000000000000000000 : ℝ)*base92 + (131217/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84183/100000 : ℝ) ≤ (-76414574945882871194111076264171/90775000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1831929/25000000000000 : ℝ)*(upper3) + (16159019/20000000000000 : ℝ)*(lower4) + (30901621/25000000000000 : ℝ)*(upper5) + (822282000289513/25000000000000 : ℝ)*(major0) + (822282000289513/25000000000000 : ℝ)*(major1) + (822282000289513/25000000000000 : ℝ)*(major2) + (476836781/10000000000000 : ℝ)*(sp4) + (6158450957/100000000000000 : ℝ)*(sp5) + (190169119603/100000000000000 : ℝ)*(sp6) + (3389396821/5000000000000 : ℝ)*(sp7) + (4457071237451383/100000000000000 : ℝ)*(sp12) + (1114267461842059/25000000000000 : ℝ)*(sp13) + (445688583669959/10000000000000 : ℝ)*(sp14) + (214917227463811/10000000000000 : ℝ)*(sp15) + (214924006257453/10000000000000 : ℝ)*(f.failure) + (4457076005819193/100000000000000 : ℝ)*(f.sum) + (99334870089261/18155000000000000000000000000 : ℝ)*base66 + (656095567659136019/181550000000000000000000000000000 : ℝ)*base68 + (172511899765586019/181550000000000000000000000000000 : ℝ)*base70 + (729655636282386019/181550000000000000000000000000000 : ℝ)*base72 + (44416784208969/18155000000000000000000000000 : ℝ)*base73 + (1243665674258636019/181550000000000000000000000000000 : ℝ)*base76 + (97065472177336019/181550000000000000000000000000000 : ℝ)*base78 + (46370248452686019/181550000000000000000000000000000 : ℝ)*base80 + (11041316730611/18155000000000000000000000000 : ℝ)*base82 + (69587/100000000000000000000 : ℝ)*base89 + (69587/100000000000000000000 : ℝ)*base91 + (69587/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1299_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29429/50000 : ℝ) else (79699/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84183/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1299_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1299_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29429/50000 : ℝ) else (79699/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84183/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1299_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2129/512 : ℝ) ≤ p) (hpb : p ≤ (4259/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15303679/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14677/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62841/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29429/50000 : ℝ) else (79699/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84183/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1299_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
