-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1510_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:55:32.9256+00:00
-- url     : https://prove2.me/submissions/cafeace2-e04f-4b7c-af39-9fbc190d4390

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
theorem support_rectangle_w1510_s6_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1870978067/10000000000 : ℝ)*x 0 + (5433491461/10000000000 : ℝ)*x 1 + (5217535589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1870978067/10000000000 : ℝ)^4517 ≤ (2861607110581/25000000000000 : ℝ)^3493 := by
    have hnat : (1870978067 : ℕ)^4517*25000000000000^3493 ≤ 2861607110581^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870978067 10000000000 2861607110581 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433491461/10000000000 : ℝ)^4517 ≤ (2271879784999/5000000000000 : ℝ)^3493 := by
    have hnat : (5433491461 : ℕ)^4517*5000000000000^3493 ≤ 2271879784999^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433491461 10000000000 2271879784999 5000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217535589/10000000000 : ℝ)^4517 ≤ (43115975852297/100000000000000 : ℝ)^3493 := by
    have hnat : (5217535589 : ℕ)^4517*100000000000000^3493 ≤ 43115975852297^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217535589 10000000000 43115975852297 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1870978067/10000000000 : ℝ), (5433491461/10000000000 : ℝ), (5217535589/10000000000 : ℝ)] ![(2861607110581/25000000000000 : ℝ), (2271879784999/5000000000000 : ℝ), (43115975852297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1870978067/10000000000 : ℝ)|^4517 ≤ (2861607110581/25000000000000 : ℝ)^3493
        have hw : |(-1870978067/10000000000 : ℝ)|=(1870978067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433491461/10000000000 : ℝ)|^4517 ≤ (2271879784999/5000000000000 : ℝ)^3493
        have hw : |(5433491461/10000000000 : ℝ)|=(5433491461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217535589/10000000000 : ℝ)|^4517 ≤ (43115975852297/100000000000000 : ℝ)^3493
        have hw : |(5217535589/10000000000 : ℝ)|=(5217535589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s6_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535170053/1000000000 : ℝ)*x 0 + (-495396129/2500000000 : ℝ)*x 1 + (5217535709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535170053/1000000000 : ℝ)^4517 ≤ (44555064095477/100000000000000 : ℝ)^3493 := by
    have hnat : (535170053 : ℕ)^4517*100000000000000^3493 ≤ 44555064095477^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535170053 1000000000 44555064095477 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495396129/2500000000 : ℝ)^4517 ≤ (6164479378277/50000000000000 : ℝ)^3493 := by
    have hnat : (495396129 : ℕ)^4517*50000000000000^3493 ≤ 6164479378277^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495396129 2500000000 6164479378277 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217535709/10000000000 : ℝ)^4517 ≤ (10778994283661/25000000000000 : ℝ)^3493 := by
    have hnat : (5217535709 : ℕ)^4517*25000000000000^3493 ≤ 10778994283661^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217535709 10000000000 10778994283661 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535170053/1000000000 : ℝ), (-495396129/2500000000 : ℝ), (5217535709/10000000000 : ℝ)] ![(44555064095477/100000000000000 : ℝ), (6164479378277/50000000000000 : ℝ), (10778994283661/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535170053/1000000000 : ℝ)|^4517 ≤ (44555064095477/100000000000000 : ℝ)^3493
        have hw : |(535170053/1000000000 : ℝ)|=(535170053/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495396129/2500000000 : ℝ)|^4517 ≤ (6164479378277/50000000000000 : ℝ)^3493
        have hw : |(-495396129/2500000000 : ℝ)|=(495396129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217535709/10000000000 : ℝ)|^4517 ≤ (10778994283661/25000000000000 : ℝ)^3493
        have hw : |(5217535709/10000000000 : ℝ)|=(5217535709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s6_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675850049/5000000000 : ℝ)*x 0 + (5217535671/10000000000 : ℝ)*x 1 + (-247698143/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675850049/5000000000 : ℝ)^4517 ≤ (44555059444539/100000000000000 : ℝ)^3493 := by
    have hnat : (2675850049 : ℕ)^4517*100000000000000^3493 ≤ 44555059444539^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675850049 5000000000 44555059444539 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217535671/10000000000 : ℝ)^4517 ≤ (5389497091071/12500000000000 : ℝ)^3493 := by
    have hnat : (5217535671 : ℕ)^4517*12500000000000^3493 ≤ 5389497091071^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217535671 10000000000 5389497091071 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (247698143/1250000000 : ℝ)^4517 ≤ (1232896380927/10000000000000 : ℝ)^3493 := by
    have hnat : (247698143 : ℕ)^4517*10000000000000^3493 ≤ 1232896380927^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247698143 1250000000 1232896380927 10000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675850049/5000000000 : ℝ), (5217535671/10000000000 : ℝ), (-247698143/1250000000 : ℝ)] ![(44555059444539/100000000000000 : ℝ), (5389497091071/12500000000000 : ℝ), (1232896380927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675850049/5000000000 : ℝ)|^4517 ≤ (44555059444539/100000000000000 : ℝ)^3493
        have hw : |(2675850049/5000000000 : ℝ)|=(2675850049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217535671/10000000000 : ℝ)|^4517 ≤ (5389497091071/12500000000000 : ℝ)^3493
        have hw : |(5217535671/10000000000 : ℝ)|=(5217535671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-247698143/1250000000 : ℝ)|^4517 ≤ (1232896380927/10000000000000 : ℝ)^3493
        have hw : |(-247698143/1250000000 : ℝ)|=(247698143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s6_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213535237/500000000 : ℝ)*x 0 + (4032151779/10000000000 : ℝ)*x 1 + (2260580923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213535237/500000000 : ℝ)^4517 ≤ (33279563991987/100000000000000 : ℝ)^3493 := by
    have hnat : (213535237 : ℕ)^4517*100000000000000^3493 ≤ 33279563991987^3493*500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213535237 500000000 33279563991987 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032151779/10000000000 : ℝ)^4517 ≤ (3089562254757/10000000000000 : ℝ)^3493 := by
    have hnat : (4032151779 : ℕ)^4517*10000000000000^3493 ≤ 3089562254757^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032151779 10000000000 3089562254757 10000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260580923/5000000000 : ℝ)^4517 ≤ (13994067751/39062500000 : ℝ)^3493 := by
    have hnat : (2260580923 : ℕ)^4517*39062500000^3493 ≤ 13994067751^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260580923 5000000000 13994067751 39062500000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213535237/500000000 : ℝ), (4032151779/10000000000 : ℝ), (2260580923/5000000000 : ℝ)] ![(33279563991987/100000000000000 : ℝ), (3089562254757/10000000000000 : ℝ), (13994067751/39062500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213535237/500000000 : ℝ)|^4517 ≤ (33279563991987/100000000000000 : ℝ)^3493
        have hw : |(213535237/500000000 : ℝ)|=(213535237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032151779/10000000000 : ℝ)|^4517 ≤ (3089562254757/10000000000000 : ℝ)^3493
        have hw : |(4032151779/10000000000 : ℝ)|=(4032151779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2260580923/5000000000 : ℝ)|^4517 ≤ (13994067751/39062500000 : ℝ)^3493
        have hw : |(2260580923/5000000000 : ℝ)|=(2260580923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s6_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871006877/10000000000 : ℝ)*x 0 + (5218647009/10000000000 : ℝ)*x 1 + (5432372031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871006877/10000000000 : ℝ)^4517 ≤ (11446656369991/100000000000000 : ℝ)^3493 := by
    have hnat : (1871006877 : ℕ)^4517*100000000000000^3493 ≤ 11446656369991^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871006877 10000000000 11446656369991 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218647009/10000000000 : ℝ)^4517 ≤ (2695490819191/6250000000000 : ℝ)^3493 := by
    have hnat : (5218647009 : ℕ)^4517*6250000000000^3493 ≤ 2695490819191^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218647009 10000000000 2695490819191 6250000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5432372031/10000000000 : ℝ)^4517 ≤ (9085098101583/20000000000000 : ℝ)^3493 := by
    have hnat : (5432372031 : ℕ)^4517*20000000000000^3493 ≤ 9085098101583^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432372031 10000000000 9085098101583 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871006877/10000000000 : ℝ), (5218647009/10000000000 : ℝ), (5432372031/10000000000 : ℝ)] ![(11446656369991/100000000000000 : ℝ), (2695490819191/6250000000000 : ℝ), (9085098101583/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871006877/10000000000 : ℝ)|^4517 ≤ (11446656369991/100000000000000 : ℝ)^3493
        have hw : |(-1871006877/10000000000 : ℝ)|=(1871006877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218647009/10000000000 : ℝ)|^4517 ≤ (2695490819191/6250000000000 : ℝ)^3493
        have hw : |(5218647009/10000000000 : ℝ)|=(5218647009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5432372031/10000000000 : ℝ)|^4517 ≤ (9085098101583/20000000000000 : ℝ)^3493
        have hw : |(5432372031/10000000000 : ℝ)|=(5432372031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s6_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647513297/5000000000 : ℝ)*x 0 + (2716186479/5000000000 : ℝ)*x 1 + (-1766747109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647513297/5000000000 : ℝ)^4517 ≤ (21972929309923/50000000000000 : ℝ)^3493 := by
    have hnat : (2647513297 : ℕ)^4517*50000000000000^3493 ≤ 21972929309923^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647513297 5000000000 21972929309923 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2716186479/5000000000 : ℝ)^4517 ≤ (22712750265961/50000000000000 : ℝ)^3493 := by
    have hnat : (2716186479 : ℕ)^4517*50000000000000^3493 ≤ 22712750265961^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716186479 5000000000 22712750265961 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1766747109/10000000000 : ℝ)^4517 ≤ (10628640837429/100000000000000 : ℝ)^3493 := by
    have hnat : (1766747109 : ℕ)^4517*100000000000000^3493 ≤ 10628640837429^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766747109 10000000000 10628640837429 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647513297/5000000000 : ℝ), (2716186479/5000000000 : ℝ), (-1766747109/10000000000 : ℝ)] ![(21972929309923/50000000000000 : ℝ), (22712750265961/50000000000000 : ℝ), (10628640837429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647513297/5000000000 : ℝ)|^4517 ≤ (21972929309923/50000000000000 : ℝ)^3493
        have hw : |(2647513297/5000000000 : ℝ)|=(2647513297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2716186479/5000000000 : ℝ)|^4517 ≤ (22712750265961/50000000000000 : ℝ)^3493
        have hw : |(2716186479/5000000000 : ℝ)|=(2716186479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1766747109/10000000000 : ℝ)|^4517 ≤ (10628640837429/100000000000000 : ℝ)^3493
        have hw : |(-1766747109/10000000000 : ℝ)|=(1766747109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s6_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (53384649/125000000 : ℝ)*x 0 + (4518643831/10000000000 : ℝ)*x 1 + (2017343479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53384649/125000000 : ℝ)^4517 ≤ (166401204819/500000000000 : ℝ)^3493 := by
    have hnat : (53384649 : ℕ)^4517*500000000000^3493 ≤ 166401204819^3493*125000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53384649 125000000 166401204819 500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518643831/10000000000 : ℝ)^4517 ≤ (4474876765453/12500000000000 : ℝ)^3493 := by
    have hnat : (4518643831 : ℕ)^4517*12500000000000^3493 ≤ 4474876765453^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518643831 10000000000 4474876765453 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017343479/5000000000 : ℝ)^4517 ≤ (3092074489571/10000000000000 : ℝ)^3493 := by
    have hnat : (2017343479 : ℕ)^4517*10000000000000^3493 ≤ 3092074489571^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017343479 5000000000 3092074489571 10000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53384649/125000000 : ℝ), (4518643831/10000000000 : ℝ), (2017343479/5000000000 : ℝ)] ![(166401204819/500000000000 : ℝ), (4474876765453/12500000000000 : ℝ), (3092074489571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53384649/125000000 : ℝ)|^4517 ≤ (166401204819/500000000000 : ℝ)^3493
        have hw : |(53384649/125000000 : ℝ)|=(53384649/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518643831/10000000000 : ℝ)|^4517 ≤ (4474876765453/12500000000000 : ℝ)^3493
        have hw : |(4518643831/10000000000 : ℝ)|=(4518643831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017343479/5000000000 : ℝ)|^4517 ≤ (3092074489571/10000000000000 : ℝ)^3493
        have hw : |(2017343479/5000000000 : ℝ)|=(2017343479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2727/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7741/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10907/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10907/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10907/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10907/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10907/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10907/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10907/100000 : ℝ) ^ (4515/1024 : ℝ) ≤ (2857852549195531/50000000000000000000 : ℝ) := by
    have hpowers : (10907/100000 : ℝ)^4515 ≤ (2857852549195531/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10907 : ℕ)^4515*50000000000000000000^1024 ≤ 2857852549195531^1024*100000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10907 100000 2857852549195531 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10907/100000 : ℝ)) (X := (2857852549195531/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4515/1024 : ℝ) ≤ (6694866973286697/25000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4515 ≤ (6694866973286697/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4515*25000000000000000000^1024 ≤ 6694866973286697^1024*50000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 6694866973286697 25000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (6694866973286697/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002857852549195531/25000000000000000000 : ℝ) ≤ (625016203276237/625000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25002857852549195531/25000000000000000000 : ℝ)^1024 ≤ (625016203276237/625000000000000 : ℝ)^4515 := by
      have hnat : (25002857852549195531 : ℕ)^1024*625000000000000^4515 ≤ 625016203276237^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002857852549195531 25000000000000000000 625016203276237 625000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625016203276237/625000000000000 : ℝ)) (X := (25002857852549195531/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000649903459830757/2000000000000000000 : ℝ) ≤ (5000368448258251/5000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (2000649903459830757/2000000000000000000 : ℝ)^1024 ≤ (5000368448258251/5000000000000000 : ℝ)^4515 := by
      have hnat : (2000649903459830757 : ℕ)^1024*5000000000000000^4515 ≤ 5000368448258251^4515*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000649903459830757 2000000000000000000 5000368448258251 5000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000368448258251/5000000000000000 : ℝ)) (X := (2000649903459830757/2000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506694866973286697/12500000000000000000 : ℝ) ≤ (2500303635153303/2500000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (12506694866973286697/12500000000000000000 : ℝ)^1024 ≤ (2500303635153303/2500000000000000 : ℝ)^4515 := by
      have hnat : (12506694866973286697 : ℕ)^1024*2500000000000000^4515 ≤ 2500303635153303^4515*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506694866973286697 12500000000000000000 2500303635153303 2500000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500303635153303/2500000000000000 : ℝ)) (X := (12506694866973286697/12500000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2857852549195531/50000000000000000000 : ℝ) ≤ ((2287038337574745823/2287500000000000000 : ℝ)+2*(47764409671/45750000000000 : ℝ)*(10907/100000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (2287038337574745823/2287500000000000000 : ℝ)+2*(47764409671/45750000000000 : ℝ)*(10907/100000 : ℝ)=(625016203276237/625000000000000 : ℝ) by norm_num, show 1+2*(2857852549195531/50000000000000000000 : ℝ)=(25002857852549195531/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6694866973286697/25000000000000000000 : ℝ)+(2857852549195531/50000000000000000000 : ℝ) ≤ ((2287038337574745823/2287500000000000000 : ℝ)+(47764409671/45750000000000 : ℝ)*((7741/50000 : ℝ)+(10907/100000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (2287038337574745823/2287500000000000000 : ℝ)+(47764409671/45750000000000 : ℝ)*((7741/50000 : ℝ)+(10907/100000 : ℝ))=(5000368448258251/5000000000000000 : ℝ) by norm_num, show 1+(6694866973286697/25000000000000000000 : ℝ)+(2857852549195531/50000000000000000000 : ℝ)=(2000649903459830757/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6694866973286697/25000000000000000000 : ℝ) ≤ ((2287038337574745823/2287500000000000000 : ℝ)+2*(47764409671/45750000000000 : ℝ)*(7741/50000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (2287038337574745823/2287500000000000000 : ℝ)+2*(47764409671/45750000000000 : ℝ)*(7741/50000 : ℝ)=(2500303635153303/2500000000000000 : ℝ) by norm_num, show 1+2*(6694866973286697/25000000000000000000 : ℝ)=(12506694866973286697/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2287038337574745823/2287500000000000000 : ℝ)*(X 1 0+X 2 0)+(47764409671/45750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (10907/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (2287038337574745823/2287500000000000000 : ℝ)) (alpha := (47764409671/45750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2287038337574745823/2287500000000000000 : ℝ)*(X 0 1+X 2 1)+(47764409671/45750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (10907/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (2287038337574745823/2287500000000000000 : ℝ)) (alpha := (47764409671/45750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2287038337574745823/2287500000000000000 : ℝ)*(X 0 2+X 1 2)+(47764409671/45750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (10907/100000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (2287038337574745823/2287500000000000000 : ℝ)) (alpha := (47764409671/45750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1870978067/10000000000 : ℝ)*X 0 0+(5433491461/10000000000 : ℝ)*X 0 1+(5217535589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535170053/1000000000 : ℝ)*X 1 0+(-495396129/2500000000 : ℝ)*X 1 1+(5217535709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675850049/5000000000 : ℝ)*X 2 0+(5217535671/10000000000 : ℝ)*X 2 1+(-247698143/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((213535237/500000000 : ℝ)*X 0 0+(4032151779/10000000000 : ℝ)*X 0 1+(2260580923/5000000000 : ℝ)*X 0 2+(213535237/500000000 : ℝ)*X 1 0+(4032151779/10000000000 : ℝ)*X 1 1+(2260580923/5000000000 : ℝ)*X 1 2+(213535237/500000000 : ℝ)*X 2 0+(4032151779/10000000000 : ℝ)*X 2 1+(2260580923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1871006877/10000000000 : ℝ)*X 0 0+(5218647009/10000000000 : ℝ)*X 0 1+(5432372031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647513297/5000000000 : ℝ)*X 2 0+(2716186479/5000000000 : ℝ)*X 2 1+(-1766747109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s6_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((53384649/125000000 : ℝ)*X 0 0+(4518643831/10000000000 : ℝ)*X 0 1+(2017343479/5000000000 : ℝ)*X 0 2+(53384649/125000000 : ℝ)*X 1 0+(4518643831/10000000000 : ℝ)*X 1 1+(2017343479/5000000000 : ℝ)*X 1 2+(53384649/125000000 : ℝ)*X 2 0+(4518643831/10000000000 : ℝ)*X 2 1+(2017343479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (181801079189543303204087591/19062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288458311/20000000000000 : ℝ)*(base19) + (1092523899/100000000000000 : ℝ)*(base23) + (49818163/10000000000000 : ℝ)*(upper3) + (29629869/100000000000000 : ℝ)*(lower4) + (1668897357553217/50000000000000 : ℝ)*(major0) + (1668897357553217/50000000000000 : ℝ)*(major1) + (1668897357553217/50000000000000 : ℝ)*(major2) + (2315302238436381/50000000000000 : ℝ)*(sp0) + (4630614538986411/100000000000000 : ℝ)*(sp1) + (4630611929261759/100000000000000 : ℝ)*(sp2) + (2044958264826013/100000000000000 : ℝ)*(sp3) + (2876101301/25000000000000 : ℝ)*(sp4) + (739873077/25000000000000 : ℝ)*(sp5) + (14866205357/100000000000000 : ℝ)*(sp6) + (204497313103137/10000000000000 : ℝ)*(f.failure) + (926123196255593/20000000000000 : ℝ)*(f.sum) + (7047570274039/2287500000000000000000000000 : ℝ)*base65 + (8787323377895803/38125000000000000000000000000000 : ℝ)*base68 + (247688494799145803/38125000000000000000000000000000 : ℝ)*base70 + (186362161835854197/38125000000000000000000000000000 : ℝ)*base71 + (2094355893289/2287500000000000000000000000 : ℝ)*base73 + (72240075847270803/38125000000000000000000000000000 : ℝ)*base76 + (152755653004145803/38125000000000000000000000000000 : ℝ)*base78 + (98809347662729197/38125000000000000000000000000000 : ℝ)*base79 + (4665247593943/1143750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (145987/100000000000000000000 : ℝ)*base90 + (145987/100000000000000000000 : ℝ)*base92 + (145987/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1510_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1510_s7_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351700917/10000000000 : ℝ)*x 0 + (1043507653/2000000000 : ℝ)*x 1 + (-1981580603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351700917/10000000000 : ℝ)^4517 ≤ (22277534130971/50000000000000 : ℝ)^3493 := by
    have hnat : (5351700917 : ℕ)^4517*50000000000000^3493 ≤ 22277534130971^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351700917 10000000000 22277534130971 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043507653/2000000000 : ℝ)^4517 ≤ (43116004448637/100000000000000 : ℝ)^3493 := by
    have hnat : (1043507653 : ℕ)^4517*100000000000000^3493 ≤ 43116004448637^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043507653 2000000000 43116004448637 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981580603/10000000000 : ℝ)^4517 ≤ (385278977301/3125000000000 : ℝ)^3493 := by
    have hnat : (1981580603 : ℕ)^4517*3125000000000^3493 ≤ 385278977301^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981580603 10000000000 385278977301 3125000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351700917/10000000000 : ℝ), (1043507653/2000000000 : ℝ), (-1981580603/10000000000 : ℝ)] ![(22277534130971/50000000000000 : ℝ), (43116004448637/100000000000000 : ℝ), (385278977301/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351700917/10000000000 : ℝ)|^4517 ≤ (22277534130971/50000000000000 : ℝ)^3493
        have hw : |(5351700917/10000000000 : ℝ)|=(5351700917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043507653/2000000000 : ℝ)|^4517 ≤ (43116004448637/100000000000000 : ℝ)^3493
        have hw : |(1043507653/2000000000 : ℝ)|=(1043507653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981580603/10000000000 : ℝ)|^4517 ≤ (385278977301/3125000000000 : ℝ)^3493
        have hw : |(-1981580603/10000000000 : ℝ)|=(1981580603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s7_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-935502587/5000000000 : ℝ)*x 0 + (5218650041/10000000000 : ℝ)*x 1 + (135809257/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (935502587/5000000000 : ℝ)^4517 ≤ (5723321448417/50000000000000 : ℝ)^3493 := by
    have hnat : (935502587 : ℕ)^4517*50000000000000^3493 ≤ 5723321448417^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935502587 5000000000 5723321448417 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218650041/10000000000 : ℝ)^4517 ≤ (10781971377429/25000000000000 : ℝ)^3493 := by
    have hnat : (5218650041 : ℕ)^4517*25000000000000^3493 ≤ 10781971377429^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218650041 10000000000 10781971377429 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135809257/250000000 : ℝ)^4517 ≤ (45425471573681/100000000000000 : ℝ)^3493 := by
    have hnat : (135809257 : ℕ)^4517*100000000000000^3493 ≤ 45425471573681^3493*250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135809257 250000000 45425471573681 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-935502587/5000000000 : ℝ), (5218650041/10000000000 : ℝ), (135809257/250000000 : ℝ)] ![(5723321448417/50000000000000 : ℝ), (10781971377429/25000000000000 : ℝ), (45425471573681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-935502587/5000000000 : ℝ)|^4517 ≤ (5723321448417/50000000000000 : ℝ)^3493
        have hw : |(-935502587/5000000000 : ℝ)|=(935502587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218650041/10000000000 : ℝ)|^4517 ≤ (10781971377429/25000000000000 : ℝ)^3493
        have hw : |(5218650041/10000000000 : ℝ)|=(5218650041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135809257/250000000 : ℝ)|^4517 ≤ (45425471573681/100000000000000 : ℝ)^3493
        have hw : |(135809257/250000000 : ℝ)|=(135809257/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s7_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323756807/2500000000 : ℝ)*x 0 + (-353349697/2000000000 : ℝ)*x 1 + (2716185669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323756807/2500000000 : ℝ)^4517 ≤ (21972932712129/50000000000000 : ℝ)^3493 := by
    have hnat : (1323756807 : ℕ)^4517*50000000000000^3493 ≤ 21972932712129^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323756807 2500000000 21972932712129 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353349697/2000000000 : ℝ)^4517 ≤ (106286515421/1000000000000 : ℝ)^3493 := by
    have hnat : (353349697 : ℕ)^4517*1000000000000^3493 ≤ 106286515421^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353349697 2000000000 106286515421 1000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716185669/5000000000 : ℝ)^4517 ≤ (283909268839/625000000000 : ℝ)^3493 := by
    have hnat : (2716185669 : ℕ)^4517*625000000000^3493 ≤ 283909268839^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716185669 5000000000 283909268839 625000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323756807/2500000000 : ℝ), (-353349697/2000000000 : ℝ), (2716185669/5000000000 : ℝ)] ![(21972932712129/50000000000000 : ℝ), (106286515421/1000000000000 : ℝ), (283909268839/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323756807/2500000000 : ℝ)|^4517 ≤ (21972932712129/50000000000000 : ℝ)^3493
        have hw : |(1323756807/2500000000 : ℝ)|=(1323756807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-353349697/2000000000 : ℝ)|^4517 ≤ (106286515421/1000000000000 : ℝ)^3493
        have hw : |(-353349697/2000000000 : ℝ)|=(353349697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716185669/5000000000 : ℝ)|^4517 ≤ (283909268839/625000000000 : ℝ)^3493
        have hw : |(2716185669/5000000000 : ℝ)|=(2716185669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s7_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295027739/10000000000 : ℝ)*x 0 + (5432371151/10000000000 : ℝ)*x 1 + (-883374021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295027739/10000000000 : ℝ)^4517 ≤ (43945870908571/100000000000000 : ℝ)^3493 := by
    have hnat : (5295027739 : ℕ)^4517*100000000000000^3493 ≤ 43945870908571^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295027739 10000000000 43945870908571 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432371151/10000000000 : ℝ)^4517 ≤ (45425480992137/100000000000000 : ℝ)^3493 := by
    have hnat : (5432371151 : ℕ)^4517*100000000000000^3493 ≤ 45425480992137^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432371151 10000000000 45425480992137 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883374021/5000000000 : ℝ)^4517 ≤ (2657162023939/25000000000000 : ℝ)^3493 := by
    have hnat : (883374021 : ℕ)^4517*25000000000000^3493 ≤ 2657162023939^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883374021 5000000000 2657162023939 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295027739/10000000000 : ℝ), (5432371151/10000000000 : ℝ), (-883374021/5000000000 : ℝ)] ![(43945870908571/100000000000000 : ℝ), (45425480992137/100000000000000 : ℝ), (2657162023939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295027739/10000000000 : ℝ)|^4517 ≤ (43945870908571/100000000000000 : ℝ)^3493
        have hw : |(5295027739/10000000000 : ℝ)|=(5295027739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432371151/10000000000 : ℝ)|^4517 ≤ (45425480992137/100000000000000 : ℝ)^3493
        have hw : |(5432371151/10000000000 : ℝ)|=(5432371151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883374021/5000000000 : ℝ)|^4517 ≤ (2657162023939/25000000000000 : ℝ)^3493
        have hw : |(-883374021/5000000000 : ℝ)|=(883374021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_s7_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270771919/10000000000 : ℝ)*x 0 + (282414907/625000000 : ℝ)*x 1 + (2017346229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270771919/10000000000 : ℝ)^4517 ≤ (33280240953723/100000000000000 : ℝ)^3493 := by
    have hnat : (4270771919 : ℕ)^4517*100000000000000^3493 ≤ 33280240953723^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270771919 10000000000 33280240953723 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282414907/625000000 : ℝ)^4517 ≤ (7159791926033/20000000000000 : ℝ)^3493 := by
    have hnat : (282414907 : ℕ)^4517*20000000000000^3493 ≤ 7159791926033^3493*625000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282414907 625000000 7159791926033 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017346229/5000000000 : ℝ)^4517 ≤ (15460399701487/50000000000000 : ℝ)^3493 := by
    have hnat : (2017346229 : ℕ)^4517*50000000000000^3493 ≤ 15460399701487^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017346229 5000000000 15460399701487 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270771919/10000000000 : ℝ), (282414907/625000000 : ℝ), (2017346229/5000000000 : ℝ)] ![(33280240953723/100000000000000 : ℝ), (7159791926033/20000000000000 : ℝ), (15460399701487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270771919/10000000000 : ℝ)|^4517 ≤ (33280240953723/100000000000000 : ℝ)^3493
        have hw : |(4270771919/10000000000 : ℝ)|=(4270771919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282414907/625000000 : ℝ)|^4517 ≤ (7159791926033/20000000000000 : ℝ)^3493
        have hw : |(282414907/625000000 : ℝ)|=(282414907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017346229/5000000000 : ℝ)|^4517 ≤ (15460399701487/50000000000000 : ℝ)^3493
        have hw : |(2017346229/5000000000 : ℝ)|=(2017346229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2727/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7741/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7741/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2727/25000 : ℝ) ^ (4515/1024 : ℝ) ≤ (2859008023189867/50000000000000000000 : ℝ) := by
    have hpowers : (2727/25000 : ℝ)^4515 ≤ (2859008023189867/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2727 : ℕ)^4515*50000000000000000000^1024 ≤ 2859008023189867^1024*25000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2727 25000 2859008023189867 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2727/25000 : ℝ)) (X := (2859008023189867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7741/50000 : ℝ) ^ (4515/1024 : ℝ) ≤ (6694866973286697/25000000000000000000 : ℝ) := by
    have hpowers : (7741/50000 : ℝ)^4515 ≤ (6694866973286697/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7741 : ℕ)^4515*25000000000000000000^1024 ≤ 6694866973286697^1024*50000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7741 50000 6694866973286697 25000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7741/50000 : ℝ)) (X := (6694866973286697/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002859008023189867/25000000000000000000 : ℝ) ≤ (5000129678617461/5000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25002859008023189867/25000000000000000000 : ℝ)^1024 ≤ (5000129678617461/5000000000000000 : ℝ)^4515 := by
      have hnat : (25002859008023189867 : ℕ)^1024*5000000000000000^4515 ≤ 5000129678617461^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002859008023189867 25000000000000000000 5000129678617461 5000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000129678617461/5000000000000000 : ℝ)) (X := (25002859008023189867/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50016248741969763261/50000000000000000000 : ℝ) ≤ (2000147389783107/2000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (50016248741969763261/50000000000000000000 : ℝ)^1024 ≤ (2000147389783107/2000000000000000 : ℝ)^4515 := by
      have hnat : (50016248741969763261 : ℕ)^1024*2000000000000000^4515 ≤ 2000147389783107^4515*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016248741969763261 50000000000000000000 2000147389783107 2000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000147389783107/2000000000000000 : ℝ)) (X := (50016248741969763261/50000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506694866973286697/12500000000000000000 : ℝ) ≤ (2500303635149037/2500000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (12506694866973286697/12500000000000000000 : ℝ)^1024 ≤ (2500303635149037/2500000000000000 : ℝ)^4515 := by
      have hnat : (12506694866973286697 : ℕ)^1024*2500000000000000^4515 ≤ 2500303635149037^4515*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506694866973286697 12500000000000000000 2500303635149037 2500000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500303635149037/2500000000000000 : ℝ)) (X := (12506694866973286697/12500000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2859008023189867/50000000000000000000 : ℝ) ≤ ((2286538357994414001/2287000000000000000 : ℝ)+2*(477591680613/457400000000000 : ℝ)*(2727/25000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (2286538357994414001/2287000000000000000 : ℝ)+2*(477591680613/457400000000000 : ℝ)*(2727/25000 : ℝ)=(5000129678617461/5000000000000000 : ℝ) by norm_num, show 1+2*(2859008023189867/50000000000000000000 : ℝ)=(25002859008023189867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6694866973286697/25000000000000000000 : ℝ)+(2859008023189867/50000000000000000000 : ℝ) ≤ ((2286538357994414001/2287000000000000000 : ℝ)+(477591680613/457400000000000 : ℝ)*((7741/50000 : ℝ)+(2727/25000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (2286538357994414001/2287000000000000000 : ℝ)+(477591680613/457400000000000 : ℝ)*((7741/50000 : ℝ)+(2727/25000 : ℝ))=(2000147389783107/2000000000000000 : ℝ) by norm_num, show 1+(6694866973286697/25000000000000000000 : ℝ)+(2859008023189867/50000000000000000000 : ℝ)=(50016248741969763261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6694866973286697/25000000000000000000 : ℝ) ≤ ((2286538357994414001/2287000000000000000 : ℝ)+2*(477591680613/457400000000000 : ℝ)*(7741/50000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (2286538357994414001/2287000000000000000 : ℝ)+2*(477591680613/457400000000000 : ℝ)*(7741/50000 : ℝ)=(2500303635149037/2500000000000000 : ℝ) by norm_num, show 1+2*(6694866973286697/25000000000000000000 : ℝ)=(12506694866973286697/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2286538357994414001/2287000000000000000 : ℝ)*(X 1 0+X 2 0)+(477591680613/457400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (2286538357994414001/2287000000000000000 : ℝ)) (alpha := (477591680613/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2286538357994414001/2287000000000000000 : ℝ)*(X 0 1+X 2 1)+(477591680613/457400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (2286538357994414001/2287000000000000000 : ℝ)) (alpha := (477591680613/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2286538357994414001/2287000000000000000 : ℝ)*(X 0 2+X 1 2)+(477591680613/457400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (7741/50000 : ℝ)) (c := (2286538357994414001/2287000000000000000 : ℝ)) (alpha := (477591680613/457400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5351700917/10000000000 : ℝ)*X 2 0+(1043507653/2000000000 : ℝ)*X 2 1+(-1981580603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-935502587/5000000000 : ℝ)*X 0 0+(5218650041/10000000000 : ℝ)*X 0 1+(135809257/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323756807/2500000000 : ℝ)*X 1 0+(-353349697/2000000000 : ℝ)*X 1 1+(2716185669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5295027739/10000000000 : ℝ)*X 2 0+(5432371151/10000000000 : ℝ)*X 2 1+(-883374021/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4270771919/10000000000 : ℝ)*X 0 0+(282414907/625000000 : ℝ)*X 0 1+(2017346229/5000000000 : ℝ)*X 0 2+(4270771919/10000000000 : ℝ)*X 1 0+(282414907/625000000 : ℝ)*X 1 1+(2017346229/5000000000 : ℝ)*X 1 2+(4270771919/10000000000 : ℝ)*X 2 0+(282414907/625000000 : ℝ)*X 2 1+(2017346229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (65876899467578674317/22870000000000000000000000 : ℝ) := by norm_num
    linear_combination (64114463/50000000000000 : ℝ)*(base23) + (166587769/50000000000000 : ℝ)*(lower1) + (312350093/100000000000000 : ℝ)*(lower2) + (161863071/100000000000000 : ℝ)*(upper3) + (106829821/100000000000000 : ℝ)*(lower4) + (23670161/20000000000000 : ℝ)*(upper5) + (168633651222821/5000000000000 : ℝ)*(major0) + (168633651222821/5000000000000 : ℝ)*(major1) + (168633651222821/5000000000000 : ℝ)*(major2) + (756988323/12500000000000 : ℝ)*(sp0) + (292437741296883/6250000000000 : ℝ)*(sp1) + (292437741296883/6250000000000 : ℝ)*(sp2) + (2339498838307309/50000000000000 : ℝ)*(sp3) + (1033171046073119/50000000000000 : ℝ)*(sp4) + (1033171046073119/50000000000000 : ℝ)*(f.failure) + (292437741296883/6250000000000 : ℝ)*(f.sum) + (5869885556651/571750000000000000000000000 : ℝ)*base66 + (1417511375241821/11435000000000000000000000000000 : ℝ)*base67 + (13768119911658179/11435000000000000000000000000000 : ℝ)*base70 + (43224982834371821/11435000000000000000000000000000 : ℝ)*base71 + (6562498621583/1143500000000000000000000000 : ℝ)*base74 + (47138859014901821/11435000000000000000000000000000 : ℝ)*base75 + (8433099026638179/11435000000000000000000000000000 : ℝ)*base78 + (63482595325808179/11435000000000000000000000000000 : ℝ)*base80 + (3545994929303/1143500000000000000000000000 : ℝ)*base82 + (1411069/500000000000000000000 : ℝ)*base90 + (1411069/500000000000000000000 : ℝ)*base92 + (1411069/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1510_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1510_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1510_box_0 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1656995009/10000000000 : ℝ)*x 0 + (2701523897/5000000000 : ℝ)*x 1 + (2701523681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1656995009/10000000000 : ℝ)^4517 ≤ (4891354832223/50000000000000 : ℝ)^3493 := by
    have hnat : (1656995009 : ℕ)^4517*50000000000000^3493 ≤ 4891354832223^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656995009 10000000000 4891354832223 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701523897/5000000000 : ℝ)^4517 ≤ (1127716187257/2500000000000 : ℝ)^3493 := by
    have hnat : (2701523897 : ℕ)^4517*2500000000000^3493 ≤ 1127716187257^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701523897 5000000000 1127716187257 2500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701523681/5000000000 : ℝ)^4517 ≤ (704822544161/1562500000000 : ℝ)^3493 := by
    have hnat : (2701523681 : ℕ)^4517*1562500000000^3493 ≤ 704822544161^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701523681 5000000000 704822544161 1562500000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1656995009/10000000000 : ℝ), (2701523897/5000000000 : ℝ), (2701523681/5000000000 : ℝ)] ![(4891354832223/50000000000000 : ℝ), (1127716187257/2500000000000 : ℝ), (704822544161/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1656995009/10000000000 : ℝ)|^4517 ≤ (4891354832223/50000000000000 : ℝ)^3493
        have hw : |(-1656995009/10000000000 : ℝ)|=(1656995009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701523897/5000000000 : ℝ)|^4517 ≤ (1127716187257/2500000000000 : ℝ)^3493
        have hw : |(2701523897/5000000000 : ℝ)|=(2701523897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701523681/5000000000 : ℝ)|^4517 ≤ (704822544161/1562500000000 : ℝ)^3493
        have hw : |(2701523681/5000000000 : ℝ)|=(2701523681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_1 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635375397/5000000000 : ℝ)*x 0 + (-1840496947/10000000000 : ℝ)*x 1 + (5403047829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635375397/5000000000 : ℝ)^4517 ≤ (8737098724439/20000000000000 : ℝ)^3493 := by
    have hnat : (2635375397 : ℕ)^4517*20000000000000^3493 ≤ 8737098724439^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635375397 5000000000 8737098724439 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1840496947/10000000000 : ℝ)^4517 ≤ (11205858494149/100000000000000 : ℝ)^3493 := by
    have hnat : (1840496947 : ℕ)^4517*100000000000000^3493 ≤ 11205858494149^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840496947 10000000000 11205858494149 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403047829/10000000000 : ℝ)^4517 ≤ (11277161967037/25000000000000 : ℝ)^3493 := by
    have hnat : (5403047829 : ℕ)^4517*25000000000000^3493 ≤ 11277161967037^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403047829 10000000000 11277161967037 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635375397/5000000000 : ℝ), (-1840496947/10000000000 : ℝ), (5403047829/10000000000 : ℝ)] ![(8737098724439/20000000000000 : ℝ), (11205858494149/100000000000000 : ℝ), (11277161967037/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635375397/5000000000 : ℝ)|^4517 ≤ (8737098724439/20000000000000 : ℝ)^3493
        have hw : |(2635375397/5000000000 : ℝ)|=(2635375397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1840496947/10000000000 : ℝ)|^4517 ≤ (11205858494149/100000000000000 : ℝ)^3493
        have hw : |(-1840496947/10000000000 : ℝ)|=(1840496947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403047829/10000000000 : ℝ)|^4517 ≤ (11277161967037/25000000000000 : ℝ)^3493
        have hw : |(5403047829/10000000000 : ℝ)|=(5403047829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_2 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635375061/5000000000 : ℝ)*x 0 + (675381029/1250000000 : ℝ)*x 1 + (-1840497309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635375061/5000000000 : ℝ)^4517 ≤ (43685486419657/100000000000000 : ℝ)^3493 := by
    have hnat : (2635375061 : ℕ)^4517*100000000000000^3493 ≤ 43685486419657^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635375061 5000000000 43685486419657 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675381029/1250000000 : ℝ)^4517 ≤ (45108652219033/100000000000000 : ℝ)^3493 := by
    have hnat : (675381029 : ℕ)^4517*100000000000000^3493 ≤ 45108652219033^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675381029 1250000000 45108652219033 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1840497309/10000000000 : ℝ)^4517 ≤ (2241172268863/20000000000000 : ℝ)^3493 := by
    have hnat : (1840497309 : ℕ)^4517*20000000000000^3493 ≤ 2241172268863^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840497309 10000000000 2241172268863 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635375061/5000000000 : ℝ), (675381029/1250000000 : ℝ), (-1840497309/10000000000 : ℝ)] ![(43685486419657/100000000000000 : ℝ), (45108652219033/100000000000000 : ℝ), (2241172268863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635375061/5000000000 : ℝ)|^4517 ≤ (43685486419657/100000000000000 : ℝ)^3493
        have hw : |(2635375061/5000000000 : ℝ)|=(2635375061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675381029/1250000000 : ℝ)|^4517 ≤ (45108652219033/100000000000000 : ℝ)^3493
        have hw : |(675381029/1250000000 : ℝ)|=(675381029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1840497309/10000000000 : ℝ)|^4517 ≤ (2241172268863/20000000000000 : ℝ)^3493
        have hw : |(-1840497309/10000000000 : ℝ)|=(1840497309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_3 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (69904013/156250000 : ℝ)*x 0 + (4176123829/10000000000 : ℝ)*x 1 + (835224587/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69904013/156250000 : ℝ)^4517 ≤ (35340836867941/100000000000000 : ℝ)^3493 := by
    have hnat : (69904013 : ℕ)^4517*100000000000000^3493 ≤ 35340836867941^3493*156250000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69904013 156250000 35340836867941 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4176123829/10000000000 : ℝ)^4517 ≤ (6465917207343/20000000000000 : ℝ)^3493 := by
    have hnat : (4176123829 : ℕ)^4517*20000000000000^3493 ≤ 6465917207343^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176123829 10000000000 6465917207343 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835224587/2000000000 : ℝ)^4517 ≤ (2020598567929/6250000000000 : ℝ)^3493 := by
    have hnat : (835224587 : ℕ)^4517*6250000000000^3493 ≤ 2020598567929^3493*2000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835224587 2000000000 2020598567929 6250000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(69904013/156250000 : ℝ), (4176123829/10000000000 : ℝ), (835224587/2000000000 : ℝ)] ![(35340836867941/100000000000000 : ℝ), (6465917207343/20000000000000 : ℝ), (2020598567929/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(69904013/156250000 : ℝ)|^4517 ≤ (35340836867941/100000000000000 : ℝ)^3493
        have hw : |(69904013/156250000 : ℝ)|=(69904013/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4176123829/10000000000 : ℝ)|^4517 ≤ (6465917207343/20000000000000 : ℝ)^3493
        have hw : |(4176123829/10000000000 : ℝ)|=(4176123829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(835224587/2000000000 : ℝ)|^4517 ≤ (2020598567929/6250000000000 : ℝ)^3493
        have hw : |(835224587/2000000000 : ℝ)|=(835224587/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_4 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2090401833/10000000000 : ℝ)*x 0 + (524356109/1000000000 : ℝ)*x 1 + (5243559409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090401833/10000000000 : ℝ)^4517 ≤ (6605715678647/50000000000000 : ℝ)^3493 := by
    have hnat : (2090401833 : ℕ)^4517*50000000000000^3493 ≤ 6605715678647^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090401833 10000000000 6605715678647 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524356109/1000000000 : ℝ)^4517 ≤ (1356071665937/3125000000000 : ℝ)^3493 := by
    have hnat : (524356109 : ℕ)^4517*3125000000000^3493 ≤ 1356071665937^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524356109 1000000000 1356071665937 3125000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243559409/10000000000 : ℝ)^4517 ≤ (43394275320219/100000000000000 : ℝ)^3493 := by
    have hnat : (5243559409 : ℕ)^4517*100000000000000^3493 ≤ 43394275320219^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243559409 10000000000 43394275320219 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2090401833/10000000000 : ℝ), (524356109/1000000000 : ℝ), (5243559409/10000000000 : ℝ)] ![(6605715678647/50000000000000 : ℝ), (1356071665937/3125000000000 : ℝ), (43394275320219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2090401833/10000000000 : ℝ)|^4517 ≤ (6605715678647/50000000000000 : ℝ)^3493
        have hw : |(-2090401833/10000000000 : ℝ)|=(2090401833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524356109/1000000000 : ℝ)|^4517 ≤ (1356071665937/3125000000000 : ℝ)^3493
        have hw : |(524356109/1000000000 : ℝ)|=(524356109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243559409/10000000000 : ℝ)|^4517 ≤ (43394275320219/100000000000000 : ℝ)^3493
        have hw : |(5243559409/10000000000 : ℝ)|=(5243559409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_5 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381806661/10000000000 : ℝ)*x 0 + (-1906251969/10000000000 : ℝ)*x 1 + (2621780051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381806661/10000000000 : ℝ)^4517 ≤ (44879455406389/100000000000000 : ℝ)^3493 := by
    have hnat : (5381806661 : ℕ)^4517*100000000000000^3493 ≤ 44879455406389^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381806661 10000000000 44879455406389 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906251969/10000000000 : ℝ)^4517 ≤ (11726261839193/100000000000000 : ℝ)^3493 := by
    have hnat : (1906251969 : ℕ)^4517*100000000000000^3493 ≤ 11726261839193^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906251969 10000000000 11726261839193 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621780051/5000000000 : ℝ)^4517 ≤ (21697141368291/50000000000000 : ℝ)^3493 := by
    have hnat : (2621780051 : ℕ)^4517*50000000000000^3493 ≤ 21697141368291^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621780051 5000000000 21697141368291 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381806661/10000000000 : ℝ), (-1906251969/10000000000 : ℝ), (2621780051/5000000000 : ℝ)] ![(44879455406389/100000000000000 : ℝ), (11726261839193/100000000000000 : ℝ), (21697141368291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381806661/10000000000 : ℝ)|^4517 ≤ (44879455406389/100000000000000 : ℝ)^3493
        have hw : |(5381806661/10000000000 : ℝ)|=(5381806661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906251969/10000000000 : ℝ)|^4517 ≤ (11726261839193/100000000000000 : ℝ)^3493
        have hw : |(-1906251969/10000000000 : ℝ)|=(1906251969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621780051/5000000000 : ℝ)|^4517 ≤ (21697141368291/50000000000000 : ℝ)^3493
        have hw : |(2621780051/5000000000 : ℝ)|=(2621780051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_6 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381806763/10000000000 : ℝ)*x 0 + (5243559569/10000000000 : ℝ)*x 1 + (-1906252549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381806763/10000000000 : ℝ)^4517 ≤ (8975891301267/20000000000000 : ℝ)^3493 := by
    have hnat : (5381806763 : ℕ)^4517*20000000000000^3493 ≤ 8975891301267^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381806763 10000000000 8975891301267 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243559569/10000000000 : ℝ)^4517 ≤ (43394277032511/100000000000000 : ℝ)^3493 := by
    have hnat : (5243559569 : ℕ)^4517*100000000000000^3493 ≤ 43394277032511^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243559569 10000000000 43394277032511 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906252549/10000000000 : ℝ)^4517 ≤ (11726266452993/100000000000000 : ℝ)^3493 := by
    have hnat : (1906252549 : ℕ)^4517*100000000000000^3493 ≤ 11726266452993^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906252549 10000000000 11726266452993 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381806763/10000000000 : ℝ), (5243559569/10000000000 : ℝ), (-1906252549/10000000000 : ℝ)] ![(8975891301267/20000000000000 : ℝ), (43394277032511/100000000000000 : ℝ), (11726266452993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381806763/10000000000 : ℝ)|^4517 ≤ (8975891301267/20000000000000 : ℝ)^3493
        have hw : |(5381806763/10000000000 : ℝ)|=(5381806763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243559569/10000000000 : ℝ)|^4517 ≤ (43394277032511/100000000000000 : ℝ)^3493
        have hw : |(5243559569/10000000000 : ℝ)|=(5243559569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1906252549/10000000000 : ℝ)|^4517 ≤ (11726266452993/100000000000000 : ℝ)^3493
        have hw : |(-1906252549/10000000000 : ℝ)|=(1906252549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_7 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2032571367/5000000000 : ℝ)*x 0 + (17521387/40000000 : ℝ)*x 1 + (1095086251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2032571367/5000000000 : ℝ)^4517 ≤ (31222907479649/100000000000000 : ℝ)^3493 := by
    have hnat : (2032571367 : ℕ)^4517*100000000000000^3493 ≤ 31222907479649^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2032571367 5000000000 31222907479649 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17521387/40000000 : ℝ)^4517 ≤ (34388555114373/100000000000000 : ℝ)^3493 := by
    have hnat : (17521387 : ℕ)^4517*100000000000000^3493 ≤ 34388555114373^3493*40000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17521387 40000000 34388555114373 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1095086251/2500000000 : ℝ)^4517 ≤ (8597134347191/25000000000000 : ℝ)^3493 := by
    have hnat : (1095086251 : ℕ)^4517*25000000000000^3493 ≤ 8597134347191^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095086251 2500000000 8597134347191 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2032571367/5000000000 : ℝ), (17521387/40000000 : ℝ), (1095086251/2500000000 : ℝ)] ![(31222907479649/100000000000000 : ℝ), (34388555114373/100000000000000 : ℝ), (8597134347191/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2032571367/5000000000 : ℝ)|^4517 ≤ (31222907479649/100000000000000 : ℝ)^3493
        have hw : |(2032571367/5000000000 : ℝ)|=(2032571367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17521387/40000000 : ℝ)|^4517 ≤ (34388555114373/100000000000000 : ℝ)^3493
        have hw : |(17521387/40000000 : ℝ)|=(17521387/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1095086251/2500000000 : ℝ)|^4517 ≤ (8597134347191/25000000000000 : ℝ)^3493
        have hw : |(1095086251/2500000000 : ℝ)|=(1095086251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_8 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1998823119/10000000000 : ℝ)*x 0 + (513184887/1000000000 : ℝ)*x 1 + (338969153/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998823119/10000000000 : ℝ)^4517 ≤ (6233916176159/50000000000000 : ℝ)^3493 := by
    have hnat : (1998823119 : ℕ)^4517*50000000000000^3493 ≤ 6233916176159^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998823119 10000000000 6233916176159 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513184887/1000000000 : ℝ)^4517 ≤ (2637657570899/6250000000000 : ℝ)^3493 := by
    have hnat : (513184887 : ℕ)^4517*6250000000000^3493 ≤ 2637657570899^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513184887 1000000000 2637657570899 6250000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338969153/625000000 : ℝ)^4517 ≤ (11332411624047/25000000000000 : ℝ)^3493 := by
    have hnat : (338969153 : ℕ)^4517*25000000000000^3493 ≤ 11332411624047^3493*625000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338969153 625000000 11332411624047 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1998823119/10000000000 : ℝ), (513184887/1000000000 : ℝ), (338969153/625000000 : ℝ)] ![(6233916176159/50000000000000 : ℝ), (2637657570899/6250000000000 : ℝ), (11332411624047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1998823119/10000000000 : ℝ)|^4517 ≤ (6233916176159/50000000000000 : ℝ)^3493
        have hw : |(-1998823119/10000000000 : ℝ)|=(1998823119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513184887/1000000000 : ℝ)|^4517 ≤ (2637657570899/6250000000000 : ℝ)^3493
        have hw : |(513184887/1000000000 : ℝ)|=(513184887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338969153/625000000 : ℝ)|^4517 ≤ (11332411624047/25000000000000 : ℝ)^3493
        have hw : |(338969153/625000000 : ℝ)|=(338969153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_9 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (657062339/1250000000 : ℝ)*x 0 + (-915907823/5000000000 : ℝ)*x 1 + (2711753197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (657062339/1250000000 : ℝ)^4517 ≤ (21766399752411/50000000000000 : ℝ)^3493 := by
    have hnat : (657062339 : ℕ)^4517*50000000000000^3493 ≤ 21766399752411^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657062339 1250000000 21766399752411 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (915907823/5000000000 : ℝ)^4517 ≤ (11137554571127/100000000000000 : ℝ)^3493 := by
    have hnat : (915907823 : ℕ)^4517*100000000000000^3493 ≤ 11137554571127^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915907823 5000000000 11137554571127 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711753197/5000000000 : ℝ)^4517 ≤ (1416551434767/3125000000000 : ℝ)^3493 := by
    have hnat : (2711753197 : ℕ)^4517*3125000000000^3493 ≤ 1416551434767^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711753197 5000000000 1416551434767 3125000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(657062339/1250000000 : ℝ), (-915907823/5000000000 : ℝ), (2711753197/5000000000 : ℝ)] ![(21766399752411/50000000000000 : ℝ), (11137554571127/100000000000000 : ℝ), (1416551434767/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(657062339/1250000000 : ℝ)|^4517 ≤ (21766399752411/50000000000000 : ℝ)^3493
        have hw : |(657062339/1250000000 : ℝ)|=(657062339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-915907823/5000000000 : ℝ)|^4517 ≤ (11137554571127/100000000000000 : ℝ)^3493
        have hw : |(-915907823/5000000000 : ℝ)|=(915907823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711753197/5000000000 : ℝ)|^4517 ≤ (1416551434767/3125000000000 : ℝ)^3493
        have hw : |(2711753197/5000000000 : ℝ)|=(2711753197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_10 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328531163/625000000 : ℝ)*x 0 + (5423506637/10000000000 : ℝ)*x 1 + (-1831815453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328531163/625000000 : ℝ)^4517 ≤ (10883199597757/25000000000000 : ℝ)^3493 := by
    have hnat : (328531163 : ℕ)^4517*25000000000000^3493 ≤ 10883199597757^3493*625000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328531163 625000000 10883199597757 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423506637/10000000000 : ℝ)^4517 ≤ (45329648538939/100000000000000 : ℝ)^3493 := by
    have hnat : (5423506637 : ℕ)^4517*100000000000000^3493 ≤ 45329648538939^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423506637 10000000000 45329648538939 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1831815453/10000000000 : ℝ)^4517 ≤ (2784388263417/25000000000000 : ℝ)^3493 := by
    have hnat : (1831815453 : ℕ)^4517*25000000000000^3493 ≤ 2784388263417^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1831815453 10000000000 2784388263417 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328531163/625000000 : ℝ), (5423506637/10000000000 : ℝ), (-1831815453/10000000000 : ℝ)] ![(10883199597757/25000000000000 : ℝ), (45329648538939/100000000000000 : ℝ), (2784388263417/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328531163/625000000 : ℝ)|^4517 ≤ (10883199597757/25000000000000 : ℝ)^3493
        have hw : |(328531163/625000000 : ℝ)|=(328531163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423506637/10000000000 : ℝ)|^4517 ≤ (45329648538939/100000000000000 : ℝ)^3493
        have hw : |(5423506637/10000000000 : ℝ)|=(5423506637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1831815453/10000000000 : ℝ)|^4517 ≤ (2784388263417/25000000000000 : ℝ)^3493
        have hw : |(-1831815453/10000000000 : ℝ)|=(1831815453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_11 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2262567413/5000000000 : ℝ)*x 0 + (207494677/500000000 : ℝ)*x 1 + (518736677/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2262567413/5000000000 : ℝ)^4517 ≤ (17932764373761/50000000000000 : ℝ)^3493 := by
    have hnat : (2262567413 : ℕ)^4517*50000000000000^3493 ≤ 17932764373761^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262567413 5000000000 17932764373761 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207494677/500000000 : ℝ)^4517 ≤ (32067236235627/100000000000000 : ℝ)^3493 := by
    have hnat : (207494677 : ℕ)^4517*100000000000000^3493 ≤ 32067236235627^3493*500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207494677 500000000 32067236235627 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518736677/1250000000 : ℝ)^4517 ≤ (4008404374569/12500000000000 : ℝ)^3493 := by
    have hnat : (518736677 : ℕ)^4517*12500000000000^3493 ≤ 4008404374569^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518736677 1250000000 4008404374569 12500000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2262567413/5000000000 : ℝ), (207494677/500000000 : ℝ), (518736677/1250000000 : ℝ)] ![(17932764373761/50000000000000 : ℝ), (32067236235627/100000000000000 : ℝ), (4008404374569/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2262567413/5000000000 : ℝ)|^4517 ≤ (17932764373761/50000000000000 : ℝ)^3493
        have hw : |(2262567413/5000000000 : ℝ)|=(2262567413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207494677/500000000 : ℝ)|^4517 ≤ (32067236235627/100000000000000 : ℝ)^3493
        have hw : |(207494677/500000000 : ℝ)|=(207494677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518736677/1250000000 : ℝ)|^4517 ≤ (4008404374569/12500000000000 : ℝ)^3493
        have hw : |(518736677/1250000000 : ℝ)|=(518736677/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_12 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-218566783/1250000000 : ℝ)*x 0 + (2755580731/5000000000 : ℝ)*x 1 + (2614267597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218566783/1250000000 : ℝ)^4517 ≤ (5243583797939/50000000000000 : ℝ)^3493 := by
    have hnat : (218566783 : ℕ)^4517*50000000000000^3493 ≤ 5243583797939^3493*1250000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218566783 1250000000 5243583797939 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2755580731/5000000000 : ℝ)^4517 ≤ (23139637991787/50000000000000 : ℝ)^3493 := by
    have hnat : (2755580731 : ℕ)^4517*50000000000000^3493 ≤ 23139637991787^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755580731 5000000000 23139637991787 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614267597/5000000000 : ℝ)^4517 ≤ (8646711281789/20000000000000 : ℝ)^3493 := by
    have hnat : (2614267597 : ℕ)^4517*20000000000000^3493 ≤ 8646711281789^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614267597 5000000000 8646711281789 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-218566783/1250000000 : ℝ), (2755580731/5000000000 : ℝ), (2614267597/5000000000 : ℝ)] ![(5243583797939/50000000000000 : ℝ), (23139637991787/50000000000000 : ℝ), (8646711281789/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-218566783/1250000000 : ℝ)|^4517 ≤ (5243583797939/50000000000000 : ℝ)^3493
        have hw : |(-218566783/1250000000 : ℝ)|=(218566783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2755580731/5000000000 : ℝ)|^4517 ≤ (23139637991787/50000000000000 : ℝ)^3493
        have hw : |(2755580731/5000000000 : ℝ)|=(2755580731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614267597/5000000000 : ℝ)|^4517 ≤ (8646711281789/20000000000000 : ℝ)^3493
        have hw : |(2614267597/5000000000 : ℝ)|=(2614267597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_13 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392268073/10000000000 : ℝ)*x 0 + (-478066951/2500000000 : ℝ)*x 1 + (522853553/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392268073/10000000000 : ℝ)^4517 ≤ (44992301093561/100000000000000 : ℝ)^3493 := by
    have hnat : (5392268073 : ℕ)^4517*100000000000000^3493 ≤ 44992301093561^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392268073 10000000000 44992301093561 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (478066951/2500000000 : ℝ)^4517 ≤ (5887069445733/50000000000000 : ℝ)^3493 := by
    have hnat : (478066951 : ℕ)^4517*50000000000000^3493 ≤ 5887069445733^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478066951 2500000000 5887069445733 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522853553/1000000000 : ℝ)^4517 ≤ (21616780000867/50000000000000 : ℝ)^3493 := by
    have hnat : (522853553 : ℕ)^4517*50000000000000^3493 ≤ 21616780000867^3493*1000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522853553 1000000000 21616780000867 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392268073/10000000000 : ℝ), (-478066951/2500000000 : ℝ), (522853553/1000000000 : ℝ)] ![(44992301093561/100000000000000 : ℝ), (5887069445733/50000000000000 : ℝ), (21616780000867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392268073/10000000000 : ℝ)|^4517 ≤ (44992301093561/100000000000000 : ℝ)^3493
        have hw : |(5392268073/10000000000 : ℝ)|=(5392268073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-478066951/2500000000 : ℝ)|^4517 ≤ (5887069445733/50000000000000 : ℝ)^3493
        have hw : |(-478066951/2500000000 : ℝ)|=(478066951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522853553/1000000000 : ℝ)|^4517 ≤ (21616780000867/50000000000000 : ℝ)^3493
        have hw : |(522853553/1000000000 : ℝ)|=(522853553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_14 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348067231/2500000000 : ℝ)*x 0 + (5228534561/10000000000 : ℝ)*x 1 + (-1912267951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348067231/2500000000 : ℝ)^4517 ≤ (44992310275783/100000000000000 : ℝ)^3493 := by
    have hnat : (1348067231 : ℕ)^4517*100000000000000^3493 ≤ 44992310275783^3493*2500000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348067231 2500000000 44992310275783 100000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228534561/10000000000 : ℝ)^4517 ≤ (10808387410097/25000000000000 : ℝ)^3493 := by
    have hnat : (5228534561 : ℕ)^4517*25000000000000^3493 ≤ 10808387410097^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228534561 10000000000 10808387410097 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1912267951/10000000000 : ℝ)^4517 ≤ (5887070030953/50000000000000 : ℝ)^3493 := by
    have hnat : (1912267951 : ℕ)^4517*50000000000000^3493 ≤ 5887070030953^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912267951 10000000000 5887070030953 50000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348067231/2500000000 : ℝ), (5228534561/10000000000 : ℝ), (-1912267951/10000000000 : ℝ)] ![(44992310275783/100000000000000 : ℝ), (10808387410097/25000000000000 : ℝ), (5887070030953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348067231/2500000000 : ℝ)|^4517 ≤ (44992310275783/100000000000000 : ℝ)^3493
        have hw : |(1348067231/2500000000 : ℝ)|=(1348067231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228534561/10000000000 : ℝ)|^4517 ≤ (10808387410097/25000000000000 : ℝ)^3493
        have hw : |(5228534561/10000000000 : ℝ)|=(5228534561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1912267951/10000000000 : ℝ)|^4517 ≤ (5887070030953/50000000000000 : ℝ)^3493
        have hw : |(-1912267951/10000000000 : ℝ)|=(1912267951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1510_box_15 (p : ℝ) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2012889567/5000000000 : ℝ)*x 0 + (4399562071/10000000000 : ℝ)*x 1 + (21997807/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2012889567/5000000000 : ℝ)^4517 ≤ (7708123323603/25000000000000 : ℝ)^3493 := by
    have hnat : (2012889567 : ℕ)^4517*25000000000000^3493 ≤ 7708123323603^3493*5000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012889567 5000000000 7708123323603 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4399562071/10000000000 : ℝ)^4517 ≤ (8645939188377/25000000000000 : ℝ)^3493 := by
    have hnat : (4399562071 : ℕ)^4517*25000000000000^3493 ≤ 8645939188377^3493*10000000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4399562071 10000000000 8645939188377 25000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21997807/50000000 : ℝ)^4517 ≤ (6916749986537/20000000000000 : ℝ)^3493 := by
    have hnat : (21997807 : ℕ)^4517*20000000000000^3493 ≤ 6916749986537^3493*50000000^4517 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21997807 50000000 6916749986537 20000000000000 4517 3493 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4517/1024 : ℝ)) 4517 3493 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2012889567/5000000000 : ℝ), (4399562071/10000000000 : ℝ), (21997807/50000000 : ℝ)] ![(7708123323603/25000000000000 : ℝ), (8645939188377/25000000000000 : ℝ), (6916749986537/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2012889567/5000000000 : ℝ)|^4517 ≤ (7708123323603/25000000000000 : ℝ)^3493
        have hw : |(2012889567/5000000000 : ℝ)|=(2012889567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4399562071/10000000000 : ℝ)|^4517 ≤ (8645939188377/25000000000000 : ℝ)^3493
        have hw : |(4399562071/10000000000 : ℝ)|=(4399562071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21997807/50000000 : ℝ)|^4517 ≤ (6916749986537/20000000000000 : ℝ)^3493
        have hw : |(21997807/50000000 : ℝ)|=(21997807/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1510_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63737/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29309/50000 : ℝ) ∧ (40149/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85989/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2727/25000 : ℝ) ^ (4515/1024 : ℝ) ≤ (2859008023189867/50000000000000000000 : ℝ) := by
    have hpowers : (2727/25000 : ℝ)^4515 ≤ (2859008023189867/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2727 : ℕ)^4515*50000000000000000000^1024 ≤ 2859008023189867^1024*25000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2727 25000 2859008023189867 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2727/25000 : ℝ)) (X := (2859008023189867/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4515/1024 : ℝ) ≤ (13385921051395937/50000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4515 ≤ (13385921051395937/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4515*50000000000000000000^1024 ≤ 13385921051395937^1024*100000^4515 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 13385921051395937 50000000000000000000 4515 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (13385921051395937/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002859008023189867/25000000000000000000 : ℝ) ≤ (5000129678617461/5000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25002859008023189867/25000000000000000000 : ℝ)^1024 ≤ (5000129678617461/5000000000000000 : ℝ)^4515 := by
      have hnat : (25002859008023189867 : ℕ)^1024*5000000000000000^4515 ≤ 5000129678617461^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002859008023189867 25000000000000000000 5000129678617461 5000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000129678617461/5000000000000000 : ℝ)) (X := (25002859008023189867/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12504061232268646451/12500000000000000000 : ℝ) ≤ (2500184194001597/2500000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (12504061232268646451/12500000000000000000 : ℝ)^1024 ≤ (2500184194001597/2500000000000000 : ℝ)^4515 := by
      have hnat : (12504061232268646451 : ℕ)^1024*2500000000000000^4515 ≤ 2500184194001597^4515*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12504061232268646451 12500000000000000000 2500184194001597 2500000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184194001597/2500000000000000 : ℝ)) (X := (12504061232268646451/12500000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013385921051395937/25000000000000000000 : ℝ) ≤ (5000607097388927/5000000000000000 : ℝ) ^ (4515/1024 : ℝ) := by
    have hpowers : (25013385921051395937/25000000000000000000 : ℝ)^1024 ≤ (5000607097388927/5000000000000000 : ℝ)^4515 := by
      have hnat : (25013385921051395937 : ℕ)^1024*5000000000000000^4515 ≤ 5000607097388927^4515*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013385921051395937 25000000000000000000 5000607097388927 5000000000000000 1024 4515 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000607097388927/5000000000000000 : ℝ)) (X := (25013385921051395937/25000000000000000000 : ℝ)) (by norm_num) 4515 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2859008023189867/50000000000000000000 : ℝ) ≤ ((914415413454339921/914600000000000000 : ℝ)+2*(238709385733/228650000000000 : ℝ)*(2727/25000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (914415413454339921/914600000000000000 : ℝ)+2*(238709385733/228650000000000 : ℝ)*(2727/25000 : ℝ)=(5000129678617461/5000000000000000 : ℝ) by norm_num, show 1+2*(2859008023189867/50000000000000000000 : ℝ)=(25002859008023189867/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13385921051395937/50000000000000000000 : ℝ)+(2859008023189867/50000000000000000000 : ℝ) ≤ ((914415413454339921/914600000000000000 : ℝ)+(238709385733/228650000000000 : ℝ)*((15481/100000 : ℝ)+(2727/25000 : ℝ)))^(4515/1024 : ℝ) := by
    rw [show (914415413454339921/914600000000000000 : ℝ)+(238709385733/228650000000000 : ℝ)*((15481/100000 : ℝ)+(2727/25000 : ℝ))=(2500184194001597/2500000000000000 : ℝ) by norm_num, show 1+(13385921051395937/50000000000000000000 : ℝ)+(2859008023189867/50000000000000000000 : ℝ)=(12504061232268646451/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13385921051395937/50000000000000000000 : ℝ) ≤ ((914415413454339921/914600000000000000 : ℝ)+2*(238709385733/228650000000000 : ℝ)*(15481/100000 : ℝ))^(4515/1024 : ℝ) := by
    rw [show (914415413454339921/914600000000000000 : ℝ)+2*(238709385733/228650000000000 : ℝ)*(15481/100000 : ℝ)=(5000607097388927/5000000000000000 : ℝ) by norm_num, show 1+2*(13385921051395937/50000000000000000000 : ℝ)=(25013385921051395937/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (914415413454339921/914600000000000000 : ℝ)*(X 1 0+X 2 0)+(238709385733/228650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (914415413454339921/914600000000000000 : ℝ)) (alpha := (238709385733/228650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (914415413454339921/914600000000000000 : ℝ)*(X 0 1+X 2 1)+(238709385733/228650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (914415413454339921/914600000000000000 : ℝ)) (alpha := (238709385733/228650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (914415413454339921/914600000000000000 : ℝ)*(X 0 2+X 1 2)+(238709385733/228650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4515/1024 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (914415413454339921/914600000000000000 : ℝ)) (alpha := (238709385733/228650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1656995009/10000000000 : ℝ)*X 0 0+(2701523897/5000000000 : ℝ)*X 0 1+(2701523681/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635375397/5000000000 : ℝ)*X 1 0+(-1840496947/10000000000 : ℝ)*X 1 1+(5403047829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635375061/5000000000 : ℝ)*X 2 0+(675381029/1250000000 : ℝ)*X 2 1+(-1840497309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((69904013/156250000 : ℝ)*X 0 0+(4176123829/10000000000 : ℝ)*X 0 1+(835224587/2000000000 : ℝ)*X 0 2+(69904013/156250000 : ℝ)*X 1 0+(4176123829/10000000000 : ℝ)*X 1 1+(835224587/2000000000 : ℝ)*X 1 2+(69904013/156250000 : ℝ)*X 2 0+(4176123829/10000000000 : ℝ)*X 2 1+(835224587/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2090401833/10000000000 : ℝ)*X 0 0+(524356109/1000000000 : ℝ)*X 0 1+(5243559409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5381806661/10000000000 : ℝ)*X 1 0+(-1906251969/10000000000 : ℝ)*X 1 1+(2621780051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5381806763/10000000000 : ℝ)*X 2 0+(5243559569/10000000000 : ℝ)*X 2 1+(-1906252549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2032571367/5000000000 : ℝ)*X 0 0+(17521387/40000000 : ℝ)*X 0 1+(1095086251/2500000000 : ℝ)*X 0 2+(2032571367/5000000000 : ℝ)*X 1 0+(17521387/40000000 : ℝ)*X 1 1+(1095086251/2500000000 : ℝ)*X 1 2+(2032571367/5000000000 : ℝ)*X 2 0+(17521387/40000000 : ℝ)*X 2 1+(1095086251/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1998823119/10000000000 : ℝ)*X 0 0+(513184887/1000000000 : ℝ)*X 0 1+(338969153/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((657062339/1250000000 : ℝ)*X 1 0+(-915907823/5000000000 : ℝ)*X 1 1+(2711753197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((328531163/625000000 : ℝ)*X 2 0+(5423506637/10000000000 : ℝ)*X 2 1+(-1831815453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2262567413/5000000000 : ℝ)*X 0 0+(207494677/500000000 : ℝ)*X 0 1+(518736677/1250000000 : ℝ)*X 0 2+(2262567413/5000000000 : ℝ)*X 1 0+(207494677/500000000 : ℝ)*X 1 1+(518736677/1250000000 : ℝ)*X 1 2+(2262567413/5000000000 : ℝ)*X 2 0+(207494677/500000000 : ℝ)*X 2 1+(518736677/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-218566783/1250000000 : ℝ)*X 0 0+(2755580731/5000000000 : ℝ)*X 0 1+(2614267597/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5392268073/10000000000 : ℝ)*X 1 0+(-478066951/2500000000 : ℝ)*X 1 1+(522853553/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1348067231/2500000000 : ℝ)*X 2 0+(5228534561/10000000000 : ℝ)*X 2 1+(-1912267951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2012889567/5000000000 : ℝ)*X 0 0+(4399562071/10000000000 : ℝ)*X 0 1+(21997807/50000000 : ℝ)*X 0 2+(2012889567/5000000000 : ℝ)*X 1 0+(4399562071/10000000000 : ℝ)*X 1 1+(21997807/50000000 : ℝ)*X 1 2+(2012889567/5000000000 : ℝ)*X 2 0+(4399562071/10000000000 : ℝ)*X 2 1+(21997807/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1510_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63737/100000 : ℝ) ≤ (-1457282212370336369544812613/2286500000000000000000000000 : ℝ) := by norm_num
    linear_combination (69873933/100000000000000 : ℝ)*(upper1) + (260181279/100000000000000 : ℝ)*(upper3) + (34322929/50000000000000 : ℝ)*(lower5) + (444096296863409/20000000000000 : ℝ)*(major0) + (444096296863409/20000000000000 : ℝ)*(major1) + (444096296863409/20000000000000 : ℝ)*(major2) + (13245684537/100000000000000 : ℝ)*(sp1) + (16094423773/100000000000000 : ℝ)*(sp2) + (2846330563/50000000000000 : ℝ)*(sp3) + (3101767911513391/100000000000000 : ℝ)*(sp4) + (310176777515761/10000000000000 : ℝ)*(sp5) + (1550882463209187/50000000000000 : ℝ)*(sp6) + (680210492259407/50000000000000 : ℝ)*(sp7) + (13109328757/100000000000000 : ℝ)*(sp8) + (68021333858997/5000000000000 : ℝ)*(f.failure) + (775445255210537/25000000000000 : ℝ)*(f.sum) + (888148964843/285812500000000000000000000 : ℝ)*base65 + (118298314570289311/18292000000000000000000000000000 : ℝ)*base68 + (62247316737293311/18292000000000000000000000000000 : ℝ)*base70 + (90117328154406689/18292000000000000000000000000000 : ℝ)*base71 + (11796961757631/4573000000000000000000000000 : ℝ)*base74 + (217098706219989311/18292000000000000000000000000000 : ℝ)*base76 + (65770656399046689/18292000000000000000000000000000 : ℝ)*base77 + (73383016340006689/18292000000000000000000000000000 : ℝ)*base79 + (1831196728273/914600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (274847/50000000000000000000 : ℝ)*base90 + (274847/50000000000000000000 : ℝ)*base92 + (274847/50000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29309/50000 : ℝ) ≤ (837727397680584006825047785233/1429062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (49606243/100000000000000 : ℝ)*(lower0) + (14927159/50000000000000 : ℝ)*(upper1) + (31778623/25000000000000 : ℝ)*(upper2) + (44433257/25000000000000 : ℝ)*(upper3) + (6790831/20000000000000 : ℝ)*(lower5) + (143536161889993/6250000000000 : ℝ)*(major0) + (143536161889993/6250000000000 : ℝ)*(major1) + (143536161889993/6250000000000 : ℝ)*(major2) + (158328384343729/5000000000000 : ℝ)*(sp0) + (158328384343729/5000000000000 : ℝ)*(sp1) + (1583279985997707/50000000000000 : ℝ)*(sp2) + (175878589024981/12500000000000 : ℝ)*(sp3) + (1542975833/20000000000000 : ℝ)*(sp6) + (20525755673/100000000000000 : ℝ)*(sp11) + (1407049237955521/100000000000000 : ℝ)*(f.failure) + (158328384343729/5000000000000 : ℝ)*(f.sum) + (6743092063651/11432500000000000000000000000 : ℝ)*base66 + (62083190559741553/5716250000000000000000000000000 : ℝ)*base67 + (14261980508943447/5716250000000000000000000000000 : ℝ)*base70 + (16868573250234053/5716250000000000000000000000000 : ℝ)*base71 + (489621472833/1429062500000000000000000000 : ℝ)*base73 + (70112194479918447/5716250000000000000000000000000 : ℝ)*base76 + (45819568117785303/5716250000000000000000000000000 : ℝ)*base77 + (72283201820180303/5716250000000000000000000000000 : ℝ)*base79 + (139857432530303/22865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1969571/1000000000000000000000 : ℝ)*base90 + (1969571/1000000000000000000000 : ℝ)*base92 + (1969571/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40149/50000 : ℝ) ≤ (7344264200055838621447752361917/9146000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22825421/100000000000000 : ℝ)*(lower2) + (12927/781250000000 : ℝ)*(lower3) + (204527/1250000000000 : ℝ)*(upper4) + (498144240729359/20000000000000 : ℝ)*(major0) + (498144240729359/20000000000000 : ℝ)*(major1) + (498144240729359/20000000000000 : ℝ)*(major2) + (1031651857/20000000000000 : ℝ)*(sp1) + (5767629651/10000000000000 : ℝ)*(sp2) + (11083496867/100000000000000 : ℝ)*(sp3) + (761704049/50000000000000 : ℝ)*(sp4) + (42858489425833/1250000000000 : ℝ)*(sp8) + (3428675519215453/100000000000000 : ℝ)*(sp9) + (857155750294557/25000000000000 : ℝ)*(sp10) + (762991942083551/50000000000000 : ℝ)*(sp11) + (1525994967663969/100000000000000 : ℝ)*(f.failure) + (1714340338737369/50000000000000 : ℝ)*(f.sum) + (2297193829437/1143250000000000000000000000 : ℝ)*base65 + (33556269268327361/18292000000000000000000000000000 : ℝ)*base68 + (144286259023639361/18292000000000000000000000000000 : ℝ)*base70 + (165479166035804639/18292000000000000000000000000000 : ℝ)*base71 + (779564571969/1143250000000000000000000000 : ℝ)*base74 + (88880887537579361/18292000000000000000000000000000 : ℝ)*base76 + (61633611197451361/18292000000000000000000000000000 : ℝ)*base78 + (43475624230360639/18292000000000000000000000000000 : ℝ)*base79 + (316011954641/182920000000000000000000000 : ℝ)*base82 + (1155581/1000000000000000000000 : ℝ)*base89 + (1155581/1000000000000000000000 : ℝ)*base91 + (1155581/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-85989/100000 : ℝ) ≤ (-1156517886822196899232000098771/1345000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49499901/100000000000000 : ℝ)*(upper1) + (109020863/100000000000000 : ℝ)*(lower2) + (183161759/100000000000000 : ℝ)*(upper3) + (23386359/12500000000000 : ℝ)*(upper5) + (1264868489334511/50000000000000 : ℝ)*(major0) + (1264868489334511/50000000000000 : ℝ)*(major1) + (1264868489334511/50000000000000 : ℝ)*(major2) + (1967055681/20000000000000 : ℝ)*(sp5) + (9671626083/5000000000000 : ℝ)*(sp6) + (11026418191/100000000000000 : ℝ)*(sp7) + (3538237272808189/100000000000000 : ℝ)*(sp12) + (442278429691223/12500000000000 : ℝ)*(sp13) + (3538043840286529/100000000000000 : ℝ)*(sp14) + (774943905720293/50000000000000 : ℝ)*(sp15) + (1549898837858777/100000000000000 : ℝ)*(f.failure) + (3538237272808189/100000000000000 : ℝ)*(f.sum) + (3809742592317/672500000000000000000000000 : ℝ)*base66 + (2885971488850257/2690000000000000000000000000000 : ℝ)*base68 + (10591736493490257/2690000000000000000000000000000 : ℝ)*base70 + (8287742952740257/2690000000000000000000000000000 : ℝ)*base72 + (3312244075081/1345000000000000000000000000 : ℝ)*base73 + (10391556955349743/2690000000000000000000000000000 : ℝ)*base75 + (20248207743650257/2690000000000000000000000000000 : ℝ)*base78 + (9549411645359743/2690000000000000000000000000000 : ℝ)*base79 + (12875912748931/1345000000000000000000000000 : ℝ)*base81 + (7396373/1000000000000000000000 : ℝ)*base89 + (7396373/1000000000000000000000 : ℝ)*base91 + (7396373/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1510_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63737/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29309/50000 : ℝ) else (40149/50000 : ℝ) ≤ X j i ∧ X j i ≤ (85989/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1510_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1510_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63737/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29309/50000 : ℝ) else (40149/50000 : ℝ) ≤ X j i ∧ X j i ≤ (85989/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1510_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1510_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1510_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4515/1024 : ℝ) ≤ p) (hpb : p ≤ (4517/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (16321949/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7741/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10907/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63737/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29309/50000 : ℝ) else (40149/50000 : ℝ) ≤ X j i ∧ X j i ≤ (85989/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1510_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
