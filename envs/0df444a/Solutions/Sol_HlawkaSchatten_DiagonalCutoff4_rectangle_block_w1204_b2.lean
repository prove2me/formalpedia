-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:39.407984+00:00
-- url     : https://prove2.me/submissions/271366f5-b063-4a71-b6e6-9230cd9c2e45

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
theorem support_rectangle_w1204_s6_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137564409/10000000000 : ℝ)*x 0 + (2696071441/5000000000 : ℝ)*x 1 + (1053291803/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137564409/10000000000 : ℝ)^8397 ≤ (3248709914949/25000000000000 : ℝ)^6349 := by
    have hnat : (2137564409 : ℕ)^8397*25000000000000^6349 ≤ 3248709914949^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137564409 10000000000 3248709914949 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696071441/5000000000 : ℝ)^8397 ≤ (552262490553/1250000000000 : ℝ)^6349 := by
    have hnat : (2696071441 : ℕ)^8397*1250000000000^6349 ≤ 552262490553^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696071441 5000000000 552262490553 1250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053291803/2000000000 : ℝ)^8397 ≤ (2141208054061/5000000000000 : ℝ)^6349 := by
    have hnat : (1053291803 : ℕ)^8397*5000000000000^6349 ≤ 2141208054061^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053291803 2000000000 2141208054061 5000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137564409/10000000000 : ℝ), (2696071441/5000000000 : ℝ), (1053291803/2000000000 : ℝ)] ![(3248709914949/25000000000000 : ℝ), (552262490553/1250000000000 : ℝ), (2141208054061/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137564409/10000000000 : ℝ)|^8397 ≤ (3248709914949/25000000000000 : ℝ)^6349
        have hw : |(-2137564409/10000000000 : ℝ)|=(2137564409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696071441/5000000000 : ℝ)|^8397 ≤ (552262490553/1250000000000 : ℝ)^6349
        have hw : |(2696071441/5000000000 : ℝ)|=(2696071441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053291803/2000000000 : ℝ)|^8397 ≤ (2141208054061/5000000000000 : ℝ)^6349
        have hw : |(1053291803/2000000000 : ℝ)|=(1053291803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s6_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344558977/10000000000 : ℝ)*x 0 + (-1100650797/5000000000 : ℝ)*x 1 + (2633229511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344558977/10000000000 : ℝ)^8397 ≤ (43666086971681/100000000000000 : ℝ)^6349 := by
    have hnat : (5344558977 : ℕ)^8397*100000000000000^6349 ≤ 43666086971681^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344558977 10000000000 43666086971681 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100650797/5000000000 : ℝ)^8397 ≤ (13509751855129/100000000000000 : ℝ)^6349 := by
    have hnat : (1100650797 : ℕ)^8397*100000000000000^6349 ≤ 13509751855129^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100650797 5000000000 13509751855129 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633229511/5000000000 : ℝ)^8397 ≤ (21412080578251/50000000000000 : ℝ)^6349 := by
    have hnat : (2633229511 : ℕ)^8397*50000000000000^6349 ≤ 21412080578251^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633229511 5000000000 21412080578251 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344558977/10000000000 : ℝ), (-1100650797/5000000000 : ℝ), (2633229511/5000000000 : ℝ)] ![(43666086971681/100000000000000 : ℝ), (13509751855129/100000000000000 : ℝ), (21412080578251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344558977/10000000000 : ℝ)|^8397 ≤ (43666086971681/100000000000000 : ℝ)^6349
        have hw : |(5344558977/10000000000 : ℝ)|=(5344558977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100650797/5000000000 : ℝ)|^8397 ≤ (13509751855129/100000000000000 : ℝ)^6349
        have hw : |(-1100650797/5000000000 : ℝ)|=(1100650797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633229511/5000000000 : ℝ)|^8397 ≤ (21412080578251/50000000000000 : ℝ)^6349
        have hw : |(2633229511/5000000000 : ℝ)|=(2633229511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s6_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672279473/5000000000 : ℝ)*x 0 + (5266459039/10000000000 : ℝ)*x 1 + (-550325403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672279473/5000000000 : ℝ)^8397 ≤ (8733217327341/20000000000000 : ℝ)^6349 := by
    have hnat : (2672279473 : ℕ)^8397*20000000000000^6349 ≤ 8733217327341^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672279473 5000000000 8733217327341 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266459039/10000000000 : ℝ)^8397 ≤ (669127520927/1562500000000 : ℝ)^6349 := by
    have hnat : (5266459039 : ℕ)^8397*1562500000000^6349 ≤ 669127520927^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266459039 10000000000 669127520927 1562500000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550325403/2500000000 : ℝ)^8397 ≤ (844359500077/6250000000000 : ℝ)^6349 := by
    have hnat : (550325403 : ℕ)^8397*6250000000000^6349 ≤ 844359500077^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550325403 2500000000 844359500077 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672279473/5000000000 : ℝ), (5266459039/10000000000 : ℝ), (-550325403/2500000000 : ℝ)] ![(8733217327341/20000000000000 : ℝ), (669127520927/1562500000000 : ℝ), (844359500077/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672279473/5000000000 : ℝ)|^8397 ≤ (8733217327341/20000000000000 : ℝ)^6349
        have hw : |(2672279473/5000000000 : ℝ)|=(2672279473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266459039/10000000000 : ℝ)|^8397 ≤ (669127520927/1562500000000 : ℝ)^6349
        have hw : |(5266459039/10000000000 : ℝ)|=(5266459039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550325403/2500000000 : ℝ)|^8397 ≤ (844359500077/6250000000000 : ℝ)^6349
        have hw : |(-550325403/2500000000 : ℝ)|=(550325403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s6_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4355999307/10000000000 : ℝ)*x 0 + (528907219/1250000000 : ℝ)*x 1 + (2242173411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355999307/10000000000 : ℝ)^8397 ≤ (33317175749983/100000000000000 : ℝ)^6349 := by
    have hnat : (4355999307 : ℕ)^8397*100000000000000^6349 ≤ 33317175749983^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355999307 10000000000 33317175749983 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528907219/1250000000 : ℝ)^8397 ≤ (6412236877353/20000000000000 : ℝ)^6349 := by
    have hnat : (528907219 : ℕ)^8397*20000000000000^6349 ≤ 6412236877353^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528907219 1250000000 6412236877353 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242173411/5000000000 : ℝ)^8397 ≤ (34621639850441/100000000000000 : ℝ)^6349 := by
    have hnat : (2242173411 : ℕ)^8397*100000000000000^6349 ≤ 34621639850441^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242173411 5000000000 34621639850441 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355999307/10000000000 : ℝ), (528907219/1250000000 : ℝ), (2242173411/5000000000 : ℝ)] ![(33317175749983/100000000000000 : ℝ), (6412236877353/20000000000000 : ℝ), (34621639850441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355999307/10000000000 : ℝ)|^8397 ≤ (33317175749983/100000000000000 : ℝ)^6349
        have hw : |(4355999307/10000000000 : ℝ)|=(4355999307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528907219/1250000000 : ℝ)|^8397 ≤ (6412236877353/20000000000000 : ℝ)^6349
        have hw : |(528907219/1250000000 : ℝ)|=(528907219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242173411/5000000000 : ℝ)|^8397 ≤ (34621639850441/100000000000000 : ℝ)^6349
        have hw : |(2242173411/5000000000 : ℝ)|=(2242173411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s6_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267196147/1250000000 : ℝ)*x 0 + (658347077/1250000000 : ℝ)*x 1 + (1078364829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267196147/1250000000 : ℝ)^8397 ≤ (12994877987769/100000000000000 : ℝ)^6349 := by
    have hnat : (267196147 : ℕ)^8397*100000000000000^6349 ≤ 12994877987769^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267196147 1250000000 12994877987769 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658347077/1250000000 : ℝ)^8397 ≤ (2676723546539/6250000000000 : ℝ)^6349 := by
    have hnat : (658347077 : ℕ)^8397*6250000000000^6349 ≤ 2676723546539^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658347077 1250000000 2676723546539 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078364829/2000000000 : ℝ)^8397 ≤ (44177545252389/100000000000000 : ℝ)^6349 := by
    have hnat : (1078364829 : ℕ)^8397*100000000000000^6349 ≤ 44177545252389^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078364829 2000000000 44177545252389 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267196147/1250000000 : ℝ), (658347077/1250000000 : ℝ), (1078364829/2000000000 : ℝ)] ![(12994877987769/100000000000000 : ℝ), (2676723546539/6250000000000 : ℝ), (44177545252389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267196147/1250000000 : ℝ)|^8397 ≤ (12994877987769/100000000000000 : ℝ)^6349
        have hw : |(-267196147/1250000000 : ℝ)|=(267196147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658347077/1250000000 : ℝ)|^8397 ≤ (2676723546539/6250000000000 : ℝ)^6349
        have hw : |(658347077/1250000000 : ℝ)|=(658347077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078364829/2000000000 : ℝ)|^8397 ≤ (44177545252389/100000000000000 : ℝ)^6349
        have hw : |(1078364829/2000000000 : ℝ)|=(1078364829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s6_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312573879/10000000000 : ℝ)*x 0 + (-2075936581/10000000000 : ℝ)*x 1 + (269591203/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312573879/10000000000 : ℝ)^8397 ≤ (10830200247089/25000000000000 : ℝ)^6349 := by
    have hnat : (5312573879 : ℕ)^8397*25000000000000^6349 ≤ 10830200247089^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312573879 10000000000 10830200247089 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075936581/10000000000 : ℝ)^8397 ≤ (12501654663307/100000000000000 : ℝ)^6349 := by
    have hnat : (2075936581 : ℕ)^8397*100000000000000^6349 ≤ 12501654663307^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075936581 10000000000 12501654663307 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269591203/500000000 : ℝ)^8397 ≤ (1380548260353/3125000000000 : ℝ)^6349 := by
    have hnat : (269591203 : ℕ)^8397*3125000000000^6349 ≤ 1380548260353^6349*500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269591203 500000000 1380548260353 3125000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312573879/10000000000 : ℝ), (-2075936581/10000000000 : ℝ), (269591203/500000000 : ℝ)] ![(10830200247089/25000000000000 : ℝ), (12501654663307/100000000000000 : ℝ), (1380548260353/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312573879/10000000000 : ℝ)|^8397 ≤ (10830200247089/25000000000000 : ℝ)^6349
        have hw : |(5312573879/10000000000 : ℝ)|=(5312573879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075936581/10000000000 : ℝ)|^8397 ≤ (12501654663307/100000000000000 : ℝ)^6349
        have hw : |(-2075936581/10000000000 : ℝ)|=(2075936581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269591203/500000000 : ℝ)|^8397 ≤ (1380548260353/3125000000000 : ℝ)^6349
        have hw : |(269591203/500000000 : ℝ)|=(269591203/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s6_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132814347/250000000 : ℝ)*x 0 + (1347956017/2500000000 : ℝ)*x 1 + (-2075936569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132814347/250000000 : ℝ)^8397 ≤ (43320800999141/100000000000000 : ℝ)^6349 := by
    have hnat : (132814347 : ℕ)^8397*100000000000000^6349 ≤ 43320800999141^6349*250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132814347 250000000 43320800999141 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347956017/2500000000 : ℝ)^8397 ≤ (44177544417987/100000000000000 : ℝ)^6349 := by
    have hnat : (1347956017 : ℕ)^8397*100000000000000^6349 ≤ 44177544417987^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347956017 2500000000 44177544417987 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2075936569/10000000000 : ℝ)^8397 ≤ (1250165456773/10000000000000 : ℝ)^6349 := by
    have hnat : (2075936569 : ℕ)^8397*10000000000000^6349 ≤ 1250165456773^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075936569 10000000000 1250165456773 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132814347/250000000 : ℝ), (1347956017/2500000000 : ℝ), (-2075936569/10000000000 : ℝ)] ![(43320800999141/100000000000000 : ℝ), (44177544417987/100000000000000 : ℝ), (1250165456773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132814347/250000000 : ℝ)|^8397 ≤ (43320800999141/100000000000000 : ℝ)^6349
        have hw : |(132814347/250000000 : ℝ)|=(132814347/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347956017/2500000000 : ℝ)|^8397 ≤ (44177544417987/100000000000000 : ℝ)^6349
        have hw : |(1347956017/2500000000 : ℝ)|=(1347956017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2075936569/10000000000 : ℝ)|^8397 ≤ (1250165456773/10000000000000 : ℝ)^6349
        have hw : |(-2075936569/10000000000 : ℝ)|=(2075936569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s6_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089002251/2500000000 : ℝ)*x 0 + (4483707229/10000000000 : ℝ)*x 1 + (33855197/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089002251/2500000000 : ℝ)^8397 ≤ (16658636921349/50000000000000 : ℝ)^6349 := by
    have hnat : (1089002251 : ℕ)^8397*50000000000000^6349 ≤ 16658636921349^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089002251 2500000000 16658636921349 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483707229/10000000000 : ℝ)^8397 ≤ (34615109131739/100000000000000 : ℝ)^6349 := by
    have hnat : (4483707229 : ℕ)^8397*100000000000000^6349 ≤ 34615109131739^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483707229 10000000000 34615109131739 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33855197/80000000 : ℝ)^8397 ≤ (32067617017763/100000000000000 : ℝ)^6349 := by
    have hnat : (33855197 : ℕ)^8397*100000000000000^6349 ≤ 32067617017763^6349*80000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33855197 80000000 32067617017763 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089002251/2500000000 : ℝ), (4483707229/10000000000 : ℝ), (33855197/80000000 : ℝ)] ![(16658636921349/50000000000000 : ℝ), (34615109131739/100000000000000 : ℝ), (32067617017763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089002251/2500000000 : ℝ)|^8397 ≤ (16658636921349/50000000000000 : ℝ)^6349
        have hw : |(1089002251/2500000000 : ℝ)|=(1089002251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483707229/10000000000 : ℝ)|^8397 ≤ (34615109131739/100000000000000 : ℝ)^6349
        have hw : |(4483707229/10000000000 : ℝ)|=(4483707229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33855197/80000000 : ℝ)|^8397 ≤ (32067617017763/100000000000000 : ℝ)^6349
        have hw : |(33855197/80000000 : ℝ)|=(33855197/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11427/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14089/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11403/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (13619048347604733/100000000000000000000 : ℝ) := by
    have hpowers : (11403/100000 : ℝ)^2099 ≤ (13619048347604733/100000000000000000000 : ℝ)^512 := by
      have hnat : (11403 : ℕ)^2099*100000000000000000000^512 ≤ 13619048347604733^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11403 100000 13619048347604733 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11403/100000 : ℝ)) (X := (13619048347604733/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (2099/512 : ℝ) ≤ (32651086060906787/100000000000000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^2099 ≤ (32651086060906787/100000000000000000000 : ℝ)^512 := by
      have hnat : (7057 : ℕ)^2099*100000000000000000000^512 ≤ 32651086060906787^512*50000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 32651086060906787 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (32651086060906787/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013619048347604733/50000000000000000000 : ℝ) ≤ (5000332169359819/5000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50013619048347604733/50000000000000000000 : ℝ)^512 ≤ (5000332169359819/5000000000000000 : ℝ)^2099 := by
      have hnat : (50013619048347604733 : ℕ)^512*5000000000000000^2099 ≤ 5000332169359819^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013619048347604733 50000000000000000000 5000332169359819 5000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000332169359819/5000000000000000 : ℝ)) (X := (50013619048347604733/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (625289188340053197/625000000000000000 : ℝ) ≤ (10001128450027183/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (625289188340053197/625000000000000000 : ℝ)^512 ≤ (10001128450027183/10000000000000000 : ℝ)^2099 := by
      have hnat : (625289188340053197 : ℕ)^512*10000000000000000^2099 ≤ 10001128450027183^2099*625000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625289188340053197 625000000000000000 10001128450027183 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001128450027183/10000000000000000 : ℝ)) (X := (625289188340053197/625000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032651086060906787/50000000000000000000 : ℝ) ≤ (1250199070166841/1250000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50032651086060906787/50000000000000000000 : ℝ)^512 ≤ (1250199070166841/1250000000000000 : ℝ)^2099 := by
      have hnat : (50032651086060906787 : ℕ)^512*1250000000000000^2099 ≤ 1250199070166841^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032651086060906787 50000000000000000000 1250199070166841 1250000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250199070166841/1250000000000000 : ℝ)) (X := (50032651086060906787/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13619048347604733/100000000000000000000 : ℝ) ≤ ((6775304124947266837/6777500000000000000 : ℝ)+2*(92822261509/54220000000000 : ℝ)*(11403/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (6775304124947266837/6777500000000000000 : ℝ)+2*(92822261509/54220000000000 : ℝ)*(11403/100000 : ℝ)=(5000332169359819/5000000000000000 : ℝ) by norm_num, show 1+2*(13619048347604733/100000000000000000000 : ℝ)=(50013619048347604733/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32651086060906787/100000000000000000000 : ℝ)+(13619048347604733/100000000000000000000 : ℝ) ≤ ((6775304124947266837/6777500000000000000 : ℝ)+(92822261509/54220000000000 : ℝ)*((7057/50000 : ℝ)+(11403/100000 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (6775304124947266837/6777500000000000000 : ℝ)+(92822261509/54220000000000 : ℝ)*((7057/50000 : ℝ)+(11403/100000 : ℝ))=(10001128450027183/10000000000000000 : ℝ) by norm_num, show 1+(32651086060906787/100000000000000000000 : ℝ)+(13619048347604733/100000000000000000000 : ℝ)=(625289188340053197/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32651086060906787/100000000000000000000 : ℝ) ≤ ((6775304124947266837/6777500000000000000 : ℝ)+2*(92822261509/54220000000000 : ℝ)*(7057/50000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (6775304124947266837/6777500000000000000 : ℝ)+2*(92822261509/54220000000000 : ℝ)*(7057/50000 : ℝ)=(1250199070166841/1250000000000000 : ℝ) by norm_num, show 1+2*(32651086060906787/100000000000000000000 : ℝ)=(50032651086060906787/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6775304124947266837/6777500000000000000 : ℝ)*(X 1 0+X 2 0)+(92822261509/54220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6775304124947266837/6777500000000000000 : ℝ)) (alpha := (92822261509/54220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6775304124947266837/6777500000000000000 : ℝ)*(X 0 1+X 2 1)+(92822261509/54220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6775304124947266837/6777500000000000000 : ℝ)) (alpha := (92822261509/54220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6775304124947266837/6777500000000000000 : ℝ)*(X 0 2+X 1 2)+(92822261509/54220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6775304124947266837/6777500000000000000 : ℝ)) (alpha := (92822261509/54220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2137564409/10000000000 : ℝ)*X 0 0+(2696071441/5000000000 : ℝ)*X 0 1+(1053291803/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344558977/10000000000 : ℝ)*X 1 0+(-1100650797/5000000000 : ℝ)*X 1 1+(2633229511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672279473/5000000000 : ℝ)*X 2 0+(5266459039/10000000000 : ℝ)*X 2 1+(-550325403/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355999307/10000000000 : ℝ)*X 0 0+(528907219/1250000000 : ℝ)*X 0 1+(2242173411/5000000000 : ℝ)*X 0 2+(4355999307/10000000000 : ℝ)*X 1 0+(528907219/1250000000 : ℝ)*X 1 1+(2242173411/5000000000 : ℝ)*X 1 2+(4355999307/10000000000 : ℝ)*X 2 0+(528907219/1250000000 : ℝ)*X 2 1+(2242173411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267196147/1250000000 : ℝ)*X 0 0+(658347077/1250000000 : ℝ)*X 0 1+(1078364829/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312573879/10000000000 : ℝ)*X 1 0+(-2075936581/10000000000 : ℝ)*X 1 1+(269591203/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132814347/250000000 : ℝ)*X 2 0+(1347956017/2500000000 : ℝ)*X 2 1+(-2075936569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089002251/2500000000 : ℝ)*X 0 0+(4483707229/10000000000 : ℝ)*X 0 1+(33855197/80000000 : ℝ)*X 0 2+(1089002251/2500000000 : ℝ)*X 1 0+(4483707229/10000000000 : ℝ)*X 1 1+(33855197/80000000 : ℝ)*X 1 2+(1089002251/2500000000 : ℝ)*X 2 0+(4483707229/10000000000 : ℝ)*X 2 1+(33855197/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260837728201465907341733487/42359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (584014503/50000000000000 : ℝ)*(base19) + (555546309/50000000000000 : ℝ)*(base23) + (6869519/5000000000000 : ℝ)*(upper3) + (5764717/100000000000000 : ℝ)*(upper4) + (45719087/50000000000000 : ℝ)*(upper5) + (1488468940874433/25000000000000 : ℝ)*(major0) + (1488468940874433/25000000000000 : ℝ)*(major1) + (1488468940874433/25000000000000 : ℝ)*(major2) + (3978253331870323/50000000000000 : ℝ)*(sp0) + (1591307816648451/20000000000000 : ℝ)*(sp1) + (7956539140178643/100000000000000 : ℝ)*(sp2) + (3951194183509787/100000000000000 : ℝ)*(sp3) + (6717506123/20000000000000 : ℝ)*(sp4) + (4221739159/25000000000000 : ℝ)*(sp7) + (3951211070466423/100000000000000 : ℝ)*(f.failure) + (7956540251271261/100000000000000 : ℝ)*(f.sum) + (1431058133401/2711000000000000000000000000 : ℝ)*base66 + (2257403659344203421/169437500000000000000000000000000 : ℝ)*base67 + (650710837501140921/169437500000000000000000000000000 : ℝ)*base69 + (463429872851203421/169437500000000000000000000000000 : ℝ)*base71 + (1608739865701/271100000000000000000000000 : ℝ)*base73 + (104435569957703421/169437500000000000000000000000000 : ℝ)*base75 + (419745980684140921/169437500000000000000000000000000 : ℝ)*base77 + (862453004006734079/169437500000000000000000000000000 : ℝ)*base80 + (41659897811/271100000000000000000000000 : ℝ)*base81 + (2768877/312500000000000000000 : ℝ)*base90 + (2768877/312500000000000000000 : ℝ)*base92 + (2768877/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (471851649053585308919369607/169437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235298789/50000000000000 : ℝ)*(base19) + (480525031/100000000000000 : ℝ)*(base23) + (3289339/25000000000000 : ℝ)*(upper3) + (1094083/12500000000000 : ℝ)*(lower4) + (19348089/25000000000000 : ℝ)*(upper5) + (5984123419923763/100000000000000 : ℝ)*(major0) + (5984123419923763/100000000000000 : ℝ)*(major1) + (5984123419923763/100000000000000 : ℝ)*(major2) + (10826631717/100000000000000 : ℝ)*(sp1) + (9489041187/100000000000000 : ℝ)*(sp2) + (7996962218579139/100000000000000 : ℝ)*(sp4) + (1999237730337461/25000000000000 : ℝ)*(sp5) + (7996952249012921/100000000000000 : ℝ)*(sp6) + (1985642264220649/50000000000000 : ℝ)*(sp7) + (1985642264220649/50000000000000 : ℝ)*(f.failure) + (7996962218579139/100000000000000 : ℝ)*(f.sum) + (18130439767759/2711000000000000000000000000 : ℝ)*base65 + (3926206430877477369/677750000000000000000000000000000 : ℝ)*base68 + (2933933294565272631/677750000000000000000000000000000 : ℝ)*base69 + (6323482245242272631/677750000000000000000000000000000 : ℝ)*base71 + (582095419587/2711000000000000000000000000 : ℝ)*base73 + (8919186745028022631/677750000000000000000000000000000 : ℝ)*base75 + (1979095258775522631/677750000000000000000000000000000 : ℝ)*base77 + (4627264045830772631/677750000000000000000000000000000 : ℝ)*base79 + (15228683257/135550000000000000000000000 : ℝ)*base81 + (1390751/156250000000000000000 : ℝ)*base90 + (1390751/156250000000000000000 : ℝ)*base92 + (1390751/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1204_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1204_s7_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-427516889/2000000000 : ℝ)*x 0 + (5391905387/10000000000 : ℝ)*x 1 + (5266683341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427516889/2000000000 : ℝ)^8397 ≤ (1624375094357/12500000000000 : ℝ)^6349 := by
    have hnat : (427516889 : ℕ)^8397*12500000000000^6349 ≤ 1624375094357^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427516889 2000000000 1624375094357 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391905387/10000000000 : ℝ)^8397 ≤ (5522303203081/12500000000000 : ℝ)^6349 := by
    have hnat : (5391905387 : ℕ)^8397*12500000000000^6349 ≤ 5522303203081^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391905387 10000000000 5522303203081 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266683341/10000000000 : ℝ)^8397 ≤ (42826573604859/100000000000000 : ℝ)^6349 := by
    have hnat : (5266683341 : ℕ)^8397*100000000000000^6349 ≤ 42826573604859^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266683341 10000000000 42826573604859 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427516889/2000000000 : ℝ), (5391905387/10000000000 : ℝ), (5266683341/10000000000 : ℝ)] ![(1624375094357/12500000000000 : ℝ), (5522303203081/12500000000000 : ℝ), (42826573604859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427516889/2000000000 : ℝ)|^8397 ≤ (1624375094357/12500000000000 : ℝ)^6349
        have hw : |(-427516889/2000000000 : ℝ)|=(427516889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391905387/10000000000 : ℝ)|^8397 ≤ (5522303203081/12500000000000 : ℝ)^6349
        have hw : |(5391905387/10000000000 : ℝ)|=(5391905387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266683341/10000000000 : ℝ)|^8397 ≤ (42826573604859/100000000000000 : ℝ)^6349
        have hw : |(5266683341/10000000000 : ℝ)|=(5266683341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s7_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534449901/1000000000 : ℝ)*x 0 + (-440216839/2000000000 : ℝ)*x 1 + (105333667/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534449901/1000000000 : ℝ)^8397 ≤ (8733087797989/20000000000000 : ℝ)^6349 := by
    have hnat : (534449901 : ℕ)^8397*20000000000000^6349 ≤ 8733087797989^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534449901 1000000000 8733087797989 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440216839/2000000000 : ℝ)^8397 ≤ (13507987291699/100000000000000 : ℝ)^6349 := by
    have hnat : (440216839 : ℕ)^8397*100000000000000^6349 ≤ 13507987291699^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440216839 2000000000 13507987291699 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105333667/200000000 : ℝ)^8397 ≤ (856531474033/2000000000000 : ℝ)^6349 := by
    have hnat : (105333667 : ℕ)^8397*2000000000000^6349 ≤ 856531474033^6349*200000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105333667 200000000 856531474033 2000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534449901/1000000000 : ℝ), (-440216839/2000000000 : ℝ), (105333667/200000000 : ℝ)] ![(8733087797989/20000000000000 : ℝ), (13507987291699/100000000000000 : ℝ), (856531474033/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534449901/1000000000 : ℝ)|^8397 ≤ (8733087797989/20000000000000 : ℝ)^6349
        have hw : |(534449901/1000000000 : ℝ)|=(534449901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440216839/2000000000 : ℝ)|^8397 ≤ (13507987291699/100000000000000 : ℝ)^6349
        have hw : |(-440216839/2000000000 : ℝ)|=(440216839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105333667/200000000 : ℝ)|^8397 ≤ (856531474033/2000000000000 : ℝ)^6349
        have hw : |(105333667/200000000 : ℝ)|=(105333667/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s7_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344499003/10000000000 : ℝ)*x 0 + (2633341687/5000000000 : ℝ)*x 1 + (-550271043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344499003/10000000000 : ℝ)^8397 ≤ (21832719457153/50000000000000 : ℝ)^6349 := by
    have hnat : (5344499003 : ℕ)^8397*50000000000000^6349 ≤ 21832719457153^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344499003 10000000000 21832719457153 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633341687/5000000000 : ℝ)^8397 ≤ (42826573959761/100000000000000 : ℝ)^6349 := by
    have hnat : (2633341687 : ℕ)^8397*100000000000000^6349 ≤ 42826573959761^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633341687 5000000000 42826573959761 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550271043/2500000000 : ℝ)^8397 ≤ (6753993552509/50000000000000 : ℝ)^6349 := by
    have hnat : (550271043 : ℕ)^8397*50000000000000^6349 ≤ 6753993552509^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550271043 2500000000 6753993552509 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344499003/10000000000 : ℝ), (2633341687/5000000000 : ℝ), (-550271043/2500000000 : ℝ)] ![(21832719457153/50000000000000 : ℝ), (42826573959761/100000000000000 : ℝ), (6753993552509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344499003/10000000000 : ℝ)|^8397 ≤ (21832719457153/50000000000000 : ℝ)^6349
        have hw : |(5344499003/10000000000 : ℝ)|=(5344499003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633341687/5000000000 : ℝ)|^8397 ≤ (42826573959761/100000000000000 : ℝ)^6349
        have hw : |(2633341687/5000000000 : ℝ)|=(2633341687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550271043/2500000000 : ℝ)|^8397 ≤ (6753993552509/50000000000000 : ℝ)^6349
        have hw : |(-550271043/2500000000 : ℝ)|=(550271043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s7_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178005563/5000000000 : ℝ)*x 0 + (264482563/625000000 : ℝ)*x 1 + (2241940221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178005563/5000000000 : ℝ)^8397 ≤ (4164661913549/12500000000000 : ℝ)^6349 := by
    have hnat : (2178005563 : ℕ)^8397*12500000000000^6349 ≤ 4164661913549^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178005563 5000000000 4164661913549 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264482563/625000000 : ℝ)^8397 ≤ (32065826947861/100000000000000 : ℝ)^6349 := by
    have hnat : (264482563 : ℕ)^8397*100000000000000^6349 ≤ 32065826947861^6349*625000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264482563 625000000 32065826947861 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241940221/5000000000 : ℝ)^8397 ≤ (17308438867607/50000000000000 : ℝ)^6349 := by
    have hnat : (2241940221 : ℕ)^8397*50000000000000^6349 ≤ 17308438867607^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241940221 5000000000 17308438867607 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178005563/5000000000 : ℝ), (264482563/625000000 : ℝ), (2241940221/5000000000 : ℝ)] ![(4164661913549/12500000000000 : ℝ), (32065826947861/100000000000000 : ℝ), (17308438867607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178005563/5000000000 : ℝ)|^8397 ≤ (4164661913549/12500000000000 : ℝ)^6349
        have hw : |(2178005563/5000000000 : ℝ)|=(2178005563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(264482563/625000000 : ℝ)|^8397 ≤ (32065826947861/100000000000000 : ℝ)^6349
        have hw : |(264482563/625000000 : ℝ)|=(264482563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241940221/5000000000 : ℝ)|^8397 ≤ (17308438867607/50000000000000 : ℝ)^6349
        have hw : |(2241940221/5000000000 : ℝ)|=(2241940221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s7_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534397259/2500000000 : ℝ)*x 0 + (2633499467/5000000000 : ℝ)*x 1 + (1347897191/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534397259/2500000000 : ℝ)^8397 ≤ (3248759416963/25000000000000 : ℝ)^6349 := by
    have hnat : (534397259 : ℕ)^8397*25000000000000^6349 ≤ 3248759416963^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534397259 2500000000 3248759416963 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633499467/5000000000 : ℝ)^8397 ≤ (21414983859751/50000000000000 : ℝ)^6349 := by
    have hnat : (2633499467 : ℕ)^8397*50000000000000^6349 ≤ 21414983859751^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633499467 5000000000 21414983859751 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347897191/2500000000 : ℝ)^8397 ≤ (22087497294839/50000000000000 : ℝ)^6349 := by
    have hnat : (1347897191 : ℕ)^8397*50000000000000^6349 ≤ 22087497294839^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347897191 2500000000 22087497294839 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534397259/2500000000 : ℝ), (2633499467/5000000000 : ℝ), (1347897191/2500000000 : ℝ)] ![(3248759416963/25000000000000 : ℝ), (21414983859751/50000000000000 : ℝ), (22087497294839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534397259/2500000000 : ℝ)|^8397 ≤ (3248759416963/25000000000000 : ℝ)^6349
        have hw : |(-534397259/2500000000 : ℝ)|=(534397259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633499467/5000000000 : ℝ)|^8397 ≤ (21414983859751/50000000000000 : ℝ)^6349
        have hw : |(2633499467/5000000000 : ℝ)|=(2633499467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347897191/2500000000 : ℝ)|^8397 ≤ (22087497294839/50000000000000 : ℝ)^6349
        have hw : |(1347897191/2500000000 : ℝ)|=(1347897191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s7_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531263157/1000000000 : ℝ)*x 0 + (-1038089221/5000000000 : ℝ)*x 1 + (5391588871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531263157/1000000000 : ℝ)^8397 ≤ (43321423172801/100000000000000 : ℝ)^6349 := by
    have hnat : (531263157 : ℕ)^8397*100000000000000^6349 ≤ 43321423172801^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531263157 1000000000 43321423172801 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038089221/5000000000 : ℝ)^8397 ≤ (156294763279/1250000000000 : ℝ)^6349 := by
    have hnat : (1038089221 : ℕ)^8397*1250000000000^6349 ≤ 156294763279^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038089221 5000000000 156294763279 1250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391588871/10000000000 : ℝ)^8397 ≤ (11043748937289/25000000000000 : ℝ)^6349 := by
    have hnat : (5391588871 : ℕ)^8397*25000000000000^6349 ≤ 11043748937289^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391588871 10000000000 11043748937289 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531263157/1000000000 : ℝ), (-1038089221/5000000000 : ℝ), (5391588871/10000000000 : ℝ)] ![(43321423172801/100000000000000 : ℝ), (156294763279/1250000000000 : ℝ), (11043748937289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531263157/1000000000 : ℝ)|^8397 ≤ (43321423172801/100000000000000 : ℝ)^6349
        have hw : |(531263157/1000000000 : ℝ)|=(531263157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1038089221/5000000000 : ℝ)|^8397 ≤ (156294763279/1250000000000 : ℝ)^6349
        have hw : |(-1038089221/5000000000 : ℝ)|=(1038089221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391588871/10000000000 : ℝ)|^8397 ≤ (11043748937289/25000000000000 : ℝ)^6349
        have hw : |(5391588871/10000000000 : ℝ)|=(5391588871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s7_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531263157/1000000000 : ℝ)*x 0 + (673948593/1250000000 : ℝ)*x 1 + (-1038089307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531263157/1000000000 : ℝ)^8397 ≤ (43321423172801/100000000000000 : ℝ)^6349 := by
    have hnat : (531263157 : ℕ)^8397*100000000000000^6349 ≤ 43321423172801^6349*1000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531263157 1000000000 43321423172801 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673948593/1250000000 : ℝ)^8397 ≤ (22087497186477/50000000000000 : ℝ)^6349 := by
    have hnat : (673948593 : ℕ)^8397*50000000000000^6349 ≤ 22087497186477^6349*1250000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673948593 1250000000 22087497186477 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038089307/5000000000 : ℝ)^8397 ≤ (12503582432309/100000000000000 : ℝ)^6349 := by
    have hnat : (1038089307 : ℕ)^8397*100000000000000^6349 ≤ 12503582432309^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038089307 5000000000 12503582432309 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531263157/1000000000 : ℝ), (673948593/1250000000 : ℝ), (-1038089307/5000000000 : ℝ)] ![(43321423172801/100000000000000 : ℝ), (22087497186477/50000000000000 : ℝ), (12503582432309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531263157/1000000000 : ℝ)|^8397 ≤ (43321423172801/100000000000000 : ℝ)^6349
        have hw : |(531263157/1000000000 : ℝ)|=(531263157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673948593/1250000000 : ℝ)|^8397 ≤ (22087497186477/50000000000000 : ℝ)^6349
        have hw : |(673948593/1250000000 : ℝ)|=(673948593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038089307/5000000000 : ℝ)|^8397 ≤ (12503582432309/100000000000000 : ℝ)^6349
        have hw : |(-1038089307/5000000000 : ℝ)|=(1038089307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s7_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178009901/5000000000 : ℝ)*x 0 + (4483245961/10000000000 : ℝ)*x 1 + (2116179329/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178009901/5000000000 : ℝ)^8397 ≤ (33317383072969/100000000000000 : ℝ)^6349 := by
    have hnat : (2178009901 : ℕ)^8397*100000000000000^6349 ≤ 33317383072969^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178009901 5000000000 33317383072969 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483245961/10000000000 : ℝ)^8397 ≤ (17305199714997/50000000000000 : ℝ)^6349 := by
    have hnat : (4483245961 : ℕ)^8397*50000000000000^6349 ≤ 17305199714997^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483245961 10000000000 17305199714997 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116179329/5000000000 : ℝ)^8397 ≤ (3207221748203/10000000000000 : ℝ)^6349 := by
    have hnat : (2116179329 : ℕ)^8397*10000000000000^6349 ≤ 3207221748203^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116179329 5000000000 3207221748203 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178009901/5000000000 : ℝ), (4483245961/10000000000 : ℝ), (2116179329/5000000000 : ℝ)] ![(33317383072969/100000000000000 : ℝ), (17305199714997/50000000000000 : ℝ), (3207221748203/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178009901/5000000000 : ℝ)|^8397 ≤ (33317383072969/100000000000000 : ℝ)^6349
        have hw : |(2178009901/5000000000 : ℝ)|=(2178009901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483245961/10000000000 : ℝ)|^8397 ≤ (17305199714997/50000000000000 : ℝ)^6349
        have hw : |(4483245961/10000000000 : ℝ)|=(4483245961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116179329/5000000000 : ℝ)|^8397 ≤ (3207221748203/10000000000000 : ℝ)^6349
        have hw : |(2116179329/5000000000 : ℝ)|=(2116179329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1429/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11427/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11427/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11427/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11427/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (13736943989791967/100000000000000000000 : ℝ) := by
    have hpowers : (11427/100000 : ℝ)^2099 ≤ (13736943989791967/100000000000000000000 : ℝ)^512 := by
      have hnat : (11427 : ℕ)^2099*100000000000000000000^512 ≤ 13736943989791967^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11427 100000 13736943989791967 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11427/100000 : ℝ)) (X := (13736943989791967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14089/100000 : ℝ) ^ (2099/512 : ℝ) ≤ (16207318487053427/50000000000000000000 : ℝ) := by
    have hpowers : (14089/100000 : ℝ)^2099 ≤ (16207318487053427/50000000000000000000 : ℝ)^512 := by
      have hnat : (14089 : ℕ)^2099*50000000000000000000^512 ≤ 16207318487053427^512*100000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14089 100000 16207318487053427 50000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14089/100000 : ℝ)) (X := (16207318487053427/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013736943989791967/50000000000000000000 : ℝ) ≤ (625041880567827/625000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50013736943989791967/50000000000000000000 : ℝ)^512 ≤ (625041880567827/625000000000000 : ℝ)^2099 := by
      have hnat : (50013736943989791967 : ℕ)^512*625000000000000^2099 ≤ 625041880567827^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013736943989791967 50000000000000000000 625041880567827 625000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625041880567827/625000000000000 : ℝ)) (X := (50013736943989791967/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046151580963898821/100000000000000000000 : ℝ) ≤ (2500281389803549/2500000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (100046151580963898821/100000000000000000000 : ℝ)^512 ≤ (2500281389803549/2500000000000000 : ℝ)^2099 := by
      have hnat : (100046151580963898821 : ℕ)^512*2500000000000000^2099 ≤ 2500281389803549^2099*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046151580963898821 100000000000000000000 2500281389803549 2500000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500281389803549/2500000000000000 : ℝ)) (X := (100046151580963898821/100000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016207318487053427/25000000000000000000 : ℝ) ≤ (250039525733579/250000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (25016207318487053427/25000000000000000000 : ℝ)^512 ≤ (250039525733579/250000000000000 : ℝ)^2099 := by
      have hnat : (25016207318487053427 : ℕ)^512*250000000000000^2099 ≤ 250039525733579^2099*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016207318487053427 25000000000000000000 250039525733579 250000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250039525733579/250000000000000 : ℝ)) (X := (25016207318487053427/25000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13736943989791967/100000000000000000000 : ℝ) ≤ ((3326421807852193041/3327500000000000000 : ℝ)+2*(113867532241/66550000000000 : ℝ)*(11427/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (3326421807852193041/3327500000000000000 : ℝ)+2*(113867532241/66550000000000 : ℝ)*(11427/100000 : ℝ)=(625041880567827/625000000000000 : ℝ) by norm_num, show 1+2*(13736943989791967/100000000000000000000 : ℝ)=(50013736943989791967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16207318487053427/50000000000000000000 : ℝ)+(13736943989791967/100000000000000000000 : ℝ) ≤ ((3326421807852193041/3327500000000000000 : ℝ)+(113867532241/66550000000000 : ℝ)*((14089/100000 : ℝ)+(11427/100000 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (3326421807852193041/3327500000000000000 : ℝ)+(113867532241/66550000000000 : ℝ)*((14089/100000 : ℝ)+(11427/100000 : ℝ))=(2500281389803549/2500000000000000 : ℝ) by norm_num, show 1+(16207318487053427/50000000000000000000 : ℝ)+(13736943989791967/100000000000000000000 : ℝ)=(100046151580963898821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16207318487053427/50000000000000000000 : ℝ) ≤ ((3326421807852193041/3327500000000000000 : ℝ)+2*(113867532241/66550000000000 : ℝ)*(14089/100000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (3326421807852193041/3327500000000000000 : ℝ)+2*(113867532241/66550000000000 : ℝ)*(14089/100000 : ℝ)=(250039525733579/250000000000000 : ℝ) by norm_num, show 1+2*(16207318487053427/50000000000000000000 : ℝ)=(25016207318487053427/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3326421807852193041/3327500000000000000 : ℝ)*(X 1 0+X 2 0)+(113867532241/66550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (3326421807852193041/3327500000000000000 : ℝ)) (alpha := (113867532241/66550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3326421807852193041/3327500000000000000 : ℝ)*(X 0 1+X 2 1)+(113867532241/66550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (3326421807852193041/3327500000000000000 : ℝ)) (alpha := (113867532241/66550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3326421807852193041/3327500000000000000 : ℝ)*(X 0 2+X 1 2)+(113867532241/66550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (11427/100000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (3326421807852193041/3327500000000000000 : ℝ)) (alpha := (113867532241/66550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-427516889/2000000000 : ℝ)*X 0 0+(5391905387/10000000000 : ℝ)*X 0 1+(5266683341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534449901/1000000000 : ℝ)*X 1 0+(-440216839/2000000000 : ℝ)*X 1 1+(105333667/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344499003/10000000000 : ℝ)*X 2 0+(2633341687/5000000000 : ℝ)*X 2 1+(-550271043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178005563/5000000000 : ℝ)*X 0 0+(264482563/625000000 : ℝ)*X 0 1+(2241940221/5000000000 : ℝ)*X 0 2+(2178005563/5000000000 : ℝ)*X 1 0+(264482563/625000000 : ℝ)*X 1 1+(2241940221/5000000000 : ℝ)*X 1 2+(2178005563/5000000000 : ℝ)*X 2 0+(264482563/625000000 : ℝ)*X 2 1+(2241940221/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534397259/2500000000 : ℝ)*X 0 0+(2633499467/5000000000 : ℝ)*X 0 1+(1347897191/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531263157/1000000000 : ℝ)*X 1 0+(-1038089221/5000000000 : ℝ)*X 1 1+(5391588871/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531263157/1000000000 : ℝ)*X 2 0+(673948593/1250000000 : ℝ)*X 2 1+(-1038089307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178009901/5000000000 : ℝ)*X 0 0+(4483245961/10000000000 : ℝ)*X 0 1+(2116179329/5000000000 : ℝ)*X 0 2+(2178009901/5000000000 : ℝ)*X 1 0+(4483245961/10000000000 : ℝ)*X 1 1+(2116179329/5000000000 : ℝ)*X 1 2+(2178009901/5000000000 : ℝ)*X 2 0+(4483245961/10000000000 : ℝ)*X 2 1+(2116179329/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332248123227226780378746867/83187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48206031/6250000000000 : ℝ)*(base19) + (187379183/25000000000000 : ℝ)*(base23) + (6050093/100000000000000 : ℝ)*(lower2) + (89049079/100000000000000 : ℝ)*(upper3) + (28990719/25000000000000 : ℝ)*(upper5) + (5975814203855129/100000000000000 : ℝ)*(major0) + (5975814203855129/100000000000000 : ℝ)*(major1) + (5975814203855129/100000000000000 : ℝ)*(major2) + (3992917686589457/50000000000000 : ℝ)*(sp0) + (12777371642269/160000000000 : ℝ)*(sp1) + (62389510142171/781250000000 : ℝ)*(sp2) + (3965757817723001/100000000000000 : ℝ)*(sp3) + (22674535707/100000000000000 : ℝ)*(sp4) + (12409140397/100000000000000 : ℝ)*(sp7) + (1982885113431699/50000000000000 : ℝ)*(f.failure) + (7985858047714621/100000000000000 : ℝ)*(f.sum) + (1859960604053/1663750000000000000000000000 : ℝ)*base66 + (2157570570067342711/332750000000000000000000000000000 : ℝ)*base68 + (366742834212907289/332750000000000000000000000000000 : ℝ)*base69 + (7880461017707092711/332750000000000000000000000000000 : ℝ)*base72 + (2215882306567/415937500000000000000000000 : ℝ)*base74 + (1370694962079092711/332750000000000000000000000000000 : ℝ)*base76 + (4787266735215592711/332750000000000000000000000000000 : ℝ)*base78 + (1314437990701342711/332750000000000000000000000000000 : ℝ)*base80 + (4742047997141/3327500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1790299/156250000000000000000 : ℝ)*base89 + (1790299/156250000000000000000 : ℝ)*base91 + (1790299/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20258882425586118131067/6655000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16450931/50000000000000 : ℝ)*(base19) + (27002543/5000000000000 : ℝ)*(base23) + (113790759/50000000000000 : ℝ)*(upper2) + (147388039/50000000000000 : ℝ)*(lower5) + (750761127587821/12500000000000 : ℝ)*(major0) + (750761127587821/12500000000000 : ℝ)*(major1) + (750761127587821/12500000000000 : ℝ)*(major2) + (202241087/2500000000000 : ℝ)*(sp1) + (21221566487/100000000000000 : ℝ)*(sp2) + (2215515957/100000000000000 : ℝ)*(sp3) + (4013158115219833/50000000000000 : ℝ)*(sp4) + (2006577026973581/25000000000000 : ℝ)*(sp5) + (8026294468822319/100000000000000 : ℝ)*(sp6) + (996464873494379/25000000000000 : ℝ)*(sp7) + (3985861709493473/100000000000000 : ℝ)*(f.failure) + (4013158115219833/50000000000000 : ℝ)*(f.sum) + (8351871244943/3327500000000000000000000000 : ℝ)*base65 + (299985263338853661/41593750000000000000000000000000 : ℝ)*base67 + (109971295407083839/41593750000000000000000000000000 : ℝ)*base70 + (1119822228580791161/41593750000000000000000000000000 : ℝ)*base71 + (12880776613361/1663750000000000000000000000 : ℝ)*base74 + (529611195681458839/41593750000000000000000000000000 : ℝ)*base76 + (184355506442009911/41593750000000000000000000000000 : ℝ)*base77 + (623460391671458839/41593750000000000000000000000000 : ℝ)*base80 + (2984841268379/1663750000000000000000000000 : ℝ)*base81 + (496827/312500000000000000000 : ℝ)*base90 + (496827/312500000000000000000 : ℝ)*base92 + (496827/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1204_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11427/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1204_s8_0 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068793903/5000000000 : ℝ)*x 0 + (53918577/100000000 : ℝ)*x 1 + (2633364439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068793903/5000000000 : ℝ)^8397 ≤ (6497513889143/50000000000000 : ℝ)^6349 := by
    have hnat : (1068793903 : ℕ)^8397*50000000000000^6349 ≤ 6497513889143^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068793903 5000000000 6497513889143 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53918577/100000000 : ℝ)^8397 ≤ (44177908867871/100000000000000 : ℝ)^6349 := by
    have hnat : (53918577 : ℕ)^8397*100000000000000^6349 ≤ 44177908867871^6349*100000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53918577 100000000 44177908867871 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633364439/5000000000 : ℝ)^8397 ≤ (5353382917317/12500000000000 : ℝ)^6349 := by
    have hnat : (2633364439 : ℕ)^8397*12500000000000^6349 ≤ 5353382917317^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633364439 5000000000 5353382917317 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068793903/5000000000 : ℝ), (53918577/100000000 : ℝ), (2633364439/5000000000 : ℝ)] ![(6497513889143/50000000000000 : ℝ), (44177908867871/100000000000000 : ℝ), (5353382917317/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068793903/5000000000 : ℝ)|^8397 ≤ (6497513889143/50000000000000 : ℝ)^6349
        have hw : |(-1068793903/5000000000 : ℝ)|=(1068793903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53918577/100000000 : ℝ)|^8397 ≤ (44177908867871/100000000000000 : ℝ)^6349
        have hw : |(53918577/100000000 : ℝ)|=(53918577/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633364439/5000000000 : ℝ)|^8397 ≤ (5353382917317/12500000000000 : ℝ)^6349
        have hw : |(2633364439/5000000000 : ℝ)|=(2633364439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s8_1 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344487167/10000000000 : ℝ)*x 0 + (-550259921/2500000000 : ℝ)*x 1 + (2633364421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344487167/10000000000 : ℝ)^8397 ≤ (10916327754761/25000000000000 : ℝ)^6349 := by
    have hnat : (5344487167 : ℕ)^8397*25000000000000^6349 ≤ 10916327754761^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344487167 10000000000 10916327754761 25000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550259921/2500000000 : ℝ)^8397 ≤ (13507626016001/100000000000000 : ℝ)^6349 := by
    have hnat : (550259921 : ℕ)^8397*100000000000000^6349 ≤ 13507626016001^6349*2500000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550259921 2500000000 13507626016001 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633364421/5000000000 : ℝ)^8397 ≤ (5353382868921/12500000000000 : ℝ)^6349 := by
    have hnat : (2633364421 : ℕ)^8397*12500000000000^6349 ≤ 5353382868921^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633364421 5000000000 5353382868921 12500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344487167/10000000000 : ℝ), (-550259921/2500000000 : ℝ), (2633364421/5000000000 : ℝ)] ![(10916327754761/25000000000000 : ℝ), (13507626016001/100000000000000 : ℝ), (5353382868921/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344487167/10000000000 : ℝ)|^8397 ≤ (10916327754761/25000000000000 : ℝ)^6349
        have hw : |(5344487167/10000000000 : ℝ)|=(5344487167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550259921/2500000000 : ℝ)|^8397 ≤ (13507626016001/100000000000000 : ℝ)^6349
        have hw : |(-550259921/2500000000 : ℝ)|=(550259921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633364421/5000000000 : ℝ)|^8397 ≤ (5353382868921/12500000000000 : ℝ)^6349
        have hw : |(2633364421/5000000000 : ℝ)|=(2633364421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s8_2 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672243603/5000000000 : ℝ)*x 0 + (5266728831/10000000000 : ℝ)*x 1 + (-2201039647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672243603/5000000000 : ℝ)^8397 ≤ (43665311440463/100000000000000 : ℝ)^6349 := by
    have hnat : (2672243603 : ℕ)^8397*100000000000000^6349 ≤ 43665311440463^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672243603 5000000000 43665311440463 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266728831/10000000000 : ℝ)^8397 ≤ (42827062833067/100000000000000 : ℝ)^6349 := by
    have hnat : (5266728831 : ℕ)^8397*100000000000000^6349 ≤ 42827062833067^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266728831 10000000000 42827062833067 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201039647/10000000000 : ℝ)^8397 ≤ (1350762571569/10000000000000 : ℝ)^6349 := by
    have hnat : (2201039647 : ℕ)^8397*10000000000000^6349 ≤ 1350762571569^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201039647 10000000000 1350762571569 10000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672243603/5000000000 : ℝ), (5266728831/10000000000 : ℝ), (-2201039647/10000000000 : ℝ)] ![(43665311440463/100000000000000 : ℝ), (42827062833067/100000000000000 : ℝ), (1350762571569/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672243603/5000000000 : ℝ)|^8397 ≤ (43665311440463/100000000000000 : ℝ)^6349
        have hw : |(2672243603/5000000000 : ℝ)|=(2672243603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266728831/10000000000 : ℝ)|^8397 ≤ (42827062833067/100000000000000 : ℝ)^6349
        have hw : |(5266728831/10000000000 : ℝ)|=(5266728831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2201039647/10000000000 : ℝ)|^8397 ≤ (1350762571569/10000000000000 : ℝ)^6349
        have hw : |(-2201039647/10000000000 : ℝ)|=(2201039647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s8_3 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4356013427/10000000000 : ℝ)*x 0 + (4231814713/10000000000 : ℝ)*x 1 + (4483786189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356013427/10000000000 : ℝ)^8397 ≤ (6663463716963/20000000000000 : ℝ)^6349 := by
    have hnat : (4356013427 : ℕ)^8397*20000000000000^6349 ≤ 6663463716963^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356013427 10000000000 6663463716963 20000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231814713/10000000000 : ℝ)^8397 ≤ (16033383020383/50000000000000 : ℝ)^6349 := by
    have hnat : (4231814713 : ℕ)^8397*50000000000000^6349 ≤ 16033383020383^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231814713 10000000000 16033383020383 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483786189/10000000000 : ℝ)^8397 ≤ (34615915355619/100000000000000 : ℝ)^6349 := by
    have hnat : (4483786189 : ℕ)^8397*100000000000000^6349 ≤ 34615915355619^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483786189 10000000000 34615915355619 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356013427/10000000000 : ℝ), (4231814713/10000000000 : ℝ), (4483786189/10000000000 : ℝ)] ![(6663463716963/20000000000000 : ℝ), (16033383020383/50000000000000 : ℝ), (34615915355619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356013427/10000000000 : ℝ)|^8397 ≤ (6663463716963/20000000000000 : ℝ)^6349
        have hw : |(4356013427/10000000000 : ℝ)|=(4356013427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231814713/10000000000 : ℝ)|^8397 ≤ (16033383020383/50000000000000 : ℝ)^6349
        have hw : |(4231814713/10000000000 : ℝ)|=(4231814713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483786189/10000000000 : ℝ)|^8397 ≤ (34615915355619/100000000000000 : ℝ)^6349
        have hw : |(4483786189/10000000000 : ℝ)|=(4483786189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s8_4 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068796293/5000000000 : ℝ)*x 0 + (5267043749/10000000000 : ℝ)*x 1 + (5391541653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068796293/5000000000 : ℝ)^8397 ≤ (6497533105459/50000000000000 : ℝ)^6349 := by
    have hnat : (1068796293 : ℕ)^8397*50000000000000^6349 ≤ 6497533105459^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068796293 5000000000 6497533105459 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267043749/10000000000 : ℝ)^8397 ≤ (1070761242441/2500000000000 : ℝ)^6349 := by
    have hnat : (5267043749 : ℕ)^8397*2500000000000^6349 ≤ 1070761242441^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267043749 10000000000 1070761242441 2500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391541653/10000000000 : ℝ)^8397 ≤ (44174484084347/100000000000000 : ℝ)^6349 := by
    have hnat : (5391541653 : ℕ)^8397*100000000000000^6349 ≤ 44174484084347^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391541653 10000000000 44174484084347 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068796293/5000000000 : ℝ), (5267043749/10000000000 : ℝ), (5391541653/10000000000 : ℝ)] ![(6497533105459/50000000000000 : ℝ), (1070761242441/2500000000000 : ℝ), (44174484084347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068796293/5000000000 : ℝ)|^8397 ≤ (6497533105459/50000000000000 : ℝ)^6349
        have hw : |(-1068796293/5000000000 : ℝ)|=(1068796293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267043749/10000000000 : ℝ)|^8397 ≤ (1070761242441/2500000000000 : ℝ)^6349
        have hw : |(5267043749/10000000000 : ℝ)|=(5267043749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391541653/10000000000 : ℝ)|^8397 ≤ (44174484084347/100000000000000 : ℝ)^6349
        have hw : |(5391541653/10000000000 : ℝ)|=(5391541653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s8_5 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312643283/10000000000 : ℝ)*x 0 + (-41524537/200000000 : ℝ)*x 1 + (42121419/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312643283/10000000000 : ℝ)^8397 ≤ (21660774747567/50000000000000 : ℝ)^6349 := by
    have hnat : (5312643283 : ℕ)^8397*50000000000000^6349 ≤ 21660774747567^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312643283 10000000000 21660774747567 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41524537/200000000 : ℝ)^8397 ≤ (12503966635961/100000000000000 : ℝ)^6349 := by
    have hnat : (41524537 : ℕ)^8397*100000000000000^6349 ≤ 12503966635961^6349*200000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41524537 200000000 12503966635961 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42121419/78125000 : ℝ)^8397 ≤ (22087241928393/50000000000000 : ℝ)^6349 := by
    have hnat : (42121419 : ℕ)^8397*50000000000000^6349 ≤ 22087241928393^6349*78125000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42121419 78125000 22087241928393 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312643283/10000000000 : ℝ), (-41524537/200000000 : ℝ), (42121419/78125000 : ℝ)] ![(21660774747567/50000000000000 : ℝ), (12503966635961/100000000000000 : ℝ), (22087241928393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312643283/10000000000 : ℝ)|^8397 ≤ (21660774747567/50000000000000 : ℝ)^6349
        have hw : |(5312643283/10000000000 : ℝ)|=(5312643283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41524537/200000000 : ℝ)|^8397 ≤ (12503966635961/100000000000000 : ℝ)^6349
        have hw : |(-41524537/200000000 : ℝ)|=(41524537/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42121419/78125000 : ℝ)|^8397 ≤ (22087241928393/50000000000000 : ℝ)^6349
        have hw : |(42121419/78125000 : ℝ)|=(42121419/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s8_6 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062528669/2000000000 : ℝ)*x 0 + (2695770823/5000000000 : ℝ)*x 1 + (-1038113373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062528669/2000000000 : ℝ)^8397 ≤ (2707596885237/6250000000000 : ℝ)^6349 := by
    have hnat : (1062528669 : ℕ)^8397*6250000000000^6349 ≤ 2707596885237^6349*2000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062528669 2000000000 2707596885237 6250000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695770823/5000000000 : ℝ)^8397 ≤ (44174484008493/100000000000000 : ℝ)^6349 := by
    have hnat : (2695770823 : ℕ)^8397*100000000000000^6349 ≤ 44174484008493^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695770823 5000000000 44174484008493 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1038113373/5000000000 : ℝ)^8397 ≤ (12503965807589/100000000000000 : ℝ)^6349 := by
    have hnat : (1038113373 : ℕ)^8397*100000000000000^6349 ≤ 12503965807589^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038113373 5000000000 12503965807589 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062528669/2000000000 : ℝ), (2695770823/5000000000 : ℝ), (-1038113373/5000000000 : ℝ)] ![(2707596885237/6250000000000 : ℝ), (44174484008493/100000000000000 : ℝ), (12503965807589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062528669/2000000000 : ℝ)|^8397 ≤ (2707596885237/6250000000000 : ℝ)^6349
        have hw : |(1062528669/2000000000 : ℝ)|=(1062528669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695770823/5000000000 : ℝ)|^8397 ≤ (44174484008493/100000000000000 : ℝ)^6349
        have hw : |(2695770823/5000000000 : ℝ)|=(2695770823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1038113373/5000000000 : ℝ)|^8397 ≤ (12503965807589/100000000000000 : ℝ)^6349
        have hw : |(-1038113373/5000000000 : ℝ)|=(1038113373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1204_s8_7 (p : ℝ) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178011523/5000000000 : ℝ)*x 0 + (4483152091/10000000000 : ℝ)*x 1 + (2116225507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178011523/5000000000 : ℝ)^8397 ≤ (166587079443/500000000000 : ℝ)^6349 := by
    have hnat : (2178011523 : ℕ)^8397*500000000000^6349 ≤ 166587079443^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178011523 5000000000 166587079443 500000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483152091/10000000000 : ℝ)^8397 ≤ (34609441004797/100000000000000 : ℝ)^6349 := by
    have hnat : (4483152091 : ℕ)^8397*100000000000000^6349 ≤ 34609441004797^6349*10000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483152091 10000000000 34609441004797 100000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116225507/5000000000 : ℝ)^8397 ≤ (16036571550231/50000000000000 : ℝ)^6349 := by
    have hnat : (2116225507 : ℕ)^8397*50000000000000^6349 ≤ 16036571550231^6349*5000000000^8397 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116225507 5000000000 16036571550231 50000000000000 8397 6349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8397/2048 : ℝ)) 8397 6349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178011523/5000000000 : ℝ), (4483152091/10000000000 : ℝ), (2116225507/5000000000 : ℝ)] ![(166587079443/500000000000 : ℝ), (34609441004797/100000000000000 : ℝ), (16036571550231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178011523/5000000000 : ℝ)|^8397 ≤ (166587079443/500000000000 : ℝ)^6349
        have hw : |(2178011523/5000000000 : ℝ)|=(2178011523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483152091/10000000000 : ℝ)|^8397 ≤ (34609441004797/100000000000000 : ℝ)^6349
        have hw : |(4483152091/10000000000 : ℝ)|=(4483152091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116225507/5000000000 : ℝ)|^8397 ≤ (16036571550231/50000000000000 : ℝ)^6349
        have hw : |(2116225507/5000000000 : ℝ)|=(2116225507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1204_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11433/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1429/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1429/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1429/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1429/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1429/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1429/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1429/12500 : ℝ) ^ (2099/512 : ℝ) ≤ (13761602389134781/100000000000000000000 : ℝ) := by
    have hpowers : (1429/12500 : ℝ)^2099 ≤ (13761602389134781/100000000000000000000 : ℝ)^512 := by
      have hnat : (1429 : ℕ)^2099*100000000000000000000^512 ≤ 13761602389134781^512*12500^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1429 12500 13761602389134781 100000000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1429/12500 : ℝ)) (X := (13761602389134781/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/25000 : ℝ) ^ (2099/512 : ℝ) ≤ (809187573520081/2500000000000000000 : ℝ) := by
    have hpowers : (3521/25000 : ℝ)^2099 ≤ (809187573520081/2500000000000000000 : ℝ)^512 := by
      have hnat : (3521 : ℕ)^2099*2500000000000000000^512 ≤ 809187573520081^512*25000^2099 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 25000 809187573520081 2500000000000000000 2099 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/25000 : ℝ)) (X := (809187573520081/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013761602389134781/50000000000000000000 : ℝ) ≤ (2000134258359709/2000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (50013761602389134781/50000000000000000000 : ℝ)^512 ≤ (2000134258359709/2000000000000000 : ℝ)^2099 := by
      have hnat : (50013761602389134781 : ℕ)^512*2000000000000000^2099 ≤ 2000134258359709^2099*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013761602389134781 50000000000000000000 2000134258359709 2000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000134258359709/2000000000000000 : ℝ)) (X := (50013761602389134781/50000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046129105329938021/100000000000000000000 : ℝ) ≤ (10001125011166947/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (100046129105329938021/100000000000000000000 : ℝ)^512 ≤ (10001125011166947/10000000000000000 : ℝ)^2099 := by
      have hnat : (100046129105329938021 : ℕ)^512*10000000000000000^2099 ≤ 10001125011166947^2099*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046129105329938021 100000000000000000000 10001125011166947 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001125011166947/10000000000000000 : ℝ)) (X := (100046129105329938021/100000000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250809187573520081/1250000000000000000 : ℝ) ≤ (10001578730535349/10000000000000000 : ℝ) ^ (2099/512 : ℝ) := by
    have hpowers : (1250809187573520081/1250000000000000000 : ℝ)^512 ≤ (10001578730535349/10000000000000000 : ℝ)^2099 := by
      have hnat : (1250809187573520081 : ℕ)^512*10000000000000000^2099 ≤ 10001578730535349^2099*1250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250809187573520081 1250000000000000000 10001578730535349 10000000000000000 512 2099 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001578730535349/10000000000000000 : ℝ)) (X := (1250809187573520081/1250000000000000000 : ℝ)) (by norm_num) 2099 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13761602389134781/100000000000000000000 : ℝ) ≤ ((6627851606552649503/6630000000000000000 : ℝ)+2*(226859684201/132600000000000 : ℝ)*(1429/12500 : ℝ))^(2099/512 : ℝ) := by
    rw [show (6627851606552649503/6630000000000000000 : ℝ)+2*(226859684201/132600000000000 : ℝ)*(1429/12500 : ℝ)=(2000134258359709/2000000000000000 : ℝ) by norm_num, show 1+2*(13761602389134781/100000000000000000000 : ℝ)=(50013761602389134781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(809187573520081/2500000000000000000 : ℝ)+(13761602389134781/100000000000000000000 : ℝ) ≤ ((6627851606552649503/6630000000000000000 : ℝ)+(226859684201/132600000000000 : ℝ)*((3521/25000 : ℝ)+(1429/12500 : ℝ)))^(2099/512 : ℝ) := by
    rw [show (6627851606552649503/6630000000000000000 : ℝ)+(226859684201/132600000000000 : ℝ)*((3521/25000 : ℝ)+(1429/12500 : ℝ))=(10001125011166947/10000000000000000 : ℝ) by norm_num, show 1+(809187573520081/2500000000000000000 : ℝ)+(13761602389134781/100000000000000000000 : ℝ)=(100046129105329938021/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(809187573520081/2500000000000000000 : ℝ) ≤ ((6627851606552649503/6630000000000000000 : ℝ)+2*(226859684201/132600000000000 : ℝ)*(3521/25000 : ℝ))^(2099/512 : ℝ) := by
    rw [show (6627851606552649503/6630000000000000000 : ℝ)+2*(226859684201/132600000000000 : ℝ)*(3521/25000 : ℝ)=(10001578730535349/10000000000000000 : ℝ) by norm_num, show 1+2*(809187573520081/2500000000000000000 : ℝ)=(1250809187573520081/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6627851606552649503/6630000000000000000 : ℝ)*(X 1 0+X 2 0)+(226859684201/132600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (6627851606552649503/6630000000000000000 : ℝ)) (alpha := (226859684201/132600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6627851606552649503/6630000000000000000 : ℝ)*(X 0 1+X 2 1)+(226859684201/132600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (6627851606552649503/6630000000000000000 : ℝ)) (alpha := (226859684201/132600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6627851606552649503/6630000000000000000 : ℝ)*(X 0 2+X 1 2)+(226859684201/132600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2099/512 : ℝ)) (lo := (1429/12500 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (6627851606552649503/6630000000000000000 : ℝ)) (alpha := (226859684201/132600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1068793903/5000000000 : ℝ)*X 0 0+(53918577/100000000 : ℝ)*X 0 1+(2633364439/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344487167/10000000000 : ℝ)*X 1 0+(-550259921/2500000000 : ℝ)*X 1 1+(2633364421/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672243603/5000000000 : ℝ)*X 2 0+(5266728831/10000000000 : ℝ)*X 2 1+(-2201039647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356013427/10000000000 : ℝ)*X 0 0+(4231814713/10000000000 : ℝ)*X 0 1+(4483786189/10000000000 : ℝ)*X 0 2+(4356013427/10000000000 : ℝ)*X 1 0+(4231814713/10000000000 : ℝ)*X 1 1+(4483786189/10000000000 : ℝ)*X 1 2+(4356013427/10000000000 : ℝ)*X 2 0+(4231814713/10000000000 : ℝ)*X 2 1+(4483786189/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1068796293/5000000000 : ℝ)*X 0 0+(5267043749/10000000000 : ℝ)*X 0 1+(5391541653/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312643283/10000000000 : ℝ)*X 1 0+(-41524537/200000000 : ℝ)*X 1 1+(42121419/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062528669/2000000000 : ℝ)*X 2 0+(2695770823/5000000000 : ℝ)*X 2 1+(-1038113373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178011523/5000000000 : ℝ)*X 0 0+(4483152091/10000000000 : ℝ)*X 0 1+(2116225507/5000000000 : ℝ)*X 0 2+(2178011523/5000000000 : ℝ)*X 1 0+(4483152091/10000000000 : ℝ)*X 1 1+(2116225507/5000000000 : ℝ)*X 1 2+(2178011523/5000000000 : ℝ)*X 2 0+(4483152091/10000000000 : ℝ)*X 2 1+(2116225507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1204_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (208477964935038578085389703/55250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (687886183/100000000000000 : ℝ)*(base19) + (140074907/20000000000000 : ℝ)*(base23) + (6123409/25000000000000 : ℝ)*(lower2) + (2866007/6250000000000 : ℝ)*(upper3) + (10422439/12500000000000 : ℝ)*(upper5) + (5980261130988401/100000000000000 : ℝ)*(major0) + (5980261130988401/100000000000000 : ℝ)*(major1) + (5980261130988401/100000000000000 : ℝ)*(major2) + (7991780657229673/100000000000000 : ℝ)*(sp0) + (3995900038473873/50000000000000 : ℝ)*(sp1) + (7991800064459393/100000000000000 : ℝ)*(sp2) + (793742472015967/20000000000000 : ℝ)*(sp3) + (628362633/3125000000000 : ℝ)*(sp4) + (9011284471/100000000000000 : ℝ)*(sp7) + (1984360685682153/50000000000000 : ℝ)*(f.failure) + (998975095604241/12500000000000 : ℝ)*(f.sum) + (20596044063691/6630000000000000000000000000 : ℝ)*base65 + (680846591812845099/221000000000000000000000000000000 : ℝ)*base68 + (1963100837643845099/221000000000000000000000000000000 : ℝ)*base70 + (448977752805845099/221000000000000000000000000000000 : ℝ)*base72 + (16414574700841/6630000000000000000000000000 : ℝ)*base73 + (1223506231113845099/221000000000000000000000000000000 : ℝ)*base76 + (486205285901845099/221000000000000000000000000000000 : ℝ)*base78 + (75474693868154901/221000000000000000000000000000000 : ℝ)*base79 + (13792348797661/6630000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (618647/156250000000000000000 : ℝ)*base90 + (618647/156250000000000000000 : ℝ)*base92 + (618647/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23671489880213997425630797/13812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (607465937/100000000000000 : ℝ)*(base19) + (767853271/100000000000000 : ℝ)*(base23) + (190138727/100000000000000 : ℝ)*(lower1) + (14588339/20000000000000 : ℝ)*(upper3) + (7226633/100000000000000 : ℝ)*(lower4) + (4995651/10000000000000 : ℝ)*(upper5) + (751316027127401/12500000000000 : ℝ)*(major0) + (751316027127401/12500000000000 : ℝ)*(major1) + (751316027127401/12500000000000 : ℝ)*(major2) + (4424949051/50000000000000 : ℝ)*(sp2) + (8032248653372673/100000000000000 : ℝ)*(sp4) + (502015502869171/6250000000000 : ℝ)*(sp5) + (8032239035621299/100000000000000 : ℝ)*(sp6) + (997201930884989/25000000000000 : ℝ)*(sp7) + (997201930884989/25000000000000 : ℝ)*(f.failure) + (8032248653372673/100000000000000 : ℝ)*(f.sum) + (5932333669517/1657500000000000000000000000 : ℝ)*base65 + (239394066695168901/27625000000000000000000000000000 : ℝ)*base67 + (59907679647668901/27625000000000000000000000000000 : ℝ)*base69 + (1939709061206206099/27625000000000000000000000000000 : ℝ)*base72 + (649060916479/207187500000000000000000000 : ℝ)*base73 + (1015306622220206099/27625000000000000000000000000000 : ℝ)*base76 + (105633952886418901/27625000000000000000000000000000 : ℝ)*base77 + (207166027892793901/27625000000000000000000000000000 : ℝ)*base79 + (6133987794359/828750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (662911/78125000000000000000 : ℝ)*base90 + (662911/78125000000000000000 : ℝ)*base92 + (662911/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1204_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1429/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1204_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1204_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1204_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1204_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1204_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2099/512 : ℝ) ≤ p) (hpb : p ≤ (8397/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4708901/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1204_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
