-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1340_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:05.609758+00:00
-- url     : https://prove2.me/submissions/b6bfe29a-0f1f-4f62-96bc-38e73711d58e

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
theorem support_rectangle_w1340_s3_0 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-204392079/1000000000 : ℝ)*x 0 + (5427429109/10000000000 : ℝ)*x 1 + (2615548111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204392079/1000000000 : ℝ)^1075 ≤ (6221591095133/50000000000000 : ℝ)^819 := by
    have hnat : (204392079 : ℕ)^1075*50000000000000^819 ≤ 6221591095133^819*1000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204392079 1000000000 6221591095133 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427429109/10000000000 : ℝ)^1075 ≤ (44836797025021/100000000000000 : ℝ)^819 := by
    have hnat : (5427429109 : ℕ)^1075*100000000000000^819 ≤ 44836797025021^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427429109 10000000000 44836797025021 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615548111/5000000000 : ℝ)^1075 ≤ (42720020767199/100000000000000 : ℝ)^819 := by
    have hnat : (2615548111 : ℕ)^1075*100000000000000^819 ≤ 42720020767199^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615548111 5000000000 42720020767199 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204392079/1000000000 : ℝ), (5427429109/10000000000 : ℝ), (2615548111/5000000000 : ℝ)] ![(6221591095133/50000000000000 : ℝ), (44836797025021/100000000000000 : ℝ), (42720020767199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204392079/1000000000 : ℝ)|^1075 ≤ (6221591095133/50000000000000 : ℝ)^819
        have hw : |(-204392079/1000000000 : ℝ)|=(204392079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427429109/10000000000 : ℝ)|^1075 ≤ (44836797025021/100000000000000 : ℝ)^819
        have hw : |(5427429109/10000000000 : ℝ)|=(5427429109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615548111/5000000000 : ℝ)|^1075 ≤ (42720020767199/100000000000000 : ℝ)^819
        have hw : |(2615548111/5000000000 : ℝ)|=(2615548111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s3_1 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5352759041/10000000000 : ℝ)*x 0 + (-2144266749/10000000000 : ℝ)*x 1 + (1046219201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352759041/10000000000 : ℝ)^1075 ≤ (44028867018009/100000000000000 : ℝ)^819 := by
    have hnat : (5352759041 : ℕ)^1075*100000000000000^819 ≤ 44028867018009^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352759041 10000000000 44028867018009 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2144266749/10000000000 : ℝ)^1075 ≤ (6625557265961/50000000000000 : ℝ)^819 := by
    have hnat : (2144266749 : ℕ)^1075*50000000000000^819 ≤ 6625557265961^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144266749 10000000000 6625557265961 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046219201/2000000000 : ℝ)^1075 ≤ (42720018441127/100000000000000 : ℝ)^819 := by
    have hnat : (1046219201 : ℕ)^1075*100000000000000^819 ≤ 42720018441127^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046219201 2000000000 42720018441127 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352759041/10000000000 : ℝ), (-2144266749/10000000000 : ℝ), (1046219201/2000000000 : ℝ)] ![(44028867018009/100000000000000 : ℝ), (6625557265961/50000000000000 : ℝ), (42720018441127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352759041/10000000000 : ℝ)|^1075 ≤ (44028867018009/100000000000000 : ℝ)^819
        have hw : |(5352759041/10000000000 : ℝ)|=(5352759041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2144266749/10000000000 : ℝ)|^1075 ≤ (6625557265961/50000000000000 : ℝ)^819
        have hw : |(-2144266749/10000000000 : ℝ)|=(2144266749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046219201/2000000000 : ℝ)|^1075 ≤ (42720018441127/100000000000000 : ℝ)^819
        have hw : |(1046219201/2000000000 : ℝ)|=(1046219201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s3_2 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334547447/625000000 : ℝ)*x 0 + (1046219099/2000000000 : ℝ)*x 1 + (-1072133637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334547447/625000000 : ℝ)^1075 ≤ (5503608527053/12500000000000 : ℝ)^819 := by
    have hnat : (334547447 : ℕ)^1075*12500000000000^819 ≤ 5503608527053^819*625000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334547447 625000000 5503608527053 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046219099/2000000000 : ℝ)^1075 ≤ (10680003243581/25000000000000 : ℝ)^819 := by
    have hnat : (1046219099 : ℕ)^1075*25000000000000^819 ≤ 10680003243581^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046219099 2000000000 10680003243581 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1072133637/5000000000 : ℝ)^1075 ≤ (1325111879043/10000000000000 : ℝ)^819 := by
    have hnat : (1072133637 : ℕ)^1075*10000000000000^819 ≤ 1325111879043^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072133637 5000000000 1325111879043 10000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334547447/625000000 : ℝ), (1046219099/2000000000 : ℝ), (-1072133637/5000000000 : ℝ)] ![(5503608527053/12500000000000 : ℝ), (10680003243581/25000000000000 : ℝ), (1325111879043/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334547447/625000000 : ℝ)|^1075 ≤ (5503608527053/12500000000000 : ℝ)^819
        have hw : |(334547447/625000000 : ℝ)|=(334547447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1046219099/2000000000 : ℝ)|^1075 ≤ (10680003243581/25000000000000 : ℝ)^819
        have hw : |(1046219099/2000000000 : ℝ)|=(1046219099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1072133637/5000000000 : ℝ)|^1075 ≤ (1325111879043/10000000000000 : ℝ)^819
        have hw : |(-1072133637/5000000000 : ℝ)|=(1072133637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s3_3 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4326065781/10000000000 : ℝ)*x 0 + (4125164319/10000000000 : ℝ)*x 1 + (4536088917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326065781/10000000000 : ℝ)^1075 ≤ (4161543713771/12500000000000 : ℝ)^819 := by
    have hnat : (4326065781 : ℕ)^1075*12500000000000^819 ≤ 4161543713771^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326065781 10000000000 4161543713771 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4125164319/10000000000 : ℝ)^1075 ≤ (31277879156561/100000000000000 : ℝ)^819 := by
    have hnat : (4125164319 : ℕ)^1075*100000000000000^819 ≤ 31277879156561^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125164319 10000000000 31277879156561 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4536088917/10000000000 : ℝ)^1075 ≤ (35429771120241/100000000000000 : ℝ)^819 := by
    have hnat : (4536088917 : ℕ)^1075*100000000000000^819 ≤ 35429771120241^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536088917 10000000000 35429771120241 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326065781/10000000000 : ℝ), (4125164319/10000000000 : ℝ), (4536088917/10000000000 : ℝ)] ![(4161543713771/12500000000000 : ℝ), (31277879156561/100000000000000 : ℝ), (35429771120241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326065781/10000000000 : ℝ)|^1075 ≤ (4161543713771/12500000000000 : ℝ)^819
        have hw : |(4326065781/10000000000 : ℝ)|=(4326065781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4125164319/10000000000 : ℝ)|^1075 ≤ (31277879156561/100000000000000 : ℝ)^819
        have hw : |(4125164319/10000000000 : ℝ)|=(4125164319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4536088917/10000000000 : ℝ)|^1075 ≤ (35429771120241/100000000000000 : ℝ)^819
        have hw : |(4536088917/10000000000 : ℝ)|=(4536088917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s3_4 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1021970073/5000000000 : ℝ)*x 0 + (5231915203/10000000000 : ℝ)*x 1 + (5426605203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1021970073/5000000000 : ℝ)^1075 ≤ (6221668430513/50000000000000 : ℝ)^819 := by
    have hnat : (1021970073 : ℕ)^1075*50000000000000^819 ≤ 6221668430513^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021970073 5000000000 6221668430513 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231915203/10000000000 : ℝ)^1075 ≤ (42728799822029/100000000000000 : ℝ)^819 := by
    have hnat : (5231915203 : ℕ)^1075*100000000000000^819 ≤ 42728799822029^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231915203 10000000000 42728799822029 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426605203/10000000000 : ℝ)^1075 ≤ (11206965826213/25000000000000 : ℝ)^819 := by
    have hnat : (5426605203 : ℕ)^1075*25000000000000^819 ≤ 11206965826213^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426605203 10000000000 11206965826213 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1021970073/5000000000 : ℝ), (5231915203/10000000000 : ℝ), (5426605203/10000000000 : ℝ)] ![(6221668430513/50000000000000 : ℝ), (42728799822029/100000000000000 : ℝ), (11206965826213/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1021970073/5000000000 : ℝ)|^1075 ≤ (6221668430513/50000000000000 : ℝ)^819
        have hw : |(-1021970073/5000000000 : ℝ)|=(1021970073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231915203/10000000000 : ℝ)|^1075 ≤ (42728799822029/100000000000000 : ℝ)^819
        have hw : |(5231915203/10000000000 : ℝ)|=(5231915203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426605203/10000000000 : ℝ)|^1075 ≤ (11206965826213/25000000000000 : ℝ)^819
        have hw : |(5426605203/10000000000 : ℝ)|=(5426605203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s3_5 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1060439603/2000000000 : ℝ)*x 0 + (-121797353/625000000 : ℝ)*x 1 + (5426605453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060439603/2000000000 : ℝ)^1075 ≤ (21741895387157/50000000000000 : ℝ)^819 := by
    have hnat : (1060439603 : ℕ)^1075*50000000000000^819 ≤ 21741895387157^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060439603 2000000000 21741895387157 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121797353/625000000 : ℝ)^1075 ≤ (58441715969/500000000000 : ℝ)^819 := by
    have hnat : (121797353 : ℕ)^1075*500000000000^819 ≤ 58441715969^819*625000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121797353 625000000 58441715969 500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426605453/10000000000 : ℝ)^1075 ≤ (4482786601557/10000000000000 : ℝ)^819 := by
    have hnat : (5426605453 : ℕ)^1075*10000000000000^819 ≤ 4482786601557^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426605453 10000000000 4482786601557 10000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060439603/2000000000 : ℝ), (-121797353/625000000 : ℝ), (5426605453/10000000000 : ℝ)] ![(21741895387157/50000000000000 : ℝ), (58441715969/500000000000 : ℝ), (4482786601557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060439603/2000000000 : ℝ)|^1075 ≤ (21741895387157/50000000000000 : ℝ)^819
        have hw : |(1060439603/2000000000 : ℝ)|=(1060439603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121797353/625000000 : ℝ)|^1075 ≤ (58441715969/500000000000 : ℝ)^819
        have hw : |(-121797353/625000000 : ℝ)|=(121797353/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426605453/10000000000 : ℝ)|^1075 ≤ (4482786601557/10000000000000 : ℝ)^819
        have hw : |(5426605453/10000000000 : ℝ)|=(5426605453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s3_6 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2651099359/5000000000 : ℝ)*x 0 + (5426605001/10000000000 : ℝ)*x 1 + (-1948757309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651099359/5000000000 : ℝ)^1075 ≤ (8696759668359/20000000000000 : ℝ)^819 := by
    have hnat : (2651099359 : ℕ)^1075*20000000000000^819 ≤ 8696759668359^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651099359 5000000000 8696759668359 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426605001/10000000000 : ℝ)^1075 ≤ (1400870659831/3125000000000 : ℝ)^819 := by
    have hnat : (5426605001 : ℕ)^1075*3125000000000^819 ≤ 1400870659831^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426605001 10000000000 1400870659831 3125000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1948757309/10000000000 : ℝ)^1075 ≤ (584417026249/5000000000000 : ℝ)^819 := by
    have hnat : (1948757309 : ℕ)^1075*5000000000000^819 ≤ 584417026249^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1948757309 10000000000 584417026249 5000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651099359/5000000000 : ℝ), (5426605001/10000000000 : ℝ), (-1948757309/10000000000 : ℝ)] ![(8696759668359/20000000000000 : ℝ), (1400870659831/3125000000000 : ℝ), (584417026249/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651099359/5000000000 : ℝ)|^1075 ≤ (8696759668359/20000000000000 : ℝ)^819
        have hw : |(2651099359/5000000000 : ℝ)|=(2651099359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426605001/10000000000 : ℝ)|^1075 ≤ (1400870659831/3125000000000 : ℝ)^819
        have hw : |(5426605001/10000000000 : ℝ)|=(5426605001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1948757309/10000000000 : ℝ)|^1075 ≤ (584417026249/5000000000000 : ℝ)^819
        have hw : |(-1948757309/10000000000 : ℝ)|=(1948757309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s3_7 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4326106511/10000000000 : ℝ)*x 0 + (4534374513/10000000000 : ℝ)*x 1 + (257930551/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326106511/10000000000 : ℝ)^1075 ≤ (33292761135417/100000000000000 : ℝ)^819 := by
    have hnat : (4326106511 : ℕ)^1075*100000000000000^819 ≤ 33292761135417^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326106511 10000000000 33292761135417 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4534374513/10000000000 : ℝ)^1075 ≤ (8853048994331/25000000000000 : ℝ)^819 := by
    have hnat : (4534374513 : ℕ)^1075*25000000000000^819 ≤ 8853048994331^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4534374513 10000000000 8853048994331 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257930551/625000000 : ℝ)^1075 ≤ (1564752143829/5000000000000 : ℝ)^819 := by
    have hnat : (257930551 : ℕ)^1075*5000000000000^819 ≤ 1564752143829^819*625000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257930551 625000000 1564752143829 5000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326106511/10000000000 : ℝ), (4534374513/10000000000 : ℝ), (257930551/625000000 : ℝ)] ![(33292761135417/100000000000000 : ℝ), (8853048994331/25000000000000 : ℝ), (1564752143829/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326106511/10000000000 : ℝ)|^1075 ≤ (33292761135417/100000000000000 : ℝ)^819
        have hw : |(4326106511/10000000000 : ℝ)|=(4326106511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4534374513/10000000000 : ℝ)|^1075 ≤ (8853048994331/25000000000000 : ℝ)^819
        have hw : |(4534374513/10000000000 : ℝ)|=(4534374513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257930551/625000000 : ℝ)|^1075 ≤ (1564752143829/5000000000000 : ℝ)^819
        have hw : |(257930551/625000000 : ℝ)|=(257930551/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1340_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1007/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10857/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1007/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4919/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1007/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4919/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1007/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4919/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1007/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4919/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1007/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4919/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1007/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4919/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4919/50000 : ℝ) ^ (4299/1024 : ℝ) ≤ (5915329179857817/100000000000000000000 : ℝ) := by
    have hpowers : (4919/50000 : ℝ)^4299 ≤ (5915329179857817/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4919 : ℕ)^4299*100000000000000000000^1024 ≤ 5915329179857817^1024*50000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4919 50000 5915329179857817 100000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4919/50000 : ℝ)) (X := (5915329179857817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1007/6250 : ℝ) ^ (4299/1024 : ℝ) ≤ (46926848188358381/100000000000000000000 : ℝ) := by
    have hpowers : (1007/6250 : ℝ)^4299 ≤ (46926848188358381/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1007 : ℕ)^4299*100000000000000000000^1024 ≤ 46926848188358381^1024*6250^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1007 6250 46926848188358381 100000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1007/6250 : ℝ)) (X := (46926848188358381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005915329179857817/50000000000000000000 : ℝ) ≤ (10000281787584903/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (50005915329179857817/50000000000000000000 : ℝ)^1024 ≤ (10000281787584903/10000000000000000 : ℝ)^4299 := by
      have hnat : (50005915329179857817 : ℕ)^1024*10000000000000000^4299 ≤ 10000281787584903^4299*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005915329179857817 50000000000000000000 10000281787584903 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281787584903/10000000000000000 : ℝ)) (X := (50005915329179857817/50000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50026421088684108099/50000000000000000000 : ℝ) ≤ (10001258420605171/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (50026421088684108099/50000000000000000000 : ℝ)^1024 ≤ (10001258420605171/10000000000000000 : ℝ)^4299 := by
      have hnat : (50026421088684108099 : ℕ)^1024*10000000000000000^4299 ≤ 10001258420605171^4299*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026421088684108099 50000000000000000000 10001258420605171 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001258420605171/10000000000000000 : ℝ)) (X := (50026421088684108099/50000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50046926848188358381/50000000000000000000 : ℝ) ≤ (10002235053625439/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (50046926848188358381/50000000000000000000 : ℝ)^1024 ≤ (10002235053625439/10000000000000000 : ℝ)^4299 := by
      have hnat : (50046926848188358381 : ℕ)^1024*10000000000000000^4299 ≤ 10002235053625439^4299*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50046926848188358381 50000000000000000000 10002235053625439 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002235053625439/10000000000000000 : ℝ)) (X := (50046926848188358381/50000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5915329179857817/100000000000000000000 : ℝ) ≤ ((31361275852000444127/31370000000000000000 : ℝ)+2*(244158255067/156850000000000 : ℝ)*(4919/50000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (31361275852000444127/31370000000000000000 : ℝ)+2*(244158255067/156850000000000 : ℝ)*(4919/50000 : ℝ)=(10000281787584903/10000000000000000 : ℝ) by norm_num, show 1+2*(5915329179857817/100000000000000000000 : ℝ)=(50005915329179857817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46926848188358381/100000000000000000000 : ℝ)+(5915329179857817/100000000000000000000 : ℝ) ≤ ((31361275852000444127/31370000000000000000 : ℝ)+(244158255067/156850000000000 : ℝ)*((1007/6250 : ℝ)+(4919/50000 : ℝ)))^(4299/1024 : ℝ) := by
    rw [show (31361275852000444127/31370000000000000000 : ℝ)+(244158255067/156850000000000 : ℝ)*((1007/6250 : ℝ)+(4919/50000 : ℝ))=(10001258420605171/10000000000000000 : ℝ) by norm_num, show 1+(46926848188358381/100000000000000000000 : ℝ)+(5915329179857817/100000000000000000000 : ℝ)=(50026421088684108099/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46926848188358381/100000000000000000000 : ℝ) ≤ ((31361275852000444127/31370000000000000000 : ℝ)+2*(244158255067/156850000000000 : ℝ)*(1007/6250 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (31361275852000444127/31370000000000000000 : ℝ)+2*(244158255067/156850000000000 : ℝ)*(1007/6250 : ℝ)=(10002235053625439/10000000000000000 : ℝ) by norm_num, show 1+2*(46926848188358381/100000000000000000000 : ℝ)=(50046926848188358381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31361275852000444127/31370000000000000000 : ℝ)*(X 1 0+X 2 0)+(244158255067/156850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (4919/50000 : ℝ)) (hi := (1007/6250 : ℝ)) (c := (31361275852000444127/31370000000000000000 : ℝ)) (alpha := (244158255067/156850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31361275852000444127/31370000000000000000 : ℝ)*(X 0 1+X 2 1)+(244158255067/156850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (4919/50000 : ℝ)) (hi := (1007/6250 : ℝ)) (c := (31361275852000444127/31370000000000000000 : ℝ)) (alpha := (244158255067/156850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31361275852000444127/31370000000000000000 : ℝ)*(X 0 2+X 1 2)+(244158255067/156850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (4919/50000 : ℝ)) (hi := (1007/6250 : ℝ)) (c := (31361275852000444127/31370000000000000000 : ℝ)) (alpha := (244158255067/156850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-204392079/1000000000 : ℝ)*X 0 0+(5427429109/10000000000 : ℝ)*X 0 1+(2615548111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352759041/10000000000 : ℝ)*X 1 0+(-2144266749/10000000000 : ℝ)*X 1 1+(1046219201/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334547447/625000000 : ℝ)*X 2 0+(1046219099/2000000000 : ℝ)*X 2 1+(-1072133637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326065781/10000000000 : ℝ)*X 0 0+(4125164319/10000000000 : ℝ)*X 0 1+(4536088917/10000000000 : ℝ)*X 0 2+(4326065781/10000000000 : ℝ)*X 1 0+(4125164319/10000000000 : ℝ)*X 1 1+(4536088917/10000000000 : ℝ)*X 1 2+(4326065781/10000000000 : ℝ)*X 2 0+(4125164319/10000000000 : ℝ)*X 2 1+(4536088917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1021970073/5000000000 : ℝ)*X 0 0+(5231915203/10000000000 : ℝ)*X 0 1+(5426605203/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060439603/2000000000 : ℝ)*X 1 0+(-121797353/625000000 : ℝ)*X 1 1+(5426605453/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651099359/5000000000 : ℝ)*X 2 0+(5426605001/10000000000 : ℝ)*X 2 1+(-1948757309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326106511/10000000000 : ℝ)*X 0 0+(4534374513/10000000000 : ℝ)*X 0 1+(257930551/625000000 : ℝ)*X 0 2+(4326106511/10000000000 : ℝ)*X 1 0+(4534374513/10000000000 : ℝ)*X 1 1+(257930551/625000000 : ℝ)*X 1 2+(4326106511/10000000000 : ℝ)*X 2 0+(4534374513/10000000000 : ℝ)*X 2 1+(257930551/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (747773824837982515076349657/196062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49462019/5000000000000 : ℝ)*(base19) + (3129867/250000000000 : ℝ)*(base23) + (304883517/100000000000000 : ℝ)*(upper3) + (48463637/50000000000000 : ℝ)*(lower4) + (940869414354703/25000000000000 : ℝ)*(major0) + (940869414354703/25000000000000 : ℝ)*(major1) + (940869414354703/25000000000000 : ℝ)*(major2) + (5093404253726479/100000000000000 : ℝ)*(sp0) + (5093406146644609/100000000000000 : ℝ)*(sp1) + (5093403343678597/100000000000000 : ℝ)*(sp2) + (1216770244393971/50000000000000 : ℝ)*(sp3) + (2882158509/100000000000000 : ℝ)*(sp4) + (317532449/12500000000000 : ℝ)*(sp6) + (1512606561/20000000000000 : ℝ)*(sp7) + (2433548051820747/100000000000000 : ℝ)*(f.failure) + (1273351783971247/25000000000000 : ℝ)*(f.sum) + (73294055907297/15685000000000000000000000000 : ℝ)*base66 + (11645450747847129281/784250000000000000000000000000000 : ℝ)*base67 + (12168778923585629281/784250000000000000000000000000000 : ℝ)*base69 + (2637997545240879281/784250000000000000000000000000000 : ℝ)*base71 + (326995200119/7842500000000000000000000000 : ℝ)*base73 + (1372556282070629281/784250000000000000000000000000000 : ℝ)*base75 + (1940632382529129281/784250000000000000000000000000000 : ℝ)*base77 + (1481679110891120719/784250000000000000000000000000000 : ℝ)*base80 + (2206587720743/3921250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (56005207/10000000000000000000000 : ℝ)*base90 + (56005207/10000000000000000000000 : ℝ)*base92 + (56005207/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1326906084412754302338251709/1568500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32001317/12500000000000 : ℝ)*(base19) + (1347882229/100000000000000 : ℝ)*(base23) + (138902719/100000000000000 : ℝ)*(upper3) + (65384391/50000000000000 : ℝ)*(lower4) + (50261263/50000000000000 : ℝ)*(upper5) + (3795224154134111/100000000000000 : ℝ)*(major0) + (3795224154134111/100000000000000 : ℝ)*(major1) + (3795224154134111/100000000000000 : ℝ)*(major2) + (136298153/2500000000000 : ℝ)*(sp1) + (5668554757/25000000000000 : ℝ)*(sp2) + (5136372239971047/100000000000000 : ℝ)*(sp4) + (5136366532034391/100000000000000 : ℝ)*(sp5) + (5136348217869789/100000000000000 : ℝ)*(sp6) + (61351901002453/2500000000000 : ℝ)*(sp7) + (61351901002453/2500000000000 : ℝ)*(f.failure) + (5136372239971047/100000000000000 : ℝ)*(f.sum) + (7350267973393/1960625000000000000000000000 : ℝ)*base65 + (11350313425370716097/3137000000000000000000000000000000 : ℝ)*base67 + (5768422183949283903/3137000000000000000000000000000000 : ℝ)*base70 + (11339958175822716097/3137000000000000000000000000000000 : ℝ)*base71 + (9038390386077/7842500000000000000000000000 : ℝ)*base73 + (16028309646116716097/3137000000000000000000000000000000 : ℝ)*base75 + (4157731469478283903/3137000000000000000000000000000000 : ℝ)*base78 + (44322799344574716097/3137000000000000000000000000000000 : ℝ)*base79 + (14441952439679/15685000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2493993/250000000000000000000 : ℝ)*base90 + (2493993/250000000000000000000 : ℝ)*base92 + (2493993/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1340_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1007/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10857/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1340_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1340_s4_0 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2045397131/10000000000 : ℝ)*x 0 + (676925471/1250000000 : ℝ)*x 1 + (327634519/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045397131/10000000000 : ℝ)^1075 ≤ (12454980713663/100000000000000 : ℝ)^819 := by
    have hnat : (2045397131 : ℕ)^1075*100000000000000^819 ≤ 12454980713663^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045397131 10000000000 12454980713663 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676925471/1250000000 : ℝ)^1075 ≤ (698538230743/1562500000000 : ℝ)^819 := by
    have hnat : (676925471 : ℕ)^1075*1562500000000^819 ≤ 698538230743^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676925471 1250000000 698538230743 1562500000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327634519/625000000 : ℝ)^1075 ≤ (8567714500923/20000000000000 : ℝ)^819 := by
    have hnat : (327634519 : ℕ)^1075*20000000000000^819 ≤ 8567714500923^819*625000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327634519 625000000 8567714500923 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2045397131/10000000000 : ℝ), (676925471/1250000000 : ℝ), (327634519/625000000 : ℝ)] ![(12454980713663/100000000000000 : ℝ), (698538230743/1562500000000 : ℝ), (8567714500923/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2045397131/10000000000 : ℝ)|^1075 ≤ (12454980713663/100000000000000 : ℝ)^819
        have hw : |(-2045397131/10000000000 : ℝ)|=(2045397131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676925471/1250000000 : ℝ)|^1075 ≤ (698538230743/1562500000000 : ℝ)^819
        have hw : |(676925471/1250000000 : ℝ)|=(676925471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327634519/625000000 : ℝ)|^1075 ≤ (8567714500923/20000000000000 : ℝ)^819
        have hw : |(327634519/625000000 : ℝ)|=(327634519/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s4_1 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349695357/10000000000 : ℝ)*x 0 + (-266715081/1250000000 : ℝ)*x 1 + (5242152157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349695357/10000000000 : ℝ)^1075 ≤ (43995792807079/100000000000000 : ℝ)^819 := by
    have hnat : (5349695357 : ℕ)^1075*100000000000000^819 ≤ 43995792807079^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349695357 10000000000 43995792807079 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266715081/1250000000 : ℝ)^1075 ≤ (6582818128277/50000000000000 : ℝ)^819 := by
    have hnat : (266715081 : ℕ)^1075*50000000000000^819 ≤ 6582818128277^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266715081 1250000000 6582818128277 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242152157/10000000000 : ℝ)^1075 ≤ (42838570927849/100000000000000 : ℝ)^819 := by
    have hnat : (5242152157 : ℕ)^1075*100000000000000^819 ≤ 42838570927849^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242152157 10000000000 42838570927849 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349695357/10000000000 : ℝ), (-266715081/1250000000 : ℝ), (5242152157/10000000000 : ℝ)] ![(43995792807079/100000000000000 : ℝ), (6582818128277/50000000000000 : ℝ), (42838570927849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349695357/10000000000 : ℝ)|^1075 ≤ (43995792807079/100000000000000 : ℝ)^819
        have hw : |(5349695357/10000000000 : ℝ)|=(5349695357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266715081/1250000000 : ℝ)|^1075 ≤ (6582818128277/50000000000000 : ℝ)^819
        have hw : |(-266715081/1250000000 : ℝ)|=(266715081/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242152157/10000000000 : ℝ)|^1075 ≤ (42838570927849/100000000000000 : ℝ)^819
        have hw : |(5242152157/10000000000 : ℝ)|=(5242152157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s4_2 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349695701/10000000000 : ℝ)*x 0 + (262107593/500000000 : ℝ)*x 1 + (-1066860291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349695701/10000000000 : ℝ)^1075 ≤ (21997898260211/50000000000000 : ℝ)^819 := by
    have hnat : (5349695701 : ℕ)^1075*50000000000000^819 ≤ 21997898260211^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349695701 10000000000 21997898260211 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262107593/500000000 : ℝ)^1075 ≤ (21419283871069/50000000000000 : ℝ)^819 := by
    have hnat : (262107593 : ℕ)^1075*50000000000000^819 ≤ 21419283871069^819*500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262107593 500000000 21419283871069 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066860291/5000000000 : ℝ)^1075 ≤ (13165635722023/100000000000000 : ℝ)^819 := by
    have hnat : (1066860291 : ℕ)^1075*100000000000000^819 ≤ 13165635722023^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066860291 5000000000 13165635722023 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349695701/10000000000 : ℝ), (262107593/500000000 : ℝ), (-1066860291/5000000000 : ℝ)] ![(21997898260211/50000000000000 : ℝ), (21419283871069/50000000000000 : ℝ), (13165635722023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349695701/10000000000 : ℝ)|^1075 ≤ (21997898260211/50000000000000 : ℝ)^819
        have hw : |(5349695701/10000000000 : ℝ)|=(5349695701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262107593/500000000 : ℝ)|^1075 ≤ (21419283871069/50000000000000 : ℝ)^819
        have hw : |(262107593/500000000 : ℝ)|=(262107593/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066860291/5000000000 : ℝ)|^1075 ≤ (13165635722023/100000000000000 : ℝ)^819
        have hw : |(-1066860291/5000000000 : ℝ)|=(1066860291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s4_3 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2163481509/5000000000 : ℝ)*x 0 + (82984153/200000000 : ℝ)*x 1 + (225591157/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163481509/5000000000 : ℝ)^1075 ≤ (16650706617643/50000000000000 : ℝ)^819 := by
    have hnat : (2163481509 : ℕ)^1075*50000000000000^819 ≤ 16650706617643^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163481509 5000000000 16650706617643 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82984153/200000000 : ℝ)^1075 ≤ (15758690853561/50000000000000 : ℝ)^819 := by
    have hnat : (82984153 : ℕ)^1075*50000000000000^819 ≤ 15758690853561^819*200000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82984153 200000000 15758690853561 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225591157/500000000 : ℝ)^1075 ≤ (35181205044041/100000000000000 : ℝ)^819 := by
    have hnat : (225591157 : ℕ)^1075*100000000000000^819 ≤ 35181205044041^819*500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225591157 500000000 35181205044041 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163481509/5000000000 : ℝ), (82984153/200000000 : ℝ), (225591157/500000000 : ℝ)] ![(16650706617643/50000000000000 : ℝ), (15758690853561/50000000000000 : ℝ), (35181205044041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163481509/5000000000 : ℝ)|^1075 ≤ (16650706617643/50000000000000 : ℝ)^819
        have hw : |(2163481509/5000000000 : ℝ)|=(2163481509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82984153/200000000 : ℝ)|^1075 ≤ (15758690853561/50000000000000 : ℝ)^819
        have hw : |(82984153/200000000 : ℝ)|=(82984153/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225591157/500000000 : ℝ)|^1075 ≤ (35181205044041/100000000000000 : ℝ)^819
        have hw : |(225591157/500000000 : ℝ)|=(225591157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s4_4 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-81816431/400000000 : ℝ)*x 0 + (2621395231/5000000000 : ℝ)*x 1 + (216590479/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81816431/400000000 : ℝ)^1075 ≤ (1556886220661/12500000000000 : ℝ)^819 := by
    have hnat : (81816431 : ℕ)^1075*12500000000000^819 ≤ 1556886220661^819*400000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81816431 400000000 1556886220661 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621395231/5000000000 : ℝ)^1075 ≤ (42845417708669/100000000000000 : ℝ)^819 := by
    have hnat : (2621395231 : ℕ)^1075*100000000000000^819 ≤ 42845417708669^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621395231 5000000000 42845417708669 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216590479/400000000 : ℝ)^1075 ≤ (893989850189/2000000000000 : ℝ)^819 := by
    have hnat : (216590479 : ℕ)^1075*2000000000000^819 ≤ 893989850189^819*400000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216590479 400000000 893989850189 2000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81816431/400000000 : ℝ), (2621395231/5000000000 : ℝ), (216590479/400000000 : ℝ)] ![(1556886220661/12500000000000 : ℝ), (42845417708669/100000000000000 : ℝ), (893989850189/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81816431/400000000 : ℝ)|^1075 ≤ (1556886220661/12500000000000 : ℝ)^819
        have hw : |(-81816431/400000000 : ℝ)|=(81816431/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621395231/5000000000 : ℝ)|^1075 ≤ (42845417708669/100000000000000 : ℝ)^819
        have hw : |(2621395231/5000000000 : ℝ)|=(2621395231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216590479/400000000 : ℝ)|^1075 ≤ (893989850189/2000000000000 : ℝ)^819
        have hw : |(216590479/400000000 : ℝ)|=(216590479/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s4_5 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652539977/5000000000 : ℝ)*x 0 + (-1961110927/10000000000 : ℝ)*x 1 + (5414761893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652539977/5000000000 : ℝ)^1075 ≤ (69623705913/160000000000 : ℝ)^819 := by
    have hnat : (2652539977 : ℕ)^1075*160000000000^819 ≤ 69623705913^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652539977 5000000000 69623705913 160000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1961110927/10000000000 : ℝ)^1075 ≤ (11785692164283/100000000000000 : ℝ)^819 := by
    have hnat : (1961110927 : ℕ)^1075*100000000000000^819 ≤ 11785692164283^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961110927 10000000000 11785692164283 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414761893/10000000000 : ℝ)^1075 ≤ (22349745810471/50000000000000 : ℝ)^819 := by
    have hnat : (5414761893 : ℕ)^1075*50000000000000^819 ≤ 22349745810471^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414761893 10000000000 22349745810471 50000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652539977/5000000000 : ℝ), (-1961110927/10000000000 : ℝ), (5414761893/10000000000 : ℝ)] ![(69623705913/160000000000 : ℝ), (11785692164283/100000000000000 : ℝ), (22349745810471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652539977/5000000000 : ℝ)|^1075 ≤ (69623705913/160000000000 : ℝ)^819
        have hw : |(2652539977/5000000000 : ℝ)|=(2652539977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1961110927/10000000000 : ℝ)|^1075 ≤ (11785692164283/100000000000000 : ℝ)^819
        have hw : |(-1961110927/10000000000 : ℝ)|=(1961110927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414761893/10000000000 : ℝ)|^1075 ≤ (22349745810471/50000000000000 : ℝ)^819
        have hw : |(5414761893/10000000000 : ℝ)|=(5414761893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s4_6 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530507987/1000000000 : ℝ)*x 0 + (1353690483/2500000000 : ℝ)*x 1 + (-490277747/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530507987/1000000000 : ℝ)^1075 ≤ (43514815291249/100000000000000 : ℝ)^819 := by
    have hnat : (530507987 : ℕ)^1075*100000000000000^819 ≤ 43514815291249^819*1000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530507987 1000000000 43514815291249 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353690483/2500000000 : ℝ)^1075 ≤ (1787979681741/4000000000000 : ℝ)^819 := by
    have hnat : (1353690483 : ℕ)^1075*4000000000000^819 ≤ 1787979681741^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353690483 2500000000 1787979681741 4000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490277747/2500000000 : ℝ)^1075 ≤ (11785692645463/100000000000000 : ℝ)^819 := by
    have hnat : (490277747 : ℕ)^1075*100000000000000^819 ≤ 11785692645463^819*2500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490277747 2500000000 11785692645463 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530507987/1000000000 : ℝ), (1353690483/2500000000 : ℝ), (-490277747/2500000000 : ℝ)] ![(43514815291249/100000000000000 : ℝ), (1787979681741/4000000000000 : ℝ), (11785692645463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530507987/1000000000 : ℝ)|^1075 ≤ (43514815291249/100000000000000 : ℝ)^819
        have hw : |(530507987/1000000000 : ℝ)|=(530507987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353690483/2500000000 : ℝ)|^1075 ≤ (1787979681741/4000000000000 : ℝ)^819
        have hw : |(1353690483/2500000000 : ℝ)|=(1353690483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490277747/2500000000 : ℝ)|^1075 ≤ (11785692645463/100000000000000 : ℝ)^819
        have hw : |(-490277747/2500000000 : ℝ)|=(490277747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s4_7 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (865398111/2000000000 : ℝ)*x 0 + (902097381/2000000000 : ℝ)*x 1 + (4150551309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865398111/2000000000 : ℝ)^1075 ≤ (33301691412209/100000000000000 : ℝ)^819 := by
    have hnat : (865398111 : ℕ)^1075*100000000000000^819 ≤ 33301691412209^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865398111 2000000000 33301691412209 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902097381/2000000000 : ℝ)^1075 ≤ (35167529458029/100000000000000 : ℝ)^819 := by
    have hnat : (902097381 : ℕ)^1075*100000000000000^819 ≤ 35167529458029^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902097381 2000000000 35167529458029 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4150551309/10000000000 : ℝ)^1075 ≤ (6306155821693/20000000000000 : ℝ)^819 := by
    have hnat : (4150551309 : ℕ)^1075*20000000000000^819 ≤ 6306155821693^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150551309 10000000000 6306155821693 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865398111/2000000000 : ℝ), (902097381/2000000000 : ℝ), (4150551309/10000000000 : ℝ)] ![(33301691412209/100000000000000 : ℝ), (35167529458029/100000000000000 : ℝ), (6306155821693/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865398111/2000000000 : ℝ)|^1075 ≤ (33301691412209/100000000000000 : ℝ)^819
        have hw : |(865398111/2000000000 : ℝ)|=(865398111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902097381/2000000000 : ℝ)|^1075 ≤ (35167529458029/100000000000000 : ℝ)^819
        have hw : |(902097381/2000000000 : ℝ)|=(902097381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4150551309/10000000000 : ℝ)|^1075 ≤ (6306155821693/20000000000000 : ℝ)^819
        have hw : |(4150551309/10000000000 : ℝ)|=(4150551309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1340_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11093/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10857/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10857/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10857/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10857/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10857/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10857/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10857/100000 : ℝ) ^ (4299/1024 : ℝ) ≤ (4473488904546379/50000000000000000000 : ℝ) := by
    have hpowers : (10857/100000 : ℝ)^4299 ≤ (4473488904546379/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10857 : ℕ)^4299*50000000000000000000^1024 ≤ 4473488904546379^1024*100000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10857 100000 4473488904546379 50000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10857/100000 : ℝ)) (X := (4473488904546379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15011/100000 : ℝ) ^ (4299/1024 : ℝ) ≤ (6972654368311049/20000000000000000000 : ℝ) := by
    have hpowers : (15011/100000 : ℝ)^4299 ≤ (6972654368311049/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15011 : ℕ)^4299*20000000000000000000^1024 ≤ 6972654368311049^1024*100000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15011 100000 6972654368311049 20000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15011/100000 : ℝ)) (X := (6972654368311049/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004473488904546379/25000000000000000000 : ℝ) ≤ (5000213097950541/5000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (25004473488904546379/25000000000000000000 : ℝ)^1024 ≤ (5000213097950541/5000000000000000 : ℝ)^4299 := by
      have hnat : (25004473488904546379 : ℕ)^1024*5000000000000000^4299 ≤ 5000213097950541^4299*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004473488904546379 25000000000000000000 5000213097950541 5000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000213097950541/5000000000000000 : ℝ)) (X := (25004473488904546379/25000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043810249650648003/100000000000000000000 : ℝ) ≤ (10001043363835809/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (100043810249650648003/100000000000000000000 : ℝ)^1024 ≤ (10001043363835809/10000000000000000 : ℝ)^4299 := by
      have hnat : (100043810249650648003 : ℕ)^1024*10000000000000000^4299 ≤ 10001043363835809^4299*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043810249650648003 100000000000000000000 10001043363835809 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001043363835809/10000000000000000 : ℝ)) (X := (100043810249650648003/100000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006972654368311049/10000000000000000000 : ℝ) ≤ (1250207566471317/1250000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (10006972654368311049/10000000000000000000 : ℝ)^1024 ≤ (1250207566471317/1250000000000000 : ℝ)^4299 := by
      have hnat : (10006972654368311049 : ℕ)^1024*1250000000000000^4299 ≤ 1250207566471317^4299*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006972654368311049 10000000000000000000 1250207566471317 1250000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250207566471317/1250000000000000 : ℝ)) (X := (10006972654368311049/10000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4473488904546379/50000000000000000000 : ℝ) ≤ ((830567384664768651/830800000000000000 : ℝ)+2*(617167934727/415400000000000 : ℝ)*(10857/100000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (830567384664768651/830800000000000000 : ℝ)+2*(617167934727/415400000000000 : ℝ)*(10857/100000 : ℝ)=(5000213097950541/5000000000000000 : ℝ) by norm_num, show 1+2*(4473488904546379/50000000000000000000 : ℝ)=(25004473488904546379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6972654368311049/20000000000000000000 : ℝ)+(4473488904546379/50000000000000000000 : ℝ) ≤ ((830567384664768651/830800000000000000 : ℝ)+(617167934727/415400000000000 : ℝ)*((15011/100000 : ℝ)+(10857/100000 : ℝ)))^(4299/1024 : ℝ) := by
    rw [show (830567384664768651/830800000000000000 : ℝ)+(617167934727/415400000000000 : ℝ)*((15011/100000 : ℝ)+(10857/100000 : ℝ))=(10001043363835809/10000000000000000 : ℝ) by norm_num, show 1+(6972654368311049/20000000000000000000 : ℝ)+(4473488904546379/50000000000000000000 : ℝ)=(100043810249650648003/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6972654368311049/20000000000000000000 : ℝ) ≤ ((830567384664768651/830800000000000000 : ℝ)+2*(617167934727/415400000000000 : ℝ)*(15011/100000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (830567384664768651/830800000000000000 : ℝ)+2*(617167934727/415400000000000 : ℝ)*(15011/100000 : ℝ)=(1250207566471317/1250000000000000 : ℝ) by norm_num, show 1+2*(6972654368311049/20000000000000000000 : ℝ)=(10006972654368311049/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (830567384664768651/830800000000000000 : ℝ)*(X 1 0+X 2 0)+(617167934727/415400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (10857/100000 : ℝ)) (hi := (15011/100000 : ℝ)) (c := (830567384664768651/830800000000000000 : ℝ)) (alpha := (617167934727/415400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (830567384664768651/830800000000000000 : ℝ)*(X 0 1+X 2 1)+(617167934727/415400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (10857/100000 : ℝ)) (hi := (15011/100000 : ℝ)) (c := (830567384664768651/830800000000000000 : ℝ)) (alpha := (617167934727/415400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (830567384664768651/830800000000000000 : ℝ)*(X 0 2+X 1 2)+(617167934727/415400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (10857/100000 : ℝ)) (hi := (15011/100000 : ℝ)) (c := (830567384664768651/830800000000000000 : ℝ)) (alpha := (617167934727/415400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2045397131/10000000000 : ℝ)*X 0 0+(676925471/1250000000 : ℝ)*X 0 1+(327634519/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349695357/10000000000 : ℝ)*X 1 0+(-266715081/1250000000 : ℝ)*X 1 1+(5242152157/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349695701/10000000000 : ℝ)*X 2 0+(262107593/500000000 : ℝ)*X 2 1+(-1066860291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163481509/5000000000 : ℝ)*X 0 0+(82984153/200000000 : ℝ)*X 0 1+(225591157/500000000 : ℝ)*X 0 2+(2163481509/5000000000 : ℝ)*X 1 0+(82984153/200000000 : ℝ)*X 1 1+(225591157/500000000 : ℝ)*X 1 2+(2163481509/5000000000 : ℝ)*X 2 0+(82984153/200000000 : ℝ)*X 2 1+(225591157/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-81816431/400000000 : ℝ)*X 0 0+(2621395231/5000000000 : ℝ)*X 0 1+(216590479/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652539977/5000000000 : ℝ)*X 1 0+(-1961110927/10000000000 : ℝ)*X 1 1+(5414761893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530507987/1000000000 : ℝ)*X 2 0+(1353690483/2500000000 : ℝ)*X 2 1+(-490277747/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865398111/2000000000 : ℝ)*X 0 0+(902097381/2000000000 : ℝ)*X 0 1+(4150551309/10000000000 : ℝ)*X 0 2+(865398111/2000000000 : ℝ)*X 1 0+(902097381/2000000000 : ℝ)*X 1 1+(4150551309/10000000000 : ℝ)*X 1 2+(865398111/2000000000 : ℝ)*X 2 0+(902097381/2000000000 : ℝ)*X 2 1+(4150551309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (102910761785680703983263/20770000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1286719503/100000000000000 : ℝ)*(base19) + (1272383657/100000000000000 : ℝ)*(base23) + (25414121/10000000000000 : ℝ)*(lower2) + (71081463/50000000000000 : ℝ)*(upper3) + (23957617/50000000000000 : ℝ)*(lower4) + (4264884037372313/100000000000000 : ℝ)*(major0) + (4264884037372313/100000000000000 : ℝ)*(major1) + (4264884037372313/100000000000000 : ℝ)*(major2) + (1442994266414307/25000000000000 : ℝ)*(sp0) + (2885999047309611/50000000000000 : ℝ)*(sp1) + (5771998108955067/100000000000000 : ℝ)*(sp2) + (1378876404354361/50000000000000 : ℝ)*(sp3) + (2789460187/12500000000000 : ℝ)*(sp4) + (7859768933/50000000000000 : ℝ)*(sp7) + (689442132061647/25000000000000 : ℝ)*(f.failure) + (1442999845334681/25000000000000 : ℝ)*(f.sum) + (93361126242109/20770000000000000000000000000 : ℝ)*base66 + (777824274843981763/83080000000000000000000000000000 : ℝ)*base67 + (596939308440018237/83080000000000000000000000000000 : ℝ)*base70 + (381857014461763/83080000000000000000000000000000 : ℝ)*base71 + (29142289959571/20770000000000000000000000000 : ℝ)*base73 + (1171403773141378237/83080000000000000000000000000000 : ℝ)*base76 + (588944278658421763/83080000000000000000000000000000 : ℝ)*base77 + (963877171237138237/83080000000000000000000000000000 : ℝ)*base80 + (86339585190049/20770000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (19608107/2500000000000000000000 : ℝ)*base90 + (19608107/2500000000000000000000 : ℝ)*base92 + (19608107/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82406552523369177091950267/20770000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (436042403/50000000000000 : ℝ)*(base19) + (195117749/25000000000000 : ℝ)*(base23) + (80060681/100000000000000 : ℝ)*(upper3) + (6983747/50000000000000 : ℝ)*(lower4) + (117610681/100000000000000 : ℝ)*(upper5) + (2148297669406261/50000000000000 : ℝ)*(major0) + (2148297669406261/50000000000000 : ℝ)*(major1) + (2148297669406261/50000000000000 : ℝ)*(major2) + (7882772307/50000000000000 : ℝ)*(sp1) + (12689342071/100000000000000 : ℝ)*(sp2) + (5814916786893343/100000000000000 : ℝ)*(sp4) + (5814900149263923/100000000000000 : ℝ)*(sp5) + (1453725829270069/25000000000000 : ℝ)*(sp6) + (1389136879239581/50000000000000 : ℝ)*(sp7) + (1389136879239581/50000000000000 : ℝ)*(f.failure) + (5814916786893343/100000000000000 : ℝ)*(f.sum) + (2706484901511/5192500000000000000000000000 : ℝ)*base65 + (122439279529622089/41540000000000000000000000000000 : ℝ)*base68 + (177766669583597911/41540000000000000000000000000000 : ℝ)*base69 + (166919904006417911/41540000000000000000000000000000 : ℝ)*base71 + (2359350532851/5192500000000000000000000000 : ℝ)*base73 + (20083623662882089/41540000000000000000000000000000 : ℝ)*base76 + (280161094773877911/41540000000000000000000000000000 : ℝ)*base77 + (365653193758337911/41540000000000000000000000000000 : ℝ)*base79 + (38384296302267/10385000000000000000000000000 : ℝ)*base81 + (40714161/5000000000000000000000 : ℝ)*base90 + (40714161/5000000000000000000000 : ℝ)*base92 + (40714161/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1340_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10857/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1340_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1340_s5_0 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2045652353/10000000000 : ℝ)*x 0 + (1082640541/2000000000 : ℝ)*x 1 + (2622092703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2045652353/10000000000 : ℝ)^1075 ≤ (12457020649727/100000000000000 : ℝ)^819 := by
    have hnat : (2045652353 : ℕ)^1075*100000000000000^819 ≤ 12457020649727^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045652353 10000000000 12457020649727 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082640541/2000000000 : ℝ)^1075 ≤ (223412989227/500000000000 : ℝ)^819 := by
    have hnat : (1082640541 : ℕ)^1075*500000000000^819 ≤ 223412989227^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082640541 2000000000 223412989227 500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622092703/5000000000 : ℝ)^1075 ≤ (42860381487281/100000000000000 : ℝ)^819 := by
    have hnat : (2622092703 : ℕ)^1075*100000000000000^819 ≤ 42860381487281^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622092703 5000000000 42860381487281 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2045652353/10000000000 : ℝ), (1082640541/2000000000 : ℝ), (2622092703/5000000000 : ℝ)] ![(12457020649727/100000000000000 : ℝ), (223412989227/500000000000 : ℝ), (42860381487281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2045652353/10000000000 : ℝ)|^1075 ≤ (12457020649727/100000000000000 : ℝ)^819
        have hw : |(-2045652353/10000000000 : ℝ)|=(2045652353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082640541/2000000000 : ℝ)|^1075 ≤ (223412989227/500000000000 : ℝ)^819
        have hw : |(1082640541/2000000000 : ℝ)|=(1082640541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622092703/5000000000 : ℝ)|^1075 ≤ (42860381487281/100000000000000 : ℝ)^819
        have hw : |(2622092703/5000000000 : ℝ)|=(2622092703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s5_1 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5349133167/10000000000 : ℝ)*x 0 + (-2131776657/10000000000 : ℝ)*x 1 + (5244185407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349133167/10000000000 : ℝ)^1075 ≤ (10997431072277/25000000000000 : ℝ)^819 := by
    have hnat : (5349133167 : ℕ)^1075*25000000000000^819 ≤ 10997431072277^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349133167 10000000000 10997431072277 25000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131776657/10000000000 : ℝ)^1075 ≤ (2629978841599/20000000000000 : ℝ)^819 := by
    have hnat : (2131776657 : ℕ)^1075*20000000000000^819 ≤ 2629978841599^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131776657 10000000000 2629978841599 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244185407/10000000000 : ℝ)^1075 ≤ (42860381498009/100000000000000 : ℝ)^819 := by
    have hnat : (5244185407 : ℕ)^1075*100000000000000^819 ≤ 42860381498009^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244185407 10000000000 42860381498009 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349133167/10000000000 : ℝ), (-2131776657/10000000000 : ℝ), (5244185407/10000000000 : ℝ)] ![(10997431072277/25000000000000 : ℝ), (2629978841599/20000000000000 : ℝ), (42860381498009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349133167/10000000000 : ℝ)|^1075 ≤ (10997431072277/25000000000000 : ℝ)^819
        have hw : |(5349133167/10000000000 : ℝ)|=(5349133167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131776657/10000000000 : ℝ)|^1075 ≤ (2629978841599/20000000000000 : ℝ)^819
        have hw : |(-2131776657/10000000000 : ℝ)|=(2131776657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244185407/10000000000 : ℝ)|^1075 ≤ (42860381498009/100000000000000 : ℝ)^819
        have hw : |(5244185407/10000000000 : ℝ)|=(5244185407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s5_2 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (267456659/500000000 : ℝ)*x 0 + (5244185407/10000000000 : ℝ)*x 1 + (-1065888319/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267456659/500000000 : ℝ)^1075 ≤ (43989724429433/100000000000000 : ℝ)^819 := by
    have hnat : (267456659 : ℕ)^1075*100000000000000^819 ≤ 43989724429433^819*500000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267456659 500000000 43989724429433 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244185407/10000000000 : ℝ)^1075 ≤ (42860381498009/100000000000000 : ℝ)^819 := by
    have hnat : (5244185407 : ℕ)^1075*100000000000000^819 ≤ 42860381498009^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244185407 10000000000 42860381498009 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1065888319/5000000000 : ℝ)^1075 ≤ (13149894054159/100000000000000 : ℝ)^819 := by
    have hnat : (1065888319 : ℕ)^1075*100000000000000^819 ≤ 13149894054159^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065888319 5000000000 13149894054159 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267456659/500000000 : ℝ), (5244185407/10000000000 : ℝ), (-1065888319/5000000000 : ℝ)] ![(43989724429433/100000000000000 : ℝ), (42860381498009/100000000000000 : ℝ), (13149894054159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267456659/500000000 : ℝ)|^1075 ≤ (43989724429433/100000000000000 : ℝ)^819
        have hw : |(267456659/500000000 : ℝ)|=(267456659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244185407/10000000000 : ℝ)|^1075 ≤ (42860381498009/100000000000000 : ℝ)^819
        have hw : |(5244185407/10000000000 : ℝ)|=(5244185407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1065888319/5000000000 : ℝ)|^1075 ≤ (13149894054159/100000000000000 : ℝ)^819
        have hw : |(-1065888319/5000000000 : ℝ)|=(1065888319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s5_3 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4327115139/10000000000 : ℝ)*x 0 + (4153620363/10000000000 : ℝ)*x 1 + (901474589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327115139/10000000000 : ℝ)^1075 ≤ (33302949958321/100000000000000 : ℝ)^819 := by
    have hnat : (4327115139 : ℕ)^1075*100000000000000^819 ≤ 33302949958321^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327115139 10000000000 33302949958321 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153620363/10000000000 : ℝ)^1075 ≤ (6312277044403/20000000000000 : ℝ)^819 := by
    have hnat : (4153620363 : ℕ)^1075*20000000000000^819 ≤ 6312277044403^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153620363 10000000000 6312277044403 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901474589/2000000000 : ℝ)^1075 ≤ (35135664807777/100000000000000 : ℝ)^819 := by
    have hnat : (901474589 : ℕ)^1075*100000000000000^819 ≤ 35135664807777^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901474589 2000000000 35135664807777 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327115139/10000000000 : ℝ), (4153620363/10000000000 : ℝ), (901474589/2000000000 : ℝ)] ![(33302949958321/100000000000000 : ℝ), (6312277044403/20000000000000 : ℝ), (35135664807777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327115139/10000000000 : ℝ)|^1075 ≤ (33302949958321/100000000000000 : ℝ)^819
        have hw : |(4327115139/10000000000 : ℝ)|=(4327115139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153620363/10000000000 : ℝ)|^1075 ≤ (6312277044403/20000000000000 : ℝ)^819
        have hw : |(4153620363/10000000000 : ℝ)|=(4153620363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(901474589/2000000000 : ℝ)|^1075 ≤ (35135664807777/100000000000000 : ℝ)^819
        have hw : |(901474589/2000000000 : ℝ)|=(901474589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s5_4 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-255708093/1250000000 : ℝ)*x 0 + (524479311/1000000000 : ℝ)*x 1 + (2706295917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255708093/1250000000 : ℝ)^1075 ≤ (1557139961303/12500000000000 : ℝ)^819 := by
    have hnat : (255708093 : ℕ)^1075*12500000000000^819 ≤ 1557139961303^819*1250000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255708093 1250000000 1557139961303 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524479311/1000000000 : ℝ)^1075 ≤ (133959065033/312500000000 : ℝ)^819 := by
    have hnat : (524479311 : ℕ)^1075*312500000000^819 ≤ 133959065033^819*1000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524479311 1000000000 133959065033 312500000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706295917/5000000000 : ℝ)^1075 ≤ (71481567173/160000000000 : ℝ)^819 := by
    have hnat : (2706295917 : ℕ)^1075*160000000000^819 ≤ 71481567173^819*5000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706295917 5000000000 71481567173 160000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-255708093/1250000000 : ℝ), (524479311/1000000000 : ℝ), (2706295917/5000000000 : ℝ)] ![(1557139961303/12500000000000 : ℝ), (133959065033/312500000000 : ℝ), (71481567173/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-255708093/1250000000 : ℝ)|^1075 ≤ (1557139961303/12500000000000 : ℝ)^819
        have hw : |(-255708093/1250000000 : ℝ)|=(255708093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524479311/1000000000 : ℝ)|^1075 ≤ (133959065033/312500000000 : ℝ)^819
        have hw : |(524479311/1000000000 : ℝ)|=(524479311/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706295917/5000000000 : ℝ)|^1075 ≤ (71481567173/160000000000 : ℝ)^819
        have hw : |(2706295917/5000000000 : ℝ)|=(2706295917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s5_5 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530560819/1000000000 : ℝ)*x 0 + (-1963370197/10000000000 : ℝ)*x 1 + (5412591843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530560819/1000000000 : ℝ)^1075 ≤ (8704100694931/20000000000000 : ℝ)^819 := by
    have hnat : (530560819 : ℕ)^1075*20000000000000^819 ≤ 8704100694931^819*1000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530560819 1000000000 8704100694931 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1963370197/10000000000 : ℝ)^1075 ≤ (184429952011/1562500000000 : ℝ)^819 := by
    have hnat : (1963370197 : ℕ)^1075*1562500000000^819 ≤ 184429952011^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963370197 10000000000 184429952011 1562500000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412591843/10000000000 : ℝ)^1075 ≤ (5584497447579/12500000000000 : ℝ)^819 := by
    have hnat : (5412591843 : ℕ)^1075*12500000000000^819 ≤ 5584497447579^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412591843 10000000000 5584497447579 12500000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530560819/1000000000 : ℝ), (-1963370197/10000000000 : ℝ), (5412591843/10000000000 : ℝ)] ![(8704100694931/20000000000000 : ℝ), (184429952011/1562500000000 : ℝ), (5584497447579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530560819/1000000000 : ℝ)|^1075 ≤ (8704100694931/20000000000000 : ℝ)^819
        have hw : |(530560819/1000000000 : ℝ)|=(530560819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1963370197/10000000000 : ℝ)|^1075 ≤ (184429952011/1562500000000 : ℝ)^819
        have hw : |(-1963370197/10000000000 : ℝ)|=(1963370197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412591843/10000000000 : ℝ)|^1075 ≤ (5584497447579/12500000000000 : ℝ)^819
        have hw : |(5412591843/10000000000 : ℝ)|=(5412591843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s5_6 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (33160051/62500000 : ℝ)*x 0 + (541259187/1000000000 : ℝ)*x 1 + (-9816851/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33160051/62500000 : ℝ)^1075 ≤ (43520503151653/100000000000000 : ℝ)^819 := by
    have hnat : (33160051 : ℕ)^1075*100000000000000^819 ≤ 43520503151653^819*62500000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33160051 62500000 43520503151653 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541259187/1000000000 : ℝ)^1075 ≤ (44675979873153/100000000000000 : ℝ)^819 := by
    have hnat : (541259187 : ℕ)^1075*100000000000000^819 ≤ 44675979873153^819*1000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541259187 1000000000 44675979873153 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9816851/50000000 : ℝ)^1075 ≤ (11803516952377/100000000000000 : ℝ)^819 := by
    have hnat : (9816851 : ℕ)^1075*100000000000000^819 ≤ 11803516952377^819*50000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9816851 50000000 11803516952377 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33160051/62500000 : ℝ), (541259187/1000000000 : ℝ), (-9816851/50000000 : ℝ)] ![(43520503151653/100000000000000 : ℝ), (44675979873153/100000000000000 : ℝ), (11803516952377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33160051/62500000 : ℝ)|^1075 ≤ (43520503151653/100000000000000 : ℝ)^819
        have hw : |(33160051/62500000 : ℝ)|=(33160051/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541259187/1000000000 : ℝ)|^1075 ≤ (44675979873153/100000000000000 : ℝ)^819
        have hw : |(541259187/1000000000 : ℝ)|=(541259187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-9816851/50000000 : ℝ)|^1075 ≤ (11803516952377/100000000000000 : ℝ)^819
        have hw : |(-9816851/50000000 : ℝ)|=(9816851/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1340_s5_7 (p : ℝ) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4327140973/10000000000 : ℝ)*x 0 + (4506101069/10000000000 : ℝ)*x 1 + (830979773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327140973/10000000000 : ℝ)^1075 ≤ (6660642186901/20000000000000 : ℝ)^819 := by
    have hnat : (4327140973 : ℕ)^1075*20000000000000^819 ≤ 6660642186901^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327140973 10000000000 6660642186901 20000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506101069/10000000000 : ℝ)^1075 ≤ (35122651884711/100000000000000 : ℝ)^819 := by
    have hnat : (4506101069 : ℕ)^1075*100000000000000^819 ≤ 35122651884711^819*10000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506101069 10000000000 35122651884711 100000000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830979773/2000000000 : ℝ)^1075 ≤ (1973383572369/6250000000000 : ℝ)^819 := by
    have hnat : (830979773 : ℕ)^1075*6250000000000^819 ≤ 1973383572369^819*2000000000^1075 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830979773 2000000000 1973383572369 6250000000000 1075 819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1075/256 : ℝ)) 1075 819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327140973/10000000000 : ℝ), (4506101069/10000000000 : ℝ), (830979773/2000000000 : ℝ)] ![(6660642186901/20000000000000 : ℝ), (35122651884711/100000000000000 : ℝ), (1973383572369/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327140973/10000000000 : ℝ)|^1075 ≤ (6660642186901/20000000000000 : ℝ)^819
        have hw : |(4327140973/10000000000 : ℝ)|=(4327140973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506101069/10000000000 : ℝ)|^1075 ≤ (35122651884711/100000000000000 : ℝ)^819
        have hw : |(4506101069/10000000000 : ℝ)|=(4506101069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830979773/2000000000 : ℝ)|^1075 ≤ (1973383572369/6250000000000 : ℝ)^819
        have hw : |(830979773/2000000000 : ℝ)|=(830979773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1340_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (348/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7357/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11093/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11093/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11093/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11093/100000 : ℝ) ^ (4299/1024 : ℝ) ≤ (9792294794821171/100000000000000000000 : ℝ) := by
    have hpowers : (11093/100000 : ℝ)^4299 ≤ (9792294794821171/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11093 : ℕ)^4299*100000000000000000000^1024 ≤ 9792294794821171^1024*100000^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11093 100000 9792294794821171 100000000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11093/100000 : ℝ)) (X := (9792294794821171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (4299/1024 : ℝ) ≤ (812013595188763/2500000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^4299 ≤ (812013595188763/2500000000000000000 : ℝ)^1024 := by
      have hnat : (369 : ℕ)^4299*2500000000000000000^1024 ≤ 812013595188763^1024*2500^4299 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 812013595188763 2500000000000000000 4299 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (812013595188763/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009792294794821171/50000000000000000000 : ℝ) ≤ (10000466460197101/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (50009792294794821171/50000000000000000000 : ℝ)^1024 ≤ (10000466460197101/10000000000000000 : ℝ)^4299 := by
      have hnat : (50009792294794821171 : ℕ)^1024*10000000000000000^4299 ≤ 10000466460197101^4299*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009792294794821171 50000000000000000000 10000466460197101 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000466460197101/10000000000000000 : ℝ)) (X := (50009792294794821171/50000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042272838602371691/100000000000000000000 : ℝ) ≤ (2000201351097449/2000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (100042272838602371691/100000000000000000000 : ℝ)^1024 ≤ (2000201351097449/2000000000000000 : ℝ)^4299 := by
      have hnat : (100042272838602371691 : ℕ)^1024*2000000000000000^4299 ≤ 2000201351097449^4299*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042272838602371691 100000000000000000000 2000201351097449 2000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000201351097449/2000000000000000 : ℝ)) (X := (100042272838602371691/100000000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250812013595188763/1250000000000000000 : ℝ) ≤ (10001547050777389/10000000000000000 : ℝ) ^ (4299/1024 : ℝ) := by
    have hpowers : (1250812013595188763/1250000000000000000 : ℝ)^1024 ≤ (10001547050777389/10000000000000000 : ℝ)^4299 := by
      have hnat : (1250812013595188763 : ℕ)^1024*10000000000000000^4299 ≤ 10001547050777389^4299*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250812013595188763 1250000000000000000 10001547050777389 10000000000000000 1024 4299 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001547050777389/10000000000000000 : ℝ)) (X := (1250812013595188763/1250000000000000000 : ℝ)) (by norm_num) 4299 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9792294794821171/100000000000000000000 : ℝ) ≤ ((36659723518235634583/36670000000000000000 : ℝ)+2*(16884227817/11459375000000 : ℝ)*(11093/100000 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (36659723518235634583/36670000000000000000 : ℝ)+2*(16884227817/11459375000000 : ℝ)*(11093/100000 : ℝ)=(10000466460197101/10000000000000000 : ℝ) by norm_num, show 1+2*(9792294794821171/100000000000000000000 : ℝ)=(50009792294794821171/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(812013595188763/2500000000000000000 : ℝ)+(9792294794821171/100000000000000000000 : ℝ) ≤ ((36659723518235634583/36670000000000000000 : ℝ)+(16884227817/11459375000000 : ℝ)*((369/2500 : ℝ)+(11093/100000 : ℝ)))^(4299/1024 : ℝ) := by
    rw [show (36659723518235634583/36670000000000000000 : ℝ)+(16884227817/11459375000000 : ℝ)*((369/2500 : ℝ)+(11093/100000 : ℝ))=(2000201351097449/2000000000000000 : ℝ) by norm_num, show 1+(812013595188763/2500000000000000000 : ℝ)+(9792294794821171/100000000000000000000 : ℝ)=(100042272838602371691/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(812013595188763/2500000000000000000 : ℝ) ≤ ((36659723518235634583/36670000000000000000 : ℝ)+2*(16884227817/11459375000000 : ℝ)*(369/2500 : ℝ))^(4299/1024 : ℝ) := by
    rw [show (36659723518235634583/36670000000000000000 : ℝ)+2*(16884227817/11459375000000 : ℝ)*(369/2500 : ℝ)=(10001547050777389/10000000000000000 : ℝ) by norm_num, show 1+2*(812013595188763/2500000000000000000 : ℝ)=(1250812013595188763/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36659723518235634583/36670000000000000000 : ℝ)*(X 1 0+X 2 0)+(16884227817/11459375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (36659723518235634583/36670000000000000000 : ℝ)) (alpha := (16884227817/11459375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36659723518235634583/36670000000000000000 : ℝ)*(X 0 1+X 2 1)+(16884227817/11459375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (36659723518235634583/36670000000000000000 : ℝ)) (alpha := (16884227817/11459375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36659723518235634583/36670000000000000000 : ℝ)*(X 0 2+X 1 2)+(16884227817/11459375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4299/1024 : ℝ)) (lo := (11093/100000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (36659723518235634583/36670000000000000000 : ℝ)) (alpha := (16884227817/11459375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2045652353/10000000000 : ℝ)*X 0 0+(1082640541/2000000000 : ℝ)*X 0 1+(2622092703/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349133167/10000000000 : ℝ)*X 1 0+(-2131776657/10000000000 : ℝ)*X 1 1+(5244185407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267456659/500000000 : ℝ)*X 2 0+(5244185407/10000000000 : ℝ)*X 2 1+(-1065888319/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327115139/10000000000 : ℝ)*X 0 0+(4153620363/10000000000 : ℝ)*X 0 1+(901474589/2000000000 : ℝ)*X 0 2+(4327115139/10000000000 : ℝ)*X 1 0+(4153620363/10000000000 : ℝ)*X 1 1+(901474589/2000000000 : ℝ)*X 1 2+(4327115139/10000000000 : ℝ)*X 2 0+(4153620363/10000000000 : ℝ)*X 2 1+(901474589/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-255708093/1250000000 : ℝ)*X 0 0+(524479311/1000000000 : ℝ)*X 0 1+(2706295917/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530560819/1000000000 : ℝ)*X 1 0+(-1963370197/10000000000 : ℝ)*X 1 1+(5412591843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33160051/62500000 : ℝ)*X 2 0+(541259187/1000000000 : ℝ)*X 2 1+(-9816851/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327140973/10000000000 : ℝ)*X 0 0+(4506101069/10000000000 : ℝ)*X 0 1+(830979773/2000000000 : ℝ)*X 0 2+(4327140973/10000000000 : ℝ)*X 1 0+(4506101069/10000000000 : ℝ)*X 1 1+(830979773/2000000000 : ℝ)*X 1 2+(4327140973/10000000000 : ℝ)*X 2 0+(4506101069/10000000000 : ℝ)*X 2 1+(830979773/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1340_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (176673233442922785933507/18335000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1829239007/100000000000000 : ℝ)*(base19) + (171967699/10000000000000 : ℝ)*(base23) + (33148899/50000000000000 : ℝ)*(lower2) + (7396941/3125000000000 : ℝ)*(upper3) + (339979/200000000000 : ℝ)*(upper5) + (2185875279434813/50000000000000 : ℝ)*(major0) + (2185875279434813/50000000000000 : ℝ)*(major1) + (2185875279434813/50000000000000 : ℝ)*(major2) + (2958296184859843/50000000000000 : ℝ)*(sp0) + (2958314089050117/50000000000000 : ℝ)*(sp1) + (5916628287662251/100000000000000 : ℝ)*(sp2) + (565370359968521/20000000000000 : ℝ)*(sp3) + (7527523911/20000000000000 : ℝ)*(sp4) + (18989362539/100000000000000 : ℝ)*(sp7) + (353358848650643/12500000000000 : ℝ)*(f.failure) + (5916630007339241/100000000000000 : ℝ)*(f.sum) + (6295396882963/2291875000000000000000000000 : ℝ)*base65 + (25963651694136862021/1833500000000000000000000000000000 : ℝ)*base68 + (690451442553137979/1833500000000000000000000000000000 : ℝ)*base69 + (14098814438174137979/1833500000000000000000000000000000 : ℝ)*base71 + (29973288112659/4583750000000000000000000000 : ℝ)*base74 + (10131358497588862021/1833500000000000000000000000000000 : ℝ)*base76 + (1781861796657137979/1833500000000000000000000000000000 : ℝ)*base77 + (10611306027716362021/1833500000000000000000000000000000 : ℝ)*base80 + (56203172025113/9167500000000000000000000000 : ℝ)*base82 + (9183617/1250000000000000000000 : ℝ)*base89 + (9183617/1250000000000000000000 : ℝ)*base91 + (9183617/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1945812328809084080136787581/458375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (825498341/100000000000000 : ℝ)*(base19) + (199306743/25000000000000 : ℝ)*(base23) + (106905521/100000000000000 : ℝ)*(upper3) + (976449/100000000000000 : ℝ)*(lower4) + (84560873/100000000000000 : ℝ)*(upper5) + (2201720676328831/50000000000000 : ℝ)*(major0) + (2201720676328831/50000000000000 : ℝ)*(major1) + (2201720676328831/50000000000000 : ℝ)*(major2) + (8228540297/50000000000000 : ℝ)*(sp1) + (52794227/312500000000 : ℝ)*(sp2) + (5959519805079179/100000000000000 : ℝ)*(sp4) + (1489875630625061/25000000000000 : ℝ)*(sp5) + (2979751056849783/50000000000000 : ℝ)*(sp6) + (2847362758735373/100000000000000 : ℝ)*(sp7) + (2847362758735373/100000000000000 : ℝ)*(f.failure) + (5959519805079179/100000000000000 : ℝ)*(f.sum) + (135069645742927/18335000000000000000000000000 : ℝ)*base66 + (4048141213674537527/1833500000000000000000000000000000 : ℝ)*base68 + (19735093944741462473/1833500000000000000000000000000000 : ℝ)*base69 + (10651895421815462473/1833500000000000000000000000000000 : ℝ)*base71 + (174448067337357/18335000000000000000000000000 : ℝ)*base74 + (16913746014547462473/1833500000000000000000000000000000 : ℝ)*base75 + (13281511752448462473/1833500000000000000000000000000000 : ℝ)*base77 + (7229724235290462473/1833500000000000000000000000000000 : ℝ)*base79 + (64548127098547/18335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (96652513/10000000000000000000000 : ℝ)*base90 + (96652513/10000000000000000000000 : ℝ)*base92 + (96652513/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1340_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11093/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1340_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1340_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1007/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1340_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1340_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1340_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4299/1024 : ℝ) ≤ p) (hpb : p ≤ (1075/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154649819/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1007/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4919/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (348/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7357/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1340_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
