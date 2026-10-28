-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:18.320205+00:00
-- url     : https://prove2.me/submissions/d5f253b3-27fc-4f10-b6ee-718bfe67ac57

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
theorem support_rectangle_w1084_s6_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194893041/10000000000 : ℝ)*x 0 + (2697274141/5000000000 : ℝ)*x 1 + (329018757/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194893041/10000000000 : ℝ)^8277 ≤ (13331534479887/100000000000000 : ℝ)^6229 := by
    have hnat : (2194893041 : ℕ)^8277*100000000000000^6229 ≤ 13331534479887^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194893041 10000000000 13331534479887 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697274141/5000000000 : ℝ)^8277 ≤ (44037840366233/100000000000000 : ℝ)^6229 := by
    have hnat : (2697274141 : ℕ)^8277*100000000000000^6229 ≤ 44037840366233^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697274141 5000000000 44037840366233 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329018757/625000000 : ℝ)^8277 ≤ (852612502803/2000000000000 : ℝ)^6229 := by
    have hnat : (329018757 : ℕ)^8277*2000000000000^6229 ≤ 852612502803^6229*625000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329018757 625000000 852612502803 2000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194893041/10000000000 : ℝ), (2697274141/5000000000 : ℝ), (329018757/625000000 : ℝ)] ![(13331534479887/100000000000000 : ℝ), (44037840366233/100000000000000 : ℝ), (852612502803/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194893041/10000000000 : ℝ)|^8277 ≤ (13331534479887/100000000000000 : ℝ)^6229
        have hw : |(-2194893041/10000000000 : ℝ)|=(2194893041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697274141/5000000000 : ℝ)|^8277 ≤ (44037840366233/100000000000000 : ℝ)^6229
        have hw : |(2697274141/5000000000 : ℝ)|=(2697274141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329018757/625000000 : ℝ)|^8277 ≤ (852612502803/2000000000000 : ℝ)^6229
        have hw : |(329018757/625000000 : ℝ)|=(329018757/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s6_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345060991/10000000000 : ℝ)*x 0 + (-28262241/125000000 : ℝ)*x 1 + (5264300101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345060991/10000000000 : ℝ)^8277 ≤ (43501843262547/100000000000000 : ℝ)^6229 := by
    have hnat : (5345060991 : ℕ)^8277*100000000000000^6229 ≤ 43501843262547^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345060991 10000000000 43501843262547 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28262241/125000000 : ℝ)^8277 ≤ (3466882924307/25000000000000 : ℝ)^6229 := by
    have hnat : (28262241 : ℕ)^8277*25000000000000^6229 ≤ 3466882924307^6229*125000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28262241 125000000 3466882924307 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264300101/10000000000 : ℝ)^8277 ≤ (42630625021783/100000000000000 : ℝ)^6229 := by
    have hnat : (5264300101 : ℕ)^8277*100000000000000^6229 ≤ 42630625021783^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264300101 10000000000 42630625021783 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345060991/10000000000 : ℝ), (-28262241/125000000 : ℝ), (5264300101/10000000000 : ℝ)] ![(43501843262547/100000000000000 : ℝ), (3466882924307/25000000000000 : ℝ), (42630625021783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345060991/10000000000 : ℝ)|^8277 ≤ (43501843262547/100000000000000 : ℝ)^6229
        have hw : |(5345060991/10000000000 : ℝ)|=(5345060991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28262241/125000000 : ℝ)|^8277 ≤ (3466882924307/25000000000000 : ℝ)^6229
        have hw : |(-28262241/125000000 : ℝ)|=(28262241/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264300101/10000000000 : ℝ)|^8277 ≤ (42630625021783/100000000000000 : ℝ)^6229
        have hw : |(5264300101/10000000000 : ℝ)|=(5264300101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s6_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345060979/10000000000 : ℝ)*x 0 + (131607503/250000000 : ℝ)*x 1 + (-282622409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345060979/10000000000 : ℝ)^8277 ≤ (10875460783193/25000000000000 : ℝ)^6229 := by
    have hnat : (5345060979 : ℕ)^8277*25000000000000^6229 ≤ 10875460783193^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345060979 10000000000 10875460783193 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131607503/250000000 : ℝ)^8277 ≤ (21315312613117/50000000000000 : ℝ)^6229 := by
    have hnat : (131607503 : ℕ)^8277*50000000000000^6229 ≤ 21315312613117^6229*250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131607503 250000000 21315312613117 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282622409/1250000000 : ℝ)^8277 ≤ (3466882908007/25000000000000 : ℝ)^6229 := by
    have hnat : (282622409 : ℕ)^8277*25000000000000^6229 ≤ 3466882908007^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282622409 1250000000 3466882908007 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345060979/10000000000 : ℝ), (131607503/250000000 : ℝ), (-282622409/1250000000 : ℝ)] ![(10875460783193/25000000000000 : ℝ), (21315312613117/50000000000000 : ℝ), (3466882908007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345060979/10000000000 : ℝ)|^8277 ≤ (10875460783193/25000000000000 : ℝ)^6229
        have hw : |(5345060979/10000000000 : ℝ)|=(5345060979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131607503/250000000 : ℝ)|^8277 ≤ (21315312613117/50000000000000 : ℝ)^6229
        have hw : |(131607503/250000000 : ℝ)|=(131607503/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-282622409/1250000000 : ℝ)|^8277 ≤ (3466882908007/25000000000000 : ℝ)^6229
        have hw : |(-282622409/1250000000 : ℝ)|=(282622409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s6_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093221167/2500000000 : ℝ)*x 0 + (1061671683/2500000000 : ℝ)*x 1 + (450286749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093221167/2500000000 : ℝ)^8277 ≤ (33316397848209/100000000000000 : ℝ)^6229 := by
    have hnat : (1093221167 : ℕ)^8277*100000000000000^6229 ≤ 33316397848209^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093221167 2500000000 33316397848209 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061671683/2500000000 : ℝ)^8277 ≤ (32044892869561/100000000000000 : ℝ)^6229 := by
    have hnat : (1061671683 : ℕ)^8277*100000000000000^6229 ≤ 32044892869561^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061671683 2500000000 32044892869561 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450286749/1000000000 : ℝ)^8277 ≤ (17319354633657/50000000000000 : ℝ)^6229 := by
    have hnat : (450286749 : ℕ)^8277*50000000000000^6229 ≤ 17319354633657^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450286749 1000000000 17319354633657 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093221167/2500000000 : ℝ), (1061671683/2500000000 : ℝ), (450286749/1000000000 : ℝ)] ![(33316397848209/100000000000000 : ℝ), (32044892869561/100000000000000 : ℝ), (17319354633657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093221167/2500000000 : ℝ)|^8277 ≤ (33316397848209/100000000000000 : ℝ)^6229
        have hw : |(1093221167/2500000000 : ℝ)|=(1093221167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061671683/2500000000 : ℝ)|^8277 ≤ (32044892869561/100000000000000 : ℝ)^6229
        have hw : |(1061671683/2500000000 : ℝ)|=(1061671683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450286749/1000000000 : ℝ)|^8277 ≤ (17319354633657/50000000000000 : ℝ)^6229
        have hw : |(450286749/1000000000 : ℝ)|=(450286749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s6_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097449117/5000000000 : ℝ)*x 0 + (1052925801/2000000000 : ℝ)*x 1 + (5394218151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097449117/5000000000 : ℝ)^8277 ≤ (13331576392033/100000000000000 : ℝ)^6229 := by
    have hnat : (1097449117 : ℕ)^8277*100000000000000^6229 ≤ 13331576392033^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097449117 5000000000 13331576392033 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052925801/2000000000 : ℝ)^8277 ≤ (5329270531997/12500000000000 : ℝ)^6229 := by
    have hnat : (1052925801 : ℕ)^8277*12500000000000^6229 ≤ 5329270531997^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052925801 2000000000 5329270531997 12500000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394218151/10000000000 : ℝ)^8277 ≤ (8806851868019/20000000000000 : ℝ)^6229 := by
    have hnat : (5394218151 : ℕ)^8277*20000000000000^6229 ≤ 8806851868019^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394218151 10000000000 8806851868019 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097449117/5000000000 : ℝ), (1052925801/2000000000 : ℝ), (5394218151/10000000000 : ℝ)] ![(13331576392033/100000000000000 : ℝ), (5329270531997/12500000000000 : ℝ), (8806851868019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097449117/5000000000 : ℝ)|^8277 ≤ (13331576392033/100000000000000 : ℝ)^6229
        have hw : |(-1097449117/5000000000 : ℝ)|=(1097449117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052925801/2000000000 : ℝ)|^8277 ≤ (5329270531997/12500000000000 : ℝ)^6229
        have hw : |(1052925801/2000000000 : ℝ)|=(1052925801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394218151/10000000000 : ℝ)|^8277 ≤ (8806851868019/20000000000000 : ℝ)^6229
        have hw : |(5394218151/10000000000 : ℝ)|=(5394218151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s6_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312207553/10000000000 : ℝ)*x 0 + (-1065530603/5000000000 : ℝ)*x 1 + (1348554537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312207553/10000000000 : ℝ)^8277 ≤ (43146906660853/100000000000000 : ℝ)^6229 := by
    have hnat : (5312207553 : ℕ)^8277*100000000000000^6229 ≤ 43146906660853^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312207553 10000000000 43146906660853 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065530603/5000000000 : ℝ)^8277 ≤ (6409417007249/50000000000000 : ℝ)^6229 := by
    have hnat : (1065530603 : ℕ)^8277*50000000000000^6229 ≤ 6409417007249^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065530603 5000000000 6409417007249 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348554537/2500000000 : ℝ)^8277 ≤ (22017129653777/50000000000000 : ℝ)^6229 := by
    have hnat : (1348554537 : ℕ)^8277*50000000000000^6229 ≤ 22017129653777^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348554537 2500000000 22017129653777 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312207553/10000000000 : ℝ), (-1065530603/5000000000 : ℝ), (1348554537/2500000000 : ℝ)] ![(43146906660853/100000000000000 : ℝ), (6409417007249/50000000000000 : ℝ), (22017129653777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312207553/10000000000 : ℝ)|^8277 ≤ (43146906660853/100000000000000 : ℝ)^6229
        have hw : |(5312207553/10000000000 : ℝ)|=(5312207553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065530603/5000000000 : ℝ)|^8277 ≤ (6409417007249/50000000000000 : ℝ)^6229
        have hw : |(-1065530603/5000000000 : ℝ)|=(1065530603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348554537/2500000000 : ℝ)|^8277 ≤ (22017129653777/50000000000000 : ℝ)^6229
        have hw : |(1348554537/2500000000 : ℝ)|=(1348554537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s6_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062441507/2000000000 : ℝ)*x 0 + (1348554537/2500000000 : ℝ)*x 1 + (-2131061229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062441507/2000000000 : ℝ)^8277 ≤ (8629381293317/20000000000000 : ℝ)^6229 := by
    have hnat : (1062441507 : ℕ)^8277*20000000000000^6229 ≤ 8629381293317^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062441507 2000000000 8629381293317 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348554537/2500000000 : ℝ)^8277 ≤ (22017129653777/50000000000000 : ℝ)^6229 := by
    have hnat : (1348554537 : ℕ)^8277*50000000000000^6229 ≤ 22017129653777^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348554537 2500000000 22017129653777 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131061229/10000000000 : ℝ)^8277 ≤ (200294284349/1562500000000 : ℝ)^6229 := by
    have hnat : (2131061229 : ℕ)^8277*1562500000000^6229 ≤ 200294284349^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131061229 10000000000 200294284349 1562500000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062441507/2000000000 : ℝ), (1348554537/2500000000 : ℝ), (-2131061229/10000000000 : ℝ)] ![(8629381293317/20000000000000 : ℝ), (22017129653777/50000000000000 : ℝ), (200294284349/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062441507/2000000000 : ℝ)|^8277 ≤ (8629381293317/20000000000000 : ℝ)^6229
        have hw : |(1062441507/2000000000 : ℝ)|=(1062441507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348554537/2500000000 : ℝ)|^8277 ≤ (22017129653777/50000000000000 : ℝ)^6229
        have hw : |(1348554537/2500000000 : ℝ)|=(1348554537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131061229/10000000000 : ℝ)|^8277 ≤ (200294284349/1562500000000 : ℝ)^6229
        have hw : |(-2131061229/10000000000 : ℝ)|=(2131061229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s6_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874578959/2000000000 : ℝ)*x 0 + (4502220521/10000000000 : ℝ)*x 1 + (169893441/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874578959/2000000000 : ℝ)^8277 ≤ (33316500372227/100000000000000 : ℝ)^6229 := by
    have hnat : (874578959 : ℕ)^8277*100000000000000^6229 ≤ 33316500372227^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874578959 2000000000 33316500372227 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502220521/10000000000 : ℝ)^8277 ≤ (34632096239163/100000000000000 : ℝ)^6229 := by
    have hnat : (4502220521 : ℕ)^8277*100000000000000^6229 ≤ 34632096239163^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502220521 10000000000 34632096239163 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169893441/400000000 : ℝ)^8277 ≤ (6410280675459/20000000000000 : ℝ)^6229 := by
    have hnat : (169893441 : ℕ)^8277*20000000000000^6229 ≤ 6410280675459^6229*400000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169893441 400000000 6410280675459 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874578959/2000000000 : ℝ), (4502220521/10000000000 : ℝ), (169893441/400000000 : ℝ)] ![(33316500372227/100000000000000 : ℝ), (34632096239163/100000000000000 : ℝ), (6410280675459/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874578959/2000000000 : ℝ)|^8277 ≤ (33316500372227/100000000000000 : ℝ)^6229
        have hw : |(874578959/2000000000 : ℝ)|=(874578959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502220521/10000000000 : ℝ)|^8277 ≤ (34632096239163/100000000000000 : ℝ)^6229
        have hw : |(4502220521/10000000000 : ℝ)|=(4502220521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169893441/400000000 : ℝ)|^8277 ≤ (6410280675459/20000000000000 : ℝ)^6229
        have hw : |(169893441/400000000 : ℝ)|=(169893441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5633/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (561/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2813/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2813/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11227/100000 : ℝ) ^ (2069/512 : ℝ) ≤ (2904897810585293/20000000000000000000 : ℝ) := by
    have hpowers : (11227/100000 : ℝ)^2069 ≤ (2904897810585293/20000000000000000000 : ℝ)^512 := by
      have hnat : (11227 : ℕ)^2069*20000000000000000000^512 ≤ 2904897810585293^512*100000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11227 100000 2904897810585293 20000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11227/100000 : ℝ)) (X := (2904897810585293/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2813/20000 : ℝ) ^ (2069/512 : ℝ) ≤ (36109324563468107/100000000000000000000 : ℝ) := by
    have hpowers : (2813/20000 : ℝ)^2069 ≤ (36109324563468107/100000000000000000000 : ℝ)^512 := by
      have hnat : (2813 : ℕ)^2069*100000000000000000000^512 ≤ 36109324563468107^512*20000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 20000 36109324563468107 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/20000 : ℝ)) (X := (36109324563468107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002904897810585293/10000000000000000000 : ℝ) ≤ (5000359387419181/5000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (10002904897810585293/10000000000000000000 : ℝ)^512 ≤ (5000359387419181/5000000000000000 : ℝ)^2069 := by
      have hnat : (10002904897810585293 : ℕ)^512*5000000000000000^2069 ≤ 5000359387419181^2069*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002904897810585293 10000000000000000000 5000359387419181 5000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000359387419181/5000000000000000 : ℝ)) (X := (10002904897810585293/10000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012658453404098643/25000000000000000000 : ℝ) ≤ (1000125275857489/1000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (25012658453404098643/25000000000000000000 : ℝ)^512 ≤ (1000125275857489/1000000000000000 : ℝ)^2069 := by
      have hnat : (25012658453404098643 : ℕ)^512*1000000000000000^2069 ≤ 1000125275857489^2069*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012658453404098643 25000000000000000000 1000125275857489 1000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000125275857489/1000000000000000 : ℝ)) (X := (25012658453404098643/25000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036109324563468107/50000000000000000000 : ℝ) ≤ (5000893371155709/5000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50036109324563468107/50000000000000000000 : ℝ)^512 ≤ (5000893371155709/5000000000000000 : ℝ)^2069 := by
      have hnat : (50036109324563468107 : ℕ)^512*5000000000000000^2069 ≤ 5000893371155709^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036109324563468107 50000000000000000000 5000893371155709 5000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000893371155709/5000000000000000 : ℝ)) (X := (50036109324563468107/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2904897810585293/20000000000000000000 : ℝ) ≤ ((644773859367528901/645000000000000000 : ℝ)+2*(3033998503/1612500000000 : ℝ)*(11227/100000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (644773859367528901/645000000000000000 : ℝ)+2*(3033998503/1612500000000 : ℝ)*(11227/100000 : ℝ)=(5000359387419181/5000000000000000 : ℝ) by norm_num, show 1+2*(2904897810585293/20000000000000000000 : ℝ)=(10002904897810585293/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36109324563468107/100000000000000000000 : ℝ)+(2904897810585293/20000000000000000000 : ℝ) ≤ ((644773859367528901/645000000000000000 : ℝ)+(3033998503/1612500000000 : ℝ)*((2813/20000 : ℝ)+(11227/100000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (644773859367528901/645000000000000000 : ℝ)+(3033998503/1612500000000 : ℝ)*((2813/20000 : ℝ)+(11227/100000 : ℝ))=(1000125275857489/1000000000000000 : ℝ) by norm_num, show 1+(36109324563468107/100000000000000000000 : ℝ)+(2904897810585293/20000000000000000000 : ℝ)=(25012658453404098643/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36109324563468107/100000000000000000000 : ℝ) ≤ ((644773859367528901/645000000000000000 : ℝ)+2*(3033998503/1612500000000 : ℝ)*(2813/20000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (644773859367528901/645000000000000000 : ℝ)+2*(3033998503/1612500000000 : ℝ)*(2813/20000 : ℝ)=(5000893371155709/5000000000000000 : ℝ) by norm_num, show 1+2*(36109324563468107/100000000000000000000 : ℝ)=(50036109324563468107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (644773859367528901/645000000000000000 : ℝ)*(X 1 0+X 2 0)+(3033998503/1612500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (644773859367528901/645000000000000000 : ℝ)) (alpha := (3033998503/1612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (644773859367528901/645000000000000000 : ℝ)*(X 0 1+X 2 1)+(3033998503/1612500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (644773859367528901/645000000000000000 : ℝ)) (alpha := (3033998503/1612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (644773859367528901/645000000000000000 : ℝ)*(X 0 2+X 1 2)+(3033998503/1612500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (11227/100000 : ℝ)) (hi := (2813/20000 : ℝ)) (c := (644773859367528901/645000000000000000 : ℝ)) (alpha := (3033998503/1612500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2194893041/10000000000 : ℝ)*X 0 0+(2697274141/5000000000 : ℝ)*X 0 1+(329018757/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345060991/10000000000 : ℝ)*X 1 0+(-28262241/125000000 : ℝ)*X 1 1+(5264300101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345060979/10000000000 : ℝ)*X 2 0+(131607503/250000000 : ℝ)*X 2 1+(-282622409/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093221167/2500000000 : ℝ)*X 0 0+(1061671683/2500000000 : ℝ)*X 0 1+(450286749/1000000000 : ℝ)*X 0 2+(1093221167/2500000000 : ℝ)*X 1 0+(1061671683/2500000000 : ℝ)*X 1 1+(450286749/1000000000 : ℝ)*X 1 2+(1093221167/2500000000 : ℝ)*X 2 0+(1061671683/2500000000 : ℝ)*X 2 1+(450286749/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1097449117/5000000000 : ℝ)*X 0 0+(1052925801/2000000000 : ℝ)*X 0 1+(5394218151/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312207553/10000000000 : ℝ)*X 1 0+(-1065530603/5000000000 : ℝ)*X 1 1+(1348554537/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062441507/2000000000 : ℝ)*X 2 0+(1348554537/2500000000 : ℝ)*X 2 1+(-2131061229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874578959/2000000000 : ℝ)*X 0 0+(4502220521/10000000000 : ℝ)*X 0 1+(169893441/400000000 : ℝ)*X 0 2+(874578959/2000000000 : ℝ)*X 1 0+(4502220521/10000000000 : ℝ)*X 1 1+(169893441/400000000 : ℝ)*X 1 2+(874578959/2000000000 : ℝ)*X 2 0+(4502220521/10000000000 : ℝ)*X 2 1+(169893441/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1259193604451633429559/215000000000000000000000000 : ℝ) := by norm_num
    linear_combination (311802421/25000000000000 : ℝ)*(base19) + (1139589131/100000000000000 : ℝ)*(base23) + (48310579/100000000000000 : ℝ)*(lower2) + (73574701/50000000000000 : ℝ)*(upper3) + (17992171/20000000000000 : ℝ)*(upper5) + (5790624130578081/100000000000000 : ℝ)*(major0) + (5790624130578081/100000000000000 : ℝ)*(major1) + (5790624130578081/100000000000000 : ℝ)*(major2) + (7677685970957877/100000000000000 : ℝ)*(sp0) + (383885910497551/5000000000000 : ℝ)*(sp1) + (7677718317571573/100000000000000 : ℝ)*(sp2) + (3903510396128317/100000000000000 : ℝ)*(sp3) + (33486202827/100000000000000 : ℝ)*(sp4) + (3642528663/20000000000000 : ℝ)*(sp7) + (243970538048227/6250000000000 : ℝ)*(f.failure) + (14995545814767/195312500000 : ℝ)*(f.sum) + (280347478071/107500000000000000000000000 : ℝ)*base66 + (96199050671393673/21500000000000000000000000000000 : ℝ)*base68 + (222810194321606327/21500000000000000000000000000000 : ℝ)*base69 + (523096013879106327/21500000000000000000000000000000 : ℝ)*base71 + (74696884537/215000000000000000000000000 : ℝ)*base74 + (544347600936893673/21500000000000000000000000000000 : ℝ)*base76 + (311121297218606327/21500000000000000000000000000000 : ℝ)*base77 + (144586398357893673/21500000000000000000000000000000 : ℝ)*base80 + (688937795613/215000000000000000000000000 : ℝ)*base81 + (108609/25000000000000000000 : ℝ)*base90 + (108609/25000000000000000000 : ℝ)*base92 + (108609/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41977925487266905701447189/5375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87966557/5000000000000 : ℝ)*(base19) + (1781698141/100000000000000 : ℝ)*(base23) + (88172091/50000000000000 : ℝ)*(upper3) + (14259213/50000000000000 : ℝ)*(lower4) + (1947779/1000000000000 : ℝ)*(upper5) + (2910010158275089/50000000000000 : ℝ)*(major0) + (2910010158275089/50000000000000 : ℝ)*(major1) + (2910010158275089/50000000000000 : ℝ)*(major2) + (48619138771/100000000000000 : ℝ)*(sp1) + (9556625139/20000000000000 : ℝ)*(sp2) + (3858347722677239/50000000000000 : ℝ)*(sp4) + (7716645066884567/100000000000000 : ℝ)*(sp5) + (7716645880530641/100000000000000 : ℝ)*(sp6) + (78466898548353/2000000000000 : ℝ)*(sp7) + (78466898548353/2000000000000 : ℝ)*(f.failure) + (3858347722677239/50000000000000 : ℝ)*(f.sum) + (79499917031/322500000000000000000000000 : ℝ)*base65 + (315130061567352811/32250000000000000000000000000000 : ℝ)*base68 + (465825971330352811/32250000000000000000000000000000 : ℝ)*base70 + (237421052451852811/32250000000000000000000000000000 : ℝ)*base72 + (259747280761/80625000000000000000000000 : ℝ)*base74 + (373186558279397189/32250000000000000000000000000000 : ℝ)*base75 + (238421406429852811/32250000000000000000000000000000 : ℝ)*base78 + (125713832867147189/32250000000000000000000000000000 : ℝ)*base79 + (3136104908273/645000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (51749/8000000000000000000 : ℝ)*base89 + (51749/8000000000000000000 : ℝ)*base91 + (51749/8000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1084_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (561/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1084_s7_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097463507/5000000000 : ℝ)*x 0 + (1348531759/2500000000 : ℝ)*x 1 + (1052939853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097463507/5000000000 : ℝ)^8277 ≤ (2666361734583/20000000000000 : ℝ)^6229 := by
    have hnat : (1097463507 : ℕ)^8277*20000000000000^6229 ≤ 2666361734583^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097463507 5000000000 2666361734583 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348531759/2500000000 : ℝ)^8277 ≤ (44033271002109/100000000000000 : ℝ)^6229 := by
    have hnat : (1348531759 : ℕ)^8277*100000000000000^6229 ≤ 44033271002109^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348531759 2500000000 44033271002109 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052939853/2000000000 : ℝ)^8277 ≤ (10658730077881/25000000000000 : ℝ)^6229 := by
    have hnat : (1052939853 : ℕ)^8277*25000000000000^6229 ≤ 10658730077881^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052939853 2000000000 10658730077881 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097463507/5000000000 : ℝ), (1348531759/2500000000 : ℝ), (1052939853/2000000000 : ℝ)] ![(2666361734583/20000000000000 : ℝ), (44033271002109/100000000000000 : ℝ), (10658730077881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097463507/5000000000 : ℝ)|^8277 ≤ (2666361734583/20000000000000 : ℝ)^6229
        have hw : |(-1097463507/5000000000 : ℝ)|=(1097463507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348531759/2500000000 : ℝ)|^8277 ≤ (44033271002109/100000000000000 : ℝ)^6229
        have hw : |(1348531759/2500000000 : ℝ)|=(1348531759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052939853/2000000000 : ℝ)|^8277 ≤ (10658730077881/25000000000000 : ℝ)^6229
        have hw : |(1052939853/2000000000 : ℝ)|=(1052939853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s7_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344956261/10000000000 : ℝ)*x 0 + (-452118201/2000000000 : ℝ)*x 1 + (263234971/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344956261/10000000000 : ℝ)^8277 ≤ (21750355327667/50000000000000 : ℝ)^6229 := by
    have hnat : (5344956261 : ℕ)^8277*50000000000000^6229 ≤ 21750355327667^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344956261 10000000000 21750355327667 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452118201/2000000000 : ℝ)^8277 ≤ (3466091837057/25000000000000 : ℝ)^6229 := by
    have hnat : (452118201 : ℕ)^8277*25000000000000^6229 ≤ 3466091837057^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452118201 2000000000 3466091837057 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263234971/500000000 : ℝ)^8277 ≤ (8526984395891/20000000000000 : ℝ)^6229 := by
    have hnat : (263234971 : ℕ)^8277*20000000000000^6229 ≤ 8526984395891^6229*500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263234971 500000000 8526984395891 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344956261/10000000000 : ℝ), (-452118201/2000000000 : ℝ), (263234971/500000000 : ℝ)] ![(21750355327667/50000000000000 : ℝ), (3466091837057/25000000000000 : ℝ), (8526984395891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344956261/10000000000 : ℝ)|^8277 ≤ (21750355327667/50000000000000 : ℝ)^6229
        have hw : |(5344956261/10000000000 : ℝ)|=(5344956261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-452118201/2000000000 : ℝ)|^8277 ≤ (3466091837057/25000000000000 : ℝ)^6229
        have hw : |(-452118201/2000000000 : ℝ)|=(452118201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263234971/500000000 : ℝ)|^8277 ≤ (8526984395891/20000000000000 : ℝ)^6229
        have hw : |(263234971/500000000 : ℝ)|=(263234971/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s7_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668119577/1250000000 : ℝ)*x 0 + (526469917/1000000000 : ℝ)*x 1 + (-2260590863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668119577/1250000000 : ℝ)^8277 ≤ (8700142898897/20000000000000 : ℝ)^6229 := by
    have hnat : (668119577 : ℕ)^8277*20000000000000^6229 ≤ 8700142898897^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668119577 1250000000 8700142898897 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526469917/1000000000 : ℝ)^8277 ≤ (42634919289243/100000000000000 : ℝ)^6229 := by
    have hnat : (526469917 : ℕ)^8277*100000000000000^6229 ≤ 42634919289243^6229*1000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526469917 1000000000 42634919289243 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260590863/10000000000 : ℝ)^8277 ≤ (2772873238199/20000000000000 : ℝ)^6229 := by
    have hnat : (2260590863 : ℕ)^8277*20000000000000^6229 ≤ 2772873238199^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260590863 10000000000 2772873238199 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668119577/1250000000 : ℝ), (526469917/1000000000 : ℝ), (-2260590863/10000000000 : ℝ)] ![(8700142898897/20000000000000 : ℝ), (42634919289243/100000000000000 : ℝ), (2772873238199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668119577/1250000000 : ℝ)|^8277 ≤ (8700142898897/20000000000000 : ℝ)^6229
        have hw : |(668119577/1250000000 : ℝ)|=(668119577/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526469917/1000000000 : ℝ)|^8277 ≤ (42634919289243/100000000000000 : ℝ)^6229
        have hw : |(526469917/1000000000 : ℝ)|=(526469917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2260590863/10000000000 : ℝ)|^8277 ≤ (2772873238199/20000000000000 : ℝ)^6229
        have hw : |(-2260590863/10000000000 : ℝ)|=(2260590863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s7_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372905769/10000000000 : ℝ)*x 0 + (2123745499/5000000000 : ℝ)*x 1 + (2251028809/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372905769/10000000000 : ℝ)^8277 ≤ (2082288216951/6250000000000 : ℝ)^6229 := by
    have hnat : (4372905769 : ℕ)^8277*6250000000000^6229 ≤ 2082288216951^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372905769 10000000000 2082288216951 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123745499/5000000000 : ℝ)^8277 ≤ (8013239337779/25000000000000 : ℝ)^6229 := by
    have hnat : (2123745499 : ℕ)^8277*25000000000000^6229 ≤ 8013239337779^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123745499 5000000000 8013239337779 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251028809/5000000000 : ℝ)^8277 ≤ (6926086233339/20000000000000 : ℝ)^6229 := by
    have hnat : (2251028809 : ℕ)^8277*20000000000000^6229 ≤ 6926086233339^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251028809 5000000000 6926086233339 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372905769/10000000000 : ℝ), (2123745499/5000000000 : ℝ), (2251028809/5000000000 : ℝ)] ![(2082288216951/6250000000000 : ℝ), (8013239337779/25000000000000 : ℝ), (6926086233339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372905769/10000000000 : ℝ)|^8277 ≤ (2082288216951/6250000000000 : ℝ)^6229
        have hw : |(4372905769/10000000000 : ℝ)|=(4372905769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123745499/5000000000 : ℝ)|^8277 ≤ (8013239337779/25000000000000 : ℝ)^6229
        have hw : |(2123745499/5000000000 : ℝ)|=(2123745499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251028809/5000000000 : ℝ)|^8277 ≤ (6926086233339/20000000000000 : ℝ)^6229
        have hw : |(2251028809/5000000000 : ℝ)|=(2251028809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s7_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548733049/2500000000 : ℝ)*x 0 + (5265024127/10000000000 : ℝ)*x 1 + (1078760179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548733049/2500000000 : ℝ)^8277 ≤ (13331850496493/100000000000000 : ℝ)^6229 := by
    have hnat : (548733049 : ℕ)^8277*100000000000000^6229 ≤ 13331850496493^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548733049 2500000000 13331850496493 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265024127/10000000000 : ℝ)^8277 ≤ (10659604034427/25000000000000 : ℝ)^6229 := by
    have hnat : (5265024127 : ℕ)^8277*25000000000000^6229 ≤ 10659604034427^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265024127 10000000000 10659604034427 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078760179/2000000000 : ℝ)^8277 ≤ (22014866673527/50000000000000 : ℝ)^6229 := by
    have hnat : (1078760179 : ℕ)^8277*50000000000000^6229 ≤ 22014866673527^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078760179 2000000000 22014866673527 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548733049/2500000000 : ℝ), (5265024127/10000000000 : ℝ), (1078760179/2000000000 : ℝ)] ![(13331850496493/100000000000000 : ℝ), (10659604034427/25000000000000 : ℝ), (22014866673527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548733049/2500000000 : ℝ)|^8277 ≤ (13331850496493/100000000000000 : ℝ)^6229
        have hw : |(-548733049/2500000000 : ℝ)|=(548733049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265024127/10000000000 : ℝ)|^8277 ≤ (10659604034427/25000000000000 : ℝ)^6229
        have hw : |(5265024127/10000000000 : ℝ)|=(5265024127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078760179/2000000000 : ℝ)|^8277 ≤ (22014866673527/50000000000000 : ℝ)^6229
        have hw : |(1078760179/2000000000 : ℝ)|=(1078760179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s7_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312309741/10000000000 : ℝ)*x 0 + (-2131489453/10000000000 : ℝ)*x 1 + (1078760179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312309741/10000000000 : ℝ)^8277 ≤ (2696750596663/6250000000000 : ℝ)^6229 := by
    have hnat : (5312309741 : ℕ)^8277*6250000000000^6229 ≤ 2696750596663^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312309741 10000000000 2696750596663 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131489453/10000000000 : ℝ)^8277 ≤ (12822257085447/100000000000000 : ℝ)^6229 := by
    have hnat : (2131489453 : ℕ)^8277*100000000000000^6229 ≤ 12822257085447^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131489453 10000000000 12822257085447 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078760179/2000000000 : ℝ)^8277 ≤ (22014866673527/50000000000000 : ℝ)^6229 := by
    have hnat : (1078760179 : ℕ)^8277*50000000000000^6229 ≤ 22014866673527^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078760179 2000000000 22014866673527 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312309741/10000000000 : ℝ), (-2131489453/10000000000 : ℝ), (1078760179/2000000000 : ℝ)] ![(2696750596663/6250000000000 : ℝ), (12822257085447/100000000000000 : ℝ), (22014866673527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312309741/10000000000 : ℝ)|^8277 ≤ (2696750596663/6250000000000 : ℝ)^6229
        have hw : |(5312309741/10000000000 : ℝ)|=(5312309741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131489453/10000000000 : ℝ)|^8277 ≤ (12822257085447/100000000000000 : ℝ)^6229
        have hw : |(-2131489453/10000000000 : ℝ)|=(2131489453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078760179/2000000000 : ℝ)|^8277 ≤ (22014866673527/50000000000000 : ℝ)^6229
        have hw : |(1078760179/2000000000 : ℝ)|=(1078760179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s7_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312309743/10000000000 : ℝ)*x 0 + (2696900447/5000000000 : ℝ)*x 1 + (-532872363/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312309743/10000000000 : ℝ)^8277 ≤ (43148009568193/100000000000000 : ℝ)^6229 := by
    have hnat : (5312309743 : ℕ)^8277*100000000000000^6229 ≤ 43148009568193^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312309743 10000000000 43148009568193 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696900447/5000000000 : ℝ)^8277 ≤ (2751858333513/6250000000000 : ℝ)^6229 := by
    have hnat : (2696900447 : ℕ)^8277*6250000000000^6229 ≤ 2751858333513^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696900447 5000000000 2751858333513 6250000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (532872363/2500000000 : ℝ)^8277 ≤ (12822257077453/100000000000000 : ℝ)^6229 := by
    have hnat : (532872363 : ℕ)^8277*100000000000000^6229 ≤ 12822257077453^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532872363 2500000000 12822257077453 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312309743/10000000000 : ℝ), (2696900447/5000000000 : ℝ), (-532872363/2500000000 : ℝ)] ![(43148009568193/100000000000000 : ℝ), (2751858333513/6250000000000 : ℝ), (12822257077453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312309743/10000000000 : ℝ)|^8277 ≤ (43148009568193/100000000000000 : ℝ)^6229
        have hw : |(5312309743/10000000000 : ℝ)|=(5312309743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696900447/5000000000 : ℝ)|^8277 ≤ (2751858333513/6250000000000 : ℝ)^6229
        have hw : |(2696900447/5000000000 : ℝ)|=(2696900447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-532872363/2500000000 : ℝ)|^8277 ≤ (12822257077453/100000000000000 : ℝ)^6229
        have hw : |(-532872363/2500000000 : ℝ)|=(532872363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s7_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372915569/10000000000 : ℝ)*x 0 + (562677359/1250000000 : ℝ)*x 1 + (13275413/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372915569/10000000000 : ℝ)^8277 ≤ (33316710684897/100000000000000 : ℝ)^6229 := by
    have hnat : (4372915569 : ℕ)^8277*100000000000000^6229 ≤ 33316710684897^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372915569 10000000000 33316710684897 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562677359/1250000000 : ℝ)^8277 ≤ (17311951287277/50000000000000 : ℝ)^6229 := by
    have hnat : (562677359 : ℕ)^8277*50000000000000^6229 ≤ 17311951287277^6229*1250000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562677359 1250000000 17311951287277 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13275413/31250000 : ℝ)^8277 ≤ (8014846681741/25000000000000 : ℝ)^6229 := by
    have hnat : (13275413 : ℕ)^8277*25000000000000^6229 ≤ 8014846681741^6229*31250000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13275413 31250000 8014846681741 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372915569/10000000000 : ℝ), (562677359/1250000000 : ℝ), (13275413/31250000 : ℝ)] ![(33316710684897/100000000000000 : ℝ), (17311951287277/50000000000000 : ℝ), (8014846681741/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372915569/10000000000 : ℝ)|^8277 ≤ (33316710684897/100000000000000 : ℝ)^6229
        have hw : |(4372915569/10000000000 : ℝ)|=(4372915569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562677359/1250000000 : ℝ)|^8277 ≤ (17311951287277/50000000000000 : ℝ)^6229
        have hw : |(562677359/1250000000 : ℝ)|=(562677359/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13275413/31250000 : ℝ)|^8277 ≤ (8014846681741/25000000000000 : ℝ)^6229
        have hw : |(13275413/31250000 : ℝ)|=(13275413/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5637/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (438/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (561/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5633/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (561/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5633/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (561/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5633/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5633/50000 : ℝ) ^ (2069/512 : ℝ) ≤ (1472945680358017/10000000000000000000 : ℝ) := by
    have hpowers : (5633/50000 : ℝ)^2069 ≤ (1472945680358017/10000000000000000000 : ℝ)^512 := by
      have hnat : (5633 : ℕ)^2069*10000000000000000000^512 ≤ 1472945680358017^512*50000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5633 50000 1472945680358017 10000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5633/50000 : ℝ)) (X := (1472945680358017/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (561/4000 : ℝ) ^ (2069/512 : ℝ) ≤ (35696132725417221/100000000000000000000 : ℝ) := by
    have hpowers : (561/4000 : ℝ)^2069 ≤ (35696132725417221/100000000000000000000 : ℝ)^512 := by
      have hnat : (561 : ℕ)^2069*100000000000000000000^512 ≤ 35696132725417221^512*4000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        561 4000 35696132725417221 100000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (561/4000 : ℝ)) (X := (35696132725417221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001472945680358017/5000000000000000000 : ℝ) ≤ (1250091114621727/1250000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (5001472945680358017/5000000000000000000 : ℝ)^512 ≤ (1250091114621727/1250000000000000 : ℝ)^2069 := by
      have hnat : (5001472945680358017 : ℕ)^512*1250000000000000^2069 ≤ 1250091114621727^2069*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001472945680358017 5000000000000000000 1250091114621727 1250000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250091114621727/1250000000000000 : ℝ)) (X := (5001472945680358017/5000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050425589528997391/100000000000000000000 : ℝ) ≤ (625077975485449/625000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (100050425589528997391/100000000000000000000 : ℝ)^512 ≤ (625077975485449/625000000000000 : ℝ)^2069 := by
      have hnat : (100050425589528997391 : ℕ)^512*625000000000000^2069 ≤ 625077975485449^2069*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050425589528997391 100000000000000000000 625077975485449 625000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625077975485449/625000000000000 : ℝ)) (X := (100050425589528997391/100000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035696132725417221/50000000000000000000 : ℝ) ≤ (1250220787320069/1250000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50035696132725417221/50000000000000000000 : ℝ)^512 ≤ (1250220787320069/1250000000000000 : ℝ)^2069 := by
      have hnat : (50035696132725417221 : ℕ)^512*1250000000000000^2069 ≤ 1250220787320069^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035696132725417221 50000000000000000000 1250220787320069 1250000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250220787320069/1250000000000000 : ℝ)) (X := (50035696132725417221/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1472945680358017/10000000000000000000 : ℝ) ≤ ((3447540492621823821/3448750000000000000 : ℝ)+2*(64836349171/34487500000000 : ℝ)*(5633/50000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (3447540492621823821/3448750000000000000 : ℝ)+2*(64836349171/34487500000000 : ℝ)*(5633/50000 : ℝ)=(1250091114621727/1250000000000000 : ℝ) by norm_num, show 1+2*(1472945680358017/10000000000000000000 : ℝ)=(5001472945680358017/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35696132725417221/100000000000000000000 : ℝ)+(1472945680358017/10000000000000000000 : ℝ) ≤ ((3447540492621823821/3448750000000000000 : ℝ)+(64836349171/34487500000000 : ℝ)*((561/4000 : ℝ)+(5633/50000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (3447540492621823821/3448750000000000000 : ℝ)+(64836349171/34487500000000 : ℝ)*((561/4000 : ℝ)+(5633/50000 : ℝ))=(625077975485449/625000000000000 : ℝ) by norm_num, show 1+(35696132725417221/100000000000000000000 : ℝ)+(1472945680358017/10000000000000000000 : ℝ)=(100050425589528997391/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35696132725417221/100000000000000000000 : ℝ) ≤ ((3447540492621823821/3448750000000000000 : ℝ)+2*(64836349171/34487500000000 : ℝ)*(561/4000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (3447540492621823821/3448750000000000000 : ℝ)+2*(64836349171/34487500000000 : ℝ)*(561/4000 : ℝ)=(1250220787320069/1250000000000000 : ℝ) by norm_num, show 1+2*(35696132725417221/100000000000000000000 : ℝ)=(50035696132725417221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3447540492621823821/3448750000000000000 : ℝ)*(X 1 0+X 2 0)+(64836349171/34487500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (3447540492621823821/3448750000000000000 : ℝ)) (alpha := (64836349171/34487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3447540492621823821/3448750000000000000 : ℝ)*(X 0 1+X 2 1)+(64836349171/34487500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (3447540492621823821/3448750000000000000 : ℝ)) (alpha := (64836349171/34487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3447540492621823821/3448750000000000000 : ℝ)*(X 0 2+X 1 2)+(64836349171/34487500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (5633/50000 : ℝ)) (hi := (561/4000 : ℝ)) (c := (3447540492621823821/3448750000000000000 : ℝ)) (alpha := (64836349171/34487500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1097463507/5000000000 : ℝ)*X 0 0+(1348531759/2500000000 : ℝ)*X 0 1+(1052939853/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344956261/10000000000 : ℝ)*X 1 0+(-452118201/2000000000 : ℝ)*X 1 1+(263234971/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668119577/1250000000 : ℝ)*X 2 0+(526469917/1000000000 : ℝ)*X 2 1+(-2260590863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372905769/10000000000 : ℝ)*X 0 0+(2123745499/5000000000 : ℝ)*X 0 1+(2251028809/5000000000 : ℝ)*X 0 2+(4372905769/10000000000 : ℝ)*X 1 0+(2123745499/5000000000 : ℝ)*X 1 1+(2251028809/5000000000 : ℝ)*X 1 2+(4372905769/10000000000 : ℝ)*X 2 0+(2123745499/5000000000 : ℝ)*X 2 1+(2251028809/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548733049/2500000000 : ℝ)*X 0 0+(5265024127/10000000000 : ℝ)*X 0 1+(1078760179/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312309741/10000000000 : ℝ)*X 1 0+(-2131489453/10000000000 : ℝ)*X 1 1+(1078760179/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312309743/10000000000 : ℝ)*X 2 0+(2696900447/5000000000 : ℝ)*X 2 1+(-532872363/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372915569/10000000000 : ℝ)*X 0 0+(562677359/1250000000 : ℝ)*X 0 1+(13275413/31250000 : ℝ)*X 0 2+(4372915569/10000000000 : ℝ)*X 1 0+(562677359/1250000000 : ℝ)*X 1 1+(13275413/31250000 : ℝ)*X 1 2+(4372915569/10000000000 : ℝ)*X 2 0+(562677359/1250000000 : ℝ)*X 2 1+(13275413/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (881992210496413358187071451/86218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2110233189/100000000000000 : ℝ)*(base19) + (1096624243/50000000000000 : ℝ)*(base23) + (229917633/100000000000000 : ℝ)*(lower2) + (431921/250000000000 : ℝ)*(upper3) + (173388897/100000000000000 : ℝ)*(upper5) + (2913689209095177/50000000000000 : ℝ)*(major0) + (2913689209095177/50000000000000 : ℝ)*(major1) + (2913689209095177/50000000000000 : ℝ)*(major2) + (1545275617825119/20000000000000 : ℝ)*(sp0) + (1545289854779169/20000000000000 : ℝ)*(sp1) + (1931612297720137/25000000000000 : ℝ)*(sp2) + (3928272359449217/100000000000000 : ℝ)*(sp3) + (73295003439/100000000000000 : ℝ)*(sp4) + (8187953087/25000000000000 : ℝ)*(sp7) + (982076277815391/25000000000000 : ℝ)*(f.failure) + (3863225692064517/50000000000000 : ℝ)*(f.sum) + (7684308988027/13795000000000000000000000000 : ℝ)*base65 + (1257020592303698817/172437500000000000000000000000000 : ℝ)*base67 + (1590012746995613683/172437500000000000000000000000000 : ℝ)*base70 + (306431462281613683/172437500000000000000000000000000 : ℝ)*base72 + (81986947197343/13795000000000000000000000000 : ℝ)*base74 + (472004614425613683/172437500000000000000000000000000 : ℝ)*base76 + (531233061872676183/172437500000000000000000000000000 : ℝ)*base78 + (1575566802420386317/172437500000000000000000000000000 : ℝ)*base79 + (36496704102009/6897500000000000000000000000 : ℝ)*base82 + (515397/100000000000000000000 : ℝ)*base90 + (515397/100000000000000000000 : ℝ)*base92 + (515397/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (593796160920344344993553727/86218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (316859411/25000000000000 : ℝ)*(base19) + (276784183/20000000000000 : ℝ)*(base23) + (137405477/100000000000000 : ℝ)*(upper3) + (25682133/50000000000000 : ℝ)*(lower4) + (27905349/20000000000000 : ℝ)*(upper5) + (2928367345029871/50000000000000 : ℝ)*(major0) + (2928367345029871/50000000000000 : ℝ)*(major1) + (2928367345029871/50000000000000 : ℝ)*(major2) + (34577570543/100000000000000 : ℝ)*(sp1) + (37322384989/100000000000000 : ℝ)*(sp2) + (1941343656803429/25000000000000 : ℝ)*(sp4) + (7765338782205529/100000000000000 : ℝ)*(sp5) + (1941333980226953/25000000000000 : ℝ)*(sp6) + (987023630834037/25000000000000 : ℝ)*(sp7) + (987023630834037/25000000000000 : ℝ)*(f.failure) + (1941343656803429/25000000000000 : ℝ)*(f.sum) + (2034473214591/3448750000000000000000000000 : ℝ)*base66 + (49854666804792909/172437500000000000000000000000000 : ℝ)*base68 + (1553868485157207091/172437500000000000000000000000000 : ℝ)*base69 + (1067944710168707091/172437500000000000000000000000000 : ℝ)*base71 + (10014931944453/1724375000000000000000000000 : ℝ)*base74 + (587504826124355409/172437500000000000000000000000000 : ℝ)*base76 + (67932774327957091/172437500000000000000000000000000 : ℝ)*base77 + (270772667530582091/172437500000000000000000000000000 : ℝ)*base79 + (460844160601/13795000000000000000000000000 : ℝ)*base81 + (870121/100000000000000000000 : ℝ)*base89 + (870121/100000000000000000000 : ℝ)*base91 + (870121/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1084_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (561/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (438/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1084_s8_0 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194937037/10000000000 : ℝ)*x 0 + (2697018087/5000000000 : ℝ)*x 1 + (5264783337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194937037/10000000000 : ℝ)^8277 ≤ (13331889567913/100000000000000 : ℝ)^6229 := by
    have hnat : (2194937037 : ℕ)^8277*100000000000000^6229 ≤ 13331889567913^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194937037 10000000000 13331889567913 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697018087/5000000000 : ℝ)^8277 ≤ (44032285413917/100000000000000 : ℝ)^6229 := by
    have hnat : (2697018087 : ℕ)^8277*100000000000000^6229 ≤ 44032285413917^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697018087 5000000000 44032285413917 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264783337/10000000000 : ℝ)^8277 ≤ (42635824999943/100000000000000 : ℝ)^6229 := by
    have hnat : (5264783337 : ℕ)^8277*100000000000000^6229 ≤ 42635824999943^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264783337 10000000000 42635824999943 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194937037/10000000000 : ℝ), (2697018087/5000000000 : ℝ), (5264783337/10000000000 : ℝ)] ![(13331889567913/100000000000000 : ℝ), (44032285413917/100000000000000 : ℝ), (42635824999943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194937037/10000000000 : ℝ)|^8277 ≤ (13331889567913/100000000000000 : ℝ)^6229
        have hw : |(-2194937037/10000000000 : ℝ)|=(2194937037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697018087/5000000000 : ℝ)|^8277 ≤ (44032285413917/100000000000000 : ℝ)^6229
        have hw : |(2697018087/5000000000 : ℝ)|=(2697018087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264783337/10000000000 : ℝ)|^8277 ≤ (42635824999943/100000000000000 : ℝ)^6229
        have hw : |(5264783337/10000000000 : ℝ)|=(5264783337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s8_1 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344933071/10000000000 : ℝ)*x 0 + (-2260510967/10000000000 : ℝ)*x 1 + (5264783341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344933071/10000000000 : ℝ)^8277 ≤ (43500459867041/100000000000000 : ℝ)^6229 := by
    have hnat : (5344933071 : ℕ)^8277*100000000000000^6229 ≤ 43500459867041^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344933071 10000000000 43500459867041 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260510967/10000000000 : ℝ)^8277 ≤ (6931857539879/50000000000000 : ℝ)^6229 := by
    have hnat : (2260510967 : ℕ)^8277*50000000000000^6229 ≤ 6931857539879^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260510967 10000000000 6931857539879 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264783341/10000000000 : ℝ)^8277 ≤ (42635825042987/100000000000000 : ℝ)^6229 := by
    have hnat : (5264783341 : ℕ)^8277*100000000000000^6229 ≤ 42635825042987^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264783341 10000000000 42635825042987 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344933071/10000000000 : ℝ), (-2260510967/10000000000 : ℝ), (5264783341/10000000000 : ℝ)] ![(43500459867041/100000000000000 : ℝ), (6931857539879/50000000000000 : ℝ), (42635825042987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344933071/10000000000 : ℝ)|^8277 ≤ (43500459867041/100000000000000 : ℝ)^6229
        have hw : |(5344933071/10000000000 : ℝ)|=(5344933071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2260510967/10000000000 : ℝ)|^8277 ≤ (6931857539879/50000000000000 : ℝ)^6229
        have hw : |(-2260510967/10000000000 : ℝ)|=(2260510967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264783341/10000000000 : ℝ)|^8277 ≤ (42635825042987/100000000000000 : ℝ)^6229
        have hw : |(5264783341/10000000000 : ℝ)|=(5264783341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s8_2 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068986607/2000000000 : ℝ)*x 0 + (5264783379/10000000000 : ℝ)*x 1 + (-565127741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068986607/2000000000 : ℝ)^8277 ≤ (43500459477719/100000000000000 : ℝ)^6229 := by
    have hnat : (1068986607 : ℕ)^8277*100000000000000^6229 ≤ 43500459477719^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068986607 2000000000 43500459477719 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264783379/10000000000 : ℝ)^8277 ≤ (42635825451901/100000000000000 : ℝ)^6229 := by
    have hnat : (5264783379 : ℕ)^8277*100000000000000^6229 ≤ 42635825451901^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264783379 10000000000 42635825451901 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565127741/2500000000 : ℝ)^8277 ≤ (13863715055309/100000000000000 : ℝ)^6229 := by
    have hnat : (565127741 : ℕ)^8277*100000000000000^6229 ≤ 13863715055309^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565127741 2500000000 13863715055309 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068986607/2000000000 : ℝ), (5264783379/10000000000 : ℝ), (-565127741/2500000000 : ℝ)] ![(43500459477719/100000000000000 : ℝ), (42635825451901/100000000000000 : ℝ), (13863715055309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068986607/2000000000 : ℝ)|^8277 ≤ (43500459477719/100000000000000 : ℝ)^6229
        have hw : |(1068986607/2000000000 : ℝ)|=(1068986607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264783379/10000000000 : ℝ)|^8277 ≤ (42635825451901/100000000000000 : ℝ)^6229
        have hw : |(5264783379/10000000000 : ℝ)|=(5264783379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565127741/2500000000 : ℝ)|^8277 ≤ (13863715055309/100000000000000 : ℝ)^6229
        have hw : |(-565127741/2500000000 : ℝ)|=(565127741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s8_3 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186455067/5000000000 : ℝ)*x 0 + (4247662243/10000000000 : ℝ)*x 1 + (4501885293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186455067/5000000000 : ℝ)^8277 ≤ (3331665566179/10000000000000 : ℝ)^6229 := by
    have hnat : (2186455067 : ℕ)^8277*10000000000000^6229 ≤ 3331665566179^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186455067 5000000000 3331665566179 10000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247662243/10000000000 : ℝ)^8277 ≤ (6410934902443/20000000000000 : ℝ)^6229 := by
    have hnat : (4247662243 : ℕ)^8277*20000000000000^6229 ≤ 6410934902443^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247662243 10000000000 6410934902443 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501885293/10000000000 : ℝ)^8277 ≤ (34628669811159/100000000000000 : ℝ)^6229 := by
    have hnat : (4501885293 : ℕ)^8277*100000000000000^6229 ≤ 34628669811159^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501885293 10000000000 34628669811159 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186455067/5000000000 : ℝ), (4247662243/10000000000 : ℝ), (4501885293/10000000000 : ℝ)] ![(3331665566179/10000000000000 : ℝ), (6410934902443/20000000000000 : ℝ), (34628669811159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186455067/5000000000 : ℝ)|^8277 ≤ (3331665566179/10000000000000 : ℝ)^6229
        have hw : |(2186455067/5000000000 : ℝ)|=(2186455067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247662243/10000000000 : ℝ)|^8277 ≤ (6410934902443/20000000000000 : ℝ)^6229
        have hw : |(4247662243/10000000000 : ℝ)|=(4247662243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501885293/10000000000 : ℝ)|^8277 ≤ (34628669811159/100000000000000 : ℝ)^6229
        have hw : |(4501885293/10000000000 : ℝ)|=(4501885293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s8_4 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548735447/2500000000 : ℝ)*x 0 + (5265107291/10000000000 : ℝ)*x 1 + (1348427813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548735447/2500000000 : ℝ)^8277 ≤ (533277116519/4000000000000 : ℝ)^6229 := by
    have hnat : (548735447 : ℕ)^8277*4000000000000^6229 ≤ 533277116519^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548735447 2500000000 533277116519 4000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265107291/10000000000 : ℝ)^8277 ≤ (42639311073381/100000000000000 : ℝ)^6229 := by
    have hnat : (5265107291 : ℕ)^8277*100000000000000^6229 ≤ 42639311073381^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265107291 10000000000 42639311073381 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348427813/2500000000 : ℝ)^8277 ≤ (22014380500379/50000000000000 : ℝ)^6229 := by
    have hnat : (1348427813 : ℕ)^8277*50000000000000^6229 ≤ 22014380500379^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348427813 2500000000 22014380500379 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548735447/2500000000 : ℝ), (5265107291/10000000000 : ℝ), (1348427813/2500000000 : ℝ)] ![(533277116519/4000000000000 : ℝ), (42639311073381/100000000000000 : ℝ), (22014380500379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548735447/2500000000 : ℝ)|^8277 ≤ (533277116519/4000000000000 : ℝ)^6229
        have hw : |(-548735447/2500000000 : ℝ)|=(548735447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265107291/10000000000 : ℝ)|^8277 ≤ (42639311073381/100000000000000 : ℝ)^6229
        have hw : |(5265107291/10000000000 : ℝ)|=(5265107291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348427813/2500000000 : ℝ)|^8277 ≤ (22014380500379/50000000000000 : ℝ)^6229
        have hw : |(1348427813/2500000000 : ℝ)|=(1348427813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s8_5 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312330373/10000000000 : ℝ)*x 0 + (-2131583707/10000000000 : ℝ)*x 1 + (2696855453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312330373/10000000000 : ℝ)^8277 ≤ (10787058055677/25000000000000 : ℝ)^6229 := by
    have hnat : (5312330373 : ℕ)^8277*25000000000000^6229 ≤ 10787058055677^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312330373 10000000000 10787058055677 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2131583707/10000000000 : ℝ)^8277 ≤ (12823010508429/100000000000000 : ℝ)^6229 := by
    have hnat : (2131583707 : ℕ)^8277*100000000000000^6229 ≤ 12823010508429^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131583707 10000000000 12823010508429 100000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696855453/5000000000 : ℝ)^8277 ≤ (176115028991/400000000000 : ℝ)^6229 := by
    have hnat : (2696855453 : ℕ)^8277*400000000000^6229 ≤ 176115028991^6229*5000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696855453 5000000000 176115028991 400000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312330373/10000000000 : ℝ), (-2131583707/10000000000 : ℝ), (2696855453/5000000000 : ℝ)] ![(10787058055677/25000000000000 : ℝ), (12823010508429/100000000000000 : ℝ), (176115028991/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312330373/10000000000 : ℝ)|^8277 ≤ (10787058055677/25000000000000 : ℝ)^6229
        have hw : |(5312330373/10000000000 : ℝ)|=(5312330373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2131583707/10000000000 : ℝ)|^8277 ≤ (12823010508429/100000000000000 : ℝ)^6229
        have hw : |(-2131583707/10000000000 : ℝ)|=(2131583707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696855453/5000000000 : ℝ)|^8277 ≤ (176115028991/400000000000 : ℝ)^6229
        have hw : |(2696855453/5000000000 : ℝ)|=(2696855453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s8_6 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332020689/625000000 : ℝ)*x 0 + (84276731/156250000 : ℝ)*x 1 + (-426316599/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332020689/625000000 : ℝ)^8277 ≤ (10787059812199/25000000000000 : ℝ)^6229 := by
    have hnat : (332020689 : ℕ)^8277*25000000000000^6229 ≤ 10787059812199^6229*625000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332020689 625000000 10787059812199 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84276731/156250000 : ℝ)^8277 ≤ (8805751184887/20000000000000 : ℝ)^6229 := by
    have hnat : (84276731 : ℕ)^8277*20000000000000^6229 ≤ 8805751184887^6229*156250000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84276731 156250000 8805751184887 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426316599/2000000000 : ℝ)^8277 ≤ (3205751204247/25000000000000 : ℝ)^6229 := by
    have hnat : (426316599 : ℕ)^8277*25000000000000^6229 ≤ 3205751204247^6229*2000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426316599 2000000000 3205751204247 25000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332020689/625000000 : ℝ), (84276731/156250000 : ℝ), (-426316599/2000000000 : ℝ)] ![(10787059812199/25000000000000 : ℝ), (8805751184887/20000000000000 : ℝ), (3205751204247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332020689/625000000 : ℝ)|^8277 ≤ (10787059812199/25000000000000 : ℝ)^6229
        have hw : |(332020689/625000000 : ℝ)|=(332020689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84276731/156250000 : ℝ)|^8277 ≤ (8805751184887/20000000000000 : ℝ)^6229
        have hw : |(84276731/156250000 : ℝ)|=(84276731/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426316599/2000000000 : ℝ)|^8277 ≤ (3205751204247/25000000000000 : ℝ)^6229
        have hw : |(-426316599/2000000000 : ℝ)|=(426316599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1084_s8_7 (p : ℝ) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093230051/2500000000 : ℝ)*x 0 + (56265603/125000000 : ℝ)*x 1 + (4248301391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093230051/2500000000 : ℝ)^8277 ≤ (6663351521789/20000000000000 : ℝ)^6229 := by
    have hnat : (1093230051 : ℕ)^8277*20000000000000^6229 ≤ 6663351521789^6229*2500000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093230051 2500000000 6663351521789 20000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56265603/125000000 : ℝ)^8277 ≤ (17311079302319/50000000000000 : ℝ)^6229 := by
    have hnat : (56265603 : ℕ)^8277*50000000000000^6229 ≤ 17311079302319^6229*125000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56265603 125000000 17311079302319 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248301391/10000000000 : ℝ)^8277 ≤ (16030541888369/50000000000000 : ℝ)^6229 := by
    have hnat : (4248301391 : ℕ)^8277*50000000000000^6229 ≤ 16030541888369^6229*10000000000^8277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248301391 10000000000 16030541888369 50000000000000 8277 6229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8277/2048 : ℝ)) 8277 6229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093230051/2500000000 : ℝ), (56265603/125000000 : ℝ), (4248301391/10000000000 : ℝ)] ![(6663351521789/20000000000000 : ℝ), (17311079302319/50000000000000 : ℝ), (16030541888369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093230051/2500000000 : ℝ)|^8277 ≤ (6663351521789/20000000000000 : ℝ)^6229
        have hw : |(1093230051/2500000000 : ℝ)|=(1093230051/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56265603/125000000 : ℝ)|^8277 ≤ (17311079302319/50000000000000 : ℝ)^6229
        have hw : |(56265603/125000000 : ℝ)|=(56265603/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248301391/10000000000 : ℝ)|^8277 ≤ (16030541888369/50000000000000 : ℝ)^6229
        have hw : |(4248301391/10000000000 : ℝ)|=(4248301391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1084_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (438/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2819/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7007/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (438/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (438/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (438/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (438/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (438/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (438/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5637/50000 : ℝ) ^ (2069/512 : ℝ) ≤ (7385884539857831/50000000000000000000 : ℝ) := by
    have hpowers : (5637/50000 : ℝ)^2069 ≤ (7385884539857831/50000000000000000000 : ℝ)^512 := by
      have hnat : (5637 : ℕ)^2069*50000000000000000000^512 ≤ 7385884539857831^512*50000^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5637 50000 7385884539857831 50000000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5637/50000 : ℝ)) (X := (7385884539857831/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hpowhi : (438/3125 : ℝ) ^ (2069/512 : ℝ) ≤ (4450457129907749/12500000000000000000 : ℝ) := by
    have hpowers : (438/3125 : ℝ)^2069 ≤ (4450457129907749/12500000000000000000 : ℝ)^512 := by
      have hnat : (438 : ℕ)^2069*12500000000000000000^512 ≤ 4450457129907749^512*3125^2069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        438 3125 4450457129907749 12500000000000000000 2069 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (438/3125 : ℝ)) (X := (4450457129907749/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007385884539857831/25000000000000000000 : ℝ) ≤ (2000146202129941/2000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (25007385884539857831/25000000000000000000 : ℝ)^512 ≤ (2000146202129941/2000000000000000 : ℝ)^2069 := by
      have hnat : (25007385884539857831 : ℕ)^512*2000000000000000^2069 ≤ 2000146202129941^2069*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007385884539857831 25000000000000000000 2000146202129941 2000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000146202129941/2000000000000000 : ℝ)) (X := (25007385884539857831/25000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025187713059488827/50000000000000000000 : ℝ) ≤ (1250155795860163/1250000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (50025187713059488827/50000000000000000000 : ℝ)^512 ≤ (1250155795860163/1250000000000000 : ℝ)^2069 := by
      have hnat : (50025187713059488827 : ℕ)^512*1250000000000000^2069 ≤ 1250155795860163^2069*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025187713059488827 50000000000000000000 1250155795860163 1250000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250155795860163/1250000000000000 : ℝ)) (X := (50025187713059488827/50000000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254450457129907749/6250000000000000000 : ℝ) ≤ (10001761723112903/10000000000000000 : ℝ) ^ (2069/512 : ℝ) := by
    have hpowers : (6254450457129907749/6250000000000000000 : ℝ)^512 ≤ (10001761723112903/10000000000000000 : ℝ)^2069 := by
      have hnat : (6254450457129907749 : ℕ)^512*10000000000000000^2069 ≤ 10001761723112903^2069*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254450457129907749 6250000000000000000 10001761723112903 10000000000000000 512 2069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001761723112903/10000000000000000 : ℝ)) (X := (6254450457129907749/6250000000000000000 : ℝ)) (by norm_num) 2069 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7385884539857831/50000000000000000000 : ℝ) ≤ ((4568397363148566143/4570000000000000000 : ℝ)+2*(171785410533/91400000000000 : ℝ)*(5637/50000 : ℝ))^(2069/512 : ℝ) := by
    rw [show (4568397363148566143/4570000000000000000 : ℝ)+2*(171785410533/91400000000000 : ℝ)*(5637/50000 : ℝ)=(2000146202129941/2000000000000000 : ℝ) by norm_num, show 1+2*(7385884539857831/50000000000000000000 : ℝ)=(25007385884539857831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4450457129907749/12500000000000000000 : ℝ)+(7385884539857831/50000000000000000000 : ℝ) ≤ ((4568397363148566143/4570000000000000000 : ℝ)+(171785410533/91400000000000 : ℝ)*((438/3125 : ℝ)+(5637/50000 : ℝ)))^(2069/512 : ℝ) := by
    rw [show (4568397363148566143/4570000000000000000 : ℝ)+(171785410533/91400000000000 : ℝ)*((438/3125 : ℝ)+(5637/50000 : ℝ))=(1250155795860163/1250000000000000 : ℝ) by norm_num, show 1+(4450457129907749/12500000000000000000 : ℝ)+(7385884539857831/50000000000000000000 : ℝ)=(50025187713059488827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4450457129907749/12500000000000000000 : ℝ) ≤ ((4568397363148566143/4570000000000000000 : ℝ)+2*(171785410533/91400000000000 : ℝ)*(438/3125 : ℝ))^(2069/512 : ℝ) := by
    rw [show (4568397363148566143/4570000000000000000 : ℝ)+2*(171785410533/91400000000000 : ℝ)*(438/3125 : ℝ)=(10001761723112903/10000000000000000 : ℝ) by norm_num, show 1+2*(4450457129907749/12500000000000000000 : ℝ)=(6254450457129907749/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4568397363148566143/4570000000000000000 : ℝ)*(X 1 0+X 2 0)+(171785410533/91400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (4568397363148566143/4570000000000000000 : ℝ)) (alpha := (171785410533/91400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4568397363148566143/4570000000000000000 : ℝ)*(X 0 1+X 2 1)+(171785410533/91400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (4568397363148566143/4570000000000000000 : ℝ)) (alpha := (171785410533/91400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4568397363148566143/4570000000000000000 : ℝ)*(X 0 2+X 1 2)+(171785410533/91400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2069/512 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (438/3125 : ℝ)) (c := (4568397363148566143/4570000000000000000 : ℝ)) (alpha := (171785410533/91400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2194937037/10000000000 : ℝ)*X 0 0+(2697018087/5000000000 : ℝ)*X 0 1+(5264783337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344933071/10000000000 : ℝ)*X 1 0+(-2260510967/10000000000 : ℝ)*X 1 1+(5264783341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068986607/2000000000 : ℝ)*X 2 0+(5264783379/10000000000 : ℝ)*X 2 1+(-565127741/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186455067/5000000000 : ℝ)*X 0 0+(4247662243/10000000000 : ℝ)*X 0 1+(4501885293/10000000000 : ℝ)*X 0 2+(2186455067/5000000000 : ℝ)*X 1 0+(4247662243/10000000000 : ℝ)*X 1 1+(4501885293/10000000000 : ℝ)*X 1 2+(2186455067/5000000000 : ℝ)*X 2 0+(4247662243/10000000000 : ℝ)*X 2 1+(4501885293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-548735447/2500000000 : ℝ)*X 0 0+(5265107291/10000000000 : ℝ)*X 0 1+(1348427813/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312330373/10000000000 : ℝ)*X 1 0+(-2131583707/10000000000 : ℝ)*X 1 1+(2696855453/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332020689/625000000 : ℝ)*X 2 0+(84276731/156250000 : ℝ)*X 2 1+(-426316599/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1093230051/2500000000 : ℝ)*X 0 0+(56265603/125000000 : ℝ)*X 0 1+(4248301391/10000000000 : ℝ)*X 0 2+(1093230051/2500000000 : ℝ)*X 1 0+(56265603/125000000 : ℝ)*X 1 1+(4248301391/10000000000 : ℝ)*X 1 2+(1093230051/2500000000 : ℝ)*X 2 0+(56265603/125000000 : ℝ)*X 2 1+(4248301391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1084_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (497742274631188250512022331/57125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1789253879/100000000000000 : ℝ)*(base19) + (1589036167/100000000000000 : ℝ)*(base23) + (19790573/25000000000000 : ℝ)*(lower2) + (234487873/100000000000000 : ℝ)*(upper3) + (118860633/100000000000000 : ℝ)*(upper5) + (2917619342128439/50000000000000 : ℝ)*(major0) + (2917619342128439/50000000000000 : ℝ)*(major1) + (2917619342128439/50000000000000 : ℝ)*(major2) + (3868412750191037/50000000000000 : ℝ)*(sp0) + (773687147870067/10000000000000 : ℝ)*(sp1) + (3868435839459191/50000000000000 : ℝ)*(sp2) + (196678861070899/5000000000000 : ℝ)*(sp3) + (1910702899/4000000000000 : ℝ)*(sp4) + (6647175199/25000000000000 : ℝ)*(sp7) + (491700476264847/12500000000000 : ℝ)*(f.failure) + (7736873267954549/100000000000000 : ℝ)*(f.sum) + (7331470408823/2285000000000000000000000000 : ℝ)*base66 + (2860627023216309223/228500000000000000000000000000000 : ℝ)*base68 + (672231506706809223/228500000000000000000000000000000 : ℝ)*base70 + (4597332360116809223/228500000000000000000000000000000 : ℝ)*base72 + (2857780014663/2285000000000000000000000000 : ℝ)*base74 + (3935176964818809223/228500000000000000000000000000000 : ℝ)*base76 + (2297040063583190777/228500000000000000000000000000000 : ℝ)*base77 + (1210997019910809223/228500000000000000000000000000000 : ℝ)*base80 + (3135532819493/2285000000000000000000000000 : ℝ)*base82 + (383851/50000000000000000000 : ℝ)*base89 + (383851/50000000000000000000 : ℝ)*base91 + (383851/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (264148273638223746325403133/45700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (734007841/100000000000000 : ℝ)*(base19) + (8096243/500000000000 : ℝ)*(base23) + (12988071/5000000000000 : ℝ)*(lower2) + (13812327/20000000000000 : ℝ)*(upper3) + (21200293/25000000000000 : ℝ)*(lower4) + (1618177/4000000000000 : ℝ)*(upper5) + (1172923510722977/20000000000000 : ℝ)*(major0) + (1172923510722977/20000000000000 : ℝ)*(major1) + (1172923510722977/20000000000000 : ℝ)*(major2) + (42642519041/100000000000000 : ℝ)*(sp2) + (242994576847881/3125000000000 : ℝ)*(sp4) + (7775825725124351/100000000000000 : ℝ)*(sp5) + (7775782197364551/100000000000000 : ℝ)*(sp6) + (790681691085849/20000000000000 : ℝ)*(sp7) + (790681691085849/20000000000000 : ℝ)*(f.failure) + (242994576847881/3125000000000 : ℝ)*(f.sum) + (988831774487/182800000000000000000000000 : ℝ)*base66 + (291715038749382289/91400000000000000000000000000000 : ℝ)*base68 + (473547433289182289/91400000000000000000000000000000 : ℝ)*base70 + (1029253676937217711/91400000000000000000000000000000 : ℝ)*base71 + (682331023039/914000000000000000000000000 : ℝ)*base73 + (1209230385939982289/91400000000000000000000000000000 : ℝ)*base76 + (1563638699266817711/91400000000000000000000000000000 : ℝ)*base77 + (1500372703250782289/91400000000000000000000000000000 : ℝ)*base80 + (5888117363023/914000000000000000000000000 : ℝ)*base82 + (44317/80000000000000000000 : ℝ)*base89 + (44317/80000000000000000000 : ℝ)*base91 + (44317/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1084_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (438/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1084_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1084_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1084_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1084_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1084_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2069/512 : ℝ) ≤ p) (hpb : p ≤ (8277/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5933733/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2813/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2819/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1084_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
