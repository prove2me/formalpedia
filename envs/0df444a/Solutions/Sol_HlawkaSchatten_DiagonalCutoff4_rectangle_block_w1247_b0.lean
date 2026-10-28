-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1247_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:22:12.99811+00:00
-- url     : https://prove2.me/submissions/462368f4-bf8c-4bd6-84dc-080025a511c9

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
theorem support_rectangle_w1247_s0_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1859018279/10000000000 : ℝ)*x 0 + (3015189541/5000000000 : ℝ)*x 1 + (2396803283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1859018279/10000000000 : ℝ)^1055 ≤ (10843307625129/100000000000000 : ℝ)^799 := by
    have hnat : (1859018279 : ℕ)^1055*100000000000000^799 ≤ 10843307625129^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859018279 10000000000 10843307625129 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3015189541/5000000000 : ℝ)^1055 ≤ (51282231857949/100000000000000 : ℝ)^799 := by
    have hnat : (3015189541 : ℕ)^1055*100000000000000^799 ≤ 51282231857949^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015189541 5000000000 51282231857949 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2396803283/5000000000 : ℝ)^1055 ≤ (9468615126309/25000000000000 : ℝ)^799 := by
    have hnat : (2396803283 : ℕ)^1055*25000000000000^799 ≤ 9468615126309^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396803283 5000000000 9468615126309 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1859018279/10000000000 : ℝ), (3015189541/5000000000 : ℝ), (2396803283/5000000000 : ℝ)] ![(10843307625129/100000000000000 : ℝ), (51282231857949/100000000000000 : ℝ), (9468615126309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1859018279/10000000000 : ℝ)|^1055 ≤ (10843307625129/100000000000000 : ℝ)^799
        have hw : |(-1859018279/10000000000 : ℝ)|=(1859018279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3015189541/5000000000 : ℝ)|^1055 ≤ (51282231857949/100000000000000 : ℝ)^799
        have hw : |(3015189541/5000000000 : ℝ)|=(3015189541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2396803283/5000000000 : ℝ)|^1055 ≤ (9468615126309/25000000000000 : ℝ)^799
        have hw : |(2396803283/5000000000 : ℝ)|=(2396803283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s0_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1102175563/2000000000 : ℝ)*x 0 + (-641479171/2500000000 : ℝ)*x 1 + (1198401627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102175563/2000000000 : ℝ)^1055 ≤ (45531063146781/100000000000000 : ℝ)^799 := by
    have hnat : (1102175563 : ℕ)^1055*100000000000000^799 ≤ 45531063146781^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102175563 2000000000 45531063146781 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641479171/2500000000 : ℝ)^1055 ≤ (8297238472549/50000000000000 : ℝ)^799 := by
    have hnat : (641479171 : ℕ)^1055*50000000000000^799 ≤ 8297238472549^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641479171 2500000000 8297238472549 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198401627/2500000000 : ℝ)^1055 ≤ (37874459900149/100000000000000 : ℝ)^799 := by
    have hnat : (1198401627 : ℕ)^1055*100000000000000^799 ≤ 37874459900149^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198401627 2500000000 37874459900149 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102175563/2000000000 : ℝ), (-641479171/2500000000 : ℝ), (1198401627/2500000000 : ℝ)] ![(45531063146781/100000000000000 : ℝ), (8297238472549/50000000000000 : ℝ), (37874459900149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102175563/2000000000 : ℝ)|^1055 ≤ (45531063146781/100000000000000 : ℝ)^799
        have hw : |(1102175563/2000000000 : ℝ)|=(1102175563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-641479171/2500000000 : ℝ)|^1055 ≤ (8297238472549/50000000000000 : ℝ)^799
        have hw : |(-641479171/2500000000 : ℝ)|=(641479171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198401627/2500000000 : ℝ)|^1055 ≤ (37874459900149/100000000000000 : ℝ)^799
        have hw : |(1198401627/2500000000 : ℝ)|=(1198401627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s0_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5510877731/10000000000 : ℝ)*x 0 + (4793606597/10000000000 : ℝ)*x 1 + (-1282958341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510877731/10000000000 : ℝ)^1055 ≤ (5691382778801/12500000000000 : ℝ)^799 := by
    have hnat : (5510877731 : ℕ)^1055*12500000000000^799 ≤ 5691382778801^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510877731 10000000000 5691382778801 12500000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4793606597/10000000000 : ℝ)^1055 ≤ (7574892165729/20000000000000 : ℝ)^799 := by
    have hnat : (4793606597 : ℕ)^1055*20000000000000^799 ≤ 7574892165729^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793606597 10000000000 7574892165729 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1282958341/5000000000 : ℝ)^1055 ≤ (16594476928019/100000000000000 : ℝ)^799 := by
    have hnat : (1282958341 : ℕ)^1055*100000000000000^799 ≤ 16594476928019^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282958341 5000000000 16594476928019 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510877731/10000000000 : ℝ), (4793606597/10000000000 : ℝ), (-1282958341/5000000000 : ℝ)] ![(5691382778801/12500000000000 : ℝ), (7574892165729/20000000000000 : ℝ), (16594476928019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510877731/10000000000 : ℝ)|^1055 ≤ (5691382778801/12500000000000 : ℝ)^799
        have hw : |(5510877731/10000000000 : ℝ)|=(5510877731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4793606597/10000000000 : ℝ)|^1055 ≤ (7574892165729/20000000000000 : ℝ)^799
        have hw : |(4793606597/10000000000 : ℝ)|=(4793606597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1282958341/5000000000 : ℝ)|^1055 ≤ (16594476928019/100000000000000 : ℝ)^799
        have hw : |(-1282958341/5000000000 : ℝ)|=(1282958341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s0_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2096314553/5000000000 : ℝ)*x 0 + (623340871/2000000000 : ℝ)*x 1 + (10992201/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096314553/5000000000 : ℝ)^1055 ≤ (31734445404877/100000000000000 : ℝ)^799 := by
    have hnat : (2096314553 : ℕ)^1055*100000000000000^799 ≤ 31734445404877^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096314553 5000000000 31734445404877 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623340871/2000000000 : ℝ)^1055 ≤ (21452377323381/100000000000000 : ℝ)^799 := by
    have hnat : (623340871 : ℕ)^1055*100000000000000^799 ≤ 21452377323381^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623340871 2000000000 21452377323381 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10992201/19531250 : ℝ)^1055 ≤ (11703294313341/25000000000000 : ℝ)^799 := by
    have hnat : (10992201 : ℕ)^1055*25000000000000^799 ≤ 11703294313341^799*19531250^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10992201 19531250 11703294313341 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096314553/5000000000 : ℝ), (623340871/2000000000 : ℝ), (10992201/19531250 : ℝ)] ![(31734445404877/100000000000000 : ℝ), (21452377323381/100000000000000 : ℝ), (11703294313341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096314553/5000000000 : ℝ)|^1055 ≤ (31734445404877/100000000000000 : ℝ)^799
        have hw : |(2096314553/5000000000 : ℝ)|=(2096314553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623340871/2000000000 : ℝ)|^1055 ≤ (21452377323381/100000000000000 : ℝ)^799
        have hw : |(623340871/2000000000 : ℝ)|=(623340871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10992201/19531250 : ℝ)|^1055 ≤ (11703294313341/25000000000000 : ℝ)^799
        have hw : |(10992201/19531250 : ℝ)|=(10992201/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s0_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1863861591/10000000000 : ℝ)*x 0 + (4825452881/10000000000 : ℝ)*x 1 + (5997406983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863861591/10000000000 : ℝ)^1055 ≤ (10880624680161/100000000000000 : ℝ)^799 := by
    have hnat : (1863861591 : ℕ)^1055*100000000000000^799 ≤ 10880624680161^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863861591 10000000000 10880624680161 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4825452881/10000000000 : ℝ)^1055 ≤ (38207051290219/100000000000000 : ℝ)^799 := by
    have hnat : (4825452881 : ℕ)^1055*100000000000000^799 ≤ 38207051290219^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4825452881 10000000000 38207051290219 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5997406983/10000000000 : ℝ)^1055 ≤ (50912324020987/100000000000000 : ℝ)^799 := by
    have hnat : (5997406983 : ℕ)^1055*100000000000000^799 ≤ 50912324020987^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5997406983 10000000000 50912324020987 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1863861591/10000000000 : ℝ), (4825452881/10000000000 : ℝ), (5997406983/10000000000 : ℝ)] ![(10880624680161/100000000000000 : ℝ), (38207051290219/100000000000000 : ℝ), (50912324020987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1863861591/10000000000 : ℝ)|^1055 ≤ (10880624680161/100000000000000 : ℝ)^799
        have hw : |(-1863861591/10000000000 : ℝ)|=(1863861591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4825452881/10000000000 : ℝ)|^1055 ≤ (38207051290219/100000000000000 : ℝ)^799
        have hw : |(4825452881/10000000000 : ℝ)|=(4825452881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5997406983/10000000000 : ℝ)|^1055 ≤ (50912324020987/100000000000000 : ℝ)^799
        have hw : |(5997406983/10000000000 : ℝ)|=(5997406983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s0_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5174348417/10000000000 : ℝ)*x 0 + (-1362114007/10000000000 : ℝ)*x 1 + (1199481861/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174348417/10000000000 : ℝ)^1055 ≤ (10474055974009/25000000000000 : ℝ)^799 := by
    have hnat : (5174348417 : ℕ)^1055*25000000000000^799 ≤ 10474055974009^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174348417 10000000000 10474055974009 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362114007/10000000000 : ℝ)^1055 ≤ (1797856507551/25000000000000 : ℝ)^799 := by
    have hnat : (1362114007 : ℕ)^1055*25000000000000^799 ≤ 1797856507551^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362114007 10000000000 1797856507551 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199481861/2000000000 : ℝ)^1055 ≤ (50912350048179/100000000000000 : ℝ)^799 := by
    have hnat : (1199481861 : ℕ)^1055*100000000000000^799 ≤ 50912350048179^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199481861 2000000000 50912350048179 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174348417/10000000000 : ℝ), (-1362114007/10000000000 : ℝ), (1199481861/2000000000 : ℝ)] ![(10474055974009/25000000000000 : ℝ), (1797856507551/25000000000000 : ℝ), (50912350048179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174348417/10000000000 : ℝ)|^1055 ≤ (10474055974009/25000000000000 : ℝ)^799
        have hw : |(5174348417/10000000000 : ℝ)|=(5174348417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1362114007/10000000000 : ℝ)|^1055 ≤ (1797856507551/25000000000000 : ℝ)^799
        have hw : |(-1362114007/10000000000 : ℝ)|=(1362114007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199481861/2000000000 : ℝ)|^1055 ≤ (50912350048179/100000000000000 : ℝ)^799
        have hw : |(1199481861/2000000000 : ℝ)|=(1199481861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s0_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1034869873/2000000000 : ℝ)*x 0 + (239896297/400000000 : ℝ)*x 1 + (-681057789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034869873/2000000000 : ℝ)^1055 ≤ (20948117015629/50000000000000 : ℝ)^799 := by
    have hnat : (1034869873 : ℕ)^1055*50000000000000^799 ≤ 20948117015629^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034869873 2000000000 20948117015629 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239896297/400000000 : ℝ)^1055 ≤ (3182020560959/6250000000000 : ℝ)^799 := by
    have hnat : (239896297 : ℕ)^1055*6250000000000^799 ≤ 3182020560959^799*400000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239896297 400000000 3182020560959 6250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681057789/5000000000 : ℝ)^1055 ≤ (7191436981953/100000000000000 : ℝ)^799 := by
    have hnat : (681057789 : ℕ)^1055*100000000000000^799 ≤ 7191436981953^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681057789 5000000000 7191436981953 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034869873/2000000000 : ℝ), (239896297/400000000 : ℝ), (-681057789/5000000000 : ℝ)] ![(20948117015629/50000000000000 : ℝ), (3182020560959/6250000000000 : ℝ), (7191436981953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034869873/2000000000 : ℝ)|^1055 ≤ (20948117015629/50000000000000 : ℝ)^799
        have hw : |(1034869873/2000000000 : ℝ)|=(1034869873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(239896297/400000000 : ℝ)|^1055 ≤ (3182020560959/6250000000000 : ℝ)^799
        have hw : |(239896297/400000000 : ℝ)|=(239896297/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-681057789/5000000000 : ℝ)|^1055 ≤ (7191436981953/100000000000000 : ℝ)^799
        have hw : |(-681057789/5000000000 : ℝ)|=(681057789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s0_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1050616241/2500000000 : ℝ)*x 0 + (2781673713/5000000000 : ℝ)*x 1 + (3183649253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050616241/2500000000 : ℝ)^1055 ≤ (31832784340007/100000000000000 : ℝ)^799 := by
    have hnat : (1050616241 : ℕ)^1055*100000000000000^799 ≤ 31832784340007^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050616241 2500000000 31832784340007 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2781673713/5000000000 : ℝ)^1055 ≤ (46104335542321/100000000000000 : ℝ)^799 := by
    have hnat : (2781673713 : ℕ)^1055*100000000000000^799 ≤ 46104335542321^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2781673713 5000000000 46104335542321 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183649253/10000000000 : ℝ)^1055 ≤ (22062880102419/100000000000000 : ℝ)^799 := by
    have hnat : (3183649253 : ℕ)^1055*100000000000000^799 ≤ 22062880102419^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183649253 10000000000 22062880102419 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050616241/2500000000 : ℝ), (2781673713/5000000000 : ℝ), (3183649253/10000000000 : ℝ)] ![(31832784340007/100000000000000 : ℝ), (46104335542321/100000000000000 : ℝ), (22062880102419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050616241/2500000000 : ℝ)|^1055 ≤ (31832784340007/100000000000000 : ℝ)^799
        have hw : |(1050616241/2500000000 : ℝ)|=(1050616241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2781673713/5000000000 : ℝ)|^1055 ≤ (46104335542321/100000000000000 : ℝ)^799
        have hw : |(2781673713/5000000000 : ℝ)|=(2781673713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183649253/10000000000 : ℝ)|^1055 ≤ (22062880102419/100000000000000 : ℝ)^799
        have hw : |(3183649253/10000000000 : ℝ)|=(3183649253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (419/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27417/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8439/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8439 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8439*1^2048 ≤ 0^2048*1^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8439/2048 : ℝ) ≤ (1146083416261625403/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8439 ≤ (1146083416261625403/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8439*50000000000000000000^2048 ≤ 1146083416261625403^2048*5^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1146083416261625403 50000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1146083416261625403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8439 := by
      have hnat : (1 : ℕ)^2048*1^8439 ≤ 1^8439*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51146083416261625403/50000000000000000000 : ℝ) ≤ (2513787627774907/2500000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (51146083416261625403/50000000000000000000 : ℝ)^2048 ≤ (2513787627774907/2500000000000000 : ℝ)^8439 := by
      have hnat : (51146083416261625403 : ℕ)^2048*2500000000000000^8439 ≤ 2513787627774907^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51146083416261625403 50000000000000000000 2513787627774907 2500000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513787627774907/2500000000000000 : ℝ)) (X := (51146083416261625403/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26146083416261625403/25000000000000000000 : ℝ) ≤ (1263787627774907/1250000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (26146083416261625403/25000000000000000000 : ℝ)^2048 ≤ (1263787627774907/1250000000000000 : ℝ)^8439 := by
      have hnat : (26146083416261625403 : ℕ)^2048*1250000000000000^8439 ≤ 1263787627774907^8439*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26146083416261625403 25000000000000000000 1263787627774907 1250000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263787627774907/1250000000000000 : ℝ)) (X := (26146083416261625403/25000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13787627774907/1000000000000000 : ℝ)*(0 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(13787627774907/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1146083416261625403/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13787627774907/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (1 : ℝ)+(13787627774907/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2513787627774907/2500000000000000 : ℝ) by norm_num, show 1+(1146083416261625403/50000000000000000000 : ℝ)+(0 : ℝ)=(51146083416261625403/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1146083416261625403/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13787627774907/1000000000000000 : ℝ)*(2/5 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(13787627774907/1000000000000000 : ℝ)*(2/5 : ℝ)=(1263787627774907/1250000000000000 : ℝ) by norm_num, show 1+2*(1146083416261625403/50000000000000000000 : ℝ)=(26146083416261625403/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13787627774907/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13787627774907/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13787627774907/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13787627774907/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13787627774907/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13787627774907/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1859018279/10000000000 : ℝ)*X 0 0+(3015189541/5000000000 : ℝ)*X 0 1+(2396803283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1102175563/2000000000 : ℝ)*X 1 0+(-641479171/2500000000 : ℝ)*X 1 1+(1198401627/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510877731/10000000000 : ℝ)*X 2 0+(4793606597/10000000000 : ℝ)*X 2 1+(-1282958341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2096314553/5000000000 : ℝ)*X 0 0+(623340871/2000000000 : ℝ)*X 0 1+(10992201/19531250 : ℝ)*X 0 2+(2096314553/5000000000 : ℝ)*X 1 0+(623340871/2000000000 : ℝ)*X 1 1+(10992201/19531250 : ℝ)*X 1 2+(2096314553/5000000000 : ℝ)*X 2 0+(623340871/2000000000 : ℝ)*X 2 1+(10992201/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1863861591/10000000000 : ℝ)*X 0 0+(4825452881/10000000000 : ℝ)*X 0 1+(5997406983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174348417/10000000000 : ℝ)*X 1 0+(-1362114007/10000000000 : ℝ)*X 1 1+(1199481861/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034869873/2000000000 : ℝ)*X 2 0+(239896297/400000000 : ℝ)*X 2 1+(-681057789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050616241/2500000000 : ℝ)*X 0 0+(2781673713/5000000000 : ℝ)*X 0 1+(3183649253/10000000000 : ℝ)*X 0 2+(1050616241/2500000000 : ℝ)*X 1 0+(2781673713/5000000000 : ℝ)*X 1 1+(3183649253/10000000000 : ℝ)*X 1 2+(1050616241/2500000000 : ℝ)*X 2 0+(2781673713/5000000000 : ℝ)*X 2 1+(3183649253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44917844263242868777107/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57723183/100000000000000 : ℝ)*(base1) + (548743349/50000000000000 : ℝ)*(base19) + (1013036639/100000000000000 : ℝ)*(base23) + (72125501/100000000000000 : ℝ)*(base24) + (244120207/100000000000000 : ℝ)*(upper3) + (603382592015133/100000000000000 : ℝ)*(major0) + (603382592015133/100000000000000 : ℝ)*(major1) + (603382592015133/100000000000000 : ℝ)*(major2) + (25267495283417/3125000000000 : ℝ)*(sp0) + (101070142965369/12500000000000 : ℝ)*(sp1) + (808561156047511/100000000000000 : ℝ)*(sp2) + (398200846702027/100000000000000 : ℝ)*(sp3) + (2449863489/100000000000000 : ℝ)*(sp4) + (7554677/400000000000 : ℝ)*(sp7) + (398202793094461/100000000000000 : ℝ)*(f.failure) + (16171244824193/2000000000000 : ℝ)*(f.sum) + (114206817317631/50000000000000000000000000000 : ℝ)*base65 + (449599851467631/100000000000000000000000000000 : ℝ)*base67 + (1226386335167631/100000000000000000000000000000 : ℝ)*base69 + (536223587467631/100000000000000000000000000000 : ℝ)*base71 + (172362715817631/50000000000000000000000000000 : ℝ)*base73 + (892074812667631/100000000000000000000000000000 : ℝ)*base75 + (369746821367631/100000000000000000000000000000 : ℝ)*base77 + (40220753532369/100000000000000000000000000000 : ℝ)*base80 + (545014943067631/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (27843599/10000000000000000000000 : ℝ)*base89 + (27843599/10000000000000000000000 : ℝ)*base91 + (27843599/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7096160013360218082423/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59822731/50000000000000 : ℝ)*(base1) + (332060783/100000000000000 : ℝ)*(base19) + (218032043/50000000000000 : ℝ)*(base23) + (9368023/12500000000000 : ℝ)*(upper3) + (318374571364937/50000000000000 : ℝ)*(major0) + (318374571364937/50000000000000 : ℝ)*(major1) + (318374571364937/50000000000000 : ℝ)*(major2) + (1531317227/100000000000000 : ℝ)*(sp1) + (726768301/100000000000000 : ℝ)*(sp2) + (669742189/100000000000000 : ℝ)*(sp3) + (426637642295787/50000000000000 : ℝ)*(sp4) + (426636650784051/50000000000000 : ℝ)*(sp5) + (34130960084549/4000000000000 : ℝ)*(sp6) + (210111141909123/50000000000000 : ℝ)*(sp7) + (420223073205897/100000000000000 : ℝ)*(f.failure) + (13332424452283/1562500000000 : ℝ)*(f.sum) + (86815889635859/25000000000000000000000000000 : ℝ)*base65 + (43097441014141/50000000000000000000000000000 : ℝ)*base68 + (314895095835859/50000000000000000000000000000 : ℝ)*base69 + (102232202385859/50000000000000000000000000000 : ℝ)*base71 + (79583490510859/25000000000000000000000000000 : ℝ)*base73 + (166138036635859/50000000000000000000000000000 : ℝ)*base75 + (52925896535859/50000000000000000000000000000 : ℝ)*base77 + (131559302585859/50000000000000000000000000000 : ℝ)*base79 + (201685306385859/25000000000000000000000000000 : ℝ)*base81 + (49671277/10000000000000000000000 : ℝ)*base90 + (49671277/10000000000000000000000 : ℝ)*base92 + (49671277/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1247_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (419/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27417/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1247_s1_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-257008723/1250000000 : ℝ)*x 0 + (709292741/1250000000 : ℝ)*x 1 + (627938547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257008723/1250000000 : ℝ)^1055 ≤ (154826339913/1250000000000 : ℝ)^799 := by
    have hnat : (257008723 : ℕ)^1055*1250000000000^799 ≤ 154826339913^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257008723 1250000000 154826339913 1250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (709292741/1250000000 : ℝ)^1055 ≤ (9464548512043/20000000000000 : ℝ)^799 := by
    have hnat : (709292741 : ℕ)^1055*20000000000000^799 ≤ 9464548512043^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709292741 1250000000 9464548512043 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627938547/1250000000 : ℝ)^1055 ≤ (40291150224069/100000000000000 : ℝ)^799 := by
    have hnat : (627938547 : ℕ)^1055*100000000000000^799 ≤ 40291150224069^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627938547 1250000000 40291150224069 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257008723/1250000000 : ℝ), (709292741/1250000000 : ℝ), (627938547/1250000000 : ℝ)] ![(154826339913/1250000000000 : ℝ), (9464548512043/20000000000000 : ℝ), (40291150224069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257008723/1250000000 : ℝ)|^1055 ≤ (154826339913/1250000000000 : ℝ)^799
        have hw : |(-257008723/1250000000 : ℝ)|=(257008723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(709292741/1250000000 : ℝ)|^1055 ≤ (9464548512043/20000000000000 : ℝ)^799
        have hw : |(709292741/1250000000 : ℝ)|=(709292741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627938547/1250000000 : ℝ)|^1055 ≤ (40291150224069/100000000000000 : ℝ)^799
        have hw : |(627938547/1250000000 : ℝ)|=(627938547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s1_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (541338399/1000000000 : ℝ)*x 0 + (-2405476173/10000000000 : ℝ)*x 1 + (5023508603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541338399/1000000000 : ℝ)^1055 ≤ (44470510526901/100000000000000 : ℝ)^799 := by
    have hnat : (541338399 : ℕ)^1055*100000000000000^799 ≤ 44470510526901^799*1000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541338399 1000000000 44470510526901 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2405476173/10000000000 : ℝ)^1055 ≤ (15238336831861/100000000000000 : ℝ)^799 := by
    have hnat : (2405476173 : ℕ)^1055*100000000000000^799 ≤ 15238336831861^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405476173 10000000000 15238336831861 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5023508603/10000000000 : ℝ)^1055 ≤ (20145576314033/50000000000000 : ℝ)^799 := by
    have hnat : (5023508603 : ℕ)^1055*50000000000000^799 ≤ 20145576314033^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023508603 10000000000 20145576314033 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541338399/1000000000 : ℝ), (-2405476173/10000000000 : ℝ), (5023508603/10000000000 : ℝ)] ![(44470510526901/100000000000000 : ℝ), (15238336831861/100000000000000 : ℝ), (20145576314033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541338399/1000000000 : ℝ)|^1055 ≤ (44470510526901/100000000000000 : ℝ)^799
        have hw : |(541338399/1000000000 : ℝ)|=(541338399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2405476173/10000000000 : ℝ)|^1055 ≤ (15238336831861/100000000000000 : ℝ)^799
        have hw : |(-2405476173/10000000000 : ℝ)|=(2405476173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5023508603/10000000000 : ℝ)|^1055 ≤ (20145576314033/50000000000000 : ℝ)^799
        have hw : |(5023508603/10000000000 : ℝ)|=(5023508603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s1_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5413384199/10000000000 : ℝ)*x 0 + (5023508453/10000000000 : ℝ)*x 1 + (-2405476091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413384199/10000000000 : ℝ)^1055 ≤ (138970352481/312500000000 : ℝ)^799 := by
    have hnat : (5413384199 : ℕ)^1055*312500000000^799 ≤ 138970352481^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413384199 10000000000 138970352481 312500000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5023508453/10000000000 : ℝ)^1055 ≤ (20145575519761/50000000000000 : ℝ)^799 := by
    have hnat : (5023508453 : ℕ)^1055*50000000000000^799 ≤ 20145575519761^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023508453 10000000000 20145575519761 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405476091/10000000000 : ℝ)^1055 ≤ (15238336145969/100000000000000 : ℝ)^799 := by
    have hnat : (2405476091 : ℕ)^1055*100000000000000^799 ≤ 15238336145969^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405476091 10000000000 15238336145969 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413384199/10000000000 : ℝ), (5023508453/10000000000 : ℝ), (-2405476091/10000000000 : ℝ)] ![(138970352481/312500000000 : ℝ), (20145575519761/50000000000000 : ℝ), (15238336145969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413384199/10000000000 : ℝ)|^1055 ≤ (138970352481/312500000000 : ℝ)^799
        have hw : |(5413384199/10000000000 : ℝ)|=(5413384199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5023508453/10000000000 : ℝ)|^1055 ≤ (20145575519761/50000000000000 : ℝ)^799
        have hw : |(5023508453/10000000000 : ℝ)|=(5023508453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2405476091/10000000000 : ℝ)|^1055 ≤ (15238336145969/100000000000000 : ℝ)^799
        have hw : |(-2405476091/10000000000 : ℝ)|=(2405476091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s1_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (861684737/2000000000 : ℝ)*x 0 + (369636673/1000000000 : ℝ)*x 1 + (2508951891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861684737/2000000000 : ℝ)^1055 ≤ (8224203484633/25000000000000 : ℝ)^799 := by
    have hnat : (861684737 : ℕ)^1055*25000000000000^799 ≤ 8224203484633^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861684737 2000000000 8224203484633 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369636673/1000000000 : ℝ)^1055 ≤ (839730610639/3125000000000 : ℝ)^799 := by
    have hnat : (369636673 : ℕ)^1055*3125000000000^799 ≤ 839730610639^799*1000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369636673 1000000000 839730610639 3125000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508951891/5000000000 : ℝ)^1055 ≤ (40231806509881/100000000000000 : ℝ)^799 := by
    have hnat : (2508951891 : ℕ)^1055*100000000000000^799 ≤ 40231806509881^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508951891 5000000000 40231806509881 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861684737/2000000000 : ℝ), (369636673/1000000000 : ℝ), (2508951891/5000000000 : ℝ)] ![(8224203484633/25000000000000 : ℝ), (839730610639/3125000000000 : ℝ), (40231806509881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861684737/2000000000 : ℝ)|^1055 ≤ (8224203484633/25000000000000 : ℝ)^799
        have hw : |(861684737/2000000000 : ℝ)|=(861684737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(369636673/1000000000 : ℝ)|^1055 ≤ (839730610639/3125000000000 : ℝ)^799
        have hw : |(369636673/1000000000 : ℝ)|=(369636673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508951891/5000000000 : ℝ)|^1055 ≤ (40231806509881/100000000000000 : ℝ)^799
        have hw : |(2508951891/5000000000 : ℝ)|=(2508951891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s1_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056739979/10000000000 : ℝ)*x 0 + (2516020333/5000000000 : ℝ)*x 1 + (5665647763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056739979/10000000000 : ℝ)^1055 ≤ (6195719206021/50000000000000 : ℝ)^799 := by
    have hnat : (2056739979 : ℕ)^1055*50000000000000^799 ≤ 6195719206021^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056739979 10000000000 6195719206021 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516020333/5000000000 : ℝ)^1055 ≤ (8076306860387/20000000000000 : ℝ)^799 := by
    have hnat : (2516020333 : ℕ)^1055*20000000000000^799 ≤ 8076306860387^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516020333 5000000000 8076306860387 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5665647763/10000000000 : ℝ)^1055 ≤ (9445405454403/20000000000000 : ℝ)^799 := by
    have hnat : (5665647763 : ℕ)^1055*20000000000000^799 ≤ 9445405454403^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665647763 10000000000 9445405454403 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056739979/10000000000 : ℝ), (2516020333/5000000000 : ℝ), (5665647763/10000000000 : ℝ)] ![(6195719206021/50000000000000 : ℝ), (8076306860387/20000000000000 : ℝ), (9445405454403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056739979/10000000000 : ℝ)|^1055 ≤ (6195719206021/50000000000000 : ℝ)^799
        have hw : |(-2056739979/10000000000 : ℝ)|=(2056739979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516020333/5000000000 : ℝ)|^1055 ≤ (8076306860387/20000000000000 : ℝ)^799
        have hw : |(2516020333/5000000000 : ℝ)|=(2516020333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5665647763/10000000000 : ℝ)|^1055 ≤ (9445405454403/20000000000000 : ℝ)^799
        have hw : |(5665647763/10000000000 : ℝ)|=(5665647763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s1_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1049134127/2000000000 : ℝ)*x 0 + (-1763336761/10000000000 : ℝ)*x 1 + (2832823993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049134127/2000000000 : ℝ)^1055 ≤ (2666276237069/6250000000000 : ℝ)^799 := by
    have hnat : (1049134127 : ℕ)^1055*6250000000000^799 ≤ 2666276237069^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049134127 2000000000 2666276237069 6250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1763336761/10000000000 : ℝ)^1055 ≤ (2022510093503/20000000000000 : ℝ)^799 := by
    have hnat : (1763336761 : ℕ)^1055*20000000000000^799 ≤ 2022510093503^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763336761 10000000000 2022510093503 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2832823993/5000000000 : ℝ)^1055 ≤ (944540594529/2000000000000 : ℝ)^799 := by
    have hnat : (2832823993 : ℕ)^1055*2000000000000^799 ≤ 944540594529^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832823993 5000000000 944540594529 2000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049134127/2000000000 : ℝ), (-1763336761/10000000000 : ℝ), (2832823993/5000000000 : ℝ)] ![(2666276237069/6250000000000 : ℝ), (2022510093503/20000000000000 : ℝ), (944540594529/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049134127/2000000000 : ℝ)|^1055 ≤ (2666276237069/6250000000000 : ℝ)^799
        have hw : |(1049134127/2000000000 : ℝ)|=(1049134127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1763336761/10000000000 : ℝ)|^1055 ≤ (2022510093503/20000000000000 : ℝ)^799
        have hw : |(-1763336761/10000000000 : ℝ)|=(1763336761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2832823993/5000000000 : ℝ)|^1055 ≤ (944540594529/2000000000000 : ℝ)^799
        have hw : |(2832823993/5000000000 : ℝ)|=(2832823993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s1_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1049134113/2000000000 : ℝ)*x 0 + (1133129561/2000000000 : ℝ)*x 1 + (-1763337123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049134113/2000000000 : ℝ)^1055 ≤ (42660419041433/100000000000000 : ℝ)^799 := by
    have hnat : (1049134113 : ℕ)^1055*100000000000000^799 ≤ 42660419041433^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049134113 2000000000 42660419041433 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133129561/2000000000 : ℝ)^1055 ≤ (9445405546857/20000000000000 : ℝ)^799 := by
    have hnat : (1133129561 : ℕ)^1055*20000000000000^799 ≤ 9445405546857^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133129561 2000000000 9445405546857 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1763337123/10000000000 : ℝ)^1055 ≤ (2528138302177/25000000000000 : ℝ)^799 := by
    have hnat : (1763337123 : ℕ)^1055*25000000000000^799 ≤ 2528138302177^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763337123 10000000000 2528138302177 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049134113/2000000000 : ℝ), (1133129561/2000000000 : ℝ), (-1763337123/10000000000 : ℝ)] ![(42660419041433/100000000000000 : ℝ), (9445405546857/20000000000000 : ℝ), (2528138302177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049134113/2000000000 : ℝ)|^1055 ≤ (42660419041433/100000000000000 : ℝ)^799
        have hw : |(1049134113/2000000000 : ℝ)|=(1049134113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133129561/2000000000 : ℝ)|^1055 ≤ (9445405546857/20000000000000 : ℝ)^799
        have hw : |(1133129561/2000000000 : ℝ)|=(1133129561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1763337123/10000000000 : ℝ)|^1055 ≤ (2528138302177/25000000000000 : ℝ)^799
        have hw : |(-1763337123/10000000000 : ℝ)|=(1763337123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s1_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (215489223/500000000 : ℝ)*x 0 + (2500289421/5000000000 : ℝ)*x 1 + (74280417/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215489223/500000000 : ℝ)^1055 ≤ (128556772617/390625000000 : ℝ)^799 := by
    have hnat : (215489223 : ℕ)^1055*390625000000^799 ≤ 128556772617^799*500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215489223 500000000 128556772617 390625000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500289421/5000000000 : ℝ)^1055 ≤ (320387978837/800000000000 : ℝ)^799 := by
    have hnat : (2500289421 : ℕ)^1055*800000000000^799 ≤ 320387978837^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500289421 5000000000 320387978837 800000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74280417/200000000 : ℝ)^1055 ≤ (27040968849379/100000000000000 : ℝ)^799 := by
    have hnat : (74280417 : ℕ)^1055*100000000000000^799 ≤ 27040968849379^799*200000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74280417 200000000 27040968849379 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215489223/500000000 : ℝ), (2500289421/5000000000 : ℝ), (74280417/200000000 : ℝ)] ![(128556772617/390625000000 : ℝ), (320387978837/800000000000 : ℝ), (27040968849379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215489223/500000000 : ℝ)|^1055 ≤ (128556772617/390625000000 : ℝ)^799
        have hw : |(215489223/500000000 : ℝ)|=(215489223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500289421/5000000000 : ℝ)|^1055 ≤ (320387978837/800000000000 : ℝ)^799
        have hw : |(2500289421/5000000000 : ℝ)|=(2500289421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74280417/200000000 : ℝ)|^1055 ≤ (27040968849379/100000000000000 : ℝ)^799
        have hw : |(74280417/200000000 : ℝ)|=(74280417/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27417/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6217/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19977/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27417/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27417/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (419/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27417/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27417/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (419/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27417/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27417/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (419/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (419/50000 : ℝ) ^ (8439/2048 : ℝ) ≤ (69254493057/25000000000000000000 : ℝ) := by
    have hpowers : (419/50000 : ℝ)^8439 ≤ (69254493057/25000000000000000000 : ℝ)^2048 := by
      have hnat : (419 : ℕ)^8439*25000000000000000000^2048 ≤ 69254493057^2048*50000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        419 50000 69254493057 25000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (419/50000 : ℝ)) (X := (69254493057/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27417/100000 : ℝ) ^ (8439/2048 : ℝ) ≤ (241697335654309741/50000000000000000000 : ℝ) := by
    have hpowers : (27417/100000 : ℝ)^8439 ≤ (241697335654309741/50000000000000000000 : ℝ)^2048 := by
      have hnat : (27417 : ℕ)^8439*50000000000000000000^2048 ≤ 241697335654309741^2048*100000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27417 100000 241697335654309741 50000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27417/100000 : ℝ)) (X := (241697335654309741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000069254493057/12500000000000000000 : ℝ) ≤ (10000000013445499/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (12500000069254493057/12500000000000000000 : ℝ)^2048 ≤ (10000000013445499/10000000000000000 : ℝ)^8439 := by
      have hnat : (12500000069254493057 : ℕ)^2048*10000000000000000^8439 ≤ 10000000013445499^8439*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000069254493057 12500000000000000000 10000000013445499 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000013445499/10000000000000000 : ℝ)) (X := (12500000069254493057/12500000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10048339494832659171/10000000000000000000 : ℝ) ≤ (2502927437696783/2500000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (10048339494832659171/10000000000000000000 : ℝ)^2048 ≤ (2502927437696783/2500000000000000 : ℝ)^8439 := by
      have hnat : (10048339494832659171 : ℕ)^2048*2500000000000000^8439 ≤ 2502927437696783^8439*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10048339494832659171 10000000000000000000 2502927437696783 2500000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502927437696783/2500000000000000 : ℝ)) (X := (10048339494832659171/10000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25241697335654309741/25000000000000000000 : ℝ) ≤ (2004683897625753/2000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (25241697335654309741/25000000000000000000 : ℝ)^2048 ≤ (2004683897625753/2000000000000000 : ℝ)^8439 := by
      have hnat : (25241697335654309741 : ℕ)^2048*2000000000000000^8439 ≤ 2004683897625753^8439*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25241697335654309741 25000000000000000000 2004683897625753 2000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004683897625753/2000000000000000 : ℝ)) (X := (25241697335654309741/25000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(69254493057/25000000000000000000 : ℝ) ≤ ((265770374837583341013/265790000000000000000 : ℝ)+2*(11709737341633/2657900000000000 : ℝ)*(419/50000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (265770374837583341013/265790000000000000000 : ℝ)+2*(11709737341633/2657900000000000 : ℝ)*(419/50000 : ℝ)=(10000000013445499/10000000000000000 : ℝ) by norm_num, show 1+2*(69254493057/25000000000000000000 : ℝ)=(12500000069254493057/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(241697335654309741/50000000000000000000 : ℝ)+(69254493057/25000000000000000000 : ℝ) ≤ ((265770374837583341013/265790000000000000000 : ℝ)+(11709737341633/2657900000000000 : ℝ)*((27417/100000 : ℝ)+(419/50000 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (265770374837583341013/265790000000000000000 : ℝ)+(11709737341633/2657900000000000 : ℝ)*((27417/100000 : ℝ)+(419/50000 : ℝ))=(2502927437696783/2500000000000000 : ℝ) by norm_num, show 1+(241697335654309741/50000000000000000000 : ℝ)+(69254493057/25000000000000000000 : ℝ)=(10048339494832659171/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(241697335654309741/50000000000000000000 : ℝ) ≤ ((265770374837583341013/265790000000000000000 : ℝ)+2*(11709737341633/2657900000000000 : ℝ)*(27417/100000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (265770374837583341013/265790000000000000000 : ℝ)+2*(11709737341633/2657900000000000 : ℝ)*(27417/100000 : ℝ)=(2004683897625753/2000000000000000 : ℝ) by norm_num, show 1+2*(241697335654309741/50000000000000000000 : ℝ)=(25241697335654309741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (265770374837583341013/265790000000000000000 : ℝ)*(X 1 0+X 2 0)+(11709737341633/2657900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (419/50000 : ℝ)) (hi := (27417/100000 : ℝ)) (c := (265770374837583341013/265790000000000000000 : ℝ)) (alpha := (11709737341633/2657900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (265770374837583341013/265790000000000000000 : ℝ)*(X 0 1+X 2 1)+(11709737341633/2657900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (419/50000 : ℝ)) (hi := (27417/100000 : ℝ)) (c := (265770374837583341013/265790000000000000000 : ℝ)) (alpha := (11709737341633/2657900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (265770374837583341013/265790000000000000000 : ℝ)*(X 0 2+X 1 2)+(11709737341633/2657900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (419/50000 : ℝ)) (hi := (27417/100000 : ℝ)) (c := (265770374837583341013/265790000000000000000 : ℝ)) (alpha := (11709737341633/2657900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-257008723/1250000000 : ℝ)*X 0 0+(709292741/1250000000 : ℝ)*X 0 1+(627938547/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541338399/1000000000 : ℝ)*X 1 0+(-2405476173/10000000000 : ℝ)*X 1 1+(5023508603/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5413384199/10000000000 : ℝ)*X 2 0+(5023508453/10000000000 : ℝ)*X 2 1+(-2405476091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((861684737/2000000000 : ℝ)*X 0 0+(369636673/1000000000 : ℝ)*X 0 1+(2508951891/5000000000 : ℝ)*X 0 2+(861684737/2000000000 : ℝ)*X 1 0+(369636673/1000000000 : ℝ)*X 1 1+(2508951891/5000000000 : ℝ)*X 1 2+(861684737/2000000000 : ℝ)*X 2 0+(369636673/1000000000 : ℝ)*X 2 1+(2508951891/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2056739979/10000000000 : ℝ)*X 0 0+(2516020333/5000000000 : ℝ)*X 0 1+(5665647763/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049134127/2000000000 : ℝ)*X 1 0+(-1763336761/10000000000 : ℝ)*X 1 1+(2832823993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1049134113/2000000000 : ℝ)*X 2 0+(1133129561/2000000000 : ℝ)*X 2 1+(-1763337123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((215489223/500000000 : ℝ)*X 0 0+(2500289421/5000000000 : ℝ)*X 0 1+(74280417/200000000 : ℝ)*X 0 2+(215489223/500000000 : ℝ)*X 1 0+(2500289421/5000000000 : ℝ)*X 1 1+(74280417/200000000 : ℝ)*X 1 2+(215489223/500000000 : ℝ)*X 2 0+(2500289421/5000000000 : ℝ)*X 2 1+(74280417/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (303060378551618142077959443/37970000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15697989/20000000000000 : ℝ)*(base1) + (351472803/20000000000000 : ℝ)*(base19) + (1816685599/100000000000000 : ℝ)*(base23) + (93767749/50000000000000 : ℝ)*(upper3) + (233472887/100000000000000 : ℝ)*(upper5) + (22932167828741/2000000000000 : ℝ)*(major0) + (22932167828741/2000000000000 : ℝ)*(major1) + (22932167828741/2000000000000 : ℝ)*(major2) + (768250450713641/50000000000000 : ℝ)*(sp0) + (96031855847137/6250000000000 : ℝ)*(sp1) + (48015926069769/3125000000000 : ℝ)*(sp2) + (37834990798489/5000000000000 : ℝ)*(sp3) + (10627980869/100000000000000 : ℝ)*(sp4) + (1292860921/25000000000000 : ℝ)*(sp7) + (47294066618963/6250000000000 : ℝ)*(f.failure) + (1536511450918207/100000000000000 : ℝ)*(f.sum) + (72781999242949/26579000000000000000000000000 : ℝ)*base66 + (3933564272041514633/531580000000000000000000000000000 : ℝ)*base67 + (3987930202007134633/531580000000000000000000000000000 : ℝ)*base69 + (2527362811479154633/531580000000000000000000000000000 : ℝ)*base71 + (22210312984841/13289500000000000000000000000 : ℝ)*base73 + (1338583100244125367/531580000000000000000000000000000 : ℝ)*base76 + (2278809339758194633/531580000000000000000000000000000 : ℝ)*base77 + (2914534732597405367/531580000000000000000000000000000 : ℝ)*base80 + (13999290157001/13289500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3142017/625000000000000000000 : ℝ)*base89 + (3142017/625000000000000000000 : ℝ)*base91 + (3142017/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (360874736477407399616628603/132895000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12378173/100000000000000 : ℝ)*(base1) + (470517293/100000000000000 : ℝ)*(base19) + (21245101/5000000000000 : ℝ)*(base23) + (74977541/100000000000000 : ℝ)*(upper3) + (6809399/12500000000000 : ℝ)*(upper5) + (23555326598523/2000000000000 : ℝ)*(major0) + (23555326598523/2000000000000 : ℝ)*(major1) + (23555326598523/2000000000000 : ℝ)*(major2) + (2447186539/100000000000000 : ℝ)*(sp1) + (1679181721/100000000000000 : ℝ)*(sp2) + (19728310137379/1250000000000 : ℝ)*(sp4) + (394565470227079/25000000000000 : ℝ)*(sp5) + (1578262694528407/100000000000000 : ℝ)*(sp6) + (388633879172859/50000000000000 : ℝ)*(sp7) + (777267770723891/100000000000000 : ℝ)*(f.failure) + (394566199653037/25000000000000 : ℝ)*(f.sum) + (658704139959/2657900000000000000000000000 : ℝ)*base65 + (3161615004128943799/531580000000000000000000000000000 : ℝ)*base67 + (1879591406610223799/531580000000000000000000000000000 : ℝ)*base69 + (124272203948023799/531580000000000000000000000000000 : ℝ)*base71 + (80744582158283/26579000000000000000000000000 : ℝ)*base73 + (1940355023076083799/531580000000000000000000000000000 : ℝ)*base75 + (2392707371868903799/531580000000000000000000000000000 : ℝ)*base77 + (2273222304893296201/531580000000000000000000000000000 : ℝ)*base80 + (59223768501489/13289500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (69931969/10000000000000000000000 : ℝ)*base89 + (69931969/10000000000000000000000 : ℝ)*base91 + (69931969/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1247_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27417/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (419/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6217/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19977/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1247_s2_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103862837/10000000000 : ℝ)*x 0 + (1372983233/2500000000 : ℝ)*x 1 + (80866141/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103862837/10000000000 : ℝ)^1055 ≤ (2553535271527/20000000000000 : ℝ)^799 := by
    have hnat : (2103862837 : ℕ)^1055*20000000000000^799 ≤ 2553535271527^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103862837 10000000000 2553535271527 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372983233/2500000000 : ℝ)^1055 ≤ (22662251820037/50000000000000 : ℝ)^799 := by
    have hnat : (1372983233 : ℕ)^1055*50000000000000^799 ≤ 22662251820037^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372983233 2500000000 22662251820037 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80866141/156250000 : ℝ)^1055 ≤ (41907819994091/100000000000000 : ℝ)^799 := by
    have hnat : (80866141 : ℕ)^1055*100000000000000^799 ≤ 41907819994091^799*156250000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80866141 156250000 41907819994091 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103862837/10000000000 : ℝ), (1372983233/2500000000 : ℝ), (80866141/156250000 : ℝ)] ![(2553535271527/20000000000000 : ℝ), (22662251820037/50000000000000 : ℝ), (41907819994091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103862837/10000000000 : ℝ)|^1055 ≤ (2553535271527/20000000000000 : ℝ)^799
        have hw : |(-2103862837/10000000000 : ℝ)|=(2103862837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372983233/2500000000 : ℝ)|^1055 ≤ (22662251820037/50000000000000 : ℝ)^799
        have hw : |(1372983233/2500000000 : ℝ)|=(1372983233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80866141/156250000 : ℝ)|^1055 ≤ (41907819994091/100000000000000 : ℝ)^799
        have hw : |(80866141/156250000 : ℝ)|=(80866141/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s2_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369480959/10000000000 : ℝ)*x 0 + (-2267778871/10000000000 : ℝ)*x 1 + (1293858269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369480959/10000000000 : ℝ)^1055 ≤ (21997457475977/50000000000000 : ℝ)^799 := by
    have hnat : (5369480959 : ℕ)^1055*50000000000000^799 ≤ 21997457475977^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369480959 10000000000 21997457475977 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267778871/10000000000 : ℝ)^1055 ≤ (14097264484643/100000000000000 : ℝ)^799 := by
    have hnat : (2267778871 : ℕ)^1055*100000000000000^799 ≤ 14097264484643^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267778871 10000000000 14097264484643 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293858269/2500000000 : ℝ)^1055 ≤ (41907820550069/100000000000000 : ℝ)^799 := by
    have hnat : (1293858269 : ℕ)^1055*100000000000000^799 ≤ 41907820550069^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293858269 2500000000 41907820550069 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369480959/10000000000 : ℝ), (-2267778871/10000000000 : ℝ), (1293858269/2500000000 : ℝ)] ![(21997457475977/50000000000000 : ℝ), (14097264484643/100000000000000 : ℝ), (41907820550069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369480959/10000000000 : ℝ)|^1055 ≤ (21997457475977/50000000000000 : ℝ)^799
        have hw : |(5369480959/10000000000 : ℝ)|=(5369480959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2267778871/10000000000 : ℝ)|^1055 ≤ (14097264484643/100000000000000 : ℝ)^799
        have hw : |(-2267778871/10000000000 : ℝ)|=(2267778871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293858269/2500000000 : ℝ)|^1055 ≤ (41907820550069/100000000000000 : ℝ)^799
        have hw : |(1293858269/2500000000 : ℝ)|=(1293858269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s2_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369480829/10000000000 : ℝ)*x 0 + (517543317/1000000000 : ℝ)*x 1 + (-2267778919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369480829/10000000000 : ℝ)^1055 ≤ (43994913545521/100000000000000 : ℝ)^799 := by
    have hnat : (5369480829 : ℕ)^1055*100000000000000^799 ≤ 43994913545521^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369480829 10000000000 43994913545521 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517543317/1000000000 : ℝ)^1055 ≤ (8381564311021/20000000000000 : ℝ)^799 := by
    have hnat : (517543317 : ℕ)^1055*20000000000000^799 ≤ 8381564311021^799*1000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517543317 1000000000 8381564311021 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267778919/10000000000 : ℝ)^1055 ≤ (1409726487863/10000000000000 : ℝ)^799 := by
    have hnat : (2267778919 : ℕ)^1055*10000000000000^799 ≤ 1409726487863^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267778919 10000000000 1409726487863 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369480829/10000000000 : ℝ), (517543317/1000000000 : ℝ), (-2267778919/10000000000 : ℝ)] ![(43994913545521/100000000000000 : ℝ), (8381564311021/20000000000000 : ℝ), (1409726487863/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369480829/10000000000 : ℝ)|^1055 ≤ (43994913545521/100000000000000 : ℝ)^799
        have hw : |(5369480829/10000000000 : ℝ)|=(5369480829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517543317/1000000000 : ℝ)|^1055 ≤ (8381564311021/20000000000000 : ℝ)^799
        have hw : |(517543317/1000000000 : ℝ)|=(517543317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2267778919/10000000000 : ℝ)|^1055 ≤ (1409726487863/10000000000000 : ℝ)^799
        have hw : |(-2267778919/10000000000 : ℝ)|=(2267778919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s2_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (135670171/312500000 : ℝ)*x 0 + (2015809801/5000000000 : ℝ)*x 1 + (4674281729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135670171/312500000 : ℝ)^1055 ≤ (33230143388389/100000000000000 : ℝ)^799 := by
    have hnat : (135670171 : ℕ)^1055*100000000000000^799 ≤ 33230143388389^799*312500000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135670171 312500000 33230143388389 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015809801/5000000000 : ℝ)^1055 ≤ (1883453988513/6250000000000 : ℝ)^799 := by
    have hnat : (2015809801 : ℕ)^1055*6250000000000^799 ≤ 1883453988513^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015809801 5000000000 1883453988513 6250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4674281729/10000000000 : ℝ)^1055 ≤ (7326918556211/20000000000000 : ℝ)^799 := by
    have hnat : (4674281729 : ℕ)^1055*20000000000000^799 ≤ 7326918556211^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4674281729 10000000000 7326918556211 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135670171/312500000 : ℝ), (2015809801/5000000000 : ℝ), (4674281729/10000000000 : ℝ)] ![(33230143388389/100000000000000 : ℝ), (1883453988513/6250000000000 : ℝ), (7326918556211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135670171/312500000 : ℝ)|^1055 ≤ (33230143388389/100000000000000 : ℝ)^799
        have hw : |(135670171/312500000 : ℝ)|=(135670171/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015809801/5000000000 : ℝ)|^1055 ≤ (1883453988513/6250000000000 : ℝ)^799
        have hw : |(2015809801/5000000000 : ℝ)|=(2015809801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4674281729/10000000000 : ℝ)|^1055 ≤ (7326918556211/20000000000000 : ℝ)^799
        have hw : |(4674281729/10000000000 : ℝ)|=(4674281729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s2_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-420788043/2000000000 : ℝ)*x 0 + (647182571/1250000000 : ℝ)*x 1 + (5489886437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420788043/2000000000 : ℝ)^1055 ≤ (6384148199157/50000000000000 : ℝ)^799 := by
    have hnat : (420788043 : ℕ)^1055*50000000000000^799 ≤ 6384148199157^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420788043 2000000000 6384148199157 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647182571/1250000000 : ℝ)^1055 ≤ (8385899922147/20000000000000 : ℝ)^799 := by
    have hnat : (647182571 : ℕ)^1055*20000000000000^799 ≤ 8385899922147^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647182571 1250000000 8385899922147 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5489886437/10000000000 : ℝ)^1055 ≤ (11325550994637/25000000000000 : ℝ)^799 := by
    have hnat : (5489886437 : ℕ)^1055*25000000000000^799 ≤ 11325550994637^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489886437 10000000000 11325550994637 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420788043/2000000000 : ℝ), (647182571/1250000000 : ℝ), (5489886437/10000000000 : ℝ)] ![(6384148199157/50000000000000 : ℝ), (8385899922147/20000000000000 : ℝ), (11325550994637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420788043/2000000000 : ℝ)|^1055 ≤ (6384148199157/50000000000000 : ℝ)^799
        have hw : |(-420788043/2000000000 : ℝ)|=(420788043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647182571/1250000000 : ℝ)|^1055 ≤ (8385899922147/20000000000000 : ℝ)^799
        have hw : |(647182571/1250000000 : ℝ)|=(647182571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5489886437/10000000000 : ℝ)|^1055 ≤ (11325550994637/25000000000000 : ℝ)^799
        have hw : |(5489886437/10000000000 : ℝ)|=(5489886437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s2_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5288630351/10000000000 : ℝ)*x 0 + (-976662637/5000000000 : ℝ)*x 1 + (2744943241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288630351/10000000000 : ℝ)^1055 ≤ (4312233211063/10000000000000 : ℝ)^799 := by
    have hnat : (5288630351 : ℕ)^1055*10000000000000^799 ≤ 4312233211063^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288630351 10000000000 4312233211063 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (976662637/5000000000 : ℝ)^1055 ≤ (11575463407451/100000000000000 : ℝ)^799 := by
    have hnat : (976662637 : ℕ)^1055*100000000000000^799 ≤ 11575463407451^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976662637 5000000000 11575463407451 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2744943241/5000000000 : ℝ)^1055 ≤ (22651102234431/50000000000000 : ℝ)^799 := by
    have hnat : (2744943241 : ℕ)^1055*50000000000000^799 ≤ 22651102234431^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744943241 5000000000 22651102234431 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288630351/10000000000 : ℝ), (-976662637/5000000000 : ℝ), (2744943241/5000000000 : ℝ)] ![(4312233211063/10000000000000 : ℝ), (11575463407451/100000000000000 : ℝ), (22651102234431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288630351/10000000000 : ℝ)|^1055 ≤ (4312233211063/10000000000000 : ℝ)^799
        have hw : |(5288630351/10000000000 : ℝ)|=(5288630351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-976662637/5000000000 : ℝ)|^1055 ≤ (11575463407451/100000000000000 : ℝ)^799
        have hw : |(-976662637/5000000000 : ℝ)|=(976662637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2744943241/5000000000 : ℝ)|^1055 ≤ (22651102234431/50000000000000 : ℝ)^799
        have hw : |(2744943241/5000000000 : ℝ)|=(2744943241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s2_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1322157627/2500000000 : ℝ)*x 0 + (1372471643/2500000000 : ℝ)*x 1 + (-488331233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322157627/2500000000 : ℝ)^1055 ≤ (10780583450233/25000000000000 : ℝ)^799 := by
    have hnat : (1322157627 : ℕ)^1055*25000000000000^799 ≤ 10780583450233^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322157627 2500000000 10780583450233 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372471643/2500000000 : ℝ)^1055 ≤ (4530220544949/10000000000000 : ℝ)^799 := by
    have hnat : (1372471643 : ℕ)^1055*10000000000000^799 ≤ 4530220544949^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372471643 2500000000 4530220544949 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488331233/2500000000 : ℝ)^1055 ≤ (22608321741/195312500000 : ℝ)^799 := by
    have hnat : (488331233 : ℕ)^1055*195312500000^799 ≤ 22608321741^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488331233 2500000000 22608321741 195312500000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322157627/2500000000 : ℝ), (1372471643/2500000000 : ℝ), (-488331233/2500000000 : ℝ)] ![(10780583450233/25000000000000 : ℝ), (4530220544949/10000000000000 : ℝ), (22608321741/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322157627/2500000000 : ℝ)|^1055 ≤ (10780583450233/25000000000000 : ℝ)^799
        have hw : |(1322157627/2500000000 : ℝ)|=(1322157627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372471643/2500000000 : ℝ)|^1055 ≤ (4530220544949/10000000000000 : ℝ)^799
        have hw : |(1372471643/2500000000 : ℝ)|=(1372471643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488331233/2500000000 : ℝ)|^1055 ≤ (22608321741/195312500000 : ℝ)^799
        have hw : |(-488331233/2500000000 : ℝ)|=(488331233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s2_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1085400519/2500000000 : ℝ)*x 0 + (4670165063/10000000000 : ℝ)*x 1 + (4035774393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085400519/2500000000 : ℝ)^1055 ≤ (2076982882871/6250000000000 : ℝ)^799 := by
    have hnat : (1085400519 : ℕ)^1055*6250000000000^799 ≤ 2076982882871^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085400519 2500000000 2076982882871 6250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4670165063/10000000000 : ℝ)^1055 ≤ (36591997007879/100000000000000 : ℝ)^799 := by
    have hnat : (4670165063 : ℕ)^1055*100000000000000^799 ≤ 36591997007879^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4670165063 10000000000 36591997007879 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035774393/10000000000 : ℝ)^1055 ≤ (30176276858819/100000000000000 : ℝ)^799 := by
    have hnat : (4035774393 : ℕ)^1055*100000000000000^799 ≤ 30176276858819^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035774393 10000000000 30176276858819 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085400519/2500000000 : ℝ), (4670165063/10000000000 : ℝ), (4035774393/10000000000 : ℝ)] ![(2076982882871/6250000000000 : ℝ), (36591997007879/100000000000000 : ℝ), (30176276858819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085400519/2500000000 : ℝ)|^1055 ≤ (2076982882871/6250000000000 : ℝ)^799
        have hw : |(1085400519/2500000000 : ℝ)|=(1085400519/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4670165063/10000000000 : ℝ)|^1055 ≤ (36591997007879/100000000000000 : ℝ)^799
        have hw : |(4670165063/10000000000 : ℝ)|=(4670165063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035774393/10000000000 : ℝ)|^1055 ≤ (30176276858819/100000000000000 : ℝ)^799
        have hw : |(4035774393/10000000000 : ℝ)|=(4035774393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (119/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1621/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19977/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6217/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19977/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6217/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19977/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6217/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6217/100000 : ℝ) ^ (8439/2048 : ℝ) ≤ (1068618588638767/100000000000000000000 : ℝ) := by
    have hpowers : (6217/100000 : ℝ)^8439 ≤ (1068618588638767/100000000000000000000 : ℝ)^2048 := by
      have hnat : (6217 : ℕ)^8439*100000000000000000000^2048 ≤ 1068618588638767^2048*100000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6217 100000 1068618588638767 100000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6217/100000 : ℝ)) (X := (1068618588638767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (19977/100000 : ℝ) ^ (8439/2048 : ℝ) ≤ (16393482324012363/12500000000000000000 : ℝ) := by
    have hpowers : (19977/100000 : ℝ)^8439 ≤ (16393482324012363/12500000000000000000 : ℝ)^2048 := by
      have hnat : (19977 : ℕ)^8439*12500000000000000000^2048 ≤ 16393482324012363^2048*100000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19977 100000 16393482324012363 12500000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19977/100000 : ℝ)) (X := (16393482324012363/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001068618588638767/50000000000000000000 : ℝ) ≤ (31250162083271/31250000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (50001068618588638767/50000000000000000000 : ℝ)^2048 ≤ (31250162083271/31250000000000 : ℝ)^8439 := by
      have hnat : (50001068618588638767 : ℕ)^2048*31250000000000^8439 ≤ 31250162083271^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001068618588638767 50000000000000000000 31250162083271 31250000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31250162083271/31250000000000 : ℝ)) (X := (50001068618588638767/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100132216477180737671/100000000000000000000 : ℝ) ≤ (1000320706108231/1000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (100132216477180737671/100000000000000000000 : ℝ)^2048 ≤ (1000320706108231/1000000000000000 : ℝ)^8439 := by
      have hnat : (100132216477180737671 : ℕ)^2048*1000000000000000^8439 ≤ 1000320706108231^8439*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100132216477180737671 100000000000000000000 1000320706108231 1000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000320706108231/1000000000000000 : ℝ)) (X := (100132216477180737671/100000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6266393482324012363/6250000000000000000 : ℝ) ≤ (100063622555179/100000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (6266393482324012363/6250000000000000000 : ℝ)^2048 ≤ (100063622555179/100000000000000 : ℝ)^8439 := by
      have hnat : (6266393482324012363 : ℕ)^2048*100000000000000^8439 ≤ 100063622555179^8439*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6266393482324012363 6250000000000000000 100063622555179 100000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100063622555179/100000000000000 : ℝ)) (X := (6266393482324012363/6250000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1068618588638767/100000000000000000000 : ℝ) ≤ ((6878074099872337057/6880000000000000000 : ℝ)+2*(315519443559/137600000000000 : ℝ)*(6217/100000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (6878074099872337057/6880000000000000000 : ℝ)+2*(315519443559/137600000000000 : ℝ)*(6217/100000 : ℝ)=(31250162083271/31250000000000 : ℝ) by norm_num, show 1+2*(1068618588638767/100000000000000000000 : ℝ)=(50001068618588638767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16393482324012363/12500000000000000000 : ℝ)+(1068618588638767/100000000000000000000 : ℝ) ≤ ((6878074099872337057/6880000000000000000 : ℝ)+(315519443559/137600000000000 : ℝ)*((19977/100000 : ℝ)+(6217/100000 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (6878074099872337057/6880000000000000000 : ℝ)+(315519443559/137600000000000 : ℝ)*((19977/100000 : ℝ)+(6217/100000 : ℝ))=(1000320706108231/1000000000000000 : ℝ) by norm_num, show 1+(16393482324012363/12500000000000000000 : ℝ)+(1068618588638767/100000000000000000000 : ℝ)=(100132216477180737671/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16393482324012363/12500000000000000000 : ℝ) ≤ ((6878074099872337057/6880000000000000000 : ℝ)+2*(315519443559/137600000000000 : ℝ)*(19977/100000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (6878074099872337057/6880000000000000000 : ℝ)+2*(315519443559/137600000000000 : ℝ)*(19977/100000 : ℝ)=(100063622555179/100000000000000 : ℝ) by norm_num, show 1+2*(16393482324012363/12500000000000000000 : ℝ)=(6266393482324012363/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6878074099872337057/6880000000000000000 : ℝ)*(X 1 0+X 2 0)+(315519443559/137600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (6217/100000 : ℝ)) (hi := (19977/100000 : ℝ)) (c := (6878074099872337057/6880000000000000000 : ℝ)) (alpha := (315519443559/137600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6878074099872337057/6880000000000000000 : ℝ)*(X 0 1+X 2 1)+(315519443559/137600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (6217/100000 : ℝ)) (hi := (19977/100000 : ℝ)) (c := (6878074099872337057/6880000000000000000 : ℝ)) (alpha := (315519443559/137600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6878074099872337057/6880000000000000000 : ℝ)*(X 0 2+X 1 2)+(315519443559/137600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (6217/100000 : ℝ)) (hi := (19977/100000 : ℝ)) (c := (6878074099872337057/6880000000000000000 : ℝ)) (alpha := (315519443559/137600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2103862837/10000000000 : ℝ)*X 0 0+(1372983233/2500000000 : ℝ)*X 0 1+(80866141/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369480959/10000000000 : ℝ)*X 1 0+(-2267778871/10000000000 : ℝ)*X 1 1+(1293858269/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369480829/10000000000 : ℝ)*X 2 0+(517543317/1000000000 : ℝ)*X 2 1+(-2267778919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((135670171/312500000 : ℝ)*X 0 0+(2015809801/5000000000 : ℝ)*X 0 1+(4674281729/10000000000 : ℝ)*X 0 2+(135670171/312500000 : ℝ)*X 1 0+(2015809801/5000000000 : ℝ)*X 1 1+(4674281729/10000000000 : ℝ)*X 1 2+(135670171/312500000 : ℝ)*X 2 0+(2015809801/5000000000 : ℝ)*X 2 1+(4674281729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-420788043/2000000000 : ℝ)*X 0 0+(647182571/1250000000 : ℝ)*X 0 1+(5489886437/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288630351/10000000000 : ℝ)*X 1 0+(-976662637/5000000000 : ℝ)*X 1 1+(2744943241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322157627/2500000000 : ℝ)*X 2 0+(1372471643/2500000000 : ℝ)*X 2 1+(-488331233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085400519/2500000000 : ℝ)*X 0 0+(4670165063/10000000000 : ℝ)*X 0 1+(4035774393/10000000000 : ℝ)*X 0 2+(1085400519/2500000000 : ℝ)*X 1 0+(4670165063/10000000000 : ℝ)*X 1 1+(4035774393/10000000000 : ℝ)*X 1 2+(1085400519/2500000000 : ℝ)*X 2 0+(4670165063/10000000000 : ℝ)*X 2 1+(4035774393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (307336543422148537554495201/86000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301738399/50000000000000 : ℝ)*(base19) + (487698179/100000000000000 : ℝ)*(base23) + (329573/1562500000000 : ℝ)*(lower2) + (4636279/4000000000000 : ℝ)*(upper3) + (16547369/50000000000000 : ℝ)*(upper5) + (1178901670179069/50000000000000 : ℝ)*(major0) + (1178901670179069/50000000000000 : ℝ)*(major1) + (1178901670179069/50000000000000 : ℝ)*(major2) + (394945798421769/12500000000000 : ℝ)*(sp0) + (19747324246063/625000000000 : ℝ)*(sp1) + (1579785997574349/50000000000000 : ℝ)*(sp2) + (1556030488735021/100000000000000 : ℝ)*(sp3) + (243818909/4000000000000 : ℝ)*(sp4) + (3590011673/100000000000000 : ℝ)*(sp7) + (311206815749339/20000000000000 : ℝ)*(f.failure) + (1579786241423439/50000000000000 : ℝ)*(f.sum) + (8257467280731/3440000000000000000000000000 : ℝ)*base65 + (5703601692323009933/344000000000000000000000000000000 : ℝ)*base67 + (5404389196819009933/344000000000000000000000000000000 : ℝ)*base69 + (4911345173723009933/344000000000000000000000000000000 : ℝ)*base71 + (17470821344731/3440000000000000000000000000 : ℝ)*base73 + (1850928427988990067/344000000000000000000000000000000 : ℝ)*base76 + (3039639824555009933/344000000000000000000000000000000 : ℝ)*base77 + (2494036560899009933/344000000000000000000000000000000 : ℝ)*base79 + (23622088390731/3440000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (10260601/2000000000000000000000 : ℝ)*base89 + (10260601/2000000000000000000000 : ℝ)*base91 + (10260601/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135998188311804497174189271/21500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1660364133/100000000000000 : ℝ)*(base19) + (481691549/25000000000000 : ℝ)*(base23) + (40736373/100000000000000 : ℝ)*(upper2) + (28769121/12500000000000 : ℝ)*(upper3) + (61433793/50000000000000 : ℝ)*(upper5) + (298567151433899/12500000000000 : ℝ)*(major0) + (298567151433899/12500000000000 : ℝ)*(major1) + (298567151433899/12500000000000 : ℝ)*(major2) + (16953020729/100000000000000 : ℝ)*(sp1) + (1445326473/6250000000000 : ℝ)*(sp2) + (1600378646053717/50000000000000 : ℝ)*(sp4) + (800184669680643/25000000000000 : ℝ)*(sp5) + (320073224011767/10000000000000 : ℝ)*(sp6) + (788158459992519/50000000000000 : ℝ)*(sp7) + (788158459992519/50000000000000 : ℝ)*(f.failure) + (1600378646053717/50000000000000 : ℝ)*(f.sum) + (6137504509461/860000000000000000000000000 : ℝ)*base65 + (208925719805254757/86000000000000000000000000000000 : ℝ)*base68 + (889680017198745243/86000000000000000000000000000000 : ℝ)*base69 + (705578425804745243/86000000000000000000000000000000 : ℝ)*base71 + (4010964301479/860000000000000000000000000 : ℝ)*base74 + (118446512498745243/86000000000000000000000000000000 : ℝ)*base75 + (559286203790745243/86000000000000000000000000000000 : ℝ)*base77 + (85949765426745243/86000000000000000000000000000000 : ℝ)*base79 + (4563928174821/860000000000000000000000000 : ℝ)*base81 + (29439779/5000000000000000000000 : ℝ)*base90 + (29439779/5000000000000000000000 : ℝ)*base92 + (29439779/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1247_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19977/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6217/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (119/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1621/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1247_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (119/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1621/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1247_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1247_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1247_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (119/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1621/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1247_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
