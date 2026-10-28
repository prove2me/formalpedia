-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:56:13.584189+00:00
-- url     : https://prove2.me/submissions/100fe131-c2b6-4285-8299-89e108f789e0

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
theorem support_rectangle_w1264_s0_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1853790727/10000000000 : ℝ)*x 0 + (753320079/1250000000 : ℝ)*x 1 + (38365643/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853790727/10000000000 : ℝ)^8457 ≤ (1352318702351/12500000000000 : ℝ)^6409 := by
    have hnat : (1853790727 : ℕ)^8457*12500000000000^6409 ≤ 1352318702351^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853790727 10000000000 1352318702351 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (753320079/1250000000 : ℝ)^8457 ≤ (51261417310771/100000000000000 : ℝ)^6409 := by
    have hnat : (753320079 : ℕ)^8457*100000000000000^6409 ≤ 51261417310771^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753320079 1250000000 51261417310771 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38365643/80000000 : ℝ)^8457 ≤ (18960016524003/50000000000000 : ℝ)^6409 := by
    have hnat : (38365643 : ℕ)^8457*50000000000000^6409 ≤ 18960016524003^6409*80000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38365643 80000000 18960016524003 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1853790727/10000000000 : ℝ), (753320079/1250000000 : ℝ), (38365643/80000000 : ℝ)] ![(1352318702351/12500000000000 : ℝ), (51261417310771/100000000000000 : ℝ), (18960016524003/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1853790727/10000000000 : ℝ)|^8457 ≤ (1352318702351/12500000000000 : ℝ)^6409
        have hw : |(-1853790727/10000000000 : ℝ)|=(1853790727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(753320079/1250000000 : ℝ)|^8457 ≤ (51261417310771/100000000000000 : ℝ)^6409
        have hw : |(753320079/1250000000 : ℝ)|=(753320079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(38365643/80000000 : ℝ)|^8457 ≤ (18960016524003/50000000000000 : ℝ)^6409
        have hw : |(38365643/80000000 : ℝ)|=(38365643/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s0_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1101984013/2000000000 : ℝ)*x 0 + (-51137083/200000000 : ℝ)*x 1 + (1198926337/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101984013/2000000000 : ℝ)^8457 ≤ (45543679532333/100000000000000 : ℝ)^6409 := by
    have hnat : (1101984013 : ℕ)^8457*100000000000000^6409 ≤ 45543679532333^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101984013 2000000000 45543679532333 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51137083/200000000 : ℝ)^8457 ≤ (4134071920743/25000000000000 : ℝ)^6409 := by
    have hnat : (51137083 : ℕ)^8457*25000000000000^6409 ≤ 4134071920743^6409*200000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51137083 200000000 4134071920743 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198926337/2500000000 : ℝ)^8457 ≤ (37920032766293/100000000000000 : ℝ)^6409 := by
    have hnat : (1198926337 : ℕ)^8457*100000000000000^6409 ≤ 37920032766293^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198926337 2500000000 37920032766293 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1101984013/2000000000 : ℝ), (-51137083/200000000 : ℝ), (1198926337/2500000000 : ℝ)] ![(45543679532333/100000000000000 : ℝ), (4134071920743/25000000000000 : ℝ), (37920032766293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1101984013/2000000000 : ℝ)|^8457 ≤ (45543679532333/100000000000000 : ℝ)^6409
        have hw : |(1101984013/2000000000 : ℝ)|=(1101984013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51137083/200000000 : ℝ)|^8457 ≤ (4134071920743/25000000000000 : ℝ)^6409
        have hw : |(-51137083/200000000 : ℝ)|=(51137083/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198926337/2500000000 : ℝ)|^8457 ≤ (37920032766293/100000000000000 : ℝ)^6409
        have hw : |(1198926337/2500000000 : ℝ)|=(1198926337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s0_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1377480023/2500000000 : ℝ)*x 0 + (4795705347/10000000000 : ℝ)*x 1 + (-2556854117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377480023/2500000000 : ℝ)^8457 ≤ (5692959978353/12500000000000 : ℝ)^6409 := by
    have hnat : (1377480023 : ℕ)^8457*12500000000000^6409 ≤ 5692959978353^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377480023 2500000000 5692959978353 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4795705347/10000000000 : ℝ)^8457 ≤ (1896001637793/5000000000000 : ℝ)^6409 := by
    have hnat : (4795705347 : ℕ)^8457*5000000000000^6409 ≤ 1896001637793^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795705347 10000000000 1896001637793 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2556854117/10000000000 : ℝ)^8457 ≤ (8268143700673/50000000000000 : ℝ)^6409 := by
    have hnat : (2556854117 : ℕ)^8457*50000000000000^6409 ≤ 8268143700673^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556854117 10000000000 8268143700673 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377480023/2500000000 : ℝ), (4795705347/10000000000 : ℝ), (-2556854117/10000000000 : ℝ)] ![(5692959978353/12500000000000 : ℝ), (1896001637793/5000000000000 : ℝ), (8268143700673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377480023/2500000000 : ℝ)|^8457 ≤ (5692959978353/12500000000000 : ℝ)^6409
        have hw : |(1377480023/2500000000 : ℝ)|=(1377480023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4795705347/10000000000 : ℝ)|^8457 ≤ (1896001637793/5000000000000 : ℝ)^6409
        have hw : |(4795705347/10000000000 : ℝ)|=(4795705347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2556854117/10000000000 : ℝ)|^8457 ≤ (8268143700673/50000000000000 : ℝ)^6409
        have hw : |(-2556854117/10000000000 : ℝ)|=(2556854117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s0_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (523912383/1250000000 : ℝ)*x 0 + (194755377/625000000 : ℝ)*x 1 + (562357349/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523912383/1250000000 : ℝ)^8457 ≤ (15872302334707/50000000000000 : ℝ)^6409 := by
    have hnat : (523912383 : ℕ)^8457*50000000000000^6409 ≤ 15872302334707^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523912383 1250000000 15872302334707 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (194755377/625000000 : ℝ)^8457 ≤ (21468021226489/100000000000000 : ℝ)^6409 := by
    have hnat : (194755377 : ℕ)^8457*100000000000000^6409 ≤ 21468021226489^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194755377 625000000 21468021226489 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562357349/1000000000 : ℝ)^8457 ≤ (23393687046047/50000000000000 : ℝ)^6409 := by
    have hnat : (562357349 : ℕ)^8457*50000000000000^6409 ≤ 23393687046047^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562357349 1000000000 23393687046047 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523912383/1250000000 : ℝ), (194755377/625000000 : ℝ), (562357349/1000000000 : ℝ)] ![(15872302334707/50000000000000 : ℝ), (21468021226489/100000000000000 : ℝ), (23393687046047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523912383/1250000000 : ℝ)|^8457 ≤ (15872302334707/50000000000000 : ℝ)^6409
        have hw : |(523912383/1250000000 : ℝ)|=(523912383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(194755377/625000000 : ℝ)|^8457 ≤ (21468021226489/100000000000000 : ℝ)^6409
        have hw : |(194755377/625000000 : ℝ)|=(194755377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562357349/1000000000 : ℝ)|^8457 ≤ (23393687046047/50000000000000 : ℝ)^6409
        have hw : |(562357349/1000000000 : ℝ)|=(562357349/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s0_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-929292981/5000000000 : ℝ)*x 0 + (96547757/200000000 : ℝ)*x 1 + (5993757697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929292981/5000000000 : ℝ)^8457 ≤ (10855491894017/100000000000000 : ℝ)^6409 := by
    have hnat : (929292981 : ℕ)^8457*100000000000000^6409 ≤ 10855491894017^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929292981 5000000000 10855491894017 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96547757/200000000 : ℝ)^8457 ≤ (7650189976847/20000000000000 : ℝ)^6409 := by
    have hnat : (96547757 : ℕ)^8457*20000000000000^6409 ≤ 7650189976847^6409*200000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96547757 200000000 7650189976847 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5993757697/10000000000 : ℝ)^8457 ≤ (2035742327947/4000000000000 : ℝ)^6409 := by
    have hnat : (5993757697 : ℕ)^8457*4000000000000^6409 ≤ 2035742327947^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993757697 10000000000 2035742327947 4000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929292981/5000000000 : ℝ), (96547757/200000000 : ℝ), (5993757697/10000000000 : ℝ)] ![(10855491894017/100000000000000 : ℝ), (7650189976847/20000000000000 : ℝ), (2035742327947/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929292981/5000000000 : ℝ)|^8457 ≤ (10855491894017/100000000000000 : ℝ)^6409
        have hw : |(-929292981/5000000000 : ℝ)|=(929292981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96547757/200000000 : ℝ)|^8457 ≤ (7650189976847/20000000000000 : ℝ)^6409
        have hw : |(96547757/200000000 : ℝ)|=(96547757/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5993757697/10000000000 : ℝ)|^8457 ≤ (2035742327947/4000000000000 : ℝ)^6409
        have hw : |(5993757697/10000000000 : ℝ)|=(5993757697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s0_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174930789/10000000000 : ℝ)*x 0 + (-1358799377/10000000000 : ℝ)*x 1 + (1498440033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174930789/10000000000 : ℝ)^8457 ≤ (10481479065927/25000000000000 : ℝ)^6409 := by
    have hnat : (5174930789 : ℕ)^8457*25000000000000^6409 ≤ 10481479065927^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174930789 10000000000 10481479065927 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358799377/10000000000 : ℝ)^8457 ≤ (7180498236873/100000000000000 : ℝ)^6409 := by
    have hnat : (1358799377 : ℕ)^8457*100000000000000^6409 ≤ 7180498236873^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358799377 10000000000 7180498236873 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498440033/2500000000 : ℝ)^8457 ≤ (2544679274073/5000000000000 : ℝ)^6409 := by
    have hnat : (1498440033 : ℕ)^8457*5000000000000^6409 ≤ 2544679274073^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498440033 2500000000 2544679274073 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174930789/10000000000 : ℝ), (-1358799377/10000000000 : ℝ), (1498440033/2500000000 : ℝ)] ![(10481479065927/25000000000000 : ℝ), (7180498236873/100000000000000 : ℝ), (2544679274073/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174930789/10000000000 : ℝ)|^8457 ≤ (10481479065927/25000000000000 : ℝ)^6409
        have hw : |(5174930789/10000000000 : ℝ)|=(5174930789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358799377/10000000000 : ℝ)|^8457 ≤ (7180498236873/100000000000000 : ℝ)^6409
        have hw : |(-1358799377/10000000000 : ℝ)|=(1358799377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498440033/2500000000 : ℝ)|^8457 ≤ (2544679274073/5000000000000 : ℝ)^6409
        have hw : |(1498440033/2500000000 : ℝ)|=(1498440033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s0_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034986373/2000000000 : ℝ)*x 0 + (187304941/312500000 : ℝ)*x 1 + (-1358800973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034986373/2000000000 : ℝ)^8457 ≤ (41925927766847/100000000000000 : ℝ)^6409 := by
    have hnat : (1034986373 : ℕ)^8457*100000000000000^6409 ≤ 41925927766847^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034986373 2000000000 41925927766847 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187304941/312500000 : ℝ)^8457 ≤ (50893562848513/100000000000000 : ℝ)^6409 := by
    have hnat : (187304941 : ℕ)^8457*100000000000000^6409 ≤ 50893562848513^6409*312500000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187304941 312500000 50893562848513 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358800973/10000000000 : ℝ)^8457 ≤ (897563670741/12500000000000 : ℝ)^6409 := by
    have hnat : (1358800973 : ℕ)^8457*12500000000000^6409 ≤ 897563670741^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358800973 10000000000 897563670741 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034986373/2000000000 : ℝ), (187304941/312500000 : ℝ), (-1358800973/10000000000 : ℝ)] ![(41925927766847/100000000000000 : ℝ), (50893562848513/100000000000000 : ℝ), (897563670741/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034986373/2000000000 : ℝ)|^8457 ≤ (41925927766847/100000000000000 : ℝ)^6409
        have hw : |(1034986373/2000000000 : ℝ)|=(1034986373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187304941/312500000 : ℝ)|^8457 ≤ (50893562848513/100000000000000 : ℝ)^6409
        have hw : |(187304941/312500000 : ℝ)|=(187304941/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1358800973/10000000000 : ℝ)|^8457 ≤ (897563670741/12500000000000 : ℝ)^6409
        have hw : |(-1358800973/10000000000 : ℝ)|=(1358800973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s0_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1050267629/2500000000 : ℝ)*x 0 + (347439761/625000000 : ℝ)*x 1 + (3182905773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050267629/2500000000 : ℝ)^8457 ≤ (7960574678581/25000000000000 : ℝ)^6409 := by
    have hnat : (1050267629 : ℕ)^8457*25000000000000^6409 ≤ 7960574678581^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050267629 2500000000 7960574678581 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (347439761/625000000 : ℝ)^8457 ≤ (46080154806521/100000000000000 : ℝ)^6409 := by
    have hnat : (347439761 : ℕ)^8457*100000000000000^6409 ≤ 46080154806521^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347439761 625000000 46080154806521 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3182905773/10000000000 : ℝ)^8457 ≤ (22077546454399/100000000000000 : ℝ)^6409 := by
    have hnat : (3182905773 : ℕ)^8457*100000000000000^6409 ≤ 22077546454399^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182905773 10000000000 22077546454399 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050267629/2500000000 : ℝ), (347439761/625000000 : ℝ), (3182905773/10000000000 : ℝ)] ![(7960574678581/25000000000000 : ℝ), (46080154806521/100000000000000 : ℝ), (22077546454399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050267629/2500000000 : ℝ)|^8457 ≤ (7960574678581/25000000000000 : ℝ)^6409
        have hw : |(1050267629/2500000000 : ℝ)|=(1050267629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(347439761/625000000 : ℝ)|^8457 ≤ (46080154806521/100000000000000 : ℝ)^6409
        have hw : |(347439761/625000000 : ℝ)|=(347439761/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3182905773/10000000000 : ℝ)|^8457 ≤ (22077546454399/100000000000000 : ℝ)^6409
        have hw : |(3182905773/10000000000 : ℝ)|=(3182905773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (181/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13677/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1057/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1057 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1057*1^256 ≤ 0^256*1^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1057/256 : ℝ) ≤ (2274798907835367073/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1057 ≤ (2274798907835367073/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1057*100000000000000000000^256 ≤ 2274798907835367073^256*5^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2274798907835367073 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2274798907835367073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1057 := by
      have hnat : (1 : ℕ)^256*1^1057 ≤ 1^1057*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (102274798907835367073/100000000000000000000 : ℝ) ≤ (502731291258253/500000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (102274798907835367073/100000000000000000000 : ℝ)^256 ≤ (502731291258253/500000000000000 : ℝ)^1057 := by
      have hnat : (102274798907835367073 : ℕ)^256*500000000000000^1057 ≤ 502731291258253^1057*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102274798907835367073 100000000000000000000 502731291258253 500000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502731291258253/500000000000000 : ℝ)) (X := (102274798907835367073/100000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (52274798907835367073/50000000000000000000 : ℝ) ≤ (252731291258253/250000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (52274798907835367073/50000000000000000000 : ℝ)^256 ≤ (252731291258253/250000000000000 : ℝ)^1057 := by
      have hnat : (52274798907835367073 : ℕ)^256*250000000000000^1057 ≤ 252731291258253^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52274798907835367073 50000000000000000000 252731291258253 250000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (252731291258253/250000000000000 : ℝ)) (X := (52274798907835367073/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2731291258253/200000000000000 : ℝ)*(0 : ℝ))^(1057/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2731291258253/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2274798907835367073/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2731291258253/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (1 : ℝ)+(2731291258253/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(502731291258253/500000000000000 : ℝ) by norm_num, show 1+(2274798907835367073/100000000000000000000 : ℝ)+(0 : ℝ)=(102274798907835367073/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2274798907835367073/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2731291258253/200000000000000 : ℝ)*(2/5 : ℝ))^(1057/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2731291258253/200000000000000 : ℝ)*(2/5 : ℝ)=(252731291258253/250000000000000 : ℝ) by norm_num, show 1+2*(2274798907835367073/100000000000000000000 : ℝ)=(52274798907835367073/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2731291258253/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2731291258253/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2731291258253/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2731291258253/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2731291258253/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2731291258253/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1853790727/10000000000 : ℝ)*X 0 0+(753320079/1250000000 : ℝ)*X 0 1+(38365643/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1101984013/2000000000 : ℝ)*X 1 0+(-51137083/200000000 : ℝ)*X 1 1+(1198926337/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1377480023/2500000000 : ℝ)*X 2 0+(4795705347/10000000000 : ℝ)*X 2 1+(-2556854117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((523912383/1250000000 : ℝ)*X 0 0+(194755377/625000000 : ℝ)*X 0 1+(562357349/1000000000 : ℝ)*X 0 2+(523912383/1250000000 : ℝ)*X 1 0+(194755377/625000000 : ℝ)*X 1 1+(562357349/1000000000 : ℝ)*X 1 2+(523912383/1250000000 : ℝ)*X 2 0+(194755377/625000000 : ℝ)*X 2 1+(562357349/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-929292981/5000000000 : ℝ)*X 0 0+(96547757/200000000 : ℝ)*X 0 1+(5993757697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174930789/10000000000 : ℝ)*X 1 0+(-1358799377/10000000000 : ℝ)*X 1 1+(1498440033/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1034986373/2000000000 : ℝ)*X 2 0+(187304941/312500000 : ℝ)*X 2 1+(-1358800973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1050267629/2500000000 : ℝ)*X 0 0+(347439761/625000000 : ℝ)*X 0 1+(3182905773/10000000000 : ℝ)*X 0 2+(1050267629/2500000000 : ℝ)*X 1 0+(347439761/625000000 : ℝ)*X 1 1+(3182905773/10000000000 : ℝ)*X 1 2+(1050267629/2500000000 : ℝ)*X 2 0+(347439761/625000000 : ℝ)*X 2 1+(3182905773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12682229002096180380327/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4460511/6250000000000 : ℝ)*(base1) + (771266033/50000000000000 : ℝ)*(base19) + (1546513281/100000000000000 : ℝ)*(base23) + (175235237/100000000000000 : ℝ)*(upper3) + (184718111/100000000000000 : ℝ)*(upper5) + (121126322372047/20000000000000 : ℝ)*(major0) + (121126322372047/20000000000000 : ℝ)*(major1) + (121126322372047/20000000000000 : ℝ)*(major2) + (3249791311563/400000000000 : ℝ)*(sp0) + (203112787008453/25000000000000 : ℝ)*(sp1) + (812451144052597/100000000000000 : ℝ)*(sp2) + (398807866281533/100000000000000 : ℝ)*(sp3) + (616755413/12500000000000 : ℝ)*(sp4) + (476826879/20000000000000 : ℝ)*(sp7) + (79762064356821/20000000000000 : ℝ)*(f.failure) + (406226345282939/50000000000000 : ℝ)*(f.sum) + (2057393214109/2000000000000000000000000000 : ℝ)*base66 + (12105701349891/4000000000000000000000000000 : ℝ)*base67 + (8042966681891/4000000000000000000000000000 : ℝ)*base69 + (4847742405891/4000000000000000000000000000 : ℝ)*base71 + (1835823701891/2000000000000000000000000000 : ℝ)*base73 + (18053571070109/4000000000000000000000000000 : ℝ)*base76 + (13063622170109/4000000000000000000000000000 : ℝ)*base78 + (4021201686109/4000000000000000000000000000 : ℝ)*base80 + (5544763941891/2000000000000000000000000000 : ℝ)*base81 + (13129223/2000000000000000000000 : ℝ)*base89 + (13129223/2000000000000000000000 : ℝ)*base91 + (13129223/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51251046447754890549063/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (242454111/100000000000000 : ℝ)*(base1) + (273752289/25000000000000 : ℝ)*(base19) + (156364327/12500000000000 : ℝ)*(base23) + (47869097/20000000000000 : ℝ)*(upper3) + (639106571568581/100000000000000 : ℝ)*(major0) + (639106571568581/100000000000000 : ℝ)*(major1) + (639106571568581/100000000000000 : ℝ)*(major2) + (1096724953/50000000000000 : ℝ)*(sp1) + (1848019923/100000000000000 : ℝ)*(sp2) + (208150273/100000000000000 : ℝ)*(sp3) + (42867976334351/5000000000000 : ℝ)*(sp4) + (857355995773847/100000000000000 : ℝ)*(sp5) + (85735618529837/10000000000000 : ℝ)*(sp6) + (84170647492609/20000000000000 : ℝ)*(sp7) + (420853688067429/100000000000000 : ℝ)*(f.failure) + (857359284232909/100000000000000 : ℝ)*(f.sum) + (14138247228993/10000000000000000000000000000 : ℝ)*base65 + (11173178628993/20000000000000000000000000000 : ℝ)*base67 + (9778918151007/20000000000000000000000000000 : ℝ)*base70 + (55628074448993/20000000000000000000000000000 : ℝ)*base71 + (988377378993/10000000000000000000000000000 : ℝ)*base73 + (62697638808993/20000000000000000000000000000 : ℝ)*base75 + (50897798588993/20000000000000000000000000000 : ℝ)*base77 + (104757204208993/20000000000000000000000000000 : ℝ)*base79 + (522973791007/10000000000000000000000000000 : ℝ)*base82 + (17526473/10000000000000000000000 : ℝ)*base90 + (17526473/10000000000000000000000 : ℝ)*base92 + (17526473/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1264_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (181/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13677/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1264_s1_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-128100053/625000000 : ℝ)*x 0 + (1417531431/2500000000 : ℝ)*x 1 + (1005359677/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128100053/625000000 : ℝ)^8457 ≤ (2470260619991/20000000000000 : ℝ)^6409 := by
    have hnat : (128100053 : ℕ)^8457*20000000000000^6409 ≤ 2470260619991^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128100053 625000000 2470260619991 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417531431/2500000000 : ℝ)^8457 ≤ (11824780430509/25000000000000 : ℝ)^6409 := by
    have hnat : (1417531431 : ℕ)^8457*25000000000000^6409 ≤ 11824780430509^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417531431 2500000000 11824780430509 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005359677/2000000000 : ℝ)^8457 ≤ (40349575156011/100000000000000 : ℝ)^6409 := by
    have hnat : (1005359677 : ℕ)^8457*100000000000000^6409 ≤ 40349575156011^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005359677 2000000000 40349575156011 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128100053/625000000 : ℝ), (1417531431/2500000000 : ℝ), (1005359677/2000000000 : ℝ)] ![(2470260619991/20000000000000 : ℝ), (11824780430509/25000000000000 : ℝ), (40349575156011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128100053/625000000 : ℝ)|^8457 ≤ (2470260619991/20000000000000 : ℝ)^6409
        have hw : |(-128100053/625000000 : ℝ)|=(128100053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1417531431/2500000000 : ℝ)|^8457 ≤ (11824780430509/25000000000000 : ℝ)^6409
        have hw : |(1417531431/2500000000 : ℝ)|=(1417531431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005359677/2000000000 : ℝ)|^8457 ≤ (40349575156011/100000000000000 : ℝ)^6409
        have hw : |(1005359677/2000000000 : ℝ)|=(1005359677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s1_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706232813/5000000000 : ℝ)*x 0 + (-1870859/7812500 : ℝ)*x 1 + (5026798517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706232813/5000000000 : ℝ)^8457 ≤ (2224187561309/5000000000000 : ℝ)^6409 := by
    have hnat : (2706232813 : ℕ)^8457*5000000000000^6409 ≤ 2224187561309^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706232813 5000000000 2224187561309 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870859/7812500 : ℝ)^8457 ≤ (7583336103911/50000000000000 : ℝ)^6409 := by
    have hnat : (1870859 : ℕ)^8457*50000000000000^6409 ≤ 7583336103911^6409*7812500^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870859 7812500 7583336103911 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5026798517/10000000000 : ℝ)^8457 ≤ (2017478827707/5000000000000 : ℝ)^6409 := by
    have hnat : (5026798517 : ℕ)^8457*5000000000000^6409 ≤ 2017478827707^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5026798517 10000000000 2017478827707 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706232813/5000000000 : ℝ), (-1870859/7812500 : ℝ), (5026798517/10000000000 : ℝ)] ![(2224187561309/5000000000000 : ℝ), (7583336103911/50000000000000 : ℝ), (2017478827707/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706232813/5000000000 : ℝ)|^8457 ≤ (2224187561309/5000000000000 : ℝ)^6409
        have hw : |(2706232813/5000000000 : ℝ)|=(2706232813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870859/7812500 : ℝ)|^8457 ≤ (7583336103911/50000000000000 : ℝ)^6409
        have hw : |(-1870859/7812500 : ℝ)|=(1870859/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5026798517/10000000000 : ℝ)|^8457 ≤ (2017478827707/5000000000000 : ℝ)^6409
        have hw : |(5026798517/10000000000 : ℝ)|=(5026798517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s1_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5412465741/10000000000 : ℝ)*x 0 + (314174903/625000000 : ℝ)*x 1 + (-1197349729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412465741/10000000000 : ℝ)^8457 ≤ (44483752473363/100000000000000 : ℝ)^6409 := by
    have hnat : (5412465741 : ℕ)^8457*100000000000000^6409 ≤ 44483752473363^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412465741 10000000000 44483752473363 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314174903/625000000 : ℝ)^8457 ≤ (403495758233/1000000000000 : ℝ)^6409 := by
    have hnat : (314174903 : ℕ)^8457*1000000000000^6409 ≤ 403495758233^6409*625000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314174903 625000000 403495758233 1000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197349729/5000000000 : ℝ)^8457 ≤ (1516667168967/10000000000000 : ℝ)^6409 := by
    have hnat : (1197349729 : ℕ)^8457*10000000000000^6409 ≤ 1516667168967^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197349729 5000000000 1516667168967 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412465741/10000000000 : ℝ), (314174903/625000000 : ℝ), (-1197349729/5000000000 : ℝ)] ![(44483752473363/100000000000000 : ℝ), (403495758233/1000000000000 : ℝ), (1516667168967/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412465741/10000000000 : ℝ)|^8457 ≤ (44483752473363/100000000000000 : ℝ)^6409
        have hw : |(5412465741/10000000000 : ℝ)|=(5412465741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314174903/625000000 : ℝ)|^8457 ≤ (403495758233/1000000000000 : ℝ)^6409
        have hw : |(314174903/625000000 : ℝ)|=(314174903/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1197349729/5000000000 : ℝ)|^8457 ≤ (1516667168967/10000000000000 : ℝ)^6409
        have hw : |(-1197349729/5000000000 : ℝ)|=(1197349729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s1_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (34455517/80000000 : ℝ)*x 0 + (1849695333/5000000000 : ℝ)*x 1 + (1252492957/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34455517/80000000 : ℝ)^8457 ≤ (32905400988887/100000000000000 : ℝ)^6409 := by
    have hnat : (34455517 : ℕ)^8457*100000000000000^6409 ≤ 32905400988887^6409*80000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34455517 80000000 32905400988887 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1849695333/5000000000 : ℝ)^8457 ≤ (6730788383/25000000000 : ℝ)^6409 := by
    have hnat : (1849695333 : ℕ)^8457*25000000000^6409 ≤ 6730788383^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849695333 5000000000 6730788383 25000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252492957/2500000000 : ℝ)^8457 ≤ (40171445467617/100000000000000 : ℝ)^6409 := by
    have hnat : (1252492957 : ℕ)^8457*100000000000000^6409 ≤ 40171445467617^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252492957 2500000000 40171445467617 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34455517/80000000 : ℝ), (1849695333/5000000000 : ℝ), (1252492957/2500000000 : ℝ)] ![(32905400988887/100000000000000 : ℝ), (6730788383/25000000000 : ℝ), (40171445467617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34455517/80000000 : ℝ)|^8457 ≤ (32905400988887/100000000000000 : ℝ)^6409
        have hw : |(34455517/80000000 : ℝ)|=(34455517/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1849695333/5000000000 : ℝ)|^8457 ≤ (6730788383/25000000000 : ℝ)^6409
        have hw : |(1849695333/5000000000 : ℝ)|=(1849695333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252492957/2500000000 : ℝ)|^8457 ≤ (40171445467617/100000000000000 : ℝ)^6409
        have hw : |(1252492957/2500000000 : ℝ)|=(1252492957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s1_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-512562893/2500000000 : ℝ)*x 0 + (5035176491/10000000000 : ℝ)*x 1 + (1132317919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512562893/2500000000 : ℝ)^8457 ≤ (12356477838349/100000000000000 : ℝ)^6409 := by
    have hnat : (512562893 : ℕ)^8457*100000000000000^6409 ≤ 12356477838349^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512562893 2500000000 12356477838349 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035176491/10000000000 : ℝ)^8457 ≤ (40438338775067/100000000000000 : ℝ)^6409 := by
    have hnat : (5035176491 : ℕ)^8457*100000000000000^6409 ≤ 40438338775067^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035176491 10000000000 40438338775067 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132317919/2000000000 : ℝ)^8457 ≤ (47205183376859/100000000000000 : ℝ)^6409 := by
    have hnat : (1132317919 : ℕ)^8457*100000000000000^6409 ≤ 47205183376859^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132317919 2000000000 47205183376859 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512562893/2500000000 : ℝ), (5035176491/10000000000 : ℝ), (1132317919/2000000000 : ℝ)] ![(12356477838349/100000000000000 : ℝ), (40438338775067/100000000000000 : ℝ), (47205183376859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512562893/2500000000 : ℝ)|^8457 ≤ (12356477838349/100000000000000 : ℝ)^6409
        have hw : |(-512562893/2500000000 : ℝ)|=(512562893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035176491/10000000000 : ℝ)|^8457 ≤ (40438338775067/100000000000000 : ℝ)^6409
        have hw : |(5035176491/10000000000 : ℝ)|=(5035176491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1132317919/2000000000 : ℝ)|^8457 ≤ (47205183376859/100000000000000 : ℝ)^6409
        have hw : |(1132317919/2000000000 : ℝ)|=(1132317919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s1_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (655819357/1250000000 : ℝ)*x 0 + (-879954057/5000000000 : ℝ)*x 1 + (2830795031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655819357/1250000000 : ℝ)^8457 ≤ (21346656010757/50000000000000 : ℝ)^6409 := by
    have hnat : (655819357 : ℕ)^8457*50000000000000^6409 ≤ 21346656010757^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655819357 1250000000 21346656010757 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (879954057/5000000000 : ℝ)^8457 ≤ (2525374860921/25000000000000 : ℝ)^6409 := by
    have hnat : (879954057 : ℕ)^8457*25000000000000^6409 ≤ 2525374860921^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879954057 5000000000 2525374860921 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2830795031/5000000000 : ℝ)^8457 ≤ (47205188514861/100000000000000 : ℝ)^6409 := by
    have hnat : (2830795031 : ℕ)^8457*100000000000000^6409 ≤ 47205188514861^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2830795031 5000000000 47205188514861 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655819357/1250000000 : ℝ), (-879954057/5000000000 : ℝ), (2830795031/5000000000 : ℝ)] ![(21346656010757/50000000000000 : ℝ), (2525374860921/25000000000000 : ℝ), (47205188514861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655819357/1250000000 : ℝ)|^8457 ≤ (21346656010757/50000000000000 : ℝ)^6409
        have hw : |(655819357/1250000000 : ℝ)|=(655819357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-879954057/5000000000 : ℝ)|^8457 ≤ (2525374860921/25000000000000 : ℝ)^6409
        have hw : |(-879954057/5000000000 : ℝ)|=(879954057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2830795031/5000000000 : ℝ)|^8457 ≤ (47205188514861/100000000000000 : ℝ)^6409
        have hw : |(2830795031/5000000000 : ℝ)|=(2830795031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s1_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1311638693/2500000000 : ℝ)*x 0 + (5661589767/10000000000 : ℝ)*x 1 + (-879954331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311638693/2500000000 : ℝ)^8457 ≤ (21346655559773/50000000000000 : ℝ)^6409 := by
    have hnat : (1311638693 : ℕ)^8457*50000000000000^6409 ≤ 21346655559773^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311638693 2500000000 21346655559773 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5661589767/10000000000 : ℝ)^8457 ≤ (11801296317307/25000000000000 : ℝ)^6409 := by
    have hnat : (5661589767 : ℕ)^8457*25000000000000^6409 ≤ 11801296317307^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5661589767 10000000000 11801296317307 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879954331/5000000000 : ℝ)^8457 ≤ (2525375898551/25000000000000 : ℝ)^6409 := by
    have hnat : (879954331 : ℕ)^8457*25000000000000^6409 ≤ 2525375898551^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879954331 5000000000 2525375898551 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311638693/2500000000 : ℝ), (5661589767/10000000000 : ℝ), (-879954331/5000000000 : ℝ)] ![(21346655559773/50000000000000 : ℝ), (11801296317307/25000000000000 : ℝ), (2525375898551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311638693/2500000000 : ℝ)|^8457 ≤ (21346655559773/50000000000000 : ℝ)^6409
        have hw : |(1311638693/2500000000 : ℝ)|=(1311638693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5661589767/10000000000 : ℝ)|^8457 ≤ (11801296317307/25000000000000 : ℝ)^6409
        have hw : |(5661589767/10000000000 : ℝ)|=(5661589767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-879954331/5000000000 : ℝ)|^8457 ≤ (2525375898551/25000000000000 : ℝ)^6409
        have hw : |(-879954331/5000000000 : ℝ)|=(879954331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s1_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4308264889/10000000000 : ℝ)*x 0 + (4992904239/10000000000 : ℝ)*x 1 + (185839021/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308264889/10000000000 : ℝ)^8457 ≤ (4114845284179/12500000000000 : ℝ)^6409 := by
    have hnat : (4308264889 : ℕ)^8457*12500000000000^6409 ≤ 4114845284179^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308264889 10000000000 4114845284179 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4992904239/10000000000 : ℝ)^8457 ≤ (19995479681437/50000000000000 : ℝ)^6409 := by
    have hnat : (4992904239 : ℕ)^8457*50000000000000^6409 ≤ 19995479681437^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4992904239 10000000000 19995479681437 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (185839021/500000000 : ℝ)^8457 ≤ (27090278346973/100000000000000 : ℝ)^6409 := by
    have hnat : (185839021 : ℕ)^8457*100000000000000^6409 ≤ 27090278346973^6409*500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185839021 500000000 27090278346973 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308264889/10000000000 : ℝ), (4992904239/10000000000 : ℝ), (185839021/500000000 : ℝ)] ![(4114845284179/12500000000000 : ℝ), (19995479681437/50000000000000 : ℝ), (27090278346973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308264889/10000000000 : ℝ)|^8457 ≤ (4114845284179/12500000000000 : ℝ)^6409
        have hw : |(4308264889/10000000000 : ℝ)|=(4308264889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4992904239/10000000000 : ℝ)|^8457 ≤ (19995479681437/50000000000000 : ℝ)^6409
        have hw : |(4992904239/10000000000 : ℝ)|=(4992904239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(185839021/500000000 : ℝ)|^8457 ≤ (27090278346973/100000000000000 : ℝ)^6409
        have hw : |(185839021/500000000 : ℝ)|=(185839021/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13677/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (181/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1261/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9953/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13677/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (181/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13677/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (181/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13677/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (181/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13677/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (181/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13677/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (181/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13677/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (181/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (181/20000 : ℝ) ^ (1057/256 : ℝ) ≤ (182878879473/50000000000000000000 : ℝ) := by
    have hpowers : (181/20000 : ℝ)^1057 ≤ (182878879473/50000000000000000000 : ℝ)^256 := by
      have hnat : (181 : ℕ)^1057*50000000000000000000^256 ≤ 182878879473^256*20000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        181 20000 182878879473 50000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (181/20000 : ℝ)) (X := (182878879473/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13677/50000 : ℝ) ^ (1057/256 : ℝ) ≤ (473709220727787721/100000000000000000000 : ℝ) := by
    have hpowers : (13677/50000 : ℝ)^1057 ≤ (473709220727787721/100000000000000000000 : ℝ)^256 := by
      have hnat : (13677 : ℕ)^1057*100000000000000000000^256 ≤ 473709220727787721^256*50000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13677 50000 473709220727787721 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13677/50000 : ℝ)) (X := (473709220727787721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000182878879473/25000000000000000000 : ℝ) ≤ (10000000017716933/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (25000000182878879473/25000000000000000000 : ℝ)^256 ≤ (10000000017716933/10000000000000000 : ℝ)^1057 := by
      have hnat : (25000000182878879473 : ℕ)^256*10000000000000000^1057 ≤ 10000000017716933^1057*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000182878879473 25000000000000000000 10000000017716933 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000017716933/10000000000000000 : ℝ)) (X := (25000000182878879473/25000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100473709586485546667/100000000000000000000 : ℝ) ≤ (5005726234139549/5000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (100473709586485546667/100000000000000000000 : ℝ)^256 ≤ (5005726234139549/5000000000000000 : ℝ)^1057 := by
      have hnat : (100473709586485546667 : ℕ)^256*5000000000000000^1057 ≤ 5005726234139549^1057*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100473709586485546667 100000000000000000000 5005726234139549 5000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005726234139549/5000000000000000 : ℝ)) (X := (100473709586485546667/100000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50473709220727787721/50000000000000000000 : ℝ) ≤ (10022904918841263/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50473709220727787721/50000000000000000000 : ℝ)^256 ≤ (10022904918841263/10000000000000000 : ℝ)^1057 := by
      have hnat : (50473709220727787721 : ℕ)^256*10000000000000000^1057 ≤ 10022904918841263^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50473709220727787721 50000000000000000000 10022904918841263 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10022904918841263/10000000000000000 : ℝ)) (X := (50473709220727787721/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(182878879473/50000000000000000000 : ℝ) ≤ ((264469271533077642267/264490000000000000000 : ℝ)+2*(2290490112433/528980000000000 : ℝ)*(181/20000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (264469271533077642267/264490000000000000000 : ℝ)+2*(2290490112433/528980000000000 : ℝ)*(181/20000 : ℝ)=(10000000017716933/10000000000000000 : ℝ) by norm_num, show 1+2*(182878879473/50000000000000000000 : ℝ)=(25000000182878879473/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(473709220727787721/100000000000000000000 : ℝ)+(182878879473/50000000000000000000 : ℝ) ≤ ((264469271533077642267/264490000000000000000 : ℝ)+(2290490112433/528980000000000 : ℝ)*((13677/50000 : ℝ)+(181/20000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (264469271533077642267/264490000000000000000 : ℝ)+(2290490112433/528980000000000 : ℝ)*((13677/50000 : ℝ)+(181/20000 : ℝ))=(5005726234139549/5000000000000000 : ℝ) by norm_num, show 1+(473709220727787721/100000000000000000000 : ℝ)+(182878879473/50000000000000000000 : ℝ)=(100473709586485546667/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(473709220727787721/100000000000000000000 : ℝ) ≤ ((264469271533077642267/264490000000000000000 : ℝ)+2*(2290490112433/528980000000000 : ℝ)*(13677/50000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (264469271533077642267/264490000000000000000 : ℝ)+2*(2290490112433/528980000000000 : ℝ)*(13677/50000 : ℝ)=(10022904918841263/10000000000000000 : ℝ) by norm_num, show 1+2*(473709220727787721/100000000000000000000 : ℝ)=(50473709220727787721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (264469271533077642267/264490000000000000000 : ℝ)*(X 1 0+X 2 0)+(2290490112433/528980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (181/20000 : ℝ)) (hi := (13677/50000 : ℝ)) (c := (264469271533077642267/264490000000000000000 : ℝ)) (alpha := (2290490112433/528980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (264469271533077642267/264490000000000000000 : ℝ)*(X 0 1+X 2 1)+(2290490112433/528980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (181/20000 : ℝ)) (hi := (13677/50000 : ℝ)) (c := (264469271533077642267/264490000000000000000 : ℝ)) (alpha := (2290490112433/528980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (264469271533077642267/264490000000000000000 : ℝ)*(X 0 2+X 1 2)+(2290490112433/528980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (181/20000 : ℝ)) (hi := (13677/50000 : ℝ)) (c := (264469271533077642267/264490000000000000000 : ℝ)) (alpha := (2290490112433/528980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-128100053/625000000 : ℝ)*X 0 0+(1417531431/2500000000 : ℝ)*X 0 1+(1005359677/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706232813/5000000000 : ℝ)*X 1 0+(-1870859/7812500 : ℝ)*X 1 1+(5026798517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5412465741/10000000000 : ℝ)*X 2 0+(314174903/625000000 : ℝ)*X 2 1+(-1197349729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34455517/80000000 : ℝ)*X 0 0+(1849695333/5000000000 : ℝ)*X 0 1+(1252492957/2500000000 : ℝ)*X 0 2+(34455517/80000000 : ℝ)*X 1 0+(1849695333/5000000000 : ℝ)*X 1 1+(1252492957/2500000000 : ℝ)*X 1 2+(34455517/80000000 : ℝ)*X 2 0+(1849695333/5000000000 : ℝ)*X 2 1+(1252492957/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-512562893/2500000000 : ℝ)*X 0 0+(5035176491/10000000000 : ℝ)*X 0 1+(1132317919/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((655819357/1250000000 : ℝ)*X 1 0+(-879954057/5000000000 : ℝ)*X 1 1+(2830795031/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311638693/2500000000 : ℝ)*X 2 0+(5661589767/10000000000 : ℝ)*X 2 1+(-879954331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4308264889/10000000000 : ℝ)*X 0 0+(4992904239/10000000000 : ℝ)*X 0 1+(185839021/500000000 : ℝ)*X 0 2+(4308264889/10000000000 : ℝ)*X 1 0+(4992904239/10000000000 : ℝ)*X 1 1+(185839021/500000000 : ℝ)*X 1 2+(4308264889/10000000000 : ℝ)*X 2 0+(4992904239/10000000000 : ℝ)*X 2 1+(185839021/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5335054832527332638549848923/661225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77586241/100000000000000 : ℝ)*(base1) + (436406387/25000000000000 : ℝ)*(base19) + (13895727/781250000000 : ℝ)*(base23) + (1488037/800000000000 : ℝ)*(upper3) + (218003957/100000000000000 : ℝ)*(upper5) + (57936738385841/5000000000000 : ℝ)*(major0) + (57936738385841/5000000000000 : ℝ)*(major1) + (57936738385841/5000000000000 : ℝ)*(major2) + (155442839945937/10000000000000 : ℝ)*(sp0) + (62177481233189/4000000000000 : ℝ)*(sp1) + (1554436997802217/100000000000000 : ℝ)*(sp2) + (763025332601149/100000000000000 : ℝ)*(sp3) + (81676423/781250000000 : ℝ)*(sp4) + (2539921471/50000000000000 : ℝ)*(sp7) + (190757622507583/25000000000000 : ℝ)*(f.failure) + (1554438776455273/100000000000000 : ℝ)*(f.sum) + (12947757906749/5289800000000000000000000000 : ℝ)*base65 + (4876889452269758453/1322450000000000000000000000000000 : ℝ)*base68 + (16549121692345458453/1322450000000000000000000000000000 : ℝ)*base70 + (5860406701229408453/1322450000000000000000000000000000 : ℝ)*base72 + (6940260397377/1653062500000000000000000000 : ℝ)*base73 + (6468361331048208453/1322450000000000000000000000000000 : ℝ)*base76 + (9807675227889558453/1322450000000000000000000000000000 : ℝ)*base78 + (1702412540658158453/1322450000000000000000000000000000 : ℝ)*base80 + (32974330178507/13224500000000000000000000000 : ℝ)*base82 + (18566229/2500000000000000000000 : ℝ)*base89 + (18566229/2500000000000000000000 : ℝ)*base91 + (18566229/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6066548805821624021672666481/1653062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31345879/5000000000000 : ℝ)*(base19) + (73601721/12500000000000 : ℝ)*(base23) + (11063103/100000000000000 : ℝ)*(upper2) + (55933643/50000000000000 : ℝ)*(upper3) + (76329911/100000000000000 : ℝ)*(upper5) + (297501649515681/25000000000000 : ℝ)*(major0) + (297501649515681/25000000000000 : ℝ)*(major1) + (297501649515681/25000000000000 : ℝ)*(major2) + (1848375851/50000000000000 : ℝ)*(sp1) + (2633236779/100000000000000 : ℝ)*(sp2) + (798194992549357/50000000000000 : ℝ)*(sp4) + (1596385661429433/100000000000000 : ℝ)*(sp5) + (1596386763048167/100000000000000 : ℝ)*(sp6) + (195905772174309/25000000000000 : ℝ)*(sp7) + (195905772174309/25000000000000 : ℝ)*(f.failure) + (798194992549357/50000000000000 : ℝ)*(f.sum) + (15688648294789/3306125000000000000000000000 : ℝ)*base66 + (28551407884669111173/6612250000000000000000000000000000 : ℝ)*base68 + (56093306828526111173/6612250000000000000000000000000000 : ℝ)*base70 + (38873810707112611173/6612250000000000000000000000000000 : ℝ)*base72 + (71242243987203/13224500000000000000000000000 : ℝ)*base74 + (80476904087913611173/6612250000000000000000000000000000 : ℝ)*base76 + (36089518281434361173/6612250000000000000000000000000000 : ℝ)*base78 + (5423036773670138827/6612250000000000000000000000000000 : ℝ)*base79 + (46803427139631/6612250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (24566967/2500000000000000000000 : ℝ)*base89 + (24566967/2500000000000000000000 : ℝ)*base91 + (24566967/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1264_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13677/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (181/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1261/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9953/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1264_s2_0 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-16379337/78125000 : ℝ)*x 0 + (1372271793/2500000000 : ℝ)*x 1 + (1294468219/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16379337/78125000 : ℝ)^8457 ≤ (12726037356477/100000000000000 : ℝ)^6409 := by
    have hnat : (16379337 : ℕ)^8457*100000000000000^6409 ≤ 12726037356477^6409*78125000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16379337 78125000 12726037356477 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372271793/2500000000 : ℝ)^8457 ≤ (11329147672853/25000000000000 : ℝ)^6409 := by
    have hnat : (1372271793 : ℕ)^8457*25000000000000^6409 ≤ 11329147672853^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372271793 2500000000 11329147672853 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294468219/2500000000 : ℝ)^8457 ≤ (41957371940211/100000000000000 : ℝ)^6409 := by
    have hnat : (1294468219 : ℕ)^8457*100000000000000^6409 ≤ 41957371940211^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294468219 2500000000 41957371940211 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16379337/78125000 : ℝ), (1372271793/2500000000 : ℝ), (1294468219/2500000000 : ℝ)] ![(12726037356477/100000000000000 : ℝ), (11329147672853/25000000000000 : ℝ), (41957371940211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16379337/78125000 : ℝ)|^8457 ≤ (12726037356477/100000000000000 : ℝ)^6409
        have hw : |(-16379337/78125000 : ℝ)|=(16379337/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372271793/2500000000 : ℝ)|^8457 ≤ (11329147672853/25000000000000 : ℝ)^6409
        have hw : |(1372271793/2500000000 : ℝ)|=(1372271793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294468219/2500000000 : ℝ)|^8457 ≤ (41957371940211/100000000000000 : ℝ)^6409
        have hw : |(1294468219/2500000000 : ℝ)|=(1294468219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s2_1 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684399011/5000000000 : ℝ)*x 0 + (-2257640083/10000000000 : ℝ)*x 1 + (1294468271/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684399011/5000000000 : ℝ)^8457 ≤ (22005392324781/50000000000000 : ℝ)^6409 := by
    have hnat : (2684399011 : ℕ)^8457*50000000000000^6409 ≤ 22005392324781^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684399011 5000000000 22005392324781 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257640083/10000000000 : ℝ)^8457 ≤ (54811879591/390625000000 : ℝ)^6409 := by
    have hnat : (2257640083 : ℕ)^8457*390625000000^6409 ≤ 54811879591^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257640083 10000000000 54811879591 390625000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294468271/2500000000 : ℝ)^8457 ≤ (4195737416427/10000000000000 : ℝ)^6409 := by
    have hnat : (1294468271 : ℕ)^8457*10000000000000^6409 ≤ 4195737416427^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294468271 2500000000 4195737416427 10000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684399011/5000000000 : ℝ), (-2257640083/10000000000 : ℝ), (1294468271/2500000000 : ℝ)] ![(22005392324781/50000000000000 : ℝ), (54811879591/390625000000 : ℝ), (4195737416427/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684399011/5000000000 : ℝ)|^8457 ≤ (22005392324781/50000000000000 : ℝ)^6409
        have hw : |(2684399011/5000000000 : ℝ)|=(2684399011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257640083/10000000000 : ℝ)|^8457 ≤ (54811879591/390625000000 : ℝ)^6409
        have hw : |(-2257640083/10000000000 : ℝ)|=(2257640083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294468271/2500000000 : ℝ)|^8457 ≤ (4195737416427/10000000000000 : ℝ)^6409
        have hw : |(1294468271/2500000000 : ℝ)|=(1294468271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s2_2 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684398979/5000000000 : ℝ)*x 0 + (1035574619/2000000000 : ℝ)*x 1 + (-2257640153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684398979/5000000000 : ℝ)^8457 ≤ (5501347994659/12500000000000 : ℝ)^6409 := by
    have hnat : (2684398979 : ℕ)^8457*12500000000000^6409 ≤ 5501347994659^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684398979 5000000000 5501347994659 12500000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035574619/2000000000 : ℝ)^8457 ≤ (41957374281889/100000000000000 : ℝ)^6409 := by
    have hnat : (1035574619 : ℕ)^8457*100000000000000^6409 ≤ 41957374281889^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035574619 2000000000 41957374281889 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257640153/10000000000 : ℝ)^8457 ≤ (876990109337/6250000000000 : ℝ)^6409 := by
    have hnat : (2257640153 : ℕ)^8457*6250000000000^6409 ≤ 876990109337^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257640153 10000000000 876990109337 6250000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684398979/5000000000 : ℝ), (1035574619/2000000000 : ℝ), (-2257640153/10000000000 : ℝ)] ![(5501347994659/12500000000000 : ℝ), (41957374281889/100000000000000 : ℝ), (876990109337/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684398979/5000000000 : ℝ)|^8457 ≤ (5501347994659/12500000000000 : ℝ)^6409
        have hw : |(2684398979/5000000000 : ℝ)|=(2684398979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035574619/2000000000 : ℝ)|^8457 ≤ (41957374281889/100000000000000 : ℝ)^6409
        have hw : |(1035574619/2000000000 : ℝ)|=(1035574619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257640153/10000000000 : ℝ)|^8457 ≤ (876990109337/6250000000000 : ℝ)^6409
        have hw : |(-2257640153/10000000000 : ℝ)|=(2257640153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s2_3 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084854401/2500000000 : ℝ)*x 0 + (806715233/2000000000 : ℝ)*x 1 + (466757859/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084854401/2500000000 : ℝ)^8457 ≤ (6646644207343/20000000000000 : ℝ)^6409 := by
    have hnat : (1084854401 : ℕ)^8457*20000000000000^6409 ≤ 6646644207343^6409*2500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084854401 2500000000 6646644207343 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806715233/2000000000 : ℝ)^8457 ≤ (30177852818031/100000000000000 : ℝ)^6409 := by
    have hnat : (806715233 : ℕ)^8457*100000000000000^6409 ≤ 30177852818031^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806715233 2000000000 30177852818031 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466757859/1000000000 : ℝ)^8457 ≤ (18294463062249/50000000000000 : ℝ)^6409 := by
    have hnat : (466757859 : ℕ)^8457*50000000000000^6409 ≤ 18294463062249^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466757859 1000000000 18294463062249 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084854401/2500000000 : ℝ), (806715233/2000000000 : ℝ), (466757859/1000000000 : ℝ)] ![(6646644207343/20000000000000 : ℝ), (30177852818031/100000000000000 : ℝ), (18294463062249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084854401/2500000000 : ℝ)|^8457 ≤ (6646644207343/20000000000000 : ℝ)^6409
        have hw : |(1084854401/2500000000 : ℝ)|=(1084854401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806715233/2000000000 : ℝ)|^8457 ≤ (30177852818031/100000000000000 : ℝ)^6409
        have hw : |(806715233/2000000000 : ℝ)|=(806715233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466757859/1000000000 : ℝ)|^8457 ≤ (18294463062249/50000000000000 : ℝ)^6409
        have hw : |(466757859/1000000000 : ℝ)|=(466757859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s2_4 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1048314549/5000000000 : ℝ)*x 0 + (647480427/1250000000 : ℝ)*x 1 + (85735913/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048314549/5000000000 : ℝ)^8457 ≤ (6363314884383/50000000000000 : ℝ)^6409 := by
    have hnat : (1048314549 : ℕ)^8457*50000000000000^6409 ≤ 6363314884383^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048314549 5000000000 6363314884383 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647480427/1250000000 : ℝ)^8457 ≤ (20989221699729/50000000000000 : ℝ)^6409 := by
    have hnat : (647480427 : ℕ)^8457*50000000000000^6409 ≤ 20989221699729^6409*1250000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647480427 1250000000 20989221699729 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85735913/156250000 : ℝ)^8457 ≤ (22647463411079/50000000000000 : ℝ)^6409 := by
    have hnat : (85735913 : ℕ)^8457*50000000000000^6409 ≤ 22647463411079^6409*156250000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85735913 156250000 22647463411079 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1048314549/5000000000 : ℝ), (647480427/1250000000 : ℝ), (85735913/156250000 : ℝ)] ![(6363314884383/50000000000000 : ℝ), (20989221699729/50000000000000 : ℝ), (22647463411079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1048314549/5000000000 : ℝ)|^8457 ≤ (6363314884383/50000000000000 : ℝ)^6409
        have hw : |(-1048314549/5000000000 : ℝ)|=(1048314549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647480427/1250000000 : ℝ)|^8457 ≤ (20989221699729/50000000000000 : ℝ)^6409
        have hw : |(647480427/1250000000 : ℝ)|=(647480427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85735913/156250000 : ℝ)|^8457 ≤ (22647463411079/50000000000000 : ℝ)^6409
        have hw : |(85735913/156250000 : ℝ)|=(85735913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s2_5 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289214389/10000000000 : ℝ)*x 0 + (-97420723/500000000 : ℝ)*x 1 + (219483939/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289214389/10000000000 : ℝ)^8457 ≤ (43151971726147/100000000000000 : ℝ)^6409 := by
    have hnat : (5289214389 : ℕ)^8457*100000000000000^6409 ≤ 43151971726147^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289214389 10000000000 43151971726147 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97420723/500000000 : ℝ)^8457 ≤ (11553100960959/100000000000000 : ℝ)^6409 := by
    have hnat : (97420723 : ℕ)^8457*100000000000000^6409 ≤ 11553100960959^6409*500000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97420723 500000000 11553100960959 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219483939/400000000 : ℝ)^8457 ≤ (45294927290541/100000000000000 : ℝ)^6409 := by
    have hnat : (219483939 : ℕ)^8457*100000000000000^6409 ≤ 45294927290541^6409*400000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219483939 400000000 45294927290541 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289214389/10000000000 : ℝ), (-97420723/500000000 : ℝ), (219483939/400000000 : ℝ)] ![(43151971726147/100000000000000 : ℝ), (11553100960959/100000000000000 : ℝ), (45294927290541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289214389/10000000000 : ℝ)|^8457 ≤ (43151971726147/100000000000000 : ℝ)^6409
        have hw : |(5289214389/10000000000 : ℝ)|=(5289214389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97420723/500000000 : ℝ)|^8457 ≤ (11553100960959/100000000000000 : ℝ)^6409
        have hw : |(-97420723/500000000 : ℝ)|=(97420723/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219483939/400000000 : ℝ)|^8457 ≤ (45294927290541/100000000000000 : ℝ)^6409
        have hw : |(219483939/400000000 : ℝ)|=(219483939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s2_6 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289214509/10000000000 : ℝ)*x 0 + (548709859/1000000000 : ℝ)*x 1 + (-389682827/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289214509/10000000000 : ℝ)^8457 ≤ (43151973018011/100000000000000 : ℝ)^6409 := by
    have hnat : (5289214509 : ℕ)^8457*100000000000000^6409 ≤ 43151973018011^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289214509 10000000000 43151973018011 100000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548709859/1000000000 : ℝ)^8457 ≤ (22647464271597/50000000000000 : ℝ)^6409 := by
    have hnat : (548709859 : ℕ)^8457*50000000000000^6409 ≤ 22647464271597^6409*1000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548709859 1000000000 22647464271597 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389682827/2000000000 : ℝ)^8457 ≤ (5776549209037/50000000000000 : ℝ)^6409 := by
    have hnat : (389682827 : ℕ)^8457*50000000000000^6409 ≤ 5776549209037^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389682827 2000000000 5776549209037 50000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289214509/10000000000 : ℝ), (548709859/1000000000 : ℝ), (-389682827/2000000000 : ℝ)] ![(43151973018011/100000000000000 : ℝ), (22647464271597/50000000000000 : ℝ), (5776549209037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289214509/10000000000 : ℝ)|^8457 ≤ (43151973018011/100000000000000 : ℝ)^6409
        have hw : |(5289214509/10000000000 : ℝ)|=(5289214509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548709859/1000000000 : ℝ)|^8457 ≤ (22647464271597/50000000000000 : ℝ)^6409
        have hw : |(548709859/1000000000 : ℝ)|=(548709859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-389682827/2000000000 : ℝ)|^8457 ≤ (5776549209037/50000000000000 : ℝ)^6409
        have hw : |(-389682827/2000000000 : ℝ)|=(389682827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1264_s2_7 (p : ℝ) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4339567851/10000000000 : ℝ)*x 0 + (932712947/2000000000 : ℝ)*x 1 + (2018813339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4339567851/10000000000 : ℝ)^8457 ≤ (8308684849621/25000000000000 : ℝ)^6409 := by
    have hnat : (4339567851 : ℕ)^8457*25000000000000^6409 ≤ 8308684849621^6409*10000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4339567851 10000000000 8308684849621 25000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932712947/2000000000 : ℝ)^8457 ≤ (7309482587497/20000000000000 : ℝ)^6409 := by
    have hnat : (932712947 : ℕ)^8457*20000000000000^6409 ≤ 7309482587497^6409*2000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932712947 2000000000 7309482587497 20000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2018813339/5000000000 : ℝ)^8457 ≤ (1510892382253/5000000000000 : ℝ)^6409 := by
    have hnat : (2018813339 : ℕ)^8457*5000000000000^6409 ≤ 1510892382253^6409*5000000000^8457 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018813339 5000000000 1510892382253 5000000000000 8457 6409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8457/2048 : ℝ)) 8457 6409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4339567851/10000000000 : ℝ), (932712947/2000000000 : ℝ), (2018813339/5000000000 : ℝ)] ![(8308684849621/25000000000000 : ℝ), (7309482587497/20000000000000 : ℝ), (1510892382253/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4339567851/10000000000 : ℝ)|^8457 ≤ (8308684849621/25000000000000 : ℝ)^6409
        have hw : |(4339567851/10000000000 : ℝ)|=(4339567851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932712947/2000000000 : ℝ)|^8457 ≤ (7309482587497/20000000000000 : ℝ)^6409
        have hw : |(932712947/2000000000 : ℝ)|=(932712947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2018813339/5000000000 : ℝ)|^8457 ≤ (1510892382253/5000000000000 : ℝ)^6409
        have hw : |(2018813339/5000000000 : ℝ)|=(2018813339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1264_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9953/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2397/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8083/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9953/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9953/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1261/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9953/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9953/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1261/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9953/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9953/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1261/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1261/20000 : ℝ) ^ (1057/256 : ℝ) ≤ (1106655049260777/100000000000000000000 : ℝ) := by
    have hpowers : (1261/20000 : ℝ)^1057 ≤ (1106655049260777/100000000000000000000 : ℝ)^256 := by
      have hnat : (1261 : ℕ)^1057*100000000000000000000^256 ≤ 1106655049260777^256*20000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1261 20000 1106655049260777 100000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1261/20000 : ℝ)) (X := (1106655049260777/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9953/50000 : ℝ) ^ (1057/256 : ℝ) ≤ (31879438526423231/25000000000000000000 : ℝ) := by
    have hpowers : (9953/50000 : ℝ)^1057 ≤ (31879438526423231/25000000000000000000 : ℝ)^256 := by
      have hnat : (9953 : ℕ)^1057*25000000000000000000^256 ≤ 31879438526423231^256*50000^1057 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9953 50000 31879438526423231 25000000000000000000 1057 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9953/50000 : ℝ)) (X := (31879438526423231/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001106655049260777/50000000000000000000 : ℝ) ≤ (2500013401197577/2500000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (50001106655049260777/50000000000000000000 : ℝ)^256 ≤ (2500013401197577/2500000000000000 : ℝ)^1057 := by
      have hnat : (50001106655049260777 : ℕ)^256*2500000000000000^1057 ≤ 2500013401197577^1057*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001106655049260777 50000000000000000000 2500013401197577 2500000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500013401197577/2500000000000000 : ℝ)) (X := (50001106655049260777/50000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100128624409154953701/100000000000000000000 : ℝ) ≤ (10003113700385287/10000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (100128624409154953701/100000000000000000000 : ℝ)^256 ≤ (10003113700385287/10000000000000000 : ℝ)^1057 := by
      have hnat : (100128624409154953701 : ℕ)^256*10000000000000000^1057 ≤ 10003113700385287^1057*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100128624409154953701 100000000000000000000 10003113700385287 10000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003113700385287/10000000000000000 : ℝ)) (X := (100128624409154953701/100000000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12531879438526423231/12500000000000000000 : ℝ) ≤ (5003086897990133/5000000000000000 : ℝ) ^ (1057/256 : ℝ) := by
    have hpowers : (12531879438526423231/12500000000000000000 : ℝ)^256 ≤ (5003086897990133/5000000000000000 : ℝ)^1057 := by
      have hnat : (12531879438526423231 : ℕ)^256*5000000000000000^1057 ≤ 5003086897990133^1057*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12531879438526423231 12500000000000000000 5003086897990133 5000000000000000 256 1057 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003086897990133/5000000000000000 : ℝ)) (X := (12531879438526423231/12500000000000000000 : ℝ)) (by norm_num) 1057 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1106655049260777/100000000000000000000 : ℝ) ≤ ((67986070636650146959/68005000000000000000 : ℝ)+2*(3060095594979/1360100000000000 : ℝ)*(1261/20000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (67986070636650146959/68005000000000000000 : ℝ)+2*(3060095594979/1360100000000000 : ℝ)*(1261/20000 : ℝ)=(2500013401197577/2500000000000000 : ℝ) by norm_num, show 1+2*(1106655049260777/100000000000000000000 : ℝ)=(50001106655049260777/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31879438526423231/25000000000000000000 : ℝ)+(1106655049260777/100000000000000000000 : ℝ) ≤ ((67986070636650146959/68005000000000000000 : ℝ)+(3060095594979/1360100000000000 : ℝ)*((9953/50000 : ℝ)+(1261/20000 : ℝ)))^(1057/256 : ℝ) := by
    rw [show (67986070636650146959/68005000000000000000 : ℝ)+(3060095594979/1360100000000000 : ℝ)*((9953/50000 : ℝ)+(1261/20000 : ℝ))=(10003113700385287/10000000000000000 : ℝ) by norm_num, show 1+(31879438526423231/25000000000000000000 : ℝ)+(1106655049260777/100000000000000000000 : ℝ)=(100128624409154953701/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31879438526423231/25000000000000000000 : ℝ) ≤ ((67986070636650146959/68005000000000000000 : ℝ)+2*(3060095594979/1360100000000000 : ℝ)*(9953/50000 : ℝ))^(1057/256 : ℝ) := by
    rw [show (67986070636650146959/68005000000000000000 : ℝ)+2*(3060095594979/1360100000000000 : ℝ)*(9953/50000 : ℝ)=(5003086897990133/5000000000000000 : ℝ) by norm_num, show 1+2*(31879438526423231/25000000000000000000 : ℝ)=(12531879438526423231/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (67986070636650146959/68005000000000000000 : ℝ)*(X 1 0+X 2 0)+(3060095594979/1360100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (1261/20000 : ℝ)) (hi := (9953/50000 : ℝ)) (c := (67986070636650146959/68005000000000000000 : ℝ)) (alpha := (3060095594979/1360100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (67986070636650146959/68005000000000000000 : ℝ)*(X 0 1+X 2 1)+(3060095594979/1360100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (1261/20000 : ℝ)) (hi := (9953/50000 : ℝ)) (c := (67986070636650146959/68005000000000000000 : ℝ)) (alpha := (3060095594979/1360100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (67986070636650146959/68005000000000000000 : ℝ)*(X 0 2+X 1 2)+(3060095594979/1360100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1057/256 : ℝ)) (lo := (1261/20000 : ℝ)) (hi := (9953/50000 : ℝ)) (c := (67986070636650146959/68005000000000000000 : ℝ)) (alpha := (3060095594979/1360100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16379337/78125000 : ℝ)*X 0 0+(1372271793/2500000000 : ℝ)*X 0 1+(1294468219/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684399011/5000000000 : ℝ)*X 1 0+(-2257640083/10000000000 : ℝ)*X 1 1+(1294468271/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684398979/5000000000 : ℝ)*X 2 0+(1035574619/2000000000 : ℝ)*X 2 1+(-2257640153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1084854401/2500000000 : ℝ)*X 0 0+(806715233/2000000000 : ℝ)*X 0 1+(466757859/1000000000 : ℝ)*X 0 2+(1084854401/2500000000 : ℝ)*X 1 0+(806715233/2000000000 : ℝ)*X 1 1+(466757859/1000000000 : ℝ)*X 1 2+(1084854401/2500000000 : ℝ)*X 2 0+(806715233/2000000000 : ℝ)*X 2 1+(466757859/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1048314549/5000000000 : ℝ)*X 0 0+(647480427/1250000000 : ℝ)*X 0 1+(85735913/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289214389/10000000000 : ℝ)*X 1 0+(-97420723/500000000 : ℝ)*X 1 1+(219483939/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289214509/10000000000 : ℝ)*X 2 0+(548709859/1000000000 : ℝ)*X 2 1+(-389682827/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4339567851/10000000000 : ℝ)*X 0 0+(932712947/2000000000 : ℝ)*X 0 1+(2018813339/5000000000 : ℝ)*X 0 2+(4339567851/10000000000 : ℝ)*X 1 0+(932712947/2000000000 : ℝ)*X 1 1+(2018813339/5000000000 : ℝ)*X 1 2+(4339567851/10000000000 : ℝ)*X 2 0+(932712947/2000000000 : ℝ)*X 2 1+(2018813339/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1264_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2609525002148468340428822877/850062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (221333803/50000000000000 : ℝ)*(base19) + (99094533/25000000000000 : ℝ)*(base23) + (428719/10000000000000 : ℝ)*(lower2) + (88239379/100000000000000 : ℝ)*(upper3) + (23990323/100000000000000 : ℝ)*(upper5) + (598815028128501/25000000000000 : ℝ)*(major0) + (598815028128501/25000000000000 : ℝ)*(major1) + (598815028128501/25000000000000 : ℝ)*(major2) + (401653449003941/12500000000000 : ℝ)*(sp0) + (1606616680114519/50000000000000 : ℝ)*(sp1) + (200827087907407/6250000000000 : ℝ)*(sp2) + (315456682229519/20000000000000 : ℝ)*(sp3) + (1242173023/20000000000000 : ℝ)*(sp4) + (181791061/6250000000000 : ℝ)*(sp7) + (1577286319804571/100000000000000 : ℝ)*(f.failure) + (3213233802896643/100000000000000 : ℝ)*(f.sum) + (19654687698763/34002500000000000000000000000 : ℝ)*base65 + (3559711324736453459/1700125000000000000000000000000000 : ℝ)*base67 + (344052745137078459/1700125000000000000000000000000000 : ℝ)*base69 + (6827878334163671541/1700125000000000000000000000000000 : ℝ)*base72 + (34699486256011/68005000000000000000000000000 : ℝ)*base73 + (8985177450035921541/1700125000000000000000000000000000 : ℝ)*base76 + (4164523135621171541/1700125000000000000000000000000000 : ℝ)*base78 + (9264404628436546541/1700125000000000000000000000000000 : ℝ)*base80 + (11426574696147/34002500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2537527/10000000000000000000000 : ℝ)*base90 + (2537527/10000000000000000000000 : ℝ)*base92 + (2537527/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (674090943205788717941258601/485750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670359739/100000000000000 : ℝ)*(base19) + (494107539/50000000000000 : ℝ)*(base23) + (608179/800000000000 : ℝ)*(upper2) + (119181121/100000000000000 : ℝ)*(upper3) + (20853261/100000000000000 : ℝ)*(upper5) + (2426113132384903/100000000000000 : ℝ)*(major0) + (2426113132384903/100000000000000 : ℝ)*(major1) + (2426113132384903/100000000000000 : ℝ)*(major2) + (6381769167/100000000000000 : ℝ)*(sp1) + (13046820919/100000000000000 : ℝ)*(sp2) + (1627311544027993/50000000000000 : ℝ)*(sp4) + (81365400898177/2500000000000 : ℝ)*(sp5) + (813652263254997/25000000000000 : ℝ)*(sp6) + (798801565228033/50000000000000 : ℝ)*(sp7) + (798801565228033/50000000000000 : ℝ)*(f.failure) + (1627311544027993/50000000000000 : ℝ)*(f.sum) + (69158577350347/68005000000000000000000000000 : ℝ)*base65 + (59185564602061809977/6800500000000000000000000000000000 : ℝ)*base67 + (47608243695854809977/6800500000000000000000000000000000 : ℝ)*base69 + (31479271661224809977/6800500000000000000000000000000000 : ℝ)*base71 + (32658048862237/4250312500000000000000000000 : ℝ)*base73 + (11696230784016809977/6800500000000000000000000000000000 : ℝ)*base75 + (58854361387474809977/6800500000000000000000000000000000 : ℝ)*base77 + (19413499667337309977/6800500000000000000000000000000000 : ℝ)*base79 + (25080154329077/4250312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (63270421/5000000000000000000000 : ℝ)*base90 + (63270421/5000000000000000000000 : ℝ)*base92 + (63270421/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1264_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9953/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1261/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2397/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8083/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1264_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1264_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2397/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8083/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1264_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1264_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1264_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1057/256 : ℝ) ≤ p) (hpb : p ≤ (8457/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151859563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2397/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8083/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1264_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
