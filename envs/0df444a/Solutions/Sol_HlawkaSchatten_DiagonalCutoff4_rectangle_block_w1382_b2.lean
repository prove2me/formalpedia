-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:23:35.310877+00:00
-- url     : https://prove2.me/submissions/72763b42-f0c5-4b05-a7d3-f35bf3da2349

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
theorem support_rectangle_w1382_s6_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-50247749/250000000 : ℝ)*x 0 + (5410648531/10000000000 : ℝ)*x 1 + (5245752133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50247749/250000000 : ℝ)^2171 ≤ (12249636710373/100000000000000 : ℝ)^1659 := by
    have hnat : (50247749 : ℕ)^2171*100000000000000^1659 ≤ 12249636710373^1659*250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50247749 250000000 12249636710373 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410648531/10000000000 : ℝ)^2171 ≤ (44763581120327/100000000000000 : ℝ)^1659 := by
    have hnat : (5410648531 : ℕ)^2171*100000000000000^1659 ≤ 44763581120327^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410648531 10000000000 44763581120327 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245752133/10000000000 : ℝ)^2171 ≤ (10746695539789/25000000000000 : ℝ)^1659 := by
    have hnat : (5245752133 : ℕ)^2171*25000000000000^1659 ≤ 10746695539789^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245752133 10000000000 10746695539789 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50247749/250000000 : ℝ), (5410648531/10000000000 : ℝ), (5245752133/10000000000 : ℝ)] ![(12249636710373/100000000000000 : ℝ), (44763581120327/100000000000000 : ℝ), (10746695539789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50247749/250000000 : ℝ)|^2171 ≤ (12249636710373/100000000000000 : ℝ)^1659
        have hw : |(-50247749/250000000 : ℝ)|=(50247749/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410648531/10000000000 : ℝ)|^2171 ≤ (44763581120327/100000000000000 : ℝ)^1659
        have hw : |(5410648531/10000000000 : ℝ)|=(5410648531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245752133/10000000000 : ℝ)|^2171 ≤ (10746695539789/25000000000000 : ℝ)^1659
        have hw : |(5245752133/10000000000 : ℝ)|=(5245752133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s6_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069654559/2000000000 : ℝ)*x 0 + (-1046947699/5000000000 : ℝ)*x 1 + (5245752171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069654559/2000000000 : ℝ)^2171 ≤ (22044736712971/50000000000000 : ℝ)^1659 := by
    have hnat : (1069654559 : ℕ)^2171*50000000000000^1659 ≤ 22044736712971^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069654559 2000000000 22044736712971 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046947699/5000000000 : ℝ)^2171 ≤ (12923743992937/100000000000000 : ℝ)^1659 := by
    have hnat : (1046947699 : ℕ)^2171*100000000000000^1659 ≤ 12923743992937^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046947699 5000000000 12923743992937 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245752171/10000000000 : ℝ)^2171 ≤ (42986782566653/100000000000000 : ℝ)^1659 := by
    have hnat : (5245752171 : ℕ)^2171*100000000000000^1659 ≤ 42986782566653^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245752171 10000000000 42986782566653 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069654559/2000000000 : ℝ), (-1046947699/5000000000 : ℝ), (5245752171/10000000000 : ℝ)] ![(22044736712971/50000000000000 : ℝ), (12923743992937/100000000000000 : ℝ), (42986782566653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069654559/2000000000 : ℝ)|^2171 ≤ (22044736712971/50000000000000 : ℝ)^1659
        have hw : |(1069654559/2000000000 : ℝ)|=(1069654559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046947699/5000000000 : ℝ)|^2171 ≤ (12923743992937/100000000000000 : ℝ)^1659
        have hw : |(-1046947699/5000000000 : ℝ)|=(1046947699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245752171/10000000000 : ℝ)|^2171 ≤ (42986782566653/100000000000000 : ℝ)^1659
        have hw : |(5245752171/10000000000 : ℝ)|=(5245752171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s6_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668534117/1250000000 : ℝ)*x 0 + (5245752099/10000000000 : ℝ)*x 1 + (-418779061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668534117/1250000000 : ℝ)^2171 ≤ (11022368736757/25000000000000 : ℝ)^1659 := by
    have hnat : (668534117 : ℕ)^2171*25000000000000^1659 ≤ 11022368736757^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668534117 1250000000 11022368736757 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245752099/10000000000 : ℝ)^2171 ≤ (21493390897277/50000000000000 : ℝ)^1659 := by
    have hnat : (5245752099 : ℕ)^2171*50000000000000^1659 ≤ 21493390897277^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245752099 10000000000 21493390897277 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (418779061/2000000000 : ℝ)^2171 ≤ (12923743241781/100000000000000 : ℝ)^1659 := by
    have hnat : (418779061 : ℕ)^2171*100000000000000^1659 ≤ 12923743241781^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      418779061 2000000000 12923743241781 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668534117/1250000000 : ℝ), (5245752099/10000000000 : ℝ), (-418779061/2000000000 : ℝ)] ![(11022368736757/25000000000000 : ℝ), (21493390897277/50000000000000 : ℝ), (12923743241781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668534117/1250000000 : ℝ)|^2171 ≤ (11022368736757/25000000000000 : ℝ)^1659
        have hw : |(668534117/1250000000 : ℝ)|=(668534117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245752099/10000000000 : ℝ)|^2171 ≤ (21493390897277/50000000000000 : ℝ)^1659
        have hw : |(5245752099/10000000000 : ℝ)|=(5245752099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-418779061/2000000000 : ℝ)|^2171 ≤ (12923743241781/100000000000000 : ℝ)^1659
        have hw : |(-418779061/2000000000 : ℝ)|=(418779061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s6_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (67441679/156250000 : ℝ)*x 0 + (4144239213/10000000000 : ℝ)*x 1 + (4494831739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67441679/156250000 : ℝ)^2171 ≤ (4162992482193/12500000000000 : ℝ)^1659 := by
    have hnat : (67441679 : ℕ)^2171*12500000000000^1659 ≤ 4162992482193^1659*156250000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67441679 156250000 4162992482193 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144239213/10000000000 : ℝ)^2171 ≤ (15788859962743/50000000000000 : ℝ)^1659 := by
    have hnat : (4144239213 : ℕ)^2171*50000000000000^1659 ≤ 15788859962743^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144239213 10000000000 15788859962743 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494831739/10000000000 : ℝ)^2171 ≤ (8779585052609/25000000000000 : ℝ)^1659 := by
    have hnat : (4494831739 : ℕ)^2171*25000000000000^1659 ≤ 8779585052609^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494831739 10000000000 8779585052609 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67441679/156250000 : ℝ), (4144239213/10000000000 : ℝ), (4494831739/10000000000 : ℝ)] ![(4162992482193/12500000000000 : ℝ), (15788859962743/50000000000000 : ℝ), (8779585052609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67441679/156250000 : ℝ)|^2171 ≤ (4162992482193/12500000000000 : ℝ)^1659
        have hw : |(67441679/156250000 : ℝ)|=(67441679/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144239213/10000000000 : ℝ)|^2171 ≤ (15788859962743/50000000000000 : ℝ)^1659
        have hw : |(4144239213/10000000000 : ℝ)|=(4144239213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494831739/10000000000 : ℝ)|^2171 ≤ (8779585052609/25000000000000 : ℝ)^1659
        have hw : |(4494831739/10000000000 : ℝ)|=(4494831739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s6_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-200992163/1000000000 : ℝ)*x 0 + (524634453/1000000000 : ℝ)*x 1 + (1352513287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (200992163/1000000000 : ℝ)^2171 ≤ (3062432446249/25000000000000 : ℝ)^1659 := by
    have hnat : (200992163 : ℕ)^2171*25000000000000^1659 ≤ 3062432446249^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200992163 1000000000 3062432446249 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524634453/1000000000 : ℝ)^2171 ≤ (21496567449177/50000000000000 : ℝ)^1659 := by
    have hnat : (524634453 : ℕ)^2171*50000000000000^1659 ≤ 21496567449177^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524634453 1000000000 21496567449177 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352513287/2500000000 : ℝ)^2171 ≤ (44757135303017/100000000000000 : ℝ)^1659 := by
    have hnat : (1352513287 : ℕ)^2171*100000000000000^1659 ≤ 44757135303017^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352513287 2500000000 44757135303017 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-200992163/1000000000 : ℝ), (524634453/1000000000 : ℝ), (1352513287/2500000000 : ℝ)] ![(3062432446249/25000000000000 : ℝ), (21496567449177/50000000000000 : ℝ), (44757135303017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-200992163/1000000000 : ℝ)|^2171 ≤ (3062432446249/25000000000000 : ℝ)^1659
        have hw : |(-200992163/1000000000 : ℝ)|=(200992163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524634453/1000000000 : ℝ)|^2171 ≤ (21496567449177/50000000000000 : ℝ)^1659
        have hw : |(524634453/1000000000 : ℝ)|=(524634453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352513287/2500000000 : ℝ)|^2171 ≤ (44757135303017/100000000000000 : ℝ)^1659
        have hw : |(1352513287/2500000000 : ℝ)|=(1352513287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s6_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530560997/1000000000 : ℝ)*x 0 + (-385918839/2000000000 : ℝ)*x 1 + (2705026653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530560997/1000000000 : ℝ)^2171 ≤ (8725960187871/20000000000000 : ℝ)^1659 := by
    have hnat : (530560997 : ℕ)^2171*20000000000000^1659 ≤ 8725960187871^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530560997 1000000000 8725960187871 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385918839/2000000000 : ℝ)^2171 ≤ (11613062027607/100000000000000 : ℝ)^1659 := by
    have hnat : (385918839 : ℕ)^2171*100000000000000^1659 ≤ 11613062027607^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385918839 2000000000 11613062027607 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705026653/5000000000 : ℝ)^2171 ≤ (895142740271/2000000000000 : ℝ)^1659 := by
    have hnat : (2705026653 : ℕ)^2171*2000000000000^1659 ≤ 895142740271^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705026653 5000000000 895142740271 2000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530560997/1000000000 : ℝ), (-385918839/2000000000 : ℝ), (2705026653/5000000000 : ℝ)] ![(8725960187871/20000000000000 : ℝ), (11613062027607/100000000000000 : ℝ), (895142740271/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530560997/1000000000 : ℝ)|^2171 ≤ (8725960187871/20000000000000 : ℝ)^1659
        have hw : |(530560997/1000000000 : ℝ)|=(530560997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385918839/2000000000 : ℝ)|^2171 ≤ (11613062027607/100000000000000 : ℝ)^1659
        have hw : |(-385918839/2000000000 : ℝ)|=(385918839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705026653/5000000000 : ℝ)|^2171 ≤ (895142740271/2000000000000 : ℝ)^1659
        have hw : |(2705026653/5000000000 : ℝ)|=(2705026653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s6_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (530561011/1000000000 : ℝ)*x 0 + (1082010637/2000000000 : ℝ)*x 1 + (-1929594171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530561011/1000000000 : ℝ)^2171 ≤ (1745192097837/4000000000000 : ℝ)^1659 := by
    have hnat : (530561011 : ℕ)^2171*4000000000000^1659 ≤ 1745192097837^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530561011 1000000000 1745192097837 4000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082010637/2000000000 : ℝ)^2171 ≤ (8951427140717/20000000000000 : ℝ)^1659 := by
    have hnat : (1082010637 : ℕ)^2171*20000000000000^1659 ≤ 8951427140717^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082010637 2000000000 8951427140717 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929594171/10000000000 : ℝ)^2171 ≤ (2903265459647/25000000000000 : ℝ)^1659 := by
    have hnat : (1929594171 : ℕ)^2171*25000000000000^1659 ≤ 2903265459647^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929594171 10000000000 2903265459647 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530561011/1000000000 : ℝ), (1082010637/2000000000 : ℝ), (-1929594171/10000000000 : ℝ)] ![(1745192097837/4000000000000 : ℝ), (8951427140717/20000000000000 : ℝ), (2903265459647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530561011/1000000000 : ℝ)|^2171 ≤ (1745192097837/4000000000000 : ℝ)^1659
        have hw : |(530561011/1000000000 : ℝ)|=(530561011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082010637/2000000000 : ℝ)|^2171 ≤ (8951427140717/20000000000000 : ℝ)^1659
        have hw : |(1082010637/2000000000 : ℝ)|=(1082010637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1929594171/10000000000 : ℝ)|^2171 ≤ (2903265459647/25000000000000 : ℝ)^1659
        have hw : |(-1929594171/10000000000 : ℝ)|=(1929594171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s6_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (431629221/1000000000 : ℝ)*x 0 + (2246786291/5000000000 : ℝ)*x 1 + (518188143/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431629221/1000000000 : ℝ)^2171 ≤ (33304189803707/100000000000000 : ℝ)^1659 := by
    have hnat : (431629221 : ℕ)^2171*100000000000000^1659 ≤ 33304189803707^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431629221 1000000000 33304189803707 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246786291/5000000000 : ℝ)^2171 ≤ (35105466756319/100000000000000 : ℝ)^1659 := by
    have hnat : (2246786291 : ℕ)^2171*100000000000000^1659 ≤ 35105466756319^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246786291 5000000000 35105466756319 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518188143/1250000000 : ℝ)^2171 ≤ (6318068685737/20000000000000 : ℝ)^1659 := by
    have hnat : (518188143 : ℕ)^2171*20000000000000^1659 ≤ 6318068685737^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518188143 1250000000 6318068685737 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431629221/1000000000 : ℝ), (2246786291/5000000000 : ℝ), (518188143/1250000000 : ℝ)] ![(33304189803707/100000000000000 : ℝ), (35105466756319/100000000000000 : ℝ), (6318068685737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431629221/1000000000 : ℝ)|^2171 ≤ (33304189803707/100000000000000 : ℝ)^1659
        have hw : |(431629221/1000000000 : ℝ)|=(431629221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246786291/5000000000 : ℝ)|^2171 ≤ (35105466756319/100000000000000 : ℝ)^1659
        have hw : |(2246786291/5000000000 : ℝ)|=(2246786291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518188143/1250000000 : ℝ)|^2171 ≤ (6318068685737/20000000000000 : ℝ)^1659
        have hw : |(518188143/1250000000 : ℝ)|=(518188143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (281/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3683/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2247/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2247/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2247/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2247/20000 : ℝ) ^ (4341/1024 : ℝ) ≤ (377741316482723/4000000000000000000 : ℝ) := by
    have hpowers : (2247/20000 : ℝ)^4341 ≤ (377741316482723/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2247 : ℕ)^4341*4000000000000000000^1024 ≤ 377741316482723^1024*20000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2247 20000 377741316482723 4000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2247/20000 : ℝ)) (X := (377741316482723/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14737/100000 : ℝ) ^ (4341/1024 : ℝ) ≤ (29831267776456711/100000000000000000000 : ℝ) := by
    have hpowers : (14737/100000 : ℝ)^4341 ≤ (29831267776456711/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14737 : ℕ)^4341*100000000000000000000^1024 ≤ 29831267776456711^1024*100000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14737 100000 29831267776456711 100000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14737/100000 : ℝ)) (X := (29831267776456711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000377741316482723/2000000000000000000 : ℝ) ≤ (10000445495507469/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (2000377741316482723/2000000000000000000 : ℝ)^1024 ≤ (10000445495507469/10000000000000000 : ℝ)^4341 := by
      have hnat : (2000377741316482723 : ℕ)^1024*10000000000000000^4341 ≤ 10000445495507469^4341*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000377741316482723 2000000000000000000 10000445495507469 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000445495507469/10000000000000000 : ℝ)) (X := (2000377741316482723/2000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019637400344262393/50000000000000000000 : ℝ) ≤ (10000926315656001/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50019637400344262393/50000000000000000000 : ℝ)^1024 ≤ (10000926315656001/10000000000000000 : ℝ)^4341 := by
      have hnat : (50019637400344262393 : ℕ)^1024*10000000000000000^4341 ≤ 10000926315656001^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019637400344262393 50000000000000000000 10000926315656001 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000926315656001/10000000000000000 : ℝ)) (X := (50019637400344262393/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029831267776456711/50000000000000000000 : ℝ) ≤ (10001407135804533/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50029831267776456711/50000000000000000000 : ℝ)^1024 ≤ (10001407135804533/10000000000000000 : ℝ)^4341 := by
      have hnat : (50029831267776456711 : ℕ)^1024*10000000000000000^4341 ≤ 10001407135804533^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029831267776456711 50000000000000000000 10001407135804533 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001407135804533/10000000000000000 : ℝ)) (X := (50029831267776456711/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(377741316482723/4000000000000000000 : ℝ) ≤ ((17505378048264821199/17510000000000000000 : ℝ)+2*(120205037133/87550000000000 : ℝ)*(2247/20000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (17505378048264821199/17510000000000000000 : ℝ)+2*(120205037133/87550000000000 : ℝ)*(2247/20000 : ℝ)=(10000445495507469/10000000000000000 : ℝ) by norm_num, show 1+2*(377741316482723/4000000000000000000 : ℝ)=(2000377741316482723/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29831267776456711/100000000000000000000 : ℝ)+(377741316482723/4000000000000000000 : ℝ) ≤ ((17505378048264821199/17510000000000000000 : ℝ)+(120205037133/87550000000000 : ℝ)*((14737/100000 : ℝ)+(2247/20000 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (17505378048264821199/17510000000000000000 : ℝ)+(120205037133/87550000000000 : ℝ)*((14737/100000 : ℝ)+(2247/20000 : ℝ))=(10000926315656001/10000000000000000 : ℝ) by norm_num, show 1+(29831267776456711/100000000000000000000 : ℝ)+(377741316482723/4000000000000000000 : ℝ)=(50019637400344262393/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29831267776456711/100000000000000000000 : ℝ) ≤ ((17505378048264821199/17510000000000000000 : ℝ)+2*(120205037133/87550000000000 : ℝ)*(14737/100000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (17505378048264821199/17510000000000000000 : ℝ)+2*(120205037133/87550000000000 : ℝ)*(14737/100000 : ℝ)=(10001407135804533/10000000000000000 : ℝ) by norm_num, show 1+2*(29831267776456711/100000000000000000000 : ℝ)=(50029831267776456711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17505378048264821199/17510000000000000000 : ℝ)*(X 1 0+X 2 0)+(120205037133/87550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (17505378048264821199/17510000000000000000 : ℝ)) (alpha := (120205037133/87550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17505378048264821199/17510000000000000000 : ℝ)*(X 0 1+X 2 1)+(120205037133/87550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (17505378048264821199/17510000000000000000 : ℝ)) (alpha := (120205037133/87550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17505378048264821199/17510000000000000000 : ℝ)*(X 0 2+X 1 2)+(120205037133/87550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (2247/20000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (17505378048264821199/17510000000000000000 : ℝ)) (alpha := (120205037133/87550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-50247749/250000000 : ℝ)*X 0 0+(5410648531/10000000000 : ℝ)*X 0 1+(5245752133/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069654559/2000000000 : ℝ)*X 1 0+(-1046947699/5000000000 : ℝ)*X 1 1+(5245752171/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668534117/1250000000 : ℝ)*X 2 0+(5245752099/10000000000 : ℝ)*X 2 1+(-418779061/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((67441679/156250000 : ℝ)*X 0 0+(4144239213/10000000000 : ℝ)*X 0 1+(4494831739/10000000000 : ℝ)*X 0 2+(67441679/156250000 : ℝ)*X 1 0+(4144239213/10000000000 : ℝ)*X 1 1+(4494831739/10000000000 : ℝ)*X 1 2+(67441679/156250000 : ℝ)*X 2 0+(4144239213/10000000000 : ℝ)*X 2 1+(4494831739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-200992163/1000000000 : ℝ)*X 0 0+(524634453/1000000000 : ℝ)*X 0 1+(1352513287/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530560997/1000000000 : ℝ)*X 1 0+(-385918839/2000000000 : ℝ)*X 1 1+(2705026653/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530561011/1000000000 : ℝ)*X 2 0+(1082010637/2000000000 : ℝ)*X 2 1+(-1929594171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431629221/1000000000 : ℝ)*X 0 0+(2246786291/5000000000 : ℝ)*X 0 1+(518188143/1250000000 : ℝ)*X 0 2+(431629221/1000000000 : ℝ)*X 1 0+(2246786291/5000000000 : ℝ)*X 1 1+(518188143/1250000000 : ℝ)*X 1 2+(431629221/1000000000 : ℝ)*X 2 0+(2246786291/5000000000 : ℝ)*X 2 1+(518188143/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14816187081573494609199603/2735937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (132292297/12500000000000 : ℝ)*(base19) + (11527231/1000000000000 : ℝ)*(base23) + (35029309/100000000000000 : ℝ)*(lower2) + (15002381/12500000000000 : ℝ)*(upper3) + (107689591/50000000000000 : ℝ)*(upper5) + (13932488196849/312500000000 : ℝ)*(major0) + (13932488196849/312500000000 : ℝ)*(major1) + (13932488196849/312500000000 : ℝ)*(major2) + (242577307407943/4000000000000 : ℝ)*(sp0) + (6064456348933981/100000000000000 : ℝ)*(sp1) + (3032228127274629/50000000000000 : ℝ)*(sp2) + (713081177207031/25000000000000 : ℝ)*(sp3) + (12361036891/50000000000000 : ℝ)*(sp4) + (10149369647/100000000000000 : ℝ)*(sp7) + (2852334858197771/100000000000000 : ℝ)*(f.failure) + (6064457407272357/100000000000000 : ℝ)*(f.sum) + (3834265534439/875500000000000000000000000 : ℝ)*base66 + (5634938693361913/2735937500000000000000000000000 : ℝ)*base67 + (11045344663261913/2735937500000000000000000000000 : ℝ)*base69 + (5886183414572803/683984375000000000000000000000 : ℝ)*base72 + (120549772269/218875000000000000000000000 : ℝ)*base74 + (23521164229769337/2735937500000000000000000000000 : ℝ)*base76 + (23051162542654299/5471875000000000000000000000000 : ℝ)*base78 + (80292302492985549/5471875000000000000000000000000 : ℝ)*base80 + (4816828118119/875500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (30117671/10000000000000000000000 : ℝ)*base89 + (30117671/10000000000000000000000 : ℝ)*base91 + (30117671/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4876662164688451888327822557/437750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14406587/800000000000 : ℝ)*(base19) + (1060280677/50000000000000 : ℝ)*(base23) + (63586199/25000000000000 : ℝ)*(upper3) + (28353613/50000000000000 : ℝ)*(lower4) + (87101891/50000000000000 : ℝ)*(upper5) + (2245354829570319/50000000000000 : ℝ)*(major0) + (2245354829570319/50000000000000 : ℝ)*(major1) + (2245354829570319/50000000000000 : ℝ)*(major2) + (40701875193/100000000000000 : ℝ)*(sp1) + (11781993019/25000000000000 : ℝ)*(sp2) + (3054205509021441/50000000000000 : ℝ)*(sp4) + (3054184257672157/50000000000000 : ℝ)*(sp5) + (6108361769509453/100000000000000 : ℝ)*(sp6) + (2873007928895371/100000000000000 : ℝ)*(sp7) + (2873007928895371/100000000000000 : ℝ)*(f.failure) + (3054205509021441/50000000000000 : ℝ)*(f.sum) + (11643195588521/4377500000000000000000000000 : ℝ)*base66 + (5315827159676792481/875500000000000000000000000000000 : ℝ)*base67 + (8760282665137792481/875500000000000000000000000000000 : ℝ)*base69 + (3620919236219707519/875500000000000000000000000000000 : ℝ)*base72 + (4091392722409/4377500000000000000000000000 : ℝ)*base73 + (20516756206237292481/875500000000000000000000000000000 : ℝ)*base75 + (175756596679792481/875500000000000000000000000000000 : ℝ)*base77 + (19916230632707519/875500000000000000000000000000000 : ℝ)*base80 + (37465678645947/8755000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5744729/10000000000000000000000 : ℝ)*base90 + (5744729/10000000000000000000000 : ℝ)*base92 + (5744729/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1382_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1382_s7_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-125619591/625000000 : ℝ)*x 0 + (1352652457/2500000000 : ℝ)*x 1 + (5245788607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125619591/625000000 : ℝ)^2171 ≤ (382802018527/3125000000000 : ℝ)^1659 := by
    have hnat : (125619591 : ℕ)^2171*3125000000000^1659 ≤ 382802018527^1659*625000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125619591 625000000 382802018527 3125000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352652457/2500000000 : ℝ)^2171 ≤ (44763162101933/100000000000000 : ℝ)^1659 := by
    have hnat : (1352652457 : ℕ)^2171*100000000000000^1659 ≤ 44763162101933^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352652457 2500000000 44763162101933 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245788607/10000000000 : ℝ)^2171 ≤ (10746793323041/25000000000000 : ℝ)^1659 := by
    have hnat : (5245788607 : ℕ)^2171*25000000000000^1659 ≤ 10746793323041^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245788607 10000000000 10746793323041 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-125619591/625000000 : ℝ), (1352652457/2500000000 : ℝ), (5245788607/10000000000 : ℝ)] ![(382802018527/3125000000000 : ℝ), (44763162101933/100000000000000 : ℝ), (10746793323041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-125619591/625000000 : ℝ)|^2171 ≤ (382802018527/3125000000000 : ℝ)^1659
        have hw : |(-125619591/625000000 : ℝ)|=(125619591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352652457/2500000000 : ℝ)|^2171 ≤ (44763162101933/100000000000000 : ℝ)^1659
        have hw : |(1352652457/2500000000 : ℝ)|=(1352652457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245788607/10000000000 : ℝ)|^2171 ≤ (10746793323041/25000000000000 : ℝ)^1659
        have hw : |(5245788607/10000000000 : ℝ)|=(5245788607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s7_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348262827/10000000000 : ℝ)*x 0 + (-1046930219/5000000000 : ℝ)*x 1 + (524578853/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348262827/10000000000 : ℝ)^2171 ≤ (44089365892709/100000000000000 : ℝ)^1659 := by
    have hnat : (5348262827 : ℕ)^2171*100000000000000^1659 ≤ 44089365892709^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348262827 10000000000 44089365892709 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1046930219/5000000000 : ℝ)^2171 ≤ (6461730811939/50000000000000 : ℝ)^1659 := by
    have hnat : (1046930219 : ℕ)^2171*50000000000000^1659 ≤ 6461730811939^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046930219 5000000000 6461730811939 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524578853/1000000000 : ℝ)^2171 ≤ (8597434493289/20000000000000 : ℝ)^1659 := by
    have hnat : (524578853 : ℕ)^2171*20000000000000^1659 ≤ 8597434493289^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524578853 1000000000 8597434493289 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348262827/10000000000 : ℝ), (-1046930219/5000000000 : ℝ), (524578853/1000000000 : ℝ)] ![(44089365892709/100000000000000 : ℝ), (6461730811939/50000000000000 : ℝ), (8597434493289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348262827/10000000000 : ℝ)|^2171 ≤ (44089365892709/100000000000000 : ℝ)^1659
        have hw : |(5348262827/10000000000 : ℝ)|=(5348262827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1046930219/5000000000 : ℝ)|^2171 ≤ (6461730811939/50000000000000 : ℝ)^1659
        have hw : |(-1046930219/5000000000 : ℝ)|=(1046930219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524578853/1000000000 : ℝ)|^2171 ≤ (8597434493289/20000000000000 : ℝ)^1659
        have hw : |(524578853/1000000000 : ℝ)|=(524578853/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s7_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674131661/5000000000 : ℝ)*x 0 + (655723537/1250000000 : ℝ)*x 1 + (-261732511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674131661/5000000000 : ℝ)^2171 ≤ (4408937123269/10000000000000 : ℝ)^1659 := by
    have hnat : (2674131661 : ℕ)^2171*10000000000000^1659 ≤ 4408937123269^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674131661 5000000000 4408937123269 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655723537/1250000000 : ℝ)^2171 ≤ (42987169957117/100000000000000 : ℝ)^1659 := by
    have hnat : (655723537 : ℕ)^2171*100000000000000^1659 ≤ 42987169957117^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655723537 1250000000 42987169957117 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261732511/1250000000 : ℝ)^2171 ≤ (3230864699241/25000000000000 : ℝ)^1659 := by
    have hnat : (261732511 : ℕ)^2171*25000000000000^1659 ≤ 3230864699241^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261732511 1250000000 3230864699241 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674131661/5000000000 : ℝ), (655723537/1250000000 : ℝ), (-261732511/1250000000 : ℝ)] ![(4408937123269/10000000000000 : ℝ), (42987169957117/100000000000000 : ℝ), (3230864699241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674131661/5000000000 : ℝ)|^2171 ≤ (4408937123269/10000000000000 : ℝ)^1659
        have hw : |(2674131661/5000000000 : ℝ)|=(2674131661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655723537/1250000000 : ℝ)|^2171 ≤ (42987169957117/100000000000000 : ℝ)^1659
        have hw : |(655723537/1250000000 : ℝ)|=(655723537/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261732511/1250000000 : ℝ)|^2171 ≤ (3230864699241/25000000000000 : ℝ)^1659
        have hw : |(-261732511/1250000000 : ℝ)|=(261732511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s7_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2158134903/5000000000 : ℝ)*x 0 + (4144319167/10000000000 : ℝ)*x 1 + (4494751441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158134903/5000000000 : ℝ)^2171 ≤ (1040748862061/3125000000000 : ℝ)^1659 := by
    have hnat : (2158134903 : ℕ)^2171*3125000000000^1659 ≤ 1040748862061^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158134903 5000000000 1040748862061 3125000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144319167/10000000000 : ℝ)^2171 ≤ (31578517168787/100000000000000 : ℝ)^1659 := by
    have hnat : (4144319167 : ℕ)^2171*100000000000000^1659 ≤ 31578517168787^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144319167 10000000000 31578517168787 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494751441/10000000000 : ℝ)^2171 ≤ (8779379805277/25000000000000 : ℝ)^1659 := by
    have hnat : (4494751441 : ℕ)^2171*25000000000000^1659 ≤ 8779379805277^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494751441 10000000000 8779379805277 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158134903/5000000000 : ℝ), (4144319167/10000000000 : ℝ), (4494751441/10000000000 : ℝ)] ![(1040748862061/3125000000000 : ℝ), (31578517168787/100000000000000 : ℝ), (8779379805277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158134903/5000000000 : ℝ)|^2171 ≤ (1040748862061/3125000000000 : ℝ)^1659
        have hw : |(2158134903/5000000000 : ℝ)|=(2158134903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144319167/10000000000 : ℝ)|^2171 ≤ (31578517168787/100000000000000 : ℝ)^1659
        have hw : |(4144319167/10000000000 : ℝ)|=(4144319167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494751441/10000000000 : ℝ)|^2171 ≤ (8779379805277/25000000000000 : ℝ)^1659
        have hw : |(4494751441/10000000000 : ℝ)|=(4494751441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s7_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2009925359/10000000000 : ℝ)*x 0 + (327898759/625000000 : ℝ)*x 1 + (5410015123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2009925359/10000000000 : ℝ)^2171 ≤ (12249759525843/100000000000000 : ℝ)^1659 := by
    have hnat : (2009925359 : ℕ)^2171*100000000000000^1659 ≤ 12249759525843^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2009925359 10000000000 12249759525843 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327898759/625000000 : ℝ)^2171 ≤ (10748379205589/25000000000000 : ℝ)^1659 := by
    have hnat : (327898759 : ℕ)^2171*25000000000000^1659 ≤ 10748379205589^1659*625000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327898759 625000000 10748379205589 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410015123/10000000000 : ℝ)^2171 ≤ (4475672363897/10000000000000 : ℝ)^1659 := by
    have hnat : (5410015123 : ℕ)^2171*10000000000000^1659 ≤ 4475672363897^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410015123 10000000000 4475672363897 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2009925359/10000000000 : ℝ), (327898759/625000000 : ℝ), (5410015123/10000000000 : ℝ)] ![(12249759525843/100000000000000 : ℝ), (10748379205589/25000000000000 : ℝ), (4475672363897/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2009925359/10000000000 : ℝ)|^2171 ≤ (12249759525843/100000000000000 : ℝ)^1659
        have hw : |(-2009925359/10000000000 : ℝ)|=(2009925359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327898759/625000000 : ℝ)|^2171 ≤ (10748379205589/25000000000000 : ℝ)^1659
        have hw : |(327898759/625000000 : ℝ)|=(327898759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410015123/10000000000 : ℝ)|^2171 ≤ (4475672363897/10000000000000 : ℝ)^1659
        have hw : |(5410015123/10000000000 : ℝ)|=(5410015123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s7_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663202501/1250000000 : ℝ)*x 0 + (-1929633457/10000000000 : ℝ)*x 1 + (5410014767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663202501/1250000000 : ℝ)^2171 ≤ (43629908960473/100000000000000 : ℝ)^1659 := by
    have hnat : (663202501 : ℕ)^2171*100000000000000^1659 ≤ 43629908960473^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663202501 1250000000 43629908960473 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929633457/10000000000 : ℝ)^2171 ≤ (1451671405987/12500000000000 : ℝ)^1659 := by
    have hnat : (1929633457 : ℕ)^2171*12500000000000^1659 ≤ 1451671405987^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929633457 10000000000 1451671405987 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410014767/10000000000 : ℝ)^2171 ≤ (11189179946217/25000000000000 : ℝ)^1659 := by
    have hnat : (5410014767 : ℕ)^2171*25000000000000^1659 ≤ 11189179946217^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410014767 10000000000 11189179946217 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663202501/1250000000 : ℝ), (-1929633457/10000000000 : ℝ), (5410014767/10000000000 : ℝ)] ![(43629908960473/100000000000000 : ℝ), (1451671405987/12500000000000 : ℝ), (11189179946217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663202501/1250000000 : ℝ)|^2171 ≤ (43629908960473/100000000000000 : ℝ)^1659
        have hw : |(663202501/1250000000 : ℝ)|=(663202501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929633457/10000000000 : ℝ)|^2171 ≤ (1451671405987/12500000000000 : ℝ)^1659
        have hw : |(-1929633457/10000000000 : ℝ)|=(1929633457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410014767/10000000000 : ℝ)|^2171 ≤ (11189179946217/25000000000000 : ℝ)^1659
        have hw : |(5410014767/10000000000 : ℝ)|=(5410014767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s7_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652809959/5000000000 : ℝ)*x 0 + (2705007487/5000000000 : ℝ)*x 1 + (-964816647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652809959/5000000000 : ℝ)^2171 ≤ (43629907991963/100000000000000 : ℝ)^1659 := by
    have hnat : (2652809959 : ℕ)^2171*100000000000000^1659 ≤ 43629907991963^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652809959 5000000000 43629907991963 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705007487/5000000000 : ℝ)^2171 ≤ (44756722025877/100000000000000 : ℝ)^1659 := by
    have hnat : (2705007487 : ℕ)^2171*100000000000000^1659 ≤ 44756722025877^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705007487 5000000000 44756722025877 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964816647/5000000000 : ℝ)^2171 ≤ (5806684982067/50000000000000 : ℝ)^1659 := by
    have hnat : (964816647 : ℕ)^2171*50000000000000^1659 ≤ 5806684982067^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964816647 5000000000 5806684982067 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652809959/5000000000 : ℝ), (2705007487/5000000000 : ℝ), (-964816647/5000000000 : ℝ)] ![(43629907991963/100000000000000 : ℝ), (44756722025877/100000000000000 : ℝ), (5806684982067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652809959/5000000000 : ℝ)|^2171 ≤ (43629907991963/100000000000000 : ℝ)^1659
        have hw : |(2652809959/5000000000 : ℝ)|=(2652809959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705007487/5000000000 : ℝ)|^2171 ≤ (44756722025877/100000000000000 : ℝ)^1659
        have hw : |(2705007487/5000000000 : ℝ)|=(2705007487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964816647/5000000000 : ℝ)|^2171 ≤ (5806684982067/50000000000000 : ℝ)^1659
        have hw : |(-964816647/5000000000 : ℝ)|=(964816647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_s7_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2158147447/5000000000 : ℝ)*x 0 + (4493493191/10000000000 : ℝ)*x 1 + (4145583817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158147447/5000000000 : ℝ)^2171 ≤ (16652108452313/50000000000000 : ℝ)^1659 := by
    have hnat : (2158147447 : ℕ)^2171*50000000000000^1659 ≤ 16652108452313^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158147447 5000000000 16652108452313 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493493191/10000000000 : ℝ)^2171 ≤ (17552327555287/50000000000000 : ℝ)^1659 := by
    have hnat : (4493493191 : ℕ)^2171*50000000000000^1659 ≤ 17552327555287^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493493191 10000000000 17552327555287 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4145583817/10000000000 : ℝ)^2171 ≤ (7897781993173/25000000000000 : ℝ)^1659 := by
    have hnat : (4145583817 : ℕ)^2171*25000000000000^1659 ≤ 7897781993173^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4145583817 10000000000 7897781993173 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158147447/5000000000 : ℝ), (4493493191/10000000000 : ℝ), (4145583817/10000000000 : ℝ)] ![(16652108452313/50000000000000 : ℝ), (17552327555287/50000000000000 : ℝ), (7897781993173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158147447/5000000000 : ℝ)|^2171 ≤ (16652108452313/50000000000000 : ℝ)^1659
        have hw : |(2158147447/5000000000 : ℝ)|=(2158147447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493493191/10000000000 : ℝ)|^2171 ≤ (17552327555287/50000000000000 : ℝ)^1659
        have hw : |(4493493191/10000000000 : ℝ)|=(4493493191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4145583817/10000000000 : ℝ)|^2171 ≤ (7897781993173/25000000000000 : ℝ)^1659
        have hw : |(4145583817/10000000000 : ℝ)|=(4145583817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11241/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14731/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3683/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3683/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (281/2500 : ℝ) ^ (4341/1024 : ℝ) ≤ (473068110585709/5000000000000000000 : ℝ) := by
    have hpowers : (281/2500 : ℝ)^4341 ≤ (473068110585709/5000000000000000000 : ℝ)^1024 := by
      have hnat : (281 : ℕ)^4341*5000000000000000000^1024 ≤ 473068110585709^1024*2500^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2500 473068110585709 5000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2500 : ℝ)) (X := (473068110585709/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3683/25000 : ℝ) ^ (4341/1024 : ℝ) ≤ (29788384910178641/100000000000000000000 : ℝ) := by
    have hpowers : (3683/25000 : ℝ)^4341 ≤ (29788384910178641/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3683 : ℕ)^4341*100000000000000000000^1024 ≤ 29788384910178641^1024*25000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3683 25000 29788384910178641 100000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3683/25000 : ℝ)) (X := (29788384910178641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500473068110585709/2500000000000000000 : ℝ) ≤ (10000446336537921/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (2500473068110585709/2500000000000000000 : ℝ)^1024 ≤ (10000446336537921/10000000000000000 : ℝ)^4341 := by
      have hnat : (2500473068110585709 : ℕ)^1024*10000000000000000^4341 ≤ 10000446336537921^4341*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500473068110585709 2500000000000000000 10000446336537921 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000446336537921/10000000000000000 : ℝ)) (X := (2500473068110585709/2500000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039249747121892821/100000000000000000000 : ℝ) ≤ (5000462862421893/5000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (100039249747121892821/100000000000000000000 : ℝ)^1024 ≤ (5000462862421893/5000000000000000 : ℝ)^4341 := by
      have hnat : (100039249747121892821 : ℕ)^1024*5000000000000000^4341 ≤ 5000462862421893^4341*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039249747121892821 100000000000000000000 5000462862421893 5000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000462862421893/5000000000000000 : ℝ)) (X := (100039249747121892821/100000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029788384910178641/50000000000000000000 : ℝ) ≤ (10001405113149651/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (50029788384910178641/50000000000000000000 : ℝ)^1024 ≤ (10001405113149651/10000000000000000 : ℝ)^4341 := by
      have hnat : (50029788384910178641 : ℕ)^1024*10000000000000000^4341 ≤ 10001405113149651^4341*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029788384910178641 50000000000000000000 10001405113149651 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001405113149651/10000000000000000 : ℝ)) (X := (50029788384910178641/50000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(473068110585709/5000000000000000000 : ℝ) ≤ ((2909231829839547911/2910000000000000000 : ℝ)+2*(31959220391/23280000000000 : ℝ)*(281/2500 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (2909231829839547911/2910000000000000000 : ℝ)+2*(31959220391/23280000000000 : ℝ)*(281/2500 : ℝ)=(10000446336537921/10000000000000000 : ℝ) by norm_num, show 1+2*(473068110585709/5000000000000000000 : ℝ)=(2500473068110585709/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29788384910178641/100000000000000000000 : ℝ)+(473068110585709/5000000000000000000 : ℝ) ≤ ((2909231829839547911/2910000000000000000 : ℝ)+(31959220391/23280000000000 : ℝ)*((3683/25000 : ℝ)+(281/2500 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (2909231829839547911/2910000000000000000 : ℝ)+(31959220391/23280000000000 : ℝ)*((3683/25000 : ℝ)+(281/2500 : ℝ))=(5000462862421893/5000000000000000 : ℝ) by norm_num, show 1+(29788384910178641/100000000000000000000 : ℝ)+(473068110585709/5000000000000000000 : ℝ)=(100039249747121892821/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29788384910178641/100000000000000000000 : ℝ) ≤ ((2909231829839547911/2910000000000000000 : ℝ)+2*(31959220391/23280000000000 : ℝ)*(3683/25000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (2909231829839547911/2910000000000000000 : ℝ)+2*(31959220391/23280000000000 : ℝ)*(3683/25000 : ℝ)=(10001405113149651/10000000000000000 : ℝ) by norm_num, show 1+2*(29788384910178641/100000000000000000000 : ℝ)=(50029788384910178641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2909231829839547911/2910000000000000000 : ℝ)*(X 1 0+X 2 0)+(31959220391/23280000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (2909231829839547911/2910000000000000000 : ℝ)) (alpha := (31959220391/23280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2909231829839547911/2910000000000000000 : ℝ)*(X 0 1+X 2 1)+(31959220391/23280000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (2909231829839547911/2910000000000000000 : ℝ)) (alpha := (31959220391/23280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2909231829839547911/2910000000000000000 : ℝ)*(X 0 2+X 1 2)+(31959220391/23280000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (3683/25000 : ℝ)) (c := (2909231829839547911/2910000000000000000 : ℝ)) (alpha := (31959220391/23280000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-125619591/625000000 : ℝ)*X 0 0+(1352652457/2500000000 : ℝ)*X 0 1+(5245788607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348262827/10000000000 : ℝ)*X 1 0+(-1046930219/5000000000 : ℝ)*X 1 1+(524578853/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674131661/5000000000 : ℝ)*X 2 0+(655723537/1250000000 : ℝ)*X 2 1+(-261732511/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158134903/5000000000 : ℝ)*X 0 0+(4144319167/10000000000 : ℝ)*X 0 1+(4494751441/10000000000 : ℝ)*X 0 2+(2158134903/5000000000 : ℝ)*X 1 0+(4144319167/10000000000 : ℝ)*X 1 1+(4494751441/10000000000 : ℝ)*X 1 2+(2158134903/5000000000 : ℝ)*X 2 0+(4144319167/10000000000 : ℝ)*X 2 1+(4494751441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2009925359/10000000000 : ℝ)*X 0 0+(327898759/625000000 : ℝ)*X 0 1+(5410015123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663202501/1250000000 : ℝ)*X 1 0+(-1929633457/10000000000 : ℝ)*X 1 1+(5410014767/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652809959/5000000000 : ℝ)*X 2 0+(2705007487/5000000000 : ℝ)*X 2 1+(-964816647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158147447/5000000000 : ℝ)*X 0 0+(4493493191/10000000000 : ℝ)*X 0 1+(4145583817/10000000000 : ℝ)*X 0 2+(2158147447/5000000000 : ℝ)*X 1 0+(4493493191/10000000000 : ℝ)*X 1 1+(4145583817/10000000000 : ℝ)*X 1 2+(2158147447/5000000000 : ℝ)*X 2 0+(4493493191/10000000000 : ℝ)*X 2 1+(4145583817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (45357366874513620562758931/9700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7861757/10000000000000 : ℝ)*(base19) + (2280193/400000000000 : ℝ)*(base23) + (10390843/12500000000000 : ℝ)*(lower2) + (1519667/2000000000000 : ℝ)*(upper5) + (892081080684821/20000000000000 : ℝ)*(major0) + (892081080684821/20000000000000 : ℝ)*(major1) + (892081080684821/20000000000000 : ℝ)*(major2) + (3033590126743899/50000000000000 : ℝ)*(sp0) + (1516794901517469/25000000000000 : ℝ)*(sp1) + (3033594907680183/50000000000000 : ℝ)*(sp2) + (142680922053923/5000000000000 : ℝ)*(sp3) + (10131920819/100000000000000 : ℝ)*(sp4) + (10700721171/100000000000000 : ℝ)*(sp5) + (1824493887/100000000000000 : ℝ)*(sp7) + (2853620265572347/100000000000000 : ℝ)*(f.failure) + (6067190385408617/100000000000000 : ℝ)*(f.sum) + (5299274312099/1164000000000000000000000000 : ℝ)*base65 + (40326895241022023/19400000000000000000000000000000 : ℝ)*base68 + (122834857494022023/19400000000000000000000000000000 : ℝ)*base70 + (134809117476422023/19400000000000000000000000000000 : ℝ)*base72 + (2415193390873/1164000000000000000000000000 : ℝ)*base74 + (277421648985622023/19400000000000000000000000000000 : ℝ)*base76 + (31483666102777977/19400000000000000000000000000000 : ℝ)*base77 + (105825339432577977/19400000000000000000000000000000 : ℝ)*base79 + (422018279771/1164000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (50866647/10000000000000000000000 : ℝ)*base89 + (50866647/10000000000000000000000 : ℝ)*base91 + (50866647/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (368387694473104744411254959/48500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106291031/5000000000000 : ℝ)*(base19) + (2083478211/100000000000000 : ℝ)*(base23) + (359553123/50000000000000 : ℝ)*(lower1) + (322723/3125000000000 : ℝ)*(upper3) + (4000239/10000000000000 : ℝ)*(lower4) + (305312167/100000000000000 : ℝ)*(upper5) + (4492707453928169/100000000000000 : ℝ)*(major0) + (4492707453928169/100000000000000 : ℝ)*(major1) + (4492707453928169/100000000000000 : ℝ)*(major2) + (1751179693/100000000000000 : ℝ)*(sp1) + (1527782150639763/25000000000000 : ℝ)*(sp4) + (305556236277937/5000000000000 : ℝ)*(sp5) + (3055563259540421/50000000000000 : ℝ)*(sp6) + (2874286052109861/100000000000000 : ℝ)*(sp7) + (2874286052109861/100000000000000 : ℝ)*(f.failure) + (1527782150639763/25000000000000 : ℝ)*(f.sum) + (437650036549/232800000000000000000000000 : ℝ)*base66 + (493958861179626653/97000000000000000000000000000000 : ℝ)*base67 + (29001399538373347/97000000000000000000000000000000 : ℝ)*base70 + (103507494057626653/97000000000000000000000000000000 : ℝ)*base71 + (3851214252211/1164000000000000000000000000 : ℝ)*base73 + (554129472516373347/97000000000000000000000000000000 : ℝ)*base76 + (573064491667373347/97000000000000000000000000000000 : ℝ)*base78 + (857858806960373347/97000000000000000000000000000000 : ℝ)*base80 + (1507794200717/1164000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (15549239/10000000000000000000000 : ℝ)*base90 + (15549239/10000000000000000000000 : ℝ)*base92 + (15549239/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1382_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3683/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1382_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1382_box_0 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1845768609/10000000000 : ℝ)*x 0 + (2694129263/5000000000 : ℝ)*x 1 + (5388258491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1845768609/10000000000 : ℝ)^2171 ≤ (2191467995409/20000000000000 : ℝ)^1659 := by
    have hnat : (1845768609 : ℕ)^2171*20000000000000^1659 ≤ 2191467995409^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1845768609 10000000000 2191467995409 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694129263/5000000000 : ℝ)^2171 ≤ (44521330190417/100000000000000 : ℝ)^1659 := by
    have hnat : (2694129263 : ℕ)^2171*100000000000000^1659 ≤ 44521330190417^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694129263 5000000000 44521330190417 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388258491/10000000000 : ℝ)^2171 ≤ (44521329811973/100000000000000 : ℝ)^1659 := by
    have hnat : (5388258491 : ℕ)^2171*100000000000000^1659 ≤ 44521329811973^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388258491 10000000000 44521329811973 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1845768609/10000000000 : ℝ), (2694129263/5000000000 : ℝ), (5388258491/10000000000 : ℝ)] ![(2191467995409/20000000000000 : ℝ), (44521330190417/100000000000000 : ℝ), (44521329811973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1845768609/10000000000 : ℝ)|^2171 ≤ (2191467995409/20000000000000 : ℝ)^1659
        have hw : |(-1845768609/10000000000 : ℝ)|=(1845768609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694129263/5000000000 : ℝ)|^2171 ≤ (44521330190417/100000000000000 : ℝ)^1659
        have hw : |(2694129263/5000000000 : ℝ)|=(2694129263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388258491/10000000000 : ℝ)|^2171 ≤ (44521329811973/100000000000000 : ℝ)^1659
        have hw : |(5388258491/10000000000 : ℝ)|=(5388258491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_1 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057130117/2000000000 : ℝ)*x 0 + (-993266691/5000000000 : ℝ)*x 1 + (5388258517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057130117/2000000000 : ℝ)^2171 ≤ (43415138479507/100000000000000 : ℝ)^1659 := by
    have hnat : (1057130117 : ℕ)^2171*100000000000000^1659 ≤ 43415138479507^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057130117 2000000000 43415138479507 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993266691/5000000000 : ℝ)^2171 ≤ (1206353141173/10000000000000 : ℝ)^1659 := by
    have hnat : (993266691 : ℕ)^2171*10000000000000^1659 ≤ 1206353141173^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993266691 5000000000 1206353141173 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5388258517/10000000000 : ℝ)^2171 ≤ (44521330093103/100000000000000 : ℝ)^1659 := by
    have hnat : (5388258517 : ℕ)^2171*100000000000000^1659 ≤ 44521330093103^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388258517 10000000000 44521330093103 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057130117/2000000000 : ℝ), (-993266691/5000000000 : ℝ), (5388258517/10000000000 : ℝ)] ![(43415138479507/100000000000000 : ℝ), (1206353141173/10000000000000 : ℝ), (44521330093103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057130117/2000000000 : ℝ)|^2171 ≤ (43415138479507/100000000000000 : ℝ)^1659
        have hw : |(1057130117/2000000000 : ℝ)|=(1057130117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-993266691/5000000000 : ℝ)|^2171 ≤ (1206353141173/10000000000000 : ℝ)^1659
        have hw : |(-993266691/5000000000 : ℝ)|=(993266691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5388258517/10000000000 : ℝ)|^2171 ≤ (44521330093103/100000000000000 : ℝ)^1659
        have hw : |(5388258517/10000000000 : ℝ)|=(5388258517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_2 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2642825311/5000000000 : ℝ)*x 0 + (2694129241/5000000000 : ℝ)*x 1 + (-99326669/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642825311/5000000000 : ℝ)^2171 ≤ (43415138877209/100000000000000 : ℝ)^1659 := by
    have hnat : (2642825311 : ℕ)^2171*100000000000000^1659 ≤ 43415138877209^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642825311 5000000000 43415138877209 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694129241/5000000000 : ℝ)^2171 ≤ (44521329714659/100000000000000 : ℝ)^1659 := by
    have hnat : (2694129241 : ℕ)^2171*100000000000000^1659 ≤ 44521329714659^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694129241 5000000000 44521329714659 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99326669/500000000 : ℝ)^2171 ≤ (12063531395837/100000000000000 : ℝ)^1659 := by
    have hnat : (99326669 : ℕ)^2171*100000000000000^1659 ≤ 12063531395837^1659*500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99326669 500000000 12063531395837 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642825311/5000000000 : ℝ), (2694129241/5000000000 : ℝ), (-99326669/500000000 : ℝ)] ![(43415138877209/100000000000000 : ℝ), (44521329714659/100000000000000 : ℝ), (12063531395837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642825311/5000000000 : ℝ)|^2171 ≤ (43415138877209/100000000000000 : ℝ)^1659
        have hw : |(2642825311/5000000000 : ℝ)|=(2642825311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694129241/5000000000 : ℝ)|^2171 ≤ (44521329714659/100000000000000 : ℝ)^1659
        have hw : |(2694129241/5000000000 : ℝ)|=(2694129241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99326669/500000000 : ℝ)|^2171 ≤ (12063531395837/100000000000000 : ℝ)^1659
        have hw : |(-99326669/500000000 : ℝ)|=(99326669/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_3 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (223177563/500000000 : ℝ)*x 0 + (2123216201/5000000000 : ℝ)*x 1 + (4246432337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223177563/500000000 : ℝ)^2171 ≤ (17399431458761/50000000000000 : ℝ)^1659 := by
    have hnat : (223177563 : ℕ)^2171*50000000000000^1659 ≤ 17399431458761^1659*500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223177563 500000000 17399431458761 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123216201/5000000000 : ℝ)^2171 ≤ (16300284430899/50000000000000 : ℝ)^1659 := by
    have hnat : (2123216201 : ℕ)^2171*50000000000000^1659 ≤ 16300284430899^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123216201 5000000000 16300284430899 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246432337/10000000000 : ℝ)^2171 ≤ (4075071026097/12500000000000 : ℝ)^1659 := by
    have hnat : (4246432337 : ℕ)^2171*12500000000000^1659 ≤ 4075071026097^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246432337 10000000000 4075071026097 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223177563/500000000 : ℝ), (2123216201/5000000000 : ℝ), (4246432337/10000000000 : ℝ)] ![(17399431458761/50000000000000 : ℝ), (16300284430899/50000000000000 : ℝ), (4075071026097/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223177563/500000000 : ℝ)|^2171 ≤ (17399431458761/50000000000000 : ℝ)^1659
        have hw : |(223177563/500000000 : ℝ)|=(223177563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123216201/5000000000 : ℝ)|^2171 ≤ (16300284430899/50000000000000 : ℝ)^1659
        have hw : |(2123216201/5000000000 : ℝ)|=(2123216201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246432337/10000000000 : ℝ)|^2171 ≤ (4075071026097/12500000000000 : ℝ)^1659
        have hw : |(4246432337/10000000000 : ℝ)|=(4246432337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_4 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-87072089/400000000 : ℝ)*x 0 + (5265743021/10000000000 : ℝ)*x 1 + (2632871659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87072089/400000000 : ℝ)^2171 ≤ (424919749927/3125000000000 : ℝ)^1659 := by
    have hnat : (87072089 : ℕ)^2171*3125000000000^1659 ≤ 424919749927^1659*400000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87072089 400000000 424919749927 3125000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265743021/10000000000 : ℝ)^2171 ≤ (43201282400051/100000000000000 : ℝ)^1659 := by
    have hnat : (5265743021 : ℕ)^2171*100000000000000^1659 ≤ 43201282400051^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265743021 10000000000 43201282400051 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632871659/5000000000 : ℝ)^2171 ≤ (43201285588701/100000000000000 : ℝ)^1659 := by
    have hnat : (2632871659 : ℕ)^2171*100000000000000^1659 ≤ 43201285588701^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632871659 5000000000 43201285588701 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87072089/400000000 : ℝ), (5265743021/10000000000 : ℝ), (2632871659/5000000000 : ℝ)] ![(424919749927/3125000000000 : ℝ), (43201282400051/100000000000000 : ℝ), (43201285588701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87072089/400000000 : ℝ)|^2171 ≤ (424919749927/3125000000000 : ℝ)^1659
        have hw : |(-87072089/400000000 : ℝ)|=(87072089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265743021/10000000000 : ℝ)|^2171 ≤ (43201282400051/100000000000000 : ℝ)^1659
        have hw : |(5265743021/10000000000 : ℝ)|=(5265743021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632871659/5000000000 : ℝ)|^2171 ≤ (43201285588701/100000000000000 : ℝ)^1659
        have hw : |(2632871659/5000000000 : ℝ)|=(2632871659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_5 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5371558763/10000000000 : ℝ)*x 0 + (-1017983339/5000000000 : ℝ)*x 1 + (2632871627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371558763/10000000000 : ℝ)^2171 ≤ (5542605937719/12500000000000 : ℝ)^1659 := by
    have hnat : (5371558763 : ℕ)^2171*12500000000000^1659 ≤ 5542605937719^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371558763 10000000000 5542605937719 12500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017983339/5000000000 : ℝ)^2171 ≤ (12457867581001/100000000000000 : ℝ)^1659 := by
    have hnat : (1017983339 : ℕ)^2171*100000000000000^1659 ≤ 12457867581001^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017983339 5000000000 12457867581001 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632871627/5000000000 : ℝ)^2171 ≤ (2700080306349/6250000000000 : ℝ)^1659 := by
    have hnat : (2632871627 : ℕ)^2171*6250000000000^1659 ≤ 2700080306349^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632871627 5000000000 2700080306349 6250000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371558763/10000000000 : ℝ), (-1017983339/5000000000 : ℝ), (2632871627/5000000000 : ℝ)] ![(5542605937719/12500000000000 : ℝ), (12457867581001/100000000000000 : ℝ), (2700080306349/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371558763/10000000000 : ℝ)|^2171 ≤ (5542605937719/12500000000000 : ℝ)^1659
        have hw : |(5371558763/10000000000 : ℝ)|=(5371558763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017983339/5000000000 : ℝ)|^2171 ≤ (12457867581001/100000000000000 : ℝ)^1659
        have hw : |(-1017983339/5000000000 : ℝ)|=(1017983339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632871627/5000000000 : ℝ)|^2171 ≤ (2700080306349/6250000000000 : ℝ)^1659
        have hw : |(2632871627/5000000000 : ℝ)|=(2632871627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_6 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5371558399/10000000000 : ℝ)*x 0 + (1316435771/2500000000 : ℝ)*x 1 + (-2035967397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371558399/10000000000 : ℝ)^2171 ≤ (44340843569707/100000000000000 : ℝ)^1659 := by
    have hnat : (5371558399 : ℕ)^2171*100000000000000^1659 ≤ 44340843569707^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371558399 10000000000 44340843569707 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316435771/2500000000 : ℝ)^2171 ≤ (43201283076431/100000000000000 : ℝ)^1659 := by
    have hnat : (1316435771 : ℕ)^2171*100000000000000^1659 ≤ 43201283076431^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316435771 2500000000 43201283076431 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2035967397/10000000000 : ℝ)^2171 ≤ (2491574667651/20000000000000 : ℝ)^1659 := by
    have hnat : (2035967397 : ℕ)^2171*20000000000000^1659 ≤ 2491574667651^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035967397 10000000000 2491574667651 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371558399/10000000000 : ℝ), (1316435771/2500000000 : ℝ), (-2035967397/10000000000 : ℝ)] ![(44340843569707/100000000000000 : ℝ), (43201283076431/100000000000000 : ℝ), (2491574667651/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371558399/10000000000 : ℝ)|^2171 ≤ (44340843569707/100000000000000 : ℝ)^1659
        have hw : |(5371558399/10000000000 : ℝ)|=(5371558399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316435771/2500000000 : ℝ)|^2171 ≤ (43201283076431/100000000000000 : ℝ)^1659
        have hw : |(1316435771/2500000000 : ℝ)|=(1316435771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2035967397/10000000000 : ℝ)|^2171 ≤ (2491574667651/20000000000000 : ℝ)^1659
        have hw : |(-2035967397/10000000000 : ℝ)|=(2035967397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_7 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2084002339/5000000000 : ℝ)*x 0 + (4394153147/10000000000 : ℝ)*x 1 + (4394153569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084002339/5000000000 : ℝ)^2171 ≤ (15907450310489/50000000000000 : ℝ)^1659 := by
    have hnat : (2084002339 : ℕ)^2171*50000000000000^1659 ≤ 15907450310489^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084002339 5000000000 15907450310489 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394153147/10000000000 : ℝ)^2171 ≤ (34092547540817/100000000000000 : ℝ)^1659 := by
    have hnat : (4394153147 : ℕ)^2171*100000000000000^1659 ≤ 34092547540817^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394153147 10000000000 34092547540817 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4394153569/10000000000 : ℝ)^2171 ≤ (6818510365083/20000000000000 : ℝ)^1659 := by
    have hnat : (4394153569 : ℕ)^2171*20000000000000^1659 ≤ 6818510365083^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394153569 10000000000 6818510365083 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084002339/5000000000 : ℝ), (4394153147/10000000000 : ℝ), (4394153569/10000000000 : ℝ)] ![(15907450310489/50000000000000 : ℝ), (34092547540817/100000000000000 : ℝ), (6818510365083/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084002339/5000000000 : ℝ)|^2171 ≤ (15907450310489/50000000000000 : ℝ)^1659
        have hw : |(2084002339/5000000000 : ℝ)|=(2084002339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394153147/10000000000 : ℝ)|^2171 ≤ (34092547540817/100000000000000 : ℝ)^1659
        have hw : |(4394153147/10000000000 : ℝ)|=(4394153147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4394153569/10000000000 : ℝ)|^2171 ≤ (6818510365083/20000000000000 : ℝ)^1659
        have hw : |(4394153569/10000000000 : ℝ)|=(4394153569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_8 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-526796393/2500000000 : ℝ)*x 0 + (5181215079/10000000000 : ℝ)*x 1 + (5402259321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526796393/2500000000 : ℝ)^2171 ≤ (325779822469/2500000000000 : ℝ)^1659 := by
    have hnat : (526796393 : ℕ)^2171*2500000000000^1659 ≤ 325779822469^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526796393 2500000000 325779822469 2500000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181215079/10000000000 : ℝ)^2171 ≤ (21148015097469/50000000000000 : ℝ)^1659 := by
    have hnat : (5181215079 : ℕ)^2171*50000000000000^1659 ≤ 21148015097469^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181215079 10000000000 21148015097469 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5402259321/10000000000 : ℝ)^2171 ≤ (11168194224411/25000000000000 : ℝ)^1659 := by
    have hnat : (5402259321 : ℕ)^2171*25000000000000^1659 ≤ 11168194224411^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402259321 10000000000 11168194224411 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-526796393/2500000000 : ℝ), (5181215079/10000000000 : ℝ), (5402259321/10000000000 : ℝ)] ![(325779822469/2500000000000 : ℝ), (21148015097469/50000000000000 : ℝ), (11168194224411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-526796393/2500000000 : ℝ)|^2171 ≤ (325779822469/2500000000000 : ℝ)^1659
        have hw : |(-526796393/2500000000 : ℝ)|=(526796393/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181215079/10000000000 : ℝ)|^2171 ≤ (21148015097469/50000000000000 : ℝ)^1659
        have hw : |(5181215079/10000000000 : ℝ)|=(5181215079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5402259321/10000000000 : ℝ)|^2171 ≤ (11168194224411/25000000000000 : ℝ)^1659
        have hw : |(5402259321/10000000000 : ℝ)|=(5402259321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_9 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (659478511/1250000000 : ℝ)*x 0 + (-1980754229/10000000000 : ℝ)*x 1 + (2701129991/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659478511/1250000000 : ℝ)^2171 ≤ (43309589637329/100000000000000 : ℝ)^1659 := by
    have hnat : (659478511 : ℕ)^2171*100000000000000^1659 ≤ 43309589637329^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659478511 1250000000 43309589637329 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1980754229/10000000000 : ℝ)^2171 ≤ (3004406573997/25000000000000 : ℝ)^1659 := by
    have hnat : (1980754229 : ℕ)^2171*25000000000000^1659 ≤ 3004406573997^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980754229 10000000000 3004406573997 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2701129991/5000000000 : ℝ)^2171 ≤ (44672784050549/100000000000000 : ℝ)^1659 := by
    have hnat : (2701129991 : ℕ)^2171*100000000000000^1659 ≤ 44672784050549^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701129991 5000000000 44672784050549 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659478511/1250000000 : ℝ), (-1980754229/10000000000 : ℝ), (2701129991/5000000000 : ℝ)] ![(43309589637329/100000000000000 : ℝ), (3004406573997/25000000000000 : ℝ), (44672784050549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659478511/1250000000 : ℝ)|^2171 ≤ (43309589637329/100000000000000 : ℝ)^1659
        have hw : |(659478511/1250000000 : ℝ)|=(659478511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1980754229/10000000000 : ℝ)|^2171 ≤ (3004406573997/25000000000000 : ℝ)^1659
        have hw : |(-1980754229/10000000000 : ℝ)|=(1980754229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2701129991/5000000000 : ℝ)|^2171 ≤ (44672784050549/100000000000000 : ℝ)^1659
        have hw : |(2701129991/5000000000 : ℝ)|=(2701129991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_10 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (82434831/156250000 : ℝ)*x 0 + (5402258671/10000000000 : ℝ)*x 1 + (-990377267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82434831/156250000 : ℝ)^2171 ≤ (43309601411151/100000000000000 : ℝ)^1659 := by
    have hnat : (82434831 : ℕ)^2171*100000000000000^1659 ≤ 43309601411151^1659*156250000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82434831 156250000 43309601411151 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402258671/10000000000 : ℝ)^2171 ≤ (1786910794551/4000000000000 : ℝ)^1659 := by
    have hnat : (5402258671 : ℕ)^2171*4000000000000^1659 ≤ 1786910794551^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402258671 10000000000 1786910794551 4000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990377267/5000000000 : ℝ)^2171 ≤ (6008814358791/50000000000000 : ℝ)^1659 := by
    have hnat : (990377267 : ℕ)^2171*50000000000000^1659 ≤ 6008814358791^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990377267 5000000000 6008814358791 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82434831/156250000 : ℝ), (5402258671/10000000000 : ℝ), (-990377267/5000000000 : ℝ)] ![(43309601411151/100000000000000 : ℝ), (1786910794551/4000000000000 : ℝ), (6008814358791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82434831/156250000 : ℝ)|^2171 ≤ (43309601411151/100000000000000 : ℝ)^1659
        have hw : |(82434831/156250000 : ℝ)|=(82434831/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402258671/10000000000 : ℝ)|^2171 ≤ (1786910794551/4000000000000 : ℝ)^1659
        have hw : |(5402258671/10000000000 : ℝ)|=(5402258671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-990377267/5000000000 : ℝ)|^2171 ≤ (6008814358791/50000000000000 : ℝ)^1659
        have hw : |(-990377267/5000000000 : ℝ)|=(990377267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_11 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4496767623/10000000000 : ℝ)*x 0 + (4229537777/10000000000 : ℝ)*x 1 + (4229536029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4496767623/10000000000 : ℝ)^2171 ≤ (7027626920519/20000000000000 : ℝ)^1659 := by
    have hnat : (4496767623 : ℕ)^2171*20000000000000^1659 ≤ 7027626920519^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496767623 10000000000 7027626920519 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229537777/10000000000 : ℝ)^2171 ≤ (32430941462181/100000000000000 : ℝ)^1659 := by
    have hnat : (4229537777 : ℕ)^2171*100000000000000^1659 ≤ 32430941462181^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229537777 10000000000 32430941462181 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229536029/10000000000 : ℝ)^2171 ≤ (8107730980627/25000000000000 : ℝ)^1659 := by
    have hnat : (4229536029 : ℕ)^2171*25000000000000^1659 ≤ 8107730980627^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229536029 10000000000 8107730980627 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4496767623/10000000000 : ℝ), (4229537777/10000000000 : ℝ), (4229536029/10000000000 : ℝ)] ![(7027626920519/20000000000000 : ℝ), (32430941462181/100000000000000 : ℝ), (8107730980627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4496767623/10000000000 : ℝ)|^2171 ≤ (7027626920519/20000000000000 : ℝ)^1659
        have hw : |(4496767623/10000000000 : ℝ)|=(4496767623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229537777/10000000000 : ℝ)|^2171 ≤ (32430941462181/100000000000000 : ℝ)^1659
        have hw : |(4229537777/10000000000 : ℝ)|=(4229537777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229536029/10000000000 : ℝ)|^2171 ≤ (8107730980627/25000000000000 : ℝ)^1659
        have hw : |(4229536029/10000000000 : ℝ)|=(4229536029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_12 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-478911931/2500000000 : ℝ)*x 0 + (5470668591/10000000000 : ℝ)*x 1 + (2627321803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478911931/2500000000 : ℝ)^2171 ≤ (718959077587/6250000000000 : ℝ)^1659 := by
    have hnat : (478911931 : ℕ)^2171*6250000000000^1659 ≤ 718959077587^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478911931 2500000000 718959077587 6250000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470668591/10000000000 : ℝ)^2171 ≤ (2838406191371/6250000000000 : ℝ)^1659 := by
    have hnat : (5470668591 : ℕ)^2171*6250000000000^1659 ≤ 2838406191371^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470668591 10000000000 2838406191371 6250000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627321803/5000000000 : ℝ)^2171 ≤ (43082155688439/100000000000000 : ℝ)^1659 := by
    have hnat : (2627321803 : ℕ)^2171*100000000000000^1659 ≤ 43082155688439^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627321803 5000000000 43082155688439 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-478911931/2500000000 : ℝ), (5470668591/10000000000 : ℝ), (2627321803/5000000000 : ℝ)] ![(718959077587/6250000000000 : ℝ), (2838406191371/6250000000000 : ℝ), (43082155688439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-478911931/2500000000 : ℝ)|^2171 ≤ (718959077587/6250000000000 : ℝ)^1659
        have hw : |(-478911931/2500000000 : ℝ)|=(478911931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470668591/10000000000 : ℝ)|^2171 ≤ (2838406191371/6250000000000 : ℝ)^1659
        have hw : |(5470668591/10000000000 : ℝ)|=(5470668591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627321803/5000000000 : ℝ)|^2171 ≤ (43082155688439/100000000000000 : ℝ)^1659
        have hw : |(2627321803/5000000000 : ℝ)|=(2627321803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_13 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5379339647/10000000000 : ℝ)*x 0 + (-255042863/1250000000 : ℝ)*x 1 + (328415257/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379339647/10000000000 : ℝ)^2171 ≤ (22212458946477/50000000000000 : ℝ)^1659 := by
    have hnat : (5379339647 : ℕ)^2171*50000000000000^1659 ≤ 22212458946477^1659*10000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379339647 10000000000 22212458946477 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (255042863/1250000000 : ℝ)^2171 ≤ (12492920983267/100000000000000 : ℝ)^1659 := by
    have hnat : (255042863 : ℕ)^2171*100000000000000^1659 ≤ 12492920983267^1659*1250000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255042863 1250000000 12492920983267 100000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328415257/625000000 : ℝ)^2171 ≤ (21541080558709/50000000000000 : ℝ)^1659 := by
    have hnat : (328415257 : ℕ)^2171*50000000000000^1659 ≤ 21541080558709^1659*625000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328415257 625000000 21541080558709 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379339647/10000000000 : ℝ), (-255042863/1250000000 : ℝ), (328415257/625000000 : ℝ)] ![(22212458946477/50000000000000 : ℝ), (12492920983267/100000000000000 : ℝ), (21541080558709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379339647/10000000000 : ℝ)|^2171 ≤ (22212458946477/50000000000000 : ℝ)^1659
        have hw : |(5379339647/10000000000 : ℝ)|=(5379339647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-255042863/1250000000 : ℝ)|^2171 ≤ (12492920983267/100000000000000 : ℝ)^1659
        have hw : |(-255042863/1250000000 : ℝ)|=(255042863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328415257/625000000 : ℝ)|^2171 ≤ (21541080558709/50000000000000 : ℝ)^1659
        have hw : |(328415257/625000000 : ℝ)|=(328415257/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_14 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1344834963/2500000000 : ℝ)*x 0 + (1050928697/2000000000 : ℝ)*x 1 + (-1020171733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344834963/2500000000 : ℝ)^2171 ≤ (2221246005421/5000000000000 : ℝ)^1659 := by
    have hnat : (1344834963 : ℕ)^2171*5000000000000^1659 ≤ 2221246005421^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344834963 2500000000 2221246005421 5000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050928697/2000000000 : ℝ)^2171 ≤ (8616430878041/20000000000000 : ℝ)^1659 := by
    have hnat : (1050928697 : ℕ)^2171*20000000000000^1659 ≤ 8616430878041^1659*2000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050928697 2000000000 8616430878041 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020171733/5000000000 : ℝ)^2171 ≤ (3123231371589/25000000000000 : ℝ)^1659 := by
    have hnat : (1020171733 : ℕ)^2171*25000000000000^1659 ≤ 3123231371589^1659*5000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020171733 5000000000 3123231371589 25000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344834963/2500000000 : ℝ), (1050928697/2000000000 : ℝ), (-1020171733/5000000000 : ℝ)] ![(2221246005421/5000000000000 : ℝ), (8616430878041/20000000000000 : ℝ), (3123231371589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344834963/2500000000 : ℝ)|^2171 ≤ (2221246005421/5000000000000 : ℝ)^1659
        have hw : |(1344834963/2500000000 : ℝ)|=(1344834963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050928697/2000000000 : ℝ)|^2171 ≤ (8616430878041/20000000000000 : ℝ)^1659
        have hw : |(1050928697/2000000000 : ℝ)|=(1050928697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020171733/5000000000 : ℝ)|^2171 ≤ (3123231371589/25000000000000 : ℝ)^1659
        have hw : |(-1020171733/5000000000 : ℝ)|=(1020171733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1382_box_15 (p : ℝ) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1035195699/2500000000 : ℝ)*x 0 + (440752497/1000000000 : ℝ)*x 1 + (3526019/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035195699/2500000000 : ℝ)^2171 ≤ (15771629790479/50000000000000 : ℝ)^1659 := by
    have hnat : (1035195699 : ℕ)^2171*50000000000000^1659 ≤ 15771629790479^1659*2500000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035195699 2500000000 15771629790479 50000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440752497/1000000000 : ℝ)^2171 ≤ (3422837640451/10000000000000 : ℝ)^1659 := by
    have hnat : (440752497 : ℕ)^2171*10000000000000^1659 ≤ 3422837640451^1659*1000000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440752497 1000000000 3422837640451 10000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3526019/8000000 : ℝ)^2171 ≤ (6845672801227/20000000000000 : ℝ)^1659 := by
    have hnat : (3526019 : ℕ)^2171*20000000000000^1659 ≤ 6845672801227^1659*8000000^2171 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3526019 8000000 6845672801227 20000000000000 2171 1659 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2171/512 : ℝ)) 2171 1659 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035195699/2500000000 : ℝ), (440752497/1000000000 : ℝ), (3526019/8000000 : ℝ)] ![(15771629790479/50000000000000 : ℝ), (3422837640451/10000000000000 : ℝ), (6845672801227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035195699/2500000000 : ℝ)|^2171 ≤ (15771629790479/50000000000000 : ℝ)^1659
        have hw : |(1035195699/2500000000 : ℝ)|=(1035195699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(440752497/1000000000 : ℝ)|^2171 ≤ (3422837640451/10000000000000 : ℝ)^1659
        have hw : |(440752497/1000000000 : ℝ)|=(440752497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3526019/8000000 : ℝ)|^2171 ≤ (6845672801227/20000000000000 : ℝ)^1659
        have hw : |(3526019/8000000 : ℝ)|=(3526019/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1382_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62873/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2951/5000 : ℝ) ∧ (16037/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84507/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11241/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14731/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11241/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14731/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11241/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11241/100000 : ℝ) ^ (4341/1024 : ℝ) ≤ (4732465577991839/50000000000000000000 : ℝ) := by
    have hpowers : (11241/100000 : ℝ)^4341 ≤ (4732465577991839/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11241 : ℕ)^4341*50000000000000000000^1024 ≤ 4732465577991839^1024*100000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11241 100000 4732465577991839 50000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11241/100000 : ℝ)) (X := (4732465577991839/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14731/100000 : ℝ) ^ (4341/1024 : ℝ) ≤ (5955962798477173/20000000000000000000 : ℝ) := by
    have hpowers : (14731/100000 : ℝ)^4341 ≤ (5955962798477173/20000000000000000000 : ℝ)^1024 := by
      have hnat : (14731 : ℕ)^4341*20000000000000000000^1024 ≤ 5955962798477173^1024*100000^4341 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14731 100000 5955962798477173 20000000000000000000 4341 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14731/100000 : ℝ)) (X := (5955962798477173/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004732465577991839/25000000000000000000 : ℝ) ≤ (2500111626222369/2500000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (25004732465577991839/25000000000000000000 : ℝ)^1024 ≤ (2500111626222369/2500000000000000 : ℝ)^4341 := by
      have hnat : (25004732465577991839 : ℕ)^1024*2500000000000000^4341 ≤ 2500111626222369^4341*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004732465577991839 25000000000000000000 2500111626222369 2500000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111626222369/2500000000000000 : ℝ)) (X := (25004732465577991839/25000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039244745148369543/100000000000000000000 : ℝ) ≤ (10000925606887431/10000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (100039244745148369543/100000000000000000000 : ℝ)^1024 ≤ (10000925606887431/10000000000000000 : ℝ)^4341 := by
      have hnat : (100039244745148369543 : ℕ)^1024*10000000000000000^4341 ≤ 10000925606887431^4341*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039244745148369543 100000000000000000000 10000925606887431 10000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000925606887431/10000000000000000 : ℝ)) (X := (100039244745148369543/100000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005955962798477173/10000000000000000000 : ℝ) ≤ (5000702354442693/5000000000000000 : ℝ) ^ (4341/1024 : ℝ) := by
    have hpowers : (10005955962798477173/10000000000000000000 : ℝ)^1024 ≤ (5000702354442693/5000000000000000 : ℝ)^4341 := by
      have hnat : (10005955962798477173 : ℕ)^1024*5000000000000000^4341 ≤ 5000702354442693^4341*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005955962798477173 10000000000000000000 5000702354442693 5000000000000000 1024 4341 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000702354442693/5000000000000000 : ℝ)) (X := (10005955962798477173/10000000000000000000 : ℝ)) (by norm_num) 4341 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4732465577991839/50000000000000000000 : ℝ) ≤ ((3489078713094624693/3490000000000000000 : ℝ)+2*(95820399591/69800000000000 : ℝ)*(11241/100000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (3489078713094624693/3490000000000000000 : ℝ)+2*(95820399591/69800000000000 : ℝ)*(11241/100000 : ℝ)=(2500111626222369/2500000000000000 : ℝ) by norm_num, show 1+2*(4732465577991839/50000000000000000000 : ℝ)=(25004732465577991839/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5955962798477173/20000000000000000000 : ℝ)+(4732465577991839/50000000000000000000 : ℝ) ≤ ((3489078713094624693/3490000000000000000 : ℝ)+(95820399591/69800000000000 : ℝ)*((14731/100000 : ℝ)+(11241/100000 : ℝ)))^(4341/1024 : ℝ) := by
    rw [show (3489078713094624693/3490000000000000000 : ℝ)+(95820399591/69800000000000 : ℝ)*((14731/100000 : ℝ)+(11241/100000 : ℝ))=(10000925606887431/10000000000000000 : ℝ) by norm_num, show 1+(5955962798477173/20000000000000000000 : ℝ)+(4732465577991839/50000000000000000000 : ℝ)=(100039244745148369543/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5955962798477173/20000000000000000000 : ℝ) ≤ ((3489078713094624693/3490000000000000000 : ℝ)+2*(95820399591/69800000000000 : ℝ)*(14731/100000 : ℝ))^(4341/1024 : ℝ) := by
    rw [show (3489078713094624693/3490000000000000000 : ℝ)+2*(95820399591/69800000000000 : ℝ)*(14731/100000 : ℝ)=(5000702354442693/5000000000000000 : ℝ) by norm_num, show 1+2*(5955962798477173/20000000000000000000 : ℝ)=(10005955962798477173/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3489078713094624693/3490000000000000000 : ℝ)*(X 1 0+X 2 0)+(95820399591/69800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (3489078713094624693/3490000000000000000 : ℝ)) (alpha := (95820399591/69800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3489078713094624693/3490000000000000000 : ℝ)*(X 0 1+X 2 1)+(95820399591/69800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (3489078713094624693/3490000000000000000 : ℝ)) (alpha := (95820399591/69800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3489078713094624693/3490000000000000000 : ℝ)*(X 0 2+X 1 2)+(95820399591/69800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4341/1024 : ℝ)) (lo := (11241/100000 : ℝ)) (hi := (14731/100000 : ℝ)) (c := (3489078713094624693/3490000000000000000 : ℝ)) (alpha := (95820399591/69800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1845768609/10000000000 : ℝ)*X 0 0+(2694129263/5000000000 : ℝ)*X 0 1+(5388258491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1057130117/2000000000 : ℝ)*X 1 0+(-993266691/5000000000 : ℝ)*X 1 1+(5388258517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642825311/5000000000 : ℝ)*X 2 0+(2694129241/5000000000 : ℝ)*X 2 1+(-99326669/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((223177563/500000000 : ℝ)*X 0 0+(2123216201/5000000000 : ℝ)*X 0 1+(4246432337/10000000000 : ℝ)*X 0 2+(223177563/500000000 : ℝ)*X 1 0+(2123216201/5000000000 : ℝ)*X 1 1+(4246432337/10000000000 : ℝ)*X 1 2+(223177563/500000000 : ℝ)*X 2 0+(2123216201/5000000000 : ℝ)*X 2 1+(4246432337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-87072089/400000000 : ℝ)*X 0 0+(5265743021/10000000000 : ℝ)*X 0 1+(2632871659/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371558763/10000000000 : ℝ)*X 1 0+(-1017983339/5000000000 : ℝ)*X 1 1+(2632871627/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371558399/10000000000 : ℝ)*X 2 0+(1316435771/2500000000 : ℝ)*X 2 1+(-2035967397/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2084002339/5000000000 : ℝ)*X 0 0+(4394153147/10000000000 : ℝ)*X 0 1+(4394153569/10000000000 : ℝ)*X 0 2+(2084002339/5000000000 : ℝ)*X 1 0+(4394153147/10000000000 : ℝ)*X 1 1+(4394153569/10000000000 : ℝ)*X 1 2+(2084002339/5000000000 : ℝ)*X 2 0+(4394153147/10000000000 : ℝ)*X 2 1+(4394153569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-526796393/2500000000 : ℝ)*X 0 0+(5181215079/10000000000 : ℝ)*X 0 1+(5402259321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((659478511/1250000000 : ℝ)*X 1 0+(-1980754229/10000000000 : ℝ)*X 1 1+(2701129991/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((82434831/156250000 : ℝ)*X 2 0+(5402258671/10000000000 : ℝ)*X 2 1+(-990377267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4496767623/10000000000 : ℝ)*X 0 0+(4229537777/10000000000 : ℝ)*X 0 1+(4229536029/10000000000 : ℝ)*X 0 2+(4496767623/10000000000 : ℝ)*X 1 0+(4229537777/10000000000 : ℝ)*X 1 1+(4229536029/10000000000 : ℝ)*X 1 2+(4496767623/10000000000 : ℝ)*X 2 0+(4229537777/10000000000 : ℝ)*X 2 1+(4229536029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-478911931/2500000000 : ℝ)*X 0 0+(5470668591/10000000000 : ℝ)*X 0 1+(2627321803/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5379339647/10000000000 : ℝ)*X 1 0+(-255042863/1250000000 : ℝ)*X 1 1+(328415257/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1344834963/2500000000 : ℝ)*X 2 0+(1050928697/2000000000 : ℝ)*X 2 1+(-1020171733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1035195699/2500000000 : ℝ)*X 0 0+(440752497/1000000000 : ℝ)*X 0 1+(3526019/8000000 : ℝ)*X 0 2+(1035195699/2500000000 : ℝ)*X 1 0+(440752497/1000000000 : ℝ)*X 1 1+(3526019/8000000 : ℝ)*X 1 2+(1035195699/2500000000 : ℝ)*X 2 0+(440752497/1000000000 : ℝ)*X 2 1+(3526019/8000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1382_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62873/100000 : ℝ) ≤ (-54854671726619264447441279163339/87250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (262535973/100000000000000 : ℝ)*(upper1) + (184836643/100000000000000 : ℝ)*(upper2) + (268278363/100000000000000 : ℝ)*(lower4) + (224745557/100000000000000 : ℝ)*(upper5) + (1482597092748647/50000000000000 : ℝ)*(major0) + (1482597092748647/50000000000000 : ℝ)*(major1) + (1482597092748647/50000000000000 : ℝ)*(major2) + (8129728849/50000000000000 : ℝ)*(sp2) + (1291843371/12500000000000 : ℝ)*(sp3) + (2027155911379169/50000000000000 : ℝ)*(sp4) + (202704933179951/5000000000000 : ℝ)*(sp5) + (25339347270629/625000000000 : ℝ)*(sp6) + (1897023108131727/100000000000000 : ℝ)*(sp7) + (106579579659/50000000000000 : ℝ)*(sp13) + (237129180359837/12500000000000 : ℝ)*(f.failure) + (2027155911379169/50000000000000 : ℝ)*(f.sum) + (15697286148057/1745000000000000000000000000 : ℝ)*base65 + (1505213536943890371/174500000000000000000000000000000 : ℝ)*base67 + (132393722573890371/174500000000000000000000000000000 : ℝ)*base69 + (966046841613390371/174500000000000000000000000000000 : ℝ)*base71 + (1945613496373/436250000000000000000000000 : ℝ)*base73 + (922466691079890371/174500000000000000000000000000000 : ℝ)*base75 + (1268914187618390371/174500000000000000000000000000000 : ℝ)*base77 + (463726149342890371/174500000000000000000000000000000 : ℝ)*base79 + (1527556798961/872500000000000000000000000 : ℝ)*base81 + (11335137/1250000000000000000000 : ℝ)*base89 + (11335137/1250000000000000000000 : ℝ)*base91 + (11335137/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (2951/5000 : ℝ) ≤ (51496706302677869193245349/87250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1050117/10000000000000 : ℝ)*(upper3) + (2860213/20000000000000 : ℝ)*(upper4) + (768447/100000000000000 : ℝ)*(lower5) + (30352149848283/1000000000000 : ℝ)*(major0) + (30352149848283/1000000000000 : ℝ)*(major1) + (30352149848283/1000000000000 : ℝ)*(major2) + (4108924791242027/100000000000000 : ℝ)*(sp0) + (513615615160953/12500000000000 : ℝ)*(sp1) + (2054462001432597/50000000000000 : ℝ)*(sp2) + (388365816840113/20000000000000 : ℝ)*(sp3) + (366603703/50000000000000 : ℝ)*(sp8) + (37697613/6250000000000 : ℝ)*(sp9) + (1521584239/100000000000000 : ℝ)*(sp10) + (678344239/50000000000000 : ℝ)*(sp11) + (1941830440889043/100000000000000 : ℝ)*(f.failure) + (4108925524449433/100000000000000 : ℝ)*(f.sum) + (117942901101/349000000000000000000000000 : ℝ)*base66 + (11940269075777881/3490000000000000000000000000000 : ℝ)*base68 + (17448497818397881/3490000000000000000000000000000 : ℝ)*base70 + (36993561783482119/3490000000000000000000000000000 : ℝ)*base71 + (710983217467/174500000000000000000000000 : ℝ)*base74 + (192305782912119/3490000000000000000000000000000 : ℝ)*base75 + (3926654618482119/3490000000000000000000000000000 : ℝ)*base77 + (20853082033267881/3490000000000000000000000000000 : ℝ)*base80 + (770141379101/349000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3814257/10000000000000000000000 : ℝ)*base90 + (3814257/10000000000000000000000 : ℝ)*base92 + (3814257/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16037/20000 : ℝ) ≤ (2798552263902410856080418597/3490000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18372013/50000000000000 : ℝ)*(lower3) + (344440389/100000000000000 : ℝ)*(upper4) + (459770959/100000000000000 : ℝ)*(lower5) + (3345538920877147/100000000000000 : ℝ)*(major0) + (3345538920877147/100000000000000 : ℝ)*(major1) + (3345538920877147/100000000000000 : ℝ)*(major2) + (3980437553/100000000000000 : ℝ)*(sp0) + (243797526899/100000000000000 : ℝ)*(sp1) + (89683287903/100000000000000 : ℝ)*(sp2) + (67456541103/50000000000000 : ℝ)*(sp3) + (4523979153155893/100000000000000 : ℝ)*(sp8) + (2261869668033273/50000000000000 : ℝ)*(sp9) + (2261946725152771/50000000000000 : ℝ)*(sp10) + (2140230547094851/100000000000000 : ℝ)*(sp11) + (2140365460177057/100000000000000 : ℝ)*(f.failure) + (904796626718689/20000000000000 : ℝ)*(f.sum) + (13945304378477/3490000000000000000000000000 : ℝ)*base65 + (367548964733440871/349000000000000000000000000000000 : ℝ)*base67 + (2996099359003559129/349000000000000000000000000000000 : ℝ)*base70 + (1887529039765440871/349000000000000000000000000000000 : ℝ)*base71 + (36001335088247/3490000000000000000000000000 : ℝ)*base73 + (1406498511874559129/349000000000000000000000000000000 : ℝ)*base76 + (2019788372346440871/349000000000000000000000000000000 : ℝ)*base77 + (834567750813559129/349000000000000000000000000000000 : ℝ)*base80 + (8124286706707/3490000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9029643/10000000000000000000000 : ℝ)*base90 + (9029643/10000000000000000000000 : ℝ)*base92 + (9029643/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84507/100000 : ℝ) ≤ (-73729881553681910483694738702597/87250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31563/16000000000 : ℝ)*(lower0) + (39404239/50000000000000 : ℝ)*(lower2) + (55455511/25000000000000 : ℝ)*(upper3) + (170761371/100000000000000 : ℝ)*(lower4) + (1691232194376843/50000000000000 : ℝ)*(major0) + (1691232194376843/50000000000000 : ℝ)*(major1) + (1691232194376843/50000000000000 : ℝ)*(major2) + (2692054981/20000000000000 : ℝ)*(sp0) + (150857159669/100000000000000 : ℝ)*(sp5) + (195483934641/50000000000000 : ℝ)*(sp6) + (2314547107325321/50000000000000 : ℝ)*(sp12) + (4628956817765877/100000000000000 : ℝ)*(sp13) + (925743341411253/20000000000000 : ℝ)*(sp14) + (1081994578330769/50000000000000 : ℝ)*(sp15) + (1081994578330769/50000000000000 : ℝ)*(f.failure) + (4629107674925547/100000000000000 : ℝ)*(f.sum) + (19222728288219/872500000000000000000000000 : ℝ)*base65 + (432605897711834199/174500000000000000000000000000000 : ℝ)*base67 + (628827275615665801/174500000000000000000000000000000 : ℝ)*base70 + (4551598479737165801/174500000000000000000000000000000 : ℝ)*base72 + (1607803036063/1745000000000000000000000000 : ℝ)*base73 + (829883532230834199/174500000000000000000000000000000 : ℝ)*base75 + (794205978378834199/174500000000000000000000000000000 : ℝ)*base77 + (1144434366417334199/174500000000000000000000000000000 : ℝ)*base79 + (1630579456507/1745000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (44663131/5000000000000000000000 : ℝ)*base90 + (44663131/5000000000000000000000 : ℝ)*base92 + (44663131/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1382_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14731/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11241/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62873/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2951/5000 : ℝ) else (16037/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84507/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1382_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1382_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62873/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2951/5000 : ℝ) else (16037/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84507/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1382_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1382_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1382_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4341/1024 : ℝ) ≤ p) (hpb : p ≤ (2171/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156306901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2247/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62873/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(2951/5000 : ℝ) else (16037/20000 : ℝ) ≤ X j i ∧ X j i ≤ (84507/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1382_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
