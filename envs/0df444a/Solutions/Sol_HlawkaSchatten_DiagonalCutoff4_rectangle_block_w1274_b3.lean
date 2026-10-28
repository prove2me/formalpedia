-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:34.134344+00:00
-- url     : https://prove2.me/submissions/67c94dd2-9a95-4dde-9123-ad8d16e36049

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
theorem support_rectangle_w1274_box_0 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1982184803/10000000000 : ℝ)*x 0 + (5374340441/10000000000 : ℝ)*x 1 + (1343585113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1982184803/10000000000 : ℝ)^2117 ≤ (5914267155059/50000000000000 : ℝ)^1605 := by
    have hnat : (1982184803 : ℕ)^2117*50000000000000^1605 ≤ 5914267155059^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982184803 10000000000 5914267155059 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374340441/10000000000 : ℝ)^2117 ≤ (44085732780379/100000000000000 : ℝ)^1605 := by
    have hnat : (5374340441 : ℕ)^2117*100000000000000^1605 ≤ 44085732780379^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374340441 10000000000 44085732780379 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343585113/2500000000 : ℝ)^2117 ≤ (44085732899397/100000000000000 : ℝ)^1605 := by
    have hnat : (1343585113 : ℕ)^2117*100000000000000^1605 ≤ 44085732899397^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343585113 2500000000 44085732899397 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1982184803/10000000000 : ℝ), (5374340441/10000000000 : ℝ), (1343585113/2500000000 : ℝ)] ![(5914267155059/50000000000000 : ℝ), (44085732780379/100000000000000 : ℝ), (44085732899397/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1982184803/10000000000 : ℝ)|^2117 ≤ (5914267155059/50000000000000 : ℝ)^1605
        have hw : |(-1982184803/10000000000 : ℝ)|=(1982184803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374340441/10000000000 : ℝ)|^2117 ≤ (44085732780379/100000000000000 : ℝ)^1605
        have hw : |(5374340441/10000000000 : ℝ)|=(5374340441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343585113/2500000000 : ℝ)|^2117 ≤ (44085732899397/100000000000000 : ℝ)^1605
        have hw : |(1343585113/2500000000 : ℝ)|=(1343585113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_1 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1324253017/2500000000 : ℝ)*x 0 + (-2087358363/10000000000 : ℝ)*x 1 + (1343585123/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1324253017/2500000000 : ℝ)^2117 ≤ (43250982719319/100000000000000 : ℝ)^1605 := by
    have hnat : (1324253017 : ℕ)^2117*100000000000000^1605 ≤ 43250982719319^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324253017 2500000000 43250982719319 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087358363/10000000000 : ℝ)^2117 ≤ (6331641968999/50000000000000 : ℝ)^1605 := by
    have hnat : (2087358363 : ℕ)^2117*50000000000000^1605 ≤ 6331641968999^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087358363 10000000000 6331641968999 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343585123/2500000000 : ℝ)^2117 ≤ (11021433333047/25000000000000 : ℝ)^1605 := by
    have hnat : (1343585123 : ℕ)^2117*25000000000000^1605 ≤ 11021433333047^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343585123 2500000000 11021433333047 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1324253017/2500000000 : ℝ), (-2087358363/10000000000 : ℝ), (1343585123/2500000000 : ℝ)] ![(43250982719319/100000000000000 : ℝ), (6331641968999/50000000000000 : ℝ), (11021433333047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1324253017/2500000000 : ℝ)|^2117 ≤ (43250982719319/100000000000000 : ℝ)^1605
        have hw : |(1324253017/2500000000 : ℝ)|=(1324253017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087358363/10000000000 : ℝ)|^2117 ≤ (6331641968999/50000000000000 : ℝ)^1605
        have hw : |(-2087358363/10000000000 : ℝ)|=(2087358363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343585123/2500000000 : ℝ)|^2117 ≤ (11021433333047/25000000000000 : ℝ)^1605
        have hw : |(1343585123/2500000000 : ℝ)|=(1343585123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_2 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5297011681/10000000000 : ℝ)*x 0 + (1343585167/2500000000 : ℝ)*x 1 + (-1043679323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5297011681/10000000000 : ℝ)^2117 ≤ (2703186159461/6250000000000 : ℝ)^1605 := by
    have hnat : (5297011681 : ℕ)^2117*6250000000000^1605 ≤ 2703186159461^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5297011681 10000000000 2703186159461 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343585167/2500000000 : ℝ)^2117 ≤ (44085735236471/100000000000000 : ℝ)^1605 := by
    have hnat : (1343585167 : ℕ)^2117*100000000000000^1605 ≤ 44085735236471^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343585167 2500000000 44085735236471 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043679323/5000000000 : ℝ)^2117 ≤ (6331643101273/50000000000000 : ℝ)^1605 := by
    have hnat : (1043679323 : ℕ)^2117*50000000000000^1605 ≤ 6331643101273^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043679323 5000000000 6331643101273 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5297011681/10000000000 : ℝ), (1343585167/2500000000 : ℝ), (-1043679323/5000000000 : ℝ)] ![(2703186159461/6250000000000 : ℝ), (44085735236471/100000000000000 : ℝ), (6331643101273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5297011681/10000000000 : ℝ)|^2117 ≤ (2703186159461/6250000000000 : ℝ)^1605
        have hw : |(5297011681/10000000000 : ℝ)|=(5297011681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343585167/2500000000 : ℝ)|^2117 ≤ (44085735236471/100000000000000 : ℝ)^1605
        have hw : |(1343585167/2500000000 : ℝ)|=(1343585167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043679323/5000000000 : ℝ)|^2117 ≤ (6331643101273/50000000000000 : ℝ)^1605
        have hw : |(-1043679323/5000000000 : ℝ)|=(1043679323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_3 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4452482449/10000000000 : ℝ)*x 0 + (4295183129/10000000000 : ℝ)*x 1 + (4295183829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452482449/10000000000 : ℝ)^2117 ≤ (17197892614063/50000000000000 : ℝ)^1605 := by
    have hnat : (4452482449 : ℕ)^2117*50000000000000^1605 ≤ 17197892614063^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452482449 10000000000 17197892614063 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4295183129/10000000000 : ℝ)^2117 ≤ (16401051926927/50000000000000 : ℝ)^1605 := by
    have hnat : (4295183129 : ℕ)^2117*50000000000000^1605 ≤ 16401051926927^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295183129 10000000000 16401051926927 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4295183829/10000000000 : ℝ)^2117 ≤ (8200527726267/25000000000000 : ℝ)^1605 := by
    have hnat : (4295183829 : ℕ)^2117*25000000000000^1605 ≤ 8200527726267^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295183829 10000000000 8200527726267 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452482449/10000000000 : ℝ), (4295183129/10000000000 : ℝ), (4295183829/10000000000 : ℝ)] ![(17197892614063/50000000000000 : ℝ), (16401051926927/50000000000000 : ℝ), (8200527726267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452482449/10000000000 : ℝ)|^2117 ≤ (17197892614063/50000000000000 : ℝ)^1605
        have hw : |(4452482449/10000000000 : ℝ)|=(4452482449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4295183129/10000000000 : ℝ)|^2117 ≤ (16401051926927/50000000000000 : ℝ)^1605
        have hw : |(4295183129/10000000000 : ℝ)|=(4295183129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4295183829/10000000000 : ℝ)|^2117 ≤ (8200527726267/25000000000000 : ℝ)^1605
        have hw : |(4295183829/10000000000 : ℝ)|=(4295183829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_4 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1114463081/5000000000 : ℝ)*x 0 + (5282607449/10000000000 : ℝ)*x 1 + (5282607483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1114463081/5000000000 : ℝ)^2117 ≤ (3452042882829/25000000000000 : ℝ)^1605 := by
    have hnat : (1114463081 : ℕ)^2117*25000000000000^1605 ≤ 3452042882829^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114463081 5000000000 3452042882829 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282607449/10000000000 : ℝ)^2117 ≤ (43095914041699/100000000000000 : ℝ)^1605 := by
    have hnat : (5282607449 : ℕ)^2117*100000000000000^1605 ≤ 43095914041699^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282607449 10000000000 43095914041699 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282607483/10000000000 : ℝ)^2117 ≤ (43095914407557/100000000000000 : ℝ)^1605 := by
    have hnat : (5282607483 : ℕ)^2117*100000000000000^1605 ≤ 43095914407557^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282607483 10000000000 43095914407557 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1114463081/5000000000 : ℝ), (5282607449/10000000000 : ℝ), (5282607483/10000000000 : ℝ)] ![(3452042882829/25000000000000 : ℝ), (43095914041699/100000000000000 : ℝ), (43095914407557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1114463081/5000000000 : ℝ)|^2117 ≤ (3452042882829/25000000000000 : ℝ)^1605
        have hw : |(-1114463081/5000000000 : ℝ)|=(1114463081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282607449/10000000000 : ℝ)|^2117 ≤ (43095914041699/100000000000000 : ℝ)^1605
        have hw : |(5282607449/10000000000 : ℝ)|=(5282607449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282607483/10000000000 : ℝ)|^2117 ≤ (43095914407557/100000000000000 : ℝ)^1605
        have hw : |(5282607483/10000000000 : ℝ)|=(5282607483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_5 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2680815113/5000000000 : ℝ)*x 0 + (-212381567/1000000000 : ℝ)*x 1 + (5282607499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680815113/5000000000 : ℝ)^2117 ≤ (21974131432437/50000000000000 : ℝ)^1605 := by
    have hnat : (2680815113 : ℕ)^2117*50000000000000^1605 ≤ 21974131432437^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680815113 5000000000 21974131432437 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (212381567/1000000000 : ℝ)^2117 ≤ (12955822531577/100000000000000 : ℝ)^1605 := by
    have hnat : (212381567 : ℕ)^2117*100000000000000^1605 ≤ 12955822531577^1605*1000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212381567 1000000000 12955822531577 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282607499/10000000000 : ℝ)^2117 ≤ (21547957289863/50000000000000 : ℝ)^1605 := by
    have hnat : (5282607499 : ℕ)^2117*50000000000000^1605 ≤ 21547957289863^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282607499 10000000000 21547957289863 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680815113/5000000000 : ℝ), (-212381567/1000000000 : ℝ), (5282607499/10000000000 : ℝ)] ![(21974131432437/50000000000000 : ℝ), (12955822531577/100000000000000 : ℝ), (21547957289863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680815113/5000000000 : ℝ)|^2117 ≤ (21974131432437/50000000000000 : ℝ)^1605
        have hw : |(2680815113/5000000000 : ℝ)|=(2680815113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-212381567/1000000000 : ℝ)|^2117 ≤ (12955822531577/100000000000000 : ℝ)^1605
        have hw : |(-212381567/1000000000 : ℝ)|=(212381567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282607499/10000000000 : ℝ)|^2117 ≤ (21547957289863/50000000000000 : ℝ)^1605
        have hw : |(5282607499/10000000000 : ℝ)|=(5282607499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_6 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5361630293/10000000000 : ℝ)*x 0 + (5282607431/10000000000 : ℝ)*x 1 + (-2123815671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361630293/10000000000 : ℝ)^2117 ≤ (43948263589253/100000000000000 : ℝ)^1605 := by
    have hnat : (5361630293 : ℕ)^2117*100000000000000^1605 ≤ 43948263589253^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361630293 10000000000 43948263589253 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282607431/10000000000 : ℝ)^2117 ≤ (4309591384801/10000000000000 : ℝ)^1605 := by
    have hnat : (5282607431 : ℕ)^2117*10000000000000^1605 ≤ 4309591384801^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282607431 10000000000 4309591384801 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123815671/10000000000 : ℝ)^2117 ≤ (12955822539623/100000000000000 : ℝ)^1605 := by
    have hnat : (2123815671 : ℕ)^2117*100000000000000^1605 ≤ 12955822539623^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123815671 10000000000 12955822539623 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361630293/10000000000 : ℝ), (5282607431/10000000000 : ℝ), (-2123815671/10000000000 : ℝ)] ![(43948263589253/100000000000000 : ℝ), (4309591384801/10000000000000 : ℝ), (12955822539623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361630293/10000000000 : ℝ)|^2117 ≤ (43948263589253/100000000000000 : ℝ)^1605
        have hw : |(5361630293/10000000000 : ℝ)|=(5361630293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282607431/10000000000 : ℝ)|^2117 ≤ (4309591384801/10000000000000 : ℝ)^1605
        have hw : |(5282607431/10000000000 : ℝ)|=(5282607431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2123815671/10000000000 : ℝ)|^2117 ≤ (12955822539623/100000000000000 : ℝ)^1605
        have hw : |(-2123815671/10000000000 : ℝ)|=(2123815671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_7 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (847928067/2000000000 : ℝ)*x 0 + (1100396153/2500000000 : ℝ)*x 1 + (2200792359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847928067/2000000000 : ℝ)^2117 ≤ (1612188483633/5000000000000 : ℝ)^1605 := by
    have hnat : (847928067 : ℕ)^2117*5000000000000^1605 ≤ 1612188483633^1605*2000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847928067 2000000000 1612188483633 5000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100396153/2500000000 : ℝ)^2117 ≤ (1693905730707/5000000000000 : ℝ)^1605 := by
    have hnat : (1100396153 : ℕ)^2117*5000000000000^1605 ≤ 1693905730707^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100396153 2500000000 1693905730707 5000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200792359/5000000000 : ℝ)^2117 ≤ (33878115690263/100000000000000 : ℝ)^1605 := by
    have hnat : (2200792359 : ℕ)^2117*100000000000000^1605 ≤ 33878115690263^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200792359 5000000000 33878115690263 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847928067/2000000000 : ℝ), (1100396153/2500000000 : ℝ), (2200792359/5000000000 : ℝ)] ![(1612188483633/5000000000000 : ℝ), (1693905730707/5000000000000 : ℝ), (33878115690263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847928067/2000000000 : ℝ)|^2117 ≤ (1612188483633/5000000000000 : ℝ)^1605
        have hw : |(847928067/2000000000 : ℝ)|=(847928067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1100396153/2500000000 : ℝ)|^2117 ≤ (1693905730707/5000000000000 : ℝ)^1605
        have hw : |(1100396153/2500000000 : ℝ)|=(1100396153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2200792359/5000000000 : ℝ)|^2117 ≤ (33878115690263/100000000000000 : ℝ)^1605
        have hw : |(2200792359/5000000000 : ℝ)|=(2200792359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_8 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2177188703/10000000000 : ℝ)*x 0 + (5219975243/10000000000 : ℝ)*x 1 + (215358149/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177188703/10000000000 : ℝ)^2117 ≤ (13386987460271/100000000000000 : ℝ)^1605 := by
    have hnat : (2177188703 : ℕ)^2117*100000000000000^1605 ≤ 13386987460271^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177188703 10000000000 13386987460271 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219975243/10000000000 : ℝ)^2117 ≤ (42423236405419/100000000000000 : ℝ)^1605 := by
    have hnat : (5219975243 : ℕ)^2117*100000000000000^1605 ≤ 42423236405419^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219975243 10000000000 42423236405419 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215358149/400000000 : ℝ)^2117 ≤ (4418977612943/10000000000000 : ℝ)^1605 := by
    have hnat : (215358149 : ℕ)^2117*10000000000000^1605 ≤ 4418977612943^1605*400000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215358149 400000000 4418977612943 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2177188703/10000000000 : ℝ), (5219975243/10000000000 : ℝ), (215358149/400000000 : ℝ)] ![(13386987460271/100000000000000 : ℝ), (42423236405419/100000000000000 : ℝ), (4418977612943/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2177188703/10000000000 : ℝ)|^2117 ≤ (13386987460271/100000000000000 : ℝ)^1605
        have hw : |(-2177188703/10000000000 : ℝ)|=(2177188703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219975243/10000000000 : ℝ)|^2117 ≤ (42423236405419/100000000000000 : ℝ)^1605
        have hw : |(5219975243/10000000000 : ℝ)|=(5219975243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215358149/400000000 : ℝ)|^2117 ≤ (4418977612943/10000000000000 : ℝ)^1605
        have hw : |(215358149/400000000 : ℝ)|=(215358149/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_9 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290236859/10000000000 : ℝ)*x 0 + (-2083471861/10000000000 : ℝ)*x 1 + (2691976899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290236859/10000000000 : ℝ)^2117 ≤ (43178029426487/100000000000000 : ℝ)^1605 := by
    have hnat : (5290236859 : ℕ)^2117*100000000000000^1605 ≤ 43178029426487^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290236859 10000000000 43178029426487 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2083471861/10000000000 : ℝ)^2117 ≤ (12632193632109/100000000000000 : ℝ)^1605 := by
    have hnat : (2083471861 : ℕ)^2117*100000000000000^1605 ≤ 12632193632109^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083471861 10000000000 12632193632109 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2691976899/5000000000 : ℝ)^2117 ≤ (1767591076789/4000000000000 : ℝ)^1605 := by
    have hnat : (2691976899 : ℕ)^2117*4000000000000^1605 ≤ 1767591076789^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691976899 5000000000 1767591076789 4000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290236859/10000000000 : ℝ), (-2083471861/10000000000 : ℝ), (2691976899/5000000000 : ℝ)] ![(43178029426487/100000000000000 : ℝ), (12632193632109/100000000000000 : ℝ), (1767591076789/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290236859/10000000000 : ℝ)|^2117 ≤ (43178029426487/100000000000000 : ℝ)^1605
        have hw : |(5290236859/10000000000 : ℝ)|=(5290236859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2083471861/10000000000 : ℝ)|^2117 ≤ (12632193632109/100000000000000 : ℝ)^1605
        have hw : |(-2083471861/10000000000 : ℝ)|=(2083471861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2691976899/5000000000 : ℝ)|^2117 ≤ (1767591076789/4000000000000 : ℝ)^1605
        have hw : |(2691976899/5000000000 : ℝ)|=(2691976899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_10 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5290236907/10000000000 : ℝ)*x 0 + (2691976853/5000000000 : ℝ)*x 1 + (-2083471923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290236907/10000000000 : ℝ)^2117 ≤ (4317802994323/10000000000000 : ℝ)^1605 := by
    have hnat : (5290236907 : ℕ)^2117*10000000000000^1605 ≤ 4317802994323^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290236907 10000000000 4317802994323 10000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2691976853/5000000000 : ℝ)^2117 ≤ (5523721990467/12500000000000 : ℝ)^1605 := by
    have hnat : (2691976853 : ℕ)^2117*12500000000000^1605 ≤ 5523721990467^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691976853 5000000000 5523721990467 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083471923/10000000000 : ℝ)^2117 ≤ (6316097063967/50000000000000 : ℝ)^1605 := by
    have hnat : (2083471923 : ℕ)^2117*50000000000000^1605 ≤ 6316097063967^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083471923 10000000000 6316097063967 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290236907/10000000000 : ℝ), (2691976853/5000000000 : ℝ), (-2083471923/10000000000 : ℝ)] ![(4317802994323/10000000000000 : ℝ), (5523721990467/12500000000000 : ℝ), (6316097063967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290236907/10000000000 : ℝ)|^2117 ≤ (4317802994323/10000000000000 : ℝ)^1605
        have hw : |(5290236907/10000000000 : ℝ)|=(5290236907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2691976853/5000000000 : ℝ)|^2117 ≤ (5523721990467/12500000000000 : ℝ)^1605
        have hw : |(2691976853/5000000000 : ℝ)|=(2691976853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2083471923/10000000000 : ℝ)|^2117 ≤ (6316097063967/50000000000000 : ℝ)^1605
        have hw : |(-2083471923/10000000000 : ℝ)|=(2083471923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_11 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1118628717/2500000000 : ℝ)*x 0 + (267751673/625000000 : ℝ)*x 1 + (4284026701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118628717/2500000000 : ℝ)^2117 ≤ (34620459463133/100000000000000 : ℝ)^1605 := by
    have hnat : (1118628717 : ℕ)^2117*100000000000000^1605 ≤ 34620459463133^1605*2500000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118628717 2500000000 34620459463133 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267751673/625000000 : ℝ)^2117 ≤ (32689770603243/100000000000000 : ℝ)^1605 := by
    have hnat : (267751673 : ℕ)^2117*100000000000000^1605 ≤ 32689770603243^1605*625000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267751673 625000000 32689770603243 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4284026701/10000000000 : ℝ)^2117 ≤ (32689769928901/100000000000000 : ℝ)^1605 := by
    have hnat : (4284026701 : ℕ)^2117*100000000000000^1605 ≤ 32689769928901^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284026701 10000000000 32689769928901 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1118628717/2500000000 : ℝ), (267751673/625000000 : ℝ), (4284026701/10000000000 : ℝ)] ![(34620459463133/100000000000000 : ℝ), (32689770603243/100000000000000 : ℝ), (32689769928901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1118628717/2500000000 : ℝ)|^2117 ≤ (34620459463133/100000000000000 : ℝ)^1605
        have hw : |(1118628717/2500000000 : ℝ)|=(1118628717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(267751673/625000000 : ℝ)|^2117 ≤ (32689770603243/100000000000000 : ℝ)^1605
        have hw : |(267751673/625000000 : ℝ)|=(267751673/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4284026701/10000000000 : ℝ)|^2117 ≤ (32689769928901/100000000000000 : ℝ)^1605
        have hw : |(4284026701/10000000000 : ℝ)|=(4284026701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_12 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017081627/5000000000 : ℝ)*x 0 + (5435785429/10000000000 : ℝ)*x 1 + (210980673/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017081627/5000000000 : ℝ)^2117 ≤ (2447872072799/20000000000000 : ℝ)^1605 := by
    have hnat : (1017081627 : ℕ)^2117*20000000000000^1605 ≤ 2447872072799^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017081627 5000000000 2447872072799 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435785429/10000000000 : ℝ)^2117 ≤ (11187940922809/25000000000000 : ℝ)^1605 := by
    have hnat : (5435785429 : ℕ)^2117*25000000000000^1605 ≤ 11187940922809^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435785429 10000000000 11187940922809 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210980673/400000000 : ℝ)^2117 ≤ (2688054745697/6250000000000 : ℝ)^1605 := by
    have hnat : (210980673 : ℕ)^2117*6250000000000^1605 ≤ 2688054745697^1605*400000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210980673 400000000 2688054745697 6250000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017081627/5000000000 : ℝ), (5435785429/10000000000 : ℝ), (210980673/400000000 : ℝ)] ![(2447872072799/20000000000000 : ℝ), (11187940922809/25000000000000 : ℝ), (2688054745697/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017081627/5000000000 : ℝ)|^2117 ≤ (2447872072799/20000000000000 : ℝ)^1605
        have hw : |(-1017081627/5000000000 : ℝ)|=(1017081627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435785429/10000000000 : ℝ)|^2117 ≤ (11187940922809/25000000000000 : ℝ)^1605
        have hw : |(5435785429/10000000000 : ℝ)|=(5435785429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210980673/400000000 : ℝ)|^2117 ≤ (2688054745697/6250000000000 : ℝ)^1605
        have hw : |(210980673/400000000 : ℝ)|=(210980673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_13 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5367327917/10000000000 : ℝ)*x 0 + (-132935979/625000000 : ℝ)*x 1 + (2637258171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367327917/10000000000 : ℝ)^2117 ≤ (44009874559907/100000000000000 : ℝ)^1605 := by
    have hnat : (5367327917 : ℕ)^2117*100000000000000^1605 ≤ 44009874559907^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367327917 10000000000 44009874559907 100000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (132935979/625000000 : ℝ)^2117 ≤ (3245313673209/25000000000000 : ℝ)^1605 := by
    have hnat : (132935979 : ℕ)^2117*25000000000000^1605 ≤ 3245313673209^1605*625000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132935979 625000000 3245313673209 25000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637258171/5000000000 : ℝ)^2117 ≤ (21504435368179/50000000000000 : ℝ)^1605 := by
    have hnat : (2637258171 : ℕ)^2117*50000000000000^1605 ≤ 21504435368179^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637258171 5000000000 21504435368179 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367327917/10000000000 : ℝ), (-132935979/625000000 : ℝ), (2637258171/5000000000 : ℝ)] ![(44009874559907/100000000000000 : ℝ), (3245313673209/25000000000000 : ℝ), (21504435368179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367327917/10000000000 : ℝ)|^2117 ≤ (44009874559907/100000000000000 : ℝ)^1605
        have hw : |(5367327917/10000000000 : ℝ)|=(5367327917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-132935979/625000000 : ℝ)|^2117 ≤ (3245313673209/25000000000000 : ℝ)^1605
        have hw : |(-132935979/625000000 : ℝ)|=(132935979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637258171/5000000000 : ℝ)|^2117 ≤ (21504435368179/50000000000000 : ℝ)^1605
        have hw : |(2637258171/5000000000 : ℝ)|=(2637258171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_14 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2683663923/5000000000 : ℝ)*x 0 + (131862913/250000000 : ℝ)*x 1 + (-1063487761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683663923/5000000000 : ℝ)^2117 ≤ (22004936896011/50000000000000 : ℝ)^1605 := by
    have hnat : (2683663923 : ℕ)^2117*50000000000000^1605 ≤ 22004936896011^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683663923 5000000000 22004936896011 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131862913/250000000 : ℝ)^2117 ≤ (8601774530159/20000000000000 : ℝ)^1605 := by
    have hnat : (131862913 : ℕ)^2117*20000000000000^1605 ≤ 8601774530159^1605*250000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131862913 250000000 8601774530159 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063487761/5000000000 : ℝ)^2117 ≤ (519250141989/4000000000000 : ℝ)^1605 := by
    have hnat : (1063487761 : ℕ)^2117*4000000000000^1605 ≤ 519250141989^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063487761 5000000000 519250141989 4000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683663923/5000000000 : ℝ), (131862913/250000000 : ℝ), (-1063487761/5000000000 : ℝ)] ![(22004936896011/50000000000000 : ℝ), (8601774530159/20000000000000 : ℝ), (519250141989/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683663923/5000000000 : ℝ)|^2117 ≤ (22004936896011/50000000000000 : ℝ)^1605
        have hw : |(2683663923/5000000000 : ℝ)|=(2683663923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131862913/250000000 : ℝ)|^2117 ≤ (8601774530159/20000000000000 : ℝ)^1605
        have hw : |(131862913/250000000 : ℝ)|=(131862913/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063487761/5000000000 : ℝ)|^2117 ≤ (519250141989/4000000000000 : ℝ)^1605
        have hw : |(-1063487761/5000000000 : ℝ)|=(1063487761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1274_box_15 (p : ℝ) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2110317533/5000000000 : ℝ)*x 0 + (4410964407/10000000000 : ℝ)*x 1 + (275685279/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110317533/5000000000 : ℝ)^2117 ≤ (4006657025407/12500000000000 : ℝ)^1605 := by
    have hnat : (2110317533 : ℕ)^2117*12500000000000^1605 ≤ 4006657025407^1605*5000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110317533 5000000000 4006657025407 12500000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4410964407/10000000000 : ℝ)^2117 ≤ (6794674321339/20000000000000 : ℝ)^1605 := by
    have hnat : (4410964407 : ℕ)^2117*20000000000000^1605 ≤ 6794674321339^1605*10000000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410964407 10000000000 6794674321339 20000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275685279/625000000 : ℝ)^2117 ≤ (16986686092879/50000000000000 : ℝ)^1605 := by
    have hnat : (275685279 : ℕ)^2117*50000000000000^1605 ≤ 16986686092879^1605*625000000^2117 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275685279 625000000 16986686092879 50000000000000 2117 1605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2117/512 : ℝ)) 2117 1605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2110317533/5000000000 : ℝ), (4410964407/10000000000 : ℝ), (275685279/625000000 : ℝ)] ![(4006657025407/12500000000000 : ℝ), (6794674321339/20000000000000 : ℝ), (16986686092879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2110317533/5000000000 : ℝ)|^2117 ≤ (4006657025407/12500000000000 : ℝ)^1605
        have hw : |(2110317533/5000000000 : ℝ)|=(2110317533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4410964407/10000000000 : ℝ)|^2117 ≤ (6794674321339/20000000000000 : ℝ)^1605
        have hw : |(4410964407/10000000000 : ℝ)|=(4410964407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275685279/625000000 : ℝ)|^2117 ≤ (16986686092879/50000000000000 : ℝ)^1605
        have hw : |(275685279/625000000 : ℝ)|=(275685279/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1274_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62253/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14851/25000 : ℝ) ∧ (40103/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41709/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5759/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5759/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5759/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14121/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5759/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5759/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14121/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5759/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5759/50000 : ℝ) ^ (8467/2048 : ℝ) ≤ (1645820685765733/12500000000000000000 : ℝ) := by
    have hpowers : (5759/50000 : ℝ)^8467 ≤ (1645820685765733/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5759 : ℕ)^8467*12500000000000000000^2048 ≤ 1645820685765733^2048*50000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5759 50000 1645820685765733 12500000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5759/50000 : ℝ)) (X := (1645820685765733/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14121/100000 : ℝ) ^ (8467/2048 : ℝ) ≤ (122283537735983/400000000000000000 : ℝ) := by
    have hpowers : (14121/100000 : ℝ)^8467 ≤ (122283537735983/400000000000000000 : ℝ)^2048 := by
      have hnat : (14121 : ℕ)^8467*400000000000000000^2048 ≤ 122283537735983^2048*100000^8467 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14121 100000 122283537735983 400000000000000000 8467 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14121/100000 : ℝ)) (X := (122283537735983/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251645820685765733/6250000000000000000 : ℝ) ≤ (625039805177331/625000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (6251645820685765733/6250000000000000000 : ℝ)^2048 ≤ (625039805177331/625000000000000 : ℝ)^8467 := by
      have hnat : (6251645820685765733 : ℕ)^2048*625000000000000^8467 ≤ 625039805177331^8467*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251645820685765733 6250000000000000000 625039805177331 625000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625039805177331/625000000000000 : ℝ)) (X := (6251645820685765733/6250000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021868724960060807/50000000000000000000 : ℝ) ≤ (5000528873571621/5000000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (50021868724960060807/50000000000000000000 : ℝ)^2048 ≤ (5000528873571621/5000000000000000 : ℝ)^8467 := by
      have hnat : (50021868724960060807 : ℕ)^2048*5000000000000000^8467 ≤ 5000528873571621^8467*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021868724960060807 50000000000000000000 5000528873571621 5000000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000528873571621/5000000000000000 : ℝ)) (X := (50021868724960060807/50000000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (200122283537735983/200000000000000000 : ℝ) ≤ (2500369652862297/2500000000000000 : ℝ) ^ (8467/2048 : ℝ) := by
    have hpowers : (200122283537735983/200000000000000000 : ℝ)^2048 ≤ (2500369652862297/2500000000000000 : ℝ)^8467 := by
      have hnat : (200122283537735983 : ℕ)^2048*2500000000000000^8467 ≤ 2500369652862297^8467*200000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200122283537735983 200000000000000000 2500369652862297 2500000000000000 2048 8467 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500369652862297/2500000000000000 : ℝ)) (X := (200122283537735983/200000000000000000 : ℝ)) (by norm_num) 8467 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1645820685765733/12500000000000000000 : ℝ) ≤ ((3252745346984213679/3253750000000000000 : ℝ)+2*(210432152973/130150000000000 : ℝ)*(5759/50000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (3252745346984213679/3253750000000000000 : ℝ)+2*(210432152973/130150000000000 : ℝ)*(5759/50000 : ℝ)=(625039805177331/625000000000000 : ℝ) by norm_num, show 1+2*(1645820685765733/12500000000000000000 : ℝ)=(6251645820685765733/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(122283537735983/400000000000000000 : ℝ)+(1645820685765733/12500000000000000000 : ℝ) ≤ ((3252745346984213679/3253750000000000000 : ℝ)+(210432152973/130150000000000 : ℝ)*((14121/100000 : ℝ)+(5759/50000 : ℝ)))^(8467/2048 : ℝ) := by
    rw [show (3252745346984213679/3253750000000000000 : ℝ)+(210432152973/130150000000000 : ℝ)*((14121/100000 : ℝ)+(5759/50000 : ℝ))=(5000528873571621/5000000000000000 : ℝ) by norm_num, show 1+(122283537735983/400000000000000000 : ℝ)+(1645820685765733/12500000000000000000 : ℝ)=(50021868724960060807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(122283537735983/400000000000000000 : ℝ) ≤ ((3252745346984213679/3253750000000000000 : ℝ)+2*(210432152973/130150000000000 : ℝ)*(14121/100000 : ℝ))^(8467/2048 : ℝ) := by
    rw [show (3252745346984213679/3253750000000000000 : ℝ)+2*(210432152973/130150000000000 : ℝ)*(14121/100000 : ℝ)=(2500369652862297/2500000000000000 : ℝ) by norm_num, show 1+2*(122283537735983/400000000000000000 : ℝ)=(200122283537735983/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3252745346984213679/3253750000000000000 : ℝ)*(X 1 0+X 2 0)+(210432152973/130150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5759/50000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (3252745346984213679/3253750000000000000 : ℝ)) (alpha := (210432152973/130150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3252745346984213679/3253750000000000000 : ℝ)*(X 0 1+X 2 1)+(210432152973/130150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5759/50000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (3252745346984213679/3253750000000000000 : ℝ)) (alpha := (210432152973/130150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3252745346984213679/3253750000000000000 : ℝ)*(X 0 2+X 1 2)+(210432152973/130150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8467/2048 : ℝ)) (lo := (5759/50000 : ℝ)) (hi := (14121/100000 : ℝ)) (c := (3252745346984213679/3253750000000000000 : ℝ)) (alpha := (210432152973/130150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1982184803/10000000000 : ℝ)*X 0 0+(5374340441/10000000000 : ℝ)*X 0 1+(1343585113/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1324253017/2500000000 : ℝ)*X 1 0+(-2087358363/10000000000 : ℝ)*X 1 1+(1343585123/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5297011681/10000000000 : ℝ)*X 2 0+(1343585167/2500000000 : ℝ)*X 2 1+(-1043679323/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4452482449/10000000000 : ℝ)*X 0 0+(4295183129/10000000000 : ℝ)*X 0 1+(4295183829/10000000000 : ℝ)*X 0 2+(4452482449/10000000000 : ℝ)*X 1 0+(4295183129/10000000000 : ℝ)*X 1 1+(4295183829/10000000000 : ℝ)*X 1 2+(4452482449/10000000000 : ℝ)*X 2 0+(4295183129/10000000000 : ℝ)*X 2 1+(4295183829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1114463081/5000000000 : ℝ)*X 0 0+(5282607449/10000000000 : ℝ)*X 0 1+(5282607483/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2680815113/5000000000 : ℝ)*X 1 0+(-212381567/1000000000 : ℝ)*X 1 1+(5282607499/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5361630293/10000000000 : ℝ)*X 2 0+(5282607431/10000000000 : ℝ)*X 2 1+(-2123815671/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((847928067/2000000000 : ℝ)*X 0 0+(1100396153/2500000000 : ℝ)*X 0 1+(2200792359/5000000000 : ℝ)*X 0 2+(847928067/2000000000 : ℝ)*X 1 0+(1100396153/2500000000 : ℝ)*X 1 1+(2200792359/5000000000 : ℝ)*X 1 2+(847928067/2000000000 : ℝ)*X 2 0+(1100396153/2500000000 : ℝ)*X 2 1+(2200792359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2177188703/10000000000 : ℝ)*X 0 0+(5219975243/10000000000 : ℝ)*X 0 1+(215358149/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5290236859/10000000000 : ℝ)*X 1 0+(-2083471861/10000000000 : ℝ)*X 1 1+(2691976899/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5290236907/10000000000 : ℝ)*X 2 0+(2691976853/5000000000 : ℝ)*X 2 1+(-2083471923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1118628717/2500000000 : ℝ)*X 0 0+(267751673/625000000 : ℝ)*X 0 1+(4284026701/10000000000 : ℝ)*X 0 2+(1118628717/2500000000 : ℝ)*X 1 0+(267751673/625000000 : ℝ)*X 1 1+(4284026701/10000000000 : ℝ)*X 1 2+(1118628717/2500000000 : ℝ)*X 2 0+(267751673/625000000 : ℝ)*X 2 1+(4284026701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1017081627/5000000000 : ℝ)*X 0 0+(5435785429/10000000000 : ℝ)*X 0 1+(210980673/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367327917/10000000000 : ℝ)*X 1 0+(-132935979/625000000 : ℝ)*X 1 1+(2637258171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2683663923/5000000000 : ℝ)*X 2 0+(131862913/250000000 : ℝ)*X 2 1+(-1063487761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2110317533/5000000000 : ℝ)*X 0 0+(4410964407/10000000000 : ℝ)*X 0 1+(275685279/625000000 : ℝ)*X 0 2+(2110317533/5000000000 : ℝ)*X 1 0+(4410964407/10000000000 : ℝ)*X 1 1+(275685279/625000000 : ℝ)*X 1 2+(2110317533/5000000000 : ℝ)*X 2 0+(4410964407/10000000000 : ℝ)*X 2 1+(275685279/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1274_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62253/100000 : ℝ) ≤ (-25318626544272621192483991577151/40671875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22646733/100000000000000 : ℝ)*(upper0) + (15283109/100000000000000 : ℝ)*(upper1) + (11641/6250000000000 : ℝ)*(upper2) + (23972483/100000000000000 : ℝ)*(upper3) + (64790527/100000000000000 : ℝ)*(upper5) + (1007519036969851/25000000000000 : ℝ)*(major0) + (1007519036969851/25000000000000 : ℝ)*(major1) + (1007519036969851/25000000000000 : ℝ)*(major2) + (176869211/3125000000000 : ℝ)*(sp2) + (3620989097/100000000000000 : ℝ)*(sp3) + (2715423997717109/50000000000000 : ℝ)*(sp4) + (2715423997717109/50000000000000 : ℝ)*(sp5) + (2715421167809733/50000000000000 : ℝ)*(sp6) + (1325025497170803/50000000000000 : ℝ)*(sp7) + (1325027307665351/50000000000000 : ℝ)*(f.failure) + (2715423997717109/50000000000000 : ℝ)*(f.sum) + (24055793953521/13015000000000000000000000000 : ℝ)*base66 + (1215331500697164421/81343750000000000000000000000000 : ℝ)*base68 + (16190922614742289421/81343750000000000000000000000000 : ℝ)*base70 + (474428919200039421/81343750000000000000000000000000 : ℝ)*base72 + (78677016818691/13015000000000000000000000000 : ℝ)*base74 + (2193855249469289421/81343750000000000000000000000000 : ℝ)*base76 + (656860856023351921/81343750000000000000000000000000 : ℝ)*base78 + (4958374722149710579/81343750000000000000000000000000 : ℝ)*base79 + (5545057406803461/13015000000000000000000000000 : ℝ)*base82 + (29285939/5000000000000000000000 : ℝ)*base90 + (29285939/5000000000000000000000 : ℝ)*base92 + (29285939/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14851/25000 : ℝ) ≤ (48323518403561244089734017782133/81343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (85561661/100000000000000 : ℝ)*(lower0) + (30277211/10000000000000 : ℝ)*(lower1) + (153994931/100000000000000 : ℝ)*(lower4) + (108237217/50000000000000 : ℝ)*(lower5) + (2048222218891909/50000000000000 : ℝ)*(major0) + (2048222218891909/50000000000000 : ℝ)*(major1) + (2048222218891909/50000000000000 : ℝ)*(major2) + (5479362186363503/100000000000000 : ℝ)*(sp0) + (684923790180101/12500000000000 : ℝ)*(sp1) + (5479381336804281/100000000000000 : ℝ)*(sp2) + (2693685055505297/100000000000000 : ℝ)*(sp3) + (4492318263/50000000000000 : ℝ)*(sp6) + (45256419/400000000000 : ℝ)*(sp7) + (3516884663/12500000000000 : ℝ)*(sp12) + (1346848184805023/50000000000000 : ℝ)*(f.failure) + (684923790180101/12500000000000 : ℝ)*(f.sum) + (42017020802171/6507500000000000000000000000 : ℝ)*base66 + (4314206903955648211/162687500000000000000000000000000 : ℝ)*base67 + (1633265181241289289/162687500000000000000000000000000 : ℝ)*base70 + (4247031624918414289/162687500000000000000000000000000 : ℝ)*base72 + (57766042404693/13015000000000000000000000000 : ℝ)*base73 + (1515936238062460711/162687500000000000000000000000000 : ℝ)*base75 + (2935773227643726789/162687500000000000000000000000000 : ℝ)*base78 + (4445749717514664289/162687500000000000000000000000000 : ℝ)*base80 + (83109960504787/13015000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (33415147/5000000000000000000000 : ℝ)*base90 + (33415147/5000000000000000000000 : ℝ)*base92 + (33415147/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (40103/50000 : ℝ) ≤ (10439096431039471906680631407/13015000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7002671/25000000000000 : ℝ)*(upper0) + (20497721/50000000000000 : ℝ)*(upper1) + (652237/3125000000000 : ℝ)*(upper2) + (11655691/50000000000000 : ℝ)*(upper3) + (12461197/100000000000000 : ℝ)*(upper4) + (4562691407180331/100000000000000 : ℝ)*(major0) + (4562691407180331/100000000000000 : ℝ)*(major1) + (4562691407180331/100000000000000 : ℝ)*(major2) + (64704165783/100000000000000 : ℝ)*(sp1) + (9086515117/100000000000000 : ℝ)*(sp2) + (6098360656314841/100000000000000 : ℝ)*(sp8) + (3049147976074529/50000000000000 : ℝ)*(sp9) + (6098351569799723/100000000000000 : ℝ)*(sp10) + (1500143046712699/50000000000000 : ℝ)*(sp11) + (1500143046712699/50000000000000 : ℝ)*(f.failure) + (6098360656314841/100000000000000 : ℝ)*(f.sum) + (63768835771511/13015000000000000000000000000 : ℝ)*base65 + (5379442473468602251/325375000000000000000000000000000 : ℝ)*base68 + (3130011118304602251/325375000000000000000000000000000 : ℝ)*base70 + (7634034607867772749/325375000000000000000000000000000 : ℝ)*base71 + (40032651465329/13015000000000000000000000000 : ℝ)*base74 + (2478062970272272749/325375000000000000000000000000000 : ℝ)*base75 + (2353959614328272749/325375000000000000000000000000000 : ℝ)*base77 + (4852341556130227251/325375000000000000000000000000000 : ℝ)*base80 + (278036774070821/13015000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (6804489/5000000000000000000000 : ℝ)*base89 + (6804489/5000000000000000000000 : ℝ)*base91 + (6804489/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41709/50000 : ℝ) ≤ (-27900061418133591113383512621/33447265625000000000000000000 : ℝ) := by norm_num
    linear_combination (48947427/100000000000000 : ℝ)*(upper1) + (17127501/20000000000000 : ℝ)*(upper3) + (53863623/25000000000000 : ℝ)*(upper5) + (1149605870433711/25000000000000 : ℝ)*(major0) + (1149605870433711/25000000000000 : ℝ)*(major1) + (1149605870433711/25000000000000 : ℝ)*(major2) + (42720080541/100000000000000 : ℝ)*(sp4) + (91644604827/20000000000000 : ℝ)*(sp5) + (380962047851/100000000000000 : ℝ)*(sp6) + (77389977761/25000000000000 : ℝ)*(sp7) + (1937758392839/31250000000 : ℝ)*(sp12) + (3100205677070603/50000000000000 : ℝ)*(sp13) + (620048861511749/10000000000000 : ℝ)*(sp14) + (151173642555293/5000000000000 : ℝ)*(sp15) + (377972801377113/12500000000000 : ℝ)*(f.failure) + (6200869577165341/100000000000000 : ℝ)*(f.sum) + (4221489811777/6507500000000000000000000000 : ℝ)*base65 + (40594012631335981/81343750000000000000000000000000 : ℝ)*base68 + (674914517457398481/81343750000000000000000000000000 : ℝ)*base70 + (95470503226007769/81343750000000000000000000000000 : ℝ)*base71 + (14105861347357/6507500000000000000000000000 : ℝ)*base73 + (7355719696268085981/81343750000000000000000000000000 : ℝ)*base76 + (67902274836898481/81343750000000000000000000000000 : ℝ)*base78 + (72495930963085981/81343750000000000000000000000000 : ℝ)*base80 + (721173817301959/13015000000000000000000000000 : ℝ)*base81 + (45843/1250000000000000000000 : ℝ)*base89 + (45843/1250000000000000000000 : ℝ)*base91 + (45843/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1274_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14851/25000 : ℝ) else (40103/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41709/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1274_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1274_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14851/25000 : ℝ) else (40103/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41709/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1274_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8467/2048 : ℝ) ≤ p) (hpb : p ≤ (2117/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152075211/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14851/25000 : ℝ) else (40103/50000 : ℝ) ≤ X j i ∧ X j i ≤ (41709/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1274_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
