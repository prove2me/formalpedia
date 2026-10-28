-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1255_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:25:29.23606+00:00
-- url     : https://prove2.me/submissions/a7564f20-3749-4513-82b1-ff983d351242

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
theorem support_rectangle_w1255_s3_0 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-527813211/2500000000 : ℝ)*x 0 + (84664467/156250000 : ℝ)*x 1 + (5241611057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527813211/2500000000 : ℝ)^33 ≤ (12834918840801/100000000000000 : ℝ)^25 := by
    have hnat : (527813211 : ℕ)^33*100000000000000^25 ≤ 12834918840801^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527813211 2500000000 12834918840801 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84664467/156250000 : ℝ)^33 ≤ (44537221687977/100000000000000 : ℝ)^25 := by
    have hnat : (84664467 : ℕ)^33*100000000000000^25 ≤ 44537221687977^25*156250000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84664467 156250000 44537221687977 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241611057/10000000000 : ℝ)^33 ≤ (8525571891889/20000000000000 : ℝ)^25 := by
    have hnat : (5241611057 : ℕ)^33*20000000000000^25 ≤ 8525571891889^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241611057 10000000000 8525571891889 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527813211/2500000000 : ℝ), (84664467/156250000 : ℝ), (5241611057/10000000000 : ℝ)] ![(12834918840801/100000000000000 : ℝ), (44537221687977/100000000000000 : ℝ), (8525571891889/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527813211/2500000000 : ℝ)|^33 ≤ (12834918840801/100000000000000 : ℝ)^25
        have hw : |(-527813211/2500000000 : ℝ)|=(527813211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84664467/156250000 : ℝ)|^33 ≤ (44537221687977/100000000000000 : ℝ)^25
        have hw : |(84664467/156250000 : ℝ)|=(84664467/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241611057/10000000000 : ℝ)|^33 ≤ (8525571891889/20000000000000 : ℝ)^25
        have hw : |(5241611057/10000000000 : ℝ)|=(5241611057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s3_1 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5351203439/10000000000 : ℝ)*x 0 + (-550370671/2500000000 : ℝ)*x 1 + (1048322231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351203439/10000000000 : ℝ)^33 ≤ (43808252527801/100000000000000 : ℝ)^25 := by
    have hnat : (5351203439 : ℕ)^33*100000000000000^25 ≤ 43808252527801^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351203439 10000000000 43808252527801 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550370671/2500000000 : ℝ)^33 ≤ (1356388695013/10000000000000 : ℝ)^25 := by
    have hnat : (550370671 : ℕ)^33*10000000000000^25 ≤ 1356388695013^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550370671 2500000000 1356388695013 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048322231/2000000000 : ℝ)^33 ≤ (42627860511477/100000000000000 : ℝ)^25 := by
    have hnat : (1048322231 : ℕ)^33*100000000000000^25 ≤ 42627860511477^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048322231 2000000000 42627860511477 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351203439/10000000000 : ℝ), (-550370671/2500000000 : ℝ), (1048322231/2000000000 : ℝ)] ![(43808252527801/100000000000000 : ℝ), (1356388695013/10000000000000 : ℝ), (42627860511477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351203439/10000000000 : ℝ)|^33 ≤ (43808252527801/100000000000000 : ℝ)^25
        have hw : |(5351203439/10000000000 : ℝ)|=(5351203439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550370671/2500000000 : ℝ)|^33 ≤ (1356388695013/10000000000000 : ℝ)^25
        have hw : |(-550370671/2500000000 : ℝ)|=(550370671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048322231/2000000000 : ℝ)|^33 ≤ (42627860511477/100000000000000 : ℝ)^25
        have hw : |(1048322231/2000000000 : ℝ)|=(1048322231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s3_2 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2675601701/5000000000 : ℝ)*x 0 + (41932893/80000000 : ℝ)*x 1 + (-17199079/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675601701/5000000000 : ℝ)^33 ≤ (43808252127967/100000000000000 : ℝ)^25 := by
    have hnat : (2675601701 : ℕ)^33*100000000000000^25 ≤ 43808252127967^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675601701 5000000000 43808252127967 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41932893/80000000 : ℝ)^33 ≤ (21313932778467/50000000000000 : ℝ)^25 := by
    have hnat : (41932893 : ℕ)^33*50000000000000^25 ≤ 21313932778467^25*80000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41932893 80000000 21313932778467 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17199079/78125000 : ℝ)^33 ≤ (678194114907/5000000000000 : ℝ)^25 := by
    have hnat : (17199079 : ℕ)^33*5000000000000^25 ≤ 678194114907^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17199079 78125000 678194114907 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675601701/5000000000 : ℝ), (41932893/80000000 : ℝ), (-17199079/78125000 : ℝ)] ![(43808252127967/100000000000000 : ℝ), (21313932778467/50000000000000 : ℝ), (678194114907/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675601701/5000000000 : ℝ)|^33 ≤ (43808252127967/100000000000000 : ℝ)^25
        have hw : |(2675601701/5000000000 : ℝ)|=(2675601701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41932893/80000000 : ℝ)|^33 ≤ (21313932778467/50000000000000 : ℝ)^25
        have hw : |(41932893/80000000 : ℝ)|=(41932893/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17199079/78125000 : ℝ)|^33 ≤ (678194114907/5000000000000 : ℝ)^25
        have hw : |(-17199079/78125000 : ℝ)|=(17199079/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s3_3 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2173678447/5000000000 : ℝ)*x 0 + (4171069409/10000000000 : ℝ)*x 1 + (4530853/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173678447/5000000000 : ℝ)^33 ≤ (33301008740849/100000000000000 : ℝ)^25 := by
    have hnat : (2173678447 : ℕ)^33*100000000000000^25 ≤ 33301008740849^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173678447 5000000000 33301008740849 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171069409/10000000000 : ℝ)^33 ≤ (31530190173971/100000000000000 : ℝ)^25 := by
    have hnat : (4171069409 : ℕ)^33*100000000000000^25 ≤ 31530190173971^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171069409 10000000000 31530190173971 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530853/10000000 : ℝ)^33 ≤ (17584400533631/50000000000000 : ℝ)^25 := by
    have hnat : (4530853 : ℕ)^33*50000000000000^25 ≤ 17584400533631^25*10000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530853 10000000 17584400533631 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173678447/5000000000 : ℝ), (4171069409/10000000000 : ℝ), (4530853/10000000 : ℝ)] ![(33301008740849/100000000000000 : ℝ), (31530190173971/100000000000000 : ℝ), (17584400533631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173678447/5000000000 : ℝ)|^33 ≤ (33301008740849/100000000000000 : ℝ)^25
        have hw : |(2173678447/5000000000 : ℝ)|=(2173678447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171069409/10000000000 : ℝ)|^33 ≤ (31530190173971/100000000000000 : ℝ)^25
        have hw : |(4171069409/10000000000 : ℝ)|=(4171069409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530853/10000000 : ℝ)|^33 ≤ (17584400533631/50000000000000 : ℝ)^25
        have hw : |(4530853/10000000 : ℝ)|=(4530853/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s3_4 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2111266991/10000000000 : ℝ)*x 0 + (5242248843/10000000000 : ℝ)*x 1 + (5417884353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111266991/10000000000 : ℝ)^33 ≤ (1604379045729/12500000000000 : ℝ)^25 := by
    have hnat : (2111266991 : ℕ)^33*12500000000000^25 ≤ 1604379045729^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111266991 10000000000 1604379045729 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242248843/10000000000 : ℝ)^33 ≤ (42634706235153/100000000000000 : ℝ)^25 := by
    have hnat : (5242248843 : ℕ)^33*100000000000000^25 ≤ 42634706235153^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242248843 10000000000 42634706235153 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417884353/10000000000 : ℝ)^33 ≤ (44530261386873/100000000000000 : ℝ)^25 := by
    have hnat : (5417884353 : ℕ)^33*100000000000000^25 ≤ 44530261386873^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417884353 10000000000 44530261386873 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2111266991/10000000000 : ℝ), (5242248843/10000000000 : ℝ), (5417884353/10000000000 : ℝ)] ![(1604379045729/12500000000000 : ℝ), (42634706235153/100000000000000 : ℝ), (44530261386873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2111266991/10000000000 : ℝ)|^33 ≤ (1604379045729/12500000000000 : ℝ)^25
        have hw : |(-2111266991/10000000000 : ℝ)|=(2111266991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242248843/10000000000 : ℝ)|^33 ≤ (42634706235153/100000000000000 : ℝ)^25
        have hw : |(5242248843/10000000000 : ℝ)|=(5242248843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417884353/10000000000 : ℝ)|^33 ≤ (44530261386873/100000000000000 : ℝ)^25
        have hw : |(5417884353/10000000000 : ℝ)|=(5417884353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s3_5 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (41453357/78125000 : ℝ)*x 0 + (-25315111/125000000 : ℝ)*x 1 + (169308881/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41453357/78125000 : ℝ)^33 ≤ (43320750579591/100000000000000 : ℝ)^25 := by
    have hnat : (41453357 : ℕ)^33*100000000000000^25 ≤ 43320750579591^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41453357 78125000 43320750579591 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25315111/125000000 : ℝ)^33 ≤ (3037247442313/25000000000000 : ℝ)^25 := by
    have hnat : (25315111 : ℕ)^33*25000000000000^25 ≤ 3037247442313^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25315111 125000000 3037247442313 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169308881/312500000 : ℝ)^33 ≤ (8906051928029/20000000000000 : ℝ)^25 := by
    have hnat : (169308881 : ℕ)^33*20000000000000^25 ≤ 8906051928029^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169308881 312500000 8906051928029 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41453357/78125000 : ℝ), (-25315111/125000000 : ℝ), (169308881/312500000 : ℝ)] ![(43320750579591/100000000000000 : ℝ), (3037247442313/25000000000000 : ℝ), (8906051928029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41453357/78125000 : ℝ)|^33 ≤ (43320750579591/100000000000000 : ℝ)^25
        have hw : |(41453357/78125000 : ℝ)|=(41453357/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25315111/125000000 : ℝ)|^33 ≤ (3037247442313/25000000000000 : ℝ)^25
        have hw : |(-25315111/125000000 : ℝ)|=(25315111/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169308881/312500000 : ℝ)|^33 ≤ (8906051928029/20000000000000 : ℝ)^25
        have hw : |(169308881/312500000 : ℝ)|=(169308881/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s3_6 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5306029047/10000000000 : ℝ)*x 0 + (5417884653/10000000000 : ℝ)*x 1 + (-506302283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5306029047/10000000000 : ℝ)^33 ≤ (16922165463/39062500000 : ℝ)^25 := by
    have hnat : (5306029047 : ℕ)^33*39062500000^25 ≤ 16922165463^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306029047 10000000000 16922165463 39062500000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417884653/10000000000 : ℝ)^33 ≤ (22265132320823/50000000000000 : ℝ)^25 := by
    have hnat : (5417884653 : ℕ)^33*50000000000000^25 ≤ 22265132320823^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417884653 10000000000 22265132320823 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506302283/2500000000 : ℝ)^33 ≤ (151862397059/1250000000000 : ℝ)^25 := by
    have hnat : (506302283 : ℕ)^33*1250000000000^25 ≤ 151862397059^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506302283 2500000000 151862397059 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5306029047/10000000000 : ℝ), (5417884653/10000000000 : ℝ), (-506302283/2500000000 : ℝ)] ![(16922165463/39062500000 : ℝ), (22265132320823/50000000000000 : ℝ), (151862397059/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5306029047/10000000000 : ℝ)|^33 ≤ (16922165463/39062500000 : ℝ)^25
        have hw : |(5306029047/10000000000 : ℝ)|=(5306029047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417884653/10000000000 : ℝ)|^33 ≤ (22265132320823/50000000000000 : ℝ)^25
        have hw : |(5417884653/10000000000 : ℝ)|=(5417884653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506302283/2500000000 : ℝ)|^33 ≤ (151862397059/1250000000000 : ℝ)^25
        have hw : |(-506302283/2500000000 : ℝ)|=(506302283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s3_7 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4347385189/10000000000 : ℝ)*x 0 + (4529555171/10000000000 : ℝ)*x 1 + (208618663/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4347385189/10000000000 : ℝ)^33 ≤ (33301294839741/100000000000000 : ℝ)^25 := by
    have hnat : (4347385189 : ℕ)^33*100000000000000^25 ≤ 33301294839741^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4347385189 10000000000 33301294839741 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529555171/10000000000 : ℝ)^33 ≤ (3515550420743/10000000000000 : ℝ)^25 := by
    have hnat : (4529555171 : ℕ)^33*10000000000000^25 ≤ 3515550420743^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529555171 10000000000 3515550420743 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208618663/500000000 : ℝ)^33 ≤ (7885800234409/25000000000000 : ℝ)^25 := by
    have hnat : (208618663 : ℕ)^33*25000000000000^25 ≤ 7885800234409^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208618663 500000000 7885800234409 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4347385189/10000000000 : ℝ), (4529555171/10000000000 : ℝ), (208618663/500000000 : ℝ)] ![(33301294839741/100000000000000 : ℝ), (3515550420743/10000000000000 : ℝ), (7885800234409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4347385189/10000000000 : ℝ)|^33 ≤ (33301294839741/100000000000000 : ℝ)^25
        have hw : |(4347385189/10000000000 : ℝ)|=(4347385189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529555171/10000000000 : ℝ)|^33 ≤ (3515550420743/10000000000000 : ℝ)^25
        have hw : |(4529555171/10000000000 : ℝ)|=(4529555171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208618663/500000000 : ℝ)|^33 ≤ (7885800234409/25000000000000 : ℝ)^25
        have hw : |(208618663/500000000 : ℝ)|=(208618663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1255_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (597/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (342/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14689/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (597/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (597/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (597/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (597/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (597/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (597/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (597/6250 : ℝ) ^ (8447/2048 : ℝ) ≤ (776778252661243/12500000000000000000 : ℝ) := by
    have hpowers : (597/6250 : ℝ)^8447 ≤ (776778252661243/12500000000000000000 : ℝ)^2048 := by
      have hnat : (597 : ℕ)^8447*12500000000000000000^2048 ≤ 776778252661243^2048*6250^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        597 6250 776778252661243 12500000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (597/6250 : ℝ)) (X := (776778252661243/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16189/100000 : ℝ) ^ (8447/2048 : ℝ) ≤ (10950872280681579/20000000000000000000 : ℝ) := by
    have hpowers : (16189/100000 : ℝ)^8447 ≤ (10950872280681579/20000000000000000000 : ℝ)^2048 := by
      have hnat : (16189 : ℕ)^8447*20000000000000000000^2048 ≤ 10950872280681579^2048*100000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16189 100000 10950872280681579 20000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16189/100000 : ℝ)) (X := (10950872280681579/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250776778252661243/6250000000000000000 : ℝ) ≤ (156254708082683/156250000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (6250776778252661243/6250000000000000000 : ℝ)^2048 ≤ (156254708082683/156250000000000 : ℝ)^8447 := by
      have hnat : (6250776778252661243 : ℕ)^2048*156250000000000^8447 ≤ 156254708082683^8447*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250776778252661243 6250000000000000000 156254708082683 156250000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156254708082683/156250000000000 : ℝ)) (X := (6250776778252661243/6250000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100060968587424697839/100000000000000000000 : ℝ) ≤ (10001477860094897/10000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (100060968587424697839/100000000000000000000 : ℝ)^2048 ≤ (10001477860094897/10000000000000000 : ℝ)^8447 := by
      have hnat : (100060968587424697839 : ℕ)^2048*10000000000000000^8447 ≤ 10001477860094897^8447*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100060968587424697839 100000000000000000000 10001477860094897 10000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001477860094897/10000000000000000 : ℝ)) (X := (100060968587424697839/100000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10010950872280681579/10000000000000000000 : ℝ) ≤ (5001327201449041/5000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (10010950872280681579/10000000000000000000 : ℝ)^2048 ≤ (5001327201449041/5000000000000000 : ℝ)^8447 := by
      have hnat : (10010950872280681579 : ℕ)^2048*5000000000000000^8447 ≤ 5001327201449041^8447*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10010950872280681579 10000000000000000000 5001327201449041 5000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001327201449041/5000000000000000 : ℝ)) (X := (10010950872280681579/10000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(776778252661243/12500000000000000000 : ℝ) ≤ ((2073422599036032697/2074062500000000000 : ℝ)+2*(235308560637/132740000000000 : ℝ)*(597/6250 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (2073422599036032697/2074062500000000000 : ℝ)+2*(235308560637/132740000000000 : ℝ)*(597/6250 : ℝ)=(156254708082683/156250000000000 : ℝ) by norm_num, show 1+2*(776778252661243/12500000000000000000 : ℝ)=(6250776778252661243/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10950872280681579/20000000000000000000 : ℝ)+(776778252661243/12500000000000000000 : ℝ) ≤ ((2073422599036032697/2074062500000000000 : ℝ)+(235308560637/132740000000000 : ℝ)*((16189/100000 : ℝ)+(597/6250 : ℝ)))^(8447/2048 : ℝ) := by
    rw [show (2073422599036032697/2074062500000000000 : ℝ)+(235308560637/132740000000000 : ℝ)*((16189/100000 : ℝ)+(597/6250 : ℝ))=(10001477860094897/10000000000000000 : ℝ) by norm_num, show 1+(10950872280681579/20000000000000000000 : ℝ)+(776778252661243/12500000000000000000 : ℝ)=(100060968587424697839/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10950872280681579/20000000000000000000 : ℝ) ≤ ((2073422599036032697/2074062500000000000 : ℝ)+2*(235308560637/132740000000000 : ℝ)*(16189/100000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (2073422599036032697/2074062500000000000 : ℝ)+2*(235308560637/132740000000000 : ℝ)*(16189/100000 : ℝ)=(5001327201449041/5000000000000000 : ℝ) by norm_num, show 1+2*(10950872280681579/20000000000000000000 : ℝ)=(10010950872280681579/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2073422599036032697/2074062500000000000 : ℝ)*(X 1 0+X 2 0)+(235308560637/132740000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (597/6250 : ℝ)) (hi := (16189/100000 : ℝ)) (c := (2073422599036032697/2074062500000000000 : ℝ)) (alpha := (235308560637/132740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2073422599036032697/2074062500000000000 : ℝ)*(X 0 1+X 2 1)+(235308560637/132740000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (597/6250 : ℝ)) (hi := (16189/100000 : ℝ)) (c := (2073422599036032697/2074062500000000000 : ℝ)) (alpha := (235308560637/132740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2073422599036032697/2074062500000000000 : ℝ)*(X 0 2+X 1 2)+(235308560637/132740000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (597/6250 : ℝ)) (hi := (16189/100000 : ℝ)) (c := (2073422599036032697/2074062500000000000 : ℝ)) (alpha := (235308560637/132740000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527813211/2500000000 : ℝ)*X 0 0+(84664467/156250000 : ℝ)*X 0 1+(5241611057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351203439/10000000000 : ℝ)*X 1 0+(-550370671/2500000000 : ℝ)*X 1 1+(1048322231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675601701/5000000000 : ℝ)*X 2 0+(41932893/80000000 : ℝ)*X 2 1+(-17199079/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173678447/5000000000 : ℝ)*X 0 0+(4171069409/10000000000 : ℝ)*X 0 1+(4530853/10000000 : ℝ)*X 0 2+(2173678447/5000000000 : ℝ)*X 1 0+(4171069409/10000000000 : ℝ)*X 1 1+(4530853/10000000 : ℝ)*X 1 2+(2173678447/5000000000 : ℝ)*X 2 0+(4171069409/10000000000 : ℝ)*X 2 1+(4530853/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2111266991/10000000000 : ℝ)*X 0 0+(5242248843/10000000000 : ℝ)*X 0 1+(5417884353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((41453357/78125000 : ℝ)*X 1 0+(-25315111/125000000 : ℝ)*X 1 1+(169308881/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5306029047/10000000000 : ℝ)*X 2 0+(5417884653/10000000000 : ℝ)*X 2 1+(-506302283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4347385189/10000000000 : ℝ)*X 0 0+(4529555171/10000000000 : ℝ)*X 0 1+(208618663/500000000 : ℝ)*X 0 2+(4347385189/10000000000 : ℝ)*X 1 0+(4529555171/10000000000 : ℝ)*X 1 1+(208618663/500000000 : ℝ)*X 1 2+(4347385189/10000000000 : ℝ)*X 2 0+(4529555171/10000000000 : ℝ)*X 2 1+(208618663/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (237711513010959165597017229/25925781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1271431417/100000000000000 : ℝ)*(base19) + (821599627/100000000000000 : ℝ)*(base23) + (247004123/100000000000000 : ℝ)*(lower2) + (1300543/1250000000000 : ℝ)*(upper5) + (2107997316611413/50000000000000 : ℝ)*(major0) + (2107997316611413/50000000000000 : ℝ)*(major1) + (2107997316611413/50000000000000 : ℝ)*(major2) + (9043954506669/160000000000 : ℝ)*(sp0) + (5652507759277739/100000000000000 : ℝ)*(sp1) + (5652514231254621/100000000000000 : ℝ)*(sp2) + (694865253453847/25000000000000 : ℝ)*(sp3) + (10871546531/25000000000000 : ℝ)*(sp4) + (6022145091/100000000000000 : ℝ)*(sp5) + (6447072607/50000000000000 : ℝ)*(sp7) + (1389736953980301/50000000000000 : ℝ)*(f.failure) + (706564381606781/12500000000000 : ℝ)*(f.sum) + (5377561652051/1659250000000000000000000000 : ℝ)*base65 + (411348693800223691/25925781250000000000000000000000 : ℝ)*base68 + (673517680622816639/103703125000000000000000000000000 : ℝ)*base70 + (37627699743222889/103703125000000000000000000000000 : ℝ)*base72 + (6795490345481/829625000000000000000000000 : ℝ)*base74 + (1148535428057808361/103703125000000000000000000000000 : ℝ)*base75 + (281382586080556757/51851562500000000000000000000000 : ℝ)*base78 + (270002504271902111/103703125000000000000000000000000 : ℝ)*base79 + (2997757371053/3318500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (11219897/1250000000000000000000 : ℝ)*base89 + (11219897/1250000000000000000000 : ℝ)*base91 + (11219897/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (387590851089653993698123581/103703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1222315283/50000000000000 : ℝ)*(base19) + (43087567/2500000000000 : ℝ)*(base23) + (10931679/100000000000000 : ℝ)*(upper3) + (77080163/100000000000000 : ℝ)*(lower4) + (415536117/100000000000000 : ℝ)*(upper5) + (2123325178836211/50000000000000 : ℝ)*(major0) + (2123325178836211/50000000000000 : ℝ)*(major1) + (2123325178836211/50000000000000 : ℝ)*(major2) + (1803947073/3125000000000 : ℝ)*(sp1) + (18879534577/50000000000000 : ℝ)*(sp2) + (5693616318782311/100000000000000 : ℝ)*(sp4) + (5693556147845409/100000000000000 : ℝ)*(sp5) + (5693576836210477/100000000000000 : ℝ)*(sp6) + (174980266998691/6250000000000 : ℝ)*(sp7) + (174980266998691/6250000000000 : ℝ)*(f.failure) + (5693616318782311/100000000000000 : ℝ)*(f.sum) + (3290560725843/6637000000000000000000000000 : ℝ)*base65 + (1094680526601190183/103703125000000000000000000000000 : ℝ)*base68 + (868276651622721433/103703125000000000000000000000000 : ℝ)*base70 + (77074695128024779/51851562500000000000000000000000 : ℝ)*base72 + (5715509012917/663700000000000000000000000 : ℝ)*base74 + (1016201816745149779/51851562500000000000000000000000 : ℝ)*base76 + (471878359619846433/103703125000000000000000000000000 : ℝ)*base78 + (1695412876592533933/103703125000000000000000000000000 : ℝ)*base80 + (12614953901069/3318500000000000000000000000 : ℝ)*base81 + (1301727/156250000000000000000 : ℝ)*base89 + (1301727/156250000000000000000 : ℝ)*base91 + (1301727/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1255_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (597/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (342/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1255_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1255_s4_0 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-528366353/2500000000 : ℝ)*x 0 + (1349243753/2500000000 : ℝ)*x 1 + (5261711657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528366353/2500000000 : ℝ)^33 ≤ (2570535386021/20000000000000 : ℝ)^25 := by
    have hnat : (528366353 : ℕ)^33*20000000000000^25 ≤ 2570535386021^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528366353 2500000000 2570535386021 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349243753/2500000000 : ℝ)^33 ≤ (44303551061881/100000000000000 : ℝ)^25 := by
    have hnat : (1349243753 : ℕ)^33*100000000000000^25 ≤ 44303551061881^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349243753 2500000000 44303551061881 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5261711657/10000000000 : ℝ)^33 ≤ (42843771987841/100000000000000 : ℝ)^25 := by
    have hnat : (5261711657 : ℕ)^33*100000000000000^25 ≤ 42843771987841^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261711657 10000000000 42843771987841 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528366353/2500000000 : ℝ), (1349243753/2500000000 : ℝ), (5261711657/10000000000 : ℝ)] ![(2570535386021/20000000000000 : ℝ), (44303551061881/100000000000000 : ℝ), (42843771987841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528366353/2500000000 : ℝ)|^33 ≤ (2570535386021/20000000000000 : ℝ)^25
        have hw : |(-528366353/2500000000 : ℝ)|=(528366353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349243753/2500000000 : ℝ)|^33 ≤ (44303551061881/100000000000000 : ℝ)^25
        have hw : |(1349243753/2500000000 : ℝ)|=(1349243753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5261711657/10000000000 : ℝ)|^33 ≤ (42843771987841/100000000000000 : ℝ)^25
        have hw : |(5261711657/10000000000 : ℝ)|=(5261711657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s4_1 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1336441019/2500000000 : ℝ)*x 0 + (-136383349/625000000 : ℝ)*x 1 + (526171167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336441019/2500000000 : ℝ)^33 ≤ (43749482514651/100000000000000 : ℝ)^25 := by
    have hnat : (1336441019 : ℕ)^33*100000000000000^25 ≤ 43749482514651^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336441019 2500000000 43749482514651 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136383349/625000000 : ℝ)^33 ≤ (6703372668971/50000000000000 : ℝ)^25 := by
    have hnat : (136383349 : ℕ)^33*50000000000000^25 ≤ 6703372668971^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136383349 625000000 6703372668971 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526171167/1000000000 : ℝ)^33 ≤ (42843772127567/100000000000000 : ℝ)^25 := by
    have hnat : (526171167 : ℕ)^33*100000000000000^25 ≤ 42843772127567^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526171167 1000000000 42843772127567 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336441019/2500000000 : ℝ), (-136383349/625000000 : ℝ), (526171167/1000000000 : ℝ)] ![(43749482514651/100000000000000 : ℝ), (6703372668971/50000000000000 : ℝ), (42843772127567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336441019/2500000000 : ℝ)|^33 ≤ (43749482514651/100000000000000 : ℝ)^25
        have hw : |(1336441019/2500000000 : ℝ)|=(1336441019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-136383349/625000000 : ℝ)|^33 ≤ (6703372668971/50000000000000 : ℝ)^25
        have hw : |(-136383349/625000000 : ℝ)|=(136383349/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526171167/1000000000 : ℝ)|^33 ≤ (42843772127567/100000000000000 : ℝ)^25
        have hw : |(526171167/1000000000 : ℝ)|=(526171167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s4_2 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2672882097/5000000000 : ℝ)*x 0 + (5261711569/10000000000 : ℝ)*x 1 + (-2182133561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672882097/5000000000 : ℝ)^33 ≤ (5468685473673/12500000000000 : ℝ)^25 := by
    have hnat : (2672882097 : ℕ)^33*12500000000000^25 ≤ 5468685473673^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672882097 5000000000 5468685473673 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261711569/10000000000 : ℝ)^33 ≤ (21421885521001/50000000000000 : ℝ)^25 := by
    have hnat : (5261711569 : ℕ)^33*50000000000000^25 ≤ 21421885521001^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261711569 10000000000 21421885521001 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2182133561/10000000000 : ℝ)^33 ≤ (2681349030283/20000000000000 : ℝ)^25 := by
    have hnat : (2182133561 : ℕ)^33*20000000000000^25 ≤ 2681349030283^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182133561 10000000000 2681349030283 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672882097/5000000000 : ℝ), (5261711569/10000000000 : ℝ), (-2182133561/10000000000 : ℝ)] ![(5468685473673/12500000000000 : ℝ), (21421885521001/50000000000000 : ℝ), (2681349030283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672882097/5000000000 : ℝ)|^33 ≤ (5468685473673/12500000000000 : ℝ)^25
        have hw : |(2672882097/5000000000 : ℝ)|=(2672882097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261711569/10000000000 : ℝ)|^33 ≤ (21421885521001/50000000000000 : ℝ)^25
        have hw : |(5261711569/10000000000 : ℝ)|=(5261711569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2182133561/10000000000 : ℝ)|^33 ≤ (2681349030283/20000000000000 : ℝ)^25
        have hw : |(-2182133561/10000000000 : ℝ)|=(2182133561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s4_3 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4348684237/10000000000 : ℝ)*x 0 + (2106626017/5000000000 : ℝ)*x 1 + (897666457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348684237/10000000000 : ℝ)^33 ≤ (8328607632433/25000000000000 : ℝ)^25 := by
    have hnat : (4348684237 : ℕ)^33*25000000000000^25 ≤ 8328607632433^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348684237 10000000000 8328607632433 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106626017/5000000000 : ℝ)^33 ≤ (31951777232161/100000000000000 : ℝ)^25 := by
    have hnat : (2106626017 : ℕ)^33*100000000000000^25 ≤ 31951777232161^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106626017 5000000000 31951777232161 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897666457/2000000000 : ℝ)^33 ≤ (34733792229703/100000000000000 : ℝ)^25 := by
    have hnat : (897666457 : ℕ)^33*100000000000000^25 ≤ 34733792229703^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897666457 2000000000 34733792229703 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348684237/10000000000 : ℝ), (2106626017/5000000000 : ℝ), (897666457/2000000000 : ℝ)] ![(8328607632433/25000000000000 : ℝ), (31951777232161/100000000000000 : ℝ), (34733792229703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348684237/10000000000 : ℝ)|^33 ≤ (8328607632433/25000000000000 : ℝ)^25
        have hw : |(4348684237/10000000000 : ℝ)|=(4348684237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2106626017/5000000000 : ℝ)|^33 ≤ (31951777232161/100000000000000 : ℝ)^25
        have hw : |(2106626017/5000000000 : ℝ)|=(2106626017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897666457/2000000000 : ℝ)|^33 ≤ (34733792229703/100000000000000 : ℝ)^25
        have hw : |(897666457/2000000000 : ℝ)|=(897666457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s4_4 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2113471269/10000000000 : ℝ)*x 0 + (5262085151/10000000000 : ℝ)*x 1 + (5396600193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2113471269/10000000000 : ℝ)^33 ≤ (6426361973167/50000000000000 : ℝ)^25 := by
    have hnat : (2113471269 : ℕ)^33*50000000000000^25 ≤ 6426361973167^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113471269 10000000000 6426361973167 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5262085151/10000000000 : ℝ)^33 ≤ (21423893205491/50000000000000 : ℝ)^25 := by
    have hnat : (5262085151 : ℕ)^33*50000000000000^25 ≤ 21423893205491^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262085151 10000000000 21423893205491 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396600193/10000000000 : ℝ)^33 ≤ (44299489633183/100000000000000 : ℝ)^25 := by
    have hnat : (5396600193 : ℕ)^33*100000000000000^25 ≤ 44299489633183^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396600193 10000000000 44299489633183 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2113471269/10000000000 : ℝ), (5262085151/10000000000 : ℝ), (5396600193/10000000000 : ℝ)] ![(6426361973167/50000000000000 : ℝ), (21423893205491/50000000000000 : ℝ), (44299489633183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2113471269/10000000000 : ℝ)|^33 ≤ (6426361973167/50000000000000 : ℝ)^25
        have hw : |(-2113471269/10000000000 : ℝ)|=(2113471269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5262085151/10000000000 : ℝ)|^33 ≤ (21423893205491/50000000000000 : ℝ)^25
        have hw : |(5262085151/10000000000 : ℝ)|=(5262085151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396600193/10000000000 : ℝ)|^33 ≤ (44299489633183/100000000000000 : ℝ)^25
        have hw : |(5396600193/10000000000 : ℝ)|=(5396600193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s4_5 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1062244541/2000000000 : ℝ)*x 0 + (-15994101/78125000 : ℝ)*x 1 + (5396600179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062244541/2000000000 : ℝ)^33 ≤ (542209058769/1250000000000 : ℝ)^25 := by
    have hnat : (1062244541 : ℕ)^33*1250000000000^25 ≤ 542209058769^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062244541 2000000000 542209058769 1250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15994101/78125000 : ℝ)^33 ≤ (6161892897603/50000000000000 : ℝ)^25 := by
    have hnat : (15994101 : ℕ)^33*50000000000000^25 ≤ 6161892897603^25*78125000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15994101 78125000 6161892897603 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396600179/10000000000 : ℝ)^33 ≤ (8859897896297/20000000000000 : ℝ)^25 := by
    have hnat : (5396600179 : ℕ)^33*20000000000000^25 ≤ 8859897896297^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396600179 10000000000 8859897896297 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062244541/2000000000 : ℝ), (-15994101/78125000 : ℝ), (5396600179/10000000000 : ℝ)] ![(542209058769/1250000000000 : ℝ), (6161892897603/50000000000000 : ℝ), (8859897896297/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062244541/2000000000 : ℝ)|^33 ≤ (542209058769/1250000000000 : ℝ)^25
        have hw : |(1062244541/2000000000 : ℝ)|=(1062244541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15994101/78125000 : ℝ)|^33 ≤ (6161892897603/50000000000000 : ℝ)^25
        have hw : |(-15994101/78125000 : ℝ)|=(15994101/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396600179/10000000000 : ℝ)|^33 ≤ (8859897896297/20000000000000 : ℝ)^25
        have hw : |(5396600179/10000000000 : ℝ)|=(5396600179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s4_6 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1327805617/2500000000 : ℝ)*x 0 + (5396600407/10000000000 : ℝ)*x 1 + (-102362247/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327805617/2500000000 : ℝ)^33 ≤ (43376722146557/100000000000000 : ℝ)^25 := by
    have hnat : (1327805617 : ℕ)^33*100000000000000^25 ≤ 43376722146557^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327805617 2500000000 43376722146557 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396600407/10000000000 : ℝ)^33 ≤ (44299491951999/100000000000000 : ℝ)^25 := by
    have hnat : (5396600407 : ℕ)^33*100000000000000^25 ≤ 44299491951999^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396600407 10000000000 44299491951999 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102362247/500000000 : ℝ)^33 ≤ (6161892945279/50000000000000 : ℝ)^25 := by
    have hnat : (102362247 : ℕ)^33*50000000000000^25 ≤ 6161892945279^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102362247 500000000 6161892945279 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327805617/2500000000 : ℝ), (5396600407/10000000000 : ℝ), (-102362247/500000000 : ℝ)] ![(43376722146557/100000000000000 : ℝ), (44299491951999/100000000000000 : ℝ), (6161892945279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327805617/2500000000 : ℝ)|^33 ≤ (43376722146557/100000000000000 : ℝ)^25
        have hw : |(1327805617/2500000000 : ℝ)|=(1327805617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396600407/10000000000 : ℝ)|^33 ≤ (44299491951999/100000000000000 : ℝ)^25
        have hw : |(5396600407/10000000000 : ℝ)|=(5396600407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102362247/500000000 : ℝ)|^33 ≤ (6161892945279/50000000000000 : ℝ)^25
        have hw : |(-102362247/500000000 : ℝ)|=(102362247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s4_7 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1087174097/2500000000 : ℝ)*x 0 + (112189329/250000000 : ℝ)*x 1 + (2107007181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087174097/2500000000 : ℝ)^33 ≤ (33314553403921/100000000000000 : ℝ)^25 := by
    have hnat : (1087174097 : ℕ)^33*100000000000000^25 ≤ 33314553403921^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087174097 2500000000 33314553403921 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112189329/250000000 : ℝ)^33 ≤ (34726037928389/100000000000000 : ℝ)^25 := by
    have hnat : (112189329 : ℕ)^33*100000000000000^25 ≤ 34726037928389^25*250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112189329 250000000 34726037928389 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107007181/5000000000 : ℝ)^33 ≤ (31959408662693/100000000000000 : ℝ)^25 := by
    have hnat : (2107007181 : ℕ)^33*100000000000000^25 ≤ 31959408662693^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107007181 5000000000 31959408662693 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087174097/2500000000 : ℝ), (112189329/250000000 : ℝ), (2107007181/5000000000 : ℝ)] ![(33314553403921/100000000000000 : ℝ), (34726037928389/100000000000000 : ℝ), (31959408662693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087174097/2500000000 : ℝ)|^33 ≤ (33314553403921/100000000000000 : ℝ)^25
        have hw : |(1087174097/2500000000 : ℝ)|=(1087174097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112189329/250000000 : ℝ)|^33 ≤ (34726037928389/100000000000000 : ℝ)^25
        have hw : |(112189329/250000000 : ℝ)|=(112189329/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2107007181/5000000000 : ℝ)|^33 ≤ (31959408662693/100000000000000 : ℝ)^25
        have hw : |(2107007181/5000000000 : ℝ)|=(2107007181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1255_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (342/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11373/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7119/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (342/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (342/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (342/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (342/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (342/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (342/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (342/3125 : ℝ) ^ (8447/2048 : ℝ) ≤ (680691798149989/6250000000000000000 : ℝ) := by
    have hpowers : (342/3125 : ℝ)^8447 ≤ (680691798149989/6250000000000000000 : ℝ)^2048 := by
      have hnat : (342 : ℕ)^8447*6250000000000000000^2048 ≤ 680691798149989^2048*3125^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        342 3125 680691798149989 6250000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (342/3125 : ℝ)) (X := (680691798149989/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14689/100000 : ℝ) ^ (8447/2048 : ℝ) ≤ (36664831566966991/100000000000000000000 : ℝ) := by
    have hpowers : (14689/100000 : ℝ)^8447 ≤ (36664831566966991/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14689 : ℕ)^8447*100000000000000000000^2048 ≤ 36664831566966991^2048*100000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14689 100000 36664831566966991 100000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14689/100000 : ℝ)) (X := (36664831566966991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125680691798149989/3125000000000000000 : ℝ) ≤ (10000528070766207/10000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (3125680691798149989/3125000000000000000 : ℝ)^2048 ≤ (10000528070766207/10000000000000000 : ℝ)^8447 := by
      have hnat : (3125680691798149989 : ℕ)^2048*10000000000000000^8447 ≤ 10000528070766207^8447*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125680691798149989 3125000000000000000 10000528070766207 10000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000528070766207/10000000000000000 : ℝ)) (X := (3125680691798149989/3125000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009511180067473363/20000000000000000000 : ℝ) ≤ (5000576399580859/5000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (20009511180067473363/20000000000000000000 : ℝ)^2048 ≤ (5000576399580859/5000000000000000 : ℝ)^8447 := by
      have hnat : (20009511180067473363 : ℕ)^2048*5000000000000000^8447 ≤ 5000576399580859^8447*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009511180067473363 20000000000000000000 5000576399580859 5000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000576399580859/5000000000000000 : ℝ)) (X := (20009511180067473363/20000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036664831566966991/50000000000000000000 : ℝ) ≤ (10001777527557229/10000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (50036664831566966991/50000000000000000000 : ℝ)^2048 ≤ (10001777527557229/10000000000000000 : ℝ)^8447 := by
      have hnat : (50036664831566966991 : ℕ)^2048*10000000000000000^8447 ≤ 10001777527557229^8447*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036664831566966991 50000000000000000000 10001777527557229 10000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001777527557229/10000000000000000 : ℝ)) (X := (50036664831566966991/50000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(680691798149989/6250000000000000000 : ℝ) ≤ ((37438303569898500447/37450000000000000000 : ℝ)+2*(624728395511/374500000000000 : ℝ)*(342/3125 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (37438303569898500447/37450000000000000000 : ℝ)+2*(624728395511/374500000000000 : ℝ)*(342/3125 : ℝ)=(10000528070766207/10000000000000000 : ℝ) by norm_num, show 1+2*(680691798149989/6250000000000000000 : ℝ)=(3125680691798149989/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36664831566966991/100000000000000000000 : ℝ)+(680691798149989/6250000000000000000 : ℝ) ≤ ((37438303569898500447/37450000000000000000 : ℝ)+(624728395511/374500000000000 : ℝ)*((14689/100000 : ℝ)+(342/3125 : ℝ)))^(8447/2048 : ℝ) := by
    rw [show (37438303569898500447/37450000000000000000 : ℝ)+(624728395511/374500000000000 : ℝ)*((14689/100000 : ℝ)+(342/3125 : ℝ))=(5000576399580859/5000000000000000 : ℝ) by norm_num, show 1+(36664831566966991/100000000000000000000 : ℝ)+(680691798149989/6250000000000000000 : ℝ)=(20009511180067473363/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36664831566966991/100000000000000000000 : ℝ) ≤ ((37438303569898500447/37450000000000000000 : ℝ)+2*(624728395511/374500000000000 : ℝ)*(14689/100000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (37438303569898500447/37450000000000000000 : ℝ)+2*(624728395511/374500000000000 : ℝ)*(14689/100000 : ℝ)=(10001777527557229/10000000000000000 : ℝ) by norm_num, show 1+2*(36664831566966991/100000000000000000000 : ℝ)=(50036664831566966991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37438303569898500447/37450000000000000000 : ℝ)*(X 1 0+X 2 0)+(624728395511/374500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (342/3125 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (37438303569898500447/37450000000000000000 : ℝ)) (alpha := (624728395511/374500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37438303569898500447/37450000000000000000 : ℝ)*(X 0 1+X 2 1)+(624728395511/374500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (342/3125 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (37438303569898500447/37450000000000000000 : ℝ)) (alpha := (624728395511/374500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37438303569898500447/37450000000000000000 : ℝ)*(X 0 2+X 1 2)+(624728395511/374500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (342/3125 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (37438303569898500447/37450000000000000000 : ℝ)) (alpha := (624728395511/374500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-528366353/2500000000 : ℝ)*X 0 0+(1349243753/2500000000 : ℝ)*X 0 1+(5261711657/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336441019/2500000000 : ℝ)*X 1 0+(-136383349/625000000 : ℝ)*X 1 1+(526171167/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672882097/5000000000 : ℝ)*X 2 0+(5261711569/10000000000 : ℝ)*X 2 1+(-2182133561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348684237/10000000000 : ℝ)*X 0 0+(2106626017/5000000000 : ℝ)*X 0 1+(897666457/2000000000 : ℝ)*X 0 2+(4348684237/10000000000 : ℝ)*X 1 0+(2106626017/5000000000 : ℝ)*X 1 1+(897666457/2000000000 : ℝ)*X 1 2+(4348684237/10000000000 : ℝ)*X 2 0+(2106626017/5000000000 : ℝ)*X 2 1+(897666457/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2113471269/10000000000 : ℝ)*X 0 0+(5262085151/10000000000 : ℝ)*X 0 1+(5396600193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062244541/2000000000 : ℝ)*X 1 0+(-15994101/78125000 : ℝ)*X 1 1+(5396600179/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327805617/2500000000 : ℝ)*X 2 0+(5396600407/10000000000 : ℝ)*X 2 1+(-102362247/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087174097/2500000000 : ℝ)*X 0 0+(112189329/250000000 : ℝ)*X 0 1+(2107007181/5000000000 : ℝ)*X 0 2+(1087174097/2500000000 : ℝ)*X 1 0+(112189329/250000000 : ℝ)*X 1 1+(2107007181/5000000000 : ℝ)*X 1 2+(1087174097/2500000000 : ℝ)*X 2 0+(112189329/250000000 : ℝ)*X 2 1+(2107007181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4222228858082544078444545859/936250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1075957731/100000000000000 : ℝ)*(base19) + (42550441/4000000000000 : ℝ)*(base23) + (11792469/6250000000000 : ℝ)*(upper3) + (18751569/20000000000000 : ℝ)*(upper4) + (31833579/25000000000000 : ℝ)*(upper5) + (2757090019719199/50000000000000 : ℝ)*(major0) + (2757090019719199/50000000000000 : ℝ)*(major1) + (2757090019719199/50000000000000 : ℝ)*(major2) + (7393008308261487/100000000000000 : ℝ)*(sp0) + (1478606350528157/20000000000000 : ℝ)*(sp1) + (7393031764837491/100000000000000 : ℝ)*(sp2) + (3635313524545559/100000000000000 : ℝ)*(sp3) + (24520337029/100000000000000 : ℝ)*(sp4) + (13575408589/100000000000000 : ℝ)*(sp7) + (908831774988537/25000000000000 : ℝ)*(f.failure) + (1478606565719703/20000000000000 : ℝ)*(f.sum) + (57480962627/292578125000000000000000000 : ℝ)*base65 + (6855392604017618047/1872500000000000000000000000000000 : ℝ)*base68 + (9774284214967618047/1872500000000000000000000000000000 : ℝ)*base70 + (6671067834752618047/1872500000000000000000000000000000 : ℝ)*base72 + (1996185184757/4681250000000000000000000000 : ℝ)*base73 + (21919724947267381953/1872500000000000000000000000000000 : ℝ)*base75 + (27326910429517618047/1872500000000000000000000000000000 : ℝ)*base78 + (16583974138872381953/1872500000000000000000000000000000 : ℝ)*base79 + (1280308124491/2340625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1403989/625000000000000000000 : ℝ)*base89 + (1403989/625000000000000000000 : ℝ)*base91 + (1403989/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4043256537913446473575543131/468125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (662470103/50000000000000 : ℝ)*(base19) + (211856393/20000000000000 : ℝ)*(base23) + (48824467/25000000000000 : ℝ)*(upper3) + (11145413/50000000000000 : ℝ)*(lower4) + (56384113/100000000000000 : ℝ)*(upper5) + (2772406297582191/50000000000000 : ℝ)*(major0) + (2772406297582191/50000000000000 : ℝ)*(major1) + (2772406297582191/50000000000000 : ℝ)*(major2) + (14983386703/50000000000000 : ℝ)*(sp1) + (33672237277/100000000000000 : ℝ)*(sp2) + (1486820542573889/20000000000000 : ℝ)*(sp4) + (3717035710577917/50000000000000 : ℝ)*(sp5) + (1858516995337551/25000000000000 : ℝ)*(sp6) + (365552218955497/10000000000000 : ℝ)*(sp7) + (365552218955497/10000000000000 : ℝ)*(f.failure) + (1486820542573889/20000000000000 : ℝ)*(f.sum) + (67821307075673/18725000000000000000000000000 : ℝ)*base66 + (11348233762544660623/1872500000000000000000000000000000 : ℝ)*base68 + (23108405654719660623/1872500000000000000000000000000000 : ℝ)*base70 + (9006017643807839377/1872500000000000000000000000000000 : ℝ)*base71 + (19874913053599/9362500000000000000000000000 : ℝ)*base74 + (42350851220542160623/1872500000000000000000000000000000 : ℝ)*base76 + (1122090277732160623/1872500000000000000000000000000000 : ℝ)*base78 + (31353610775179660623/1872500000000000000000000000000000 : ℝ)*base80 + (52887807657527/18725000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1228891/250000000000000000000 : ℝ)*base90 + (1228891/250000000000000000000 : ℝ)*base92 + (1228891/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1255_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (342/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1255_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1255_s5_0 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056946557/5000000000 : ℝ)*x 0 + (67401241/125000000 : ℝ)*x 1 + (5266306357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056946557/5000000000 : ℝ)^33 ≤ (12856110356329/100000000000000 : ℝ)^25 := by
    have hnat : (1056946557 : ℕ)^33*100000000000000^25 ≤ 12856110356329^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056946557 5000000000 12856110356329 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67401241/125000000 : ℝ)^33 ≤ (4425072611193/10000000000000 : ℝ)^25 := by
    have hnat : (67401241 : ℕ)^33*10000000000000^25 ≤ 4425072611193^25*125000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67401241 125000000 4425072611193 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266306357/10000000000 : ℝ)^33 ≤ (21446581754867/50000000000000 : ℝ)^25 := by
    have hnat : (5266306357 : ℕ)^33*50000000000000^25 ≤ 21446581754867^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266306357 10000000000 21446581754867 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056946557/5000000000 : ℝ), (67401241/125000000 : ℝ), (5266306357/10000000000 : ℝ)] ![(12856110356329/100000000000000 : ℝ), (4425072611193/10000000000000 : ℝ), (21446581754867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056946557/5000000000 : ℝ)|^33 ≤ (12856110356329/100000000000000 : ℝ)^25
        have hw : |(-1056946557/5000000000 : ℝ)|=(1056946557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67401241/125000000 : ℝ)|^33 ≤ (4425072611193/10000000000000 : ℝ)^25
        have hw : |(67401241/125000000 : ℝ)|=(67401241/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266306357/10000000000 : ℝ)|^33 ≤ (21446581754867/50000000000000 : ℝ)^25
        have hw : |(5266306357/10000000000 : ℝ)|=(5266306357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s5_1 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2672264819/5000000000 : ℝ)*x 0 + (-108884307/500000000 : ℝ)*x 1 + (526630637/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672264819/5000000000 : ℝ)^33 ≤ (43736147598211/100000000000000 : ℝ)^25 := by
    have hnat : (2672264819 : ℕ)^33*100000000000000^25 ≤ 43736147598211^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672264819 5000000000 43736147598211 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108884307/500000000 : ℝ)^33 ≤ (2674137748207/20000000000000 : ℝ)^25 := by
    have hnat : (108884307 : ℕ)^33*20000000000000^25 ≤ 2674137748207^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108884307 500000000 2674137748207 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526630637/1000000000 : ℝ)^33 ≤ (85786327299/200000000000 : ℝ)^25 := by
    have hnat : (526630637 : ℕ)^33*200000000000^25 ≤ 85786327299^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526630637 1000000000 85786327299 200000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672264819/5000000000 : ℝ), (-108884307/500000000 : ℝ), (526630637/1000000000 : ℝ)] ![(43736147598211/100000000000000 : ℝ), (2674137748207/20000000000000 : ℝ), (85786327299/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672264819/5000000000 : ℝ)|^33 ≤ (43736147598211/100000000000000 : ℝ)^25
        have hw : |(2672264819/5000000000 : ℝ)|=(2672264819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108884307/500000000 : ℝ)|^33 ≤ (2674137748207/20000000000000 : ℝ)^25
        have hw : |(-108884307/500000000 : ℝ)|=(108884307/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526630637/1000000000 : ℝ)|^33 ≤ (85786327299/200000000000 : ℝ)^25
        have hw : |(526630637/1000000000 : ℝ)|=(526630637/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s5_2 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2672264833/5000000000 : ℝ)*x 0 + (5266306377/10000000000 : ℝ)*x 1 + (-1088843047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672264833/5000000000 : ℝ)^33 ≤ (43736147900667/100000000000000 : ℝ)^25 := by
    have hnat : (2672264833 : ℕ)^33*100000000000000^25 ≤ 43736147900667^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672264833 5000000000 43736147900667 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266306377/10000000000 : ℝ)^33 ≤ (21446581862379/50000000000000 : ℝ)^25 := by
    have hnat : (5266306377 : ℕ)^33*50000000000000^25 ≤ 21446581862379^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266306377 10000000000 21446581862379 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088843047/5000000000 : ℝ)^33 ≤ (13370688368223/100000000000000 : ℝ)^25 := by
    have hnat : (1088843047 : ℕ)^33*100000000000000^25 ≤ 13370688368223^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088843047 5000000000 13370688368223 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672264833/5000000000 : ℝ), (5266306377/10000000000 : ℝ), (-1088843047/5000000000 : ℝ)] ![(43736147900667/100000000000000 : ℝ), (21446581862379/50000000000000 : ℝ), (13370688368223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672264833/5000000000 : ℝ)|^33 ≤ (43736147900667/100000000000000 : ℝ)^25
        have hw : |(2672264833/5000000000 : ℝ)|=(2672264833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266306377/10000000000 : ℝ)|^33 ≤ (21446581862379/50000000000000 : ℝ)^25
        have hw : |(5266306377/10000000000 : ℝ)|=(5266306377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1088843047/5000000000 : ℝ)|^33 ≤ (13370688368223/100000000000000 : ℝ)^25
        have hw : |(-1088843047/5000000000 : ℝ)|=(1088843047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s5_3 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4348936617/10000000000 : ℝ)*x 0 + (527856233/1250000000 : ℝ)*x 1 + (4478670153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348936617/10000000000 : ℝ)^33 ≤ (33316982686923/100000000000000 : ℝ)^25 := by
    have hnat : (4348936617 : ℕ)^33*100000000000000^25 ≤ 33316982686923^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348936617 10000000000 33316982686923 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527856233/1250000000 : ℝ)^33 ≤ (1281915614719/4000000000000 : ℝ)^25 := by
    have hnat : (527856233 : ℕ)^33*4000000000000^25 ≤ 1281915614719^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527856233 1250000000 1281915614719 4000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4478670153/10000000000 : ℝ)^33 ≤ (34635126936059/100000000000000 : ℝ)^25 := by
    have hnat : (4478670153 : ℕ)^33*100000000000000^25 ≤ 34635126936059^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478670153 10000000000 34635126936059 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348936617/10000000000 : ℝ), (527856233/1250000000 : ℝ), (4478670153/10000000000 : ℝ)] ![(33316982686923/100000000000000 : ℝ), (1281915614719/4000000000000 : ℝ), (34635126936059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348936617/10000000000 : ℝ)|^33 ≤ (33316982686923/100000000000000 : ℝ)^25
        have hw : |(4348936617/10000000000 : ℝ)|=(4348936617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(527856233/1250000000 : ℝ)|^33 ≤ (1281915614719/4000000000000 : ℝ)^25
        have hw : |(527856233/1250000000 : ℝ)|=(527856233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4478670153/10000000000 : ℝ)|^33 ≤ (34635126936059/100000000000000 : ℝ)^25
        have hw : |(4478670153/10000000000 : ℝ)|=(4478670153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s5_4 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1056948987/5000000000 : ℝ)*x 0 + (329164341/625000000 : ℝ)*x 1 + (1078355001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056948987/5000000000 : ℝ)^33 ≤ (6428074685903/50000000000000 : ℝ)^25 := by
    have hnat : (1056948987 : ℕ)^33*50000000000000^25 ≤ 6428074685903^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056948987 5000000000 6428074685903 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329164341/625000000 : ℝ)^33 ≤ (2681039827337/6250000000000 : ℝ)^25 := by
    have hnat : (329164341 : ℕ)^33*6250000000000^25 ≤ 2681039827337^25*625000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329164341 625000000 2681039827337 6250000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078355001/2000000000 : ℝ)^33 ≤ (11061803343517/25000000000000 : ℝ)^25 := by
    have hnat : (1078355001 : ℕ)^33*25000000000000^25 ≤ 11061803343517^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078355001 2000000000 11061803343517 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1056948987/5000000000 : ℝ), (329164341/625000000 : ℝ), (1078355001/2000000000 : ℝ)] ![(6428074685903/50000000000000 : ℝ), (2681039827337/6250000000000 : ℝ), (11061803343517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1056948987/5000000000 : ℝ)|^33 ≤ (6428074685903/50000000000000 : ℝ)^25
        have hw : |(-1056948987/5000000000 : ℝ)|=(1056948987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329164341/625000000 : ℝ)|^33 ≤ (2681039827337/6250000000000 : ℝ)^25
        have hw : |(329164341/625000000 : ℝ)|=(329164341/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078355001/2000000000 : ℝ)|^33 ≤ (11061803343517/25000000000000 : ℝ)^25
        have hw : |(1078355001/2000000000 : ℝ)|=(1078355001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s5_5 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1062481051/2000000000 : ℝ)*x 0 + (-1026108743/5000000000 : ℝ)*x 1 + (1347943751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062481051/2000000000 : ℝ)^33 ≤ (43389473555821/100000000000000 : ℝ)^25 := by
    have hnat : (1062481051 : ℕ)^33*100000000000000^25 ≤ 43389473555821^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062481051 2000000000 43389473555821 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1026108743/5000000000 : ℝ)^33 ≤ (12363313061331/100000000000000 : ℝ)^25 := by
    have hnat : (1026108743 : ℕ)^33*100000000000000^25 ≤ 12363313061331^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026108743 5000000000 12363313061331 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347943751/2500000000 : ℝ)^33 ≤ (8849442672647/20000000000000 : ℝ)^25 := by
    have hnat : (1347943751 : ℕ)^33*20000000000000^25 ≤ 8849442672647^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347943751 2500000000 8849442672647 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062481051/2000000000 : ℝ), (-1026108743/5000000000 : ℝ), (1347943751/2500000000 : ℝ)] ![(43389473555821/100000000000000 : ℝ), (12363313061331/100000000000000 : ℝ), (8849442672647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062481051/2000000000 : ℝ)|^33 ≤ (43389473555821/100000000000000 : ℝ)^25
        have hw : |(1062481051/2000000000 : ℝ)|=(1062481051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1026108743/5000000000 : ℝ)|^33 ≤ (12363313061331/100000000000000 : ℝ)^25
        have hw : |(-1026108743/5000000000 : ℝ)|=(1026108743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347943751/2500000000 : ℝ)|^33 ≤ (8849442672647/20000000000000 : ℝ)^25
        have hw : |(1347943751/2500000000 : ℝ)|=(1347943751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s5_6 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1062481051/2000000000 : ℝ)*x 0 + (1078355001/2000000000 : ℝ)*x 1 + (-410443497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062481051/2000000000 : ℝ)^33 ≤ (43389473555821/100000000000000 : ℝ)^25 := by
    have hnat : (1062481051 : ℕ)^33*100000000000000^25 ≤ 43389473555821^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062481051 2000000000 43389473555821 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078355001/2000000000 : ℝ)^33 ≤ (11061803343517/25000000000000 : ℝ)^25 := by
    have hnat : (1078355001 : ℕ)^33*25000000000000^25 ≤ 11061803343517^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078355001 2000000000 11061803343517 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410443497/2000000000 : ℝ)^33 ≤ (12363313053379/100000000000000 : ℝ)^25 := by
    have hnat : (410443497 : ℕ)^33*100000000000000^25 ≤ 12363313053379^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410443497 2000000000 12363313053379 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062481051/2000000000 : ℝ), (1078355001/2000000000 : ℝ), (-410443497/2000000000 : ℝ)] ![(43389473555821/100000000000000 : ℝ), (11061803343517/25000000000000 : ℝ), (12363313053379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062481051/2000000000 : ℝ)|^33 ≤ (43389473555821/100000000000000 : ℝ)^25
        have hw : |(1062481051/2000000000 : ℝ)|=(1062481051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078355001/2000000000 : ℝ)|^33 ≤ (11061803343517/25000000000000 : ℝ)^25
        have hw : |(1078355001/2000000000 : ℝ)|=(1078355001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410443497/2000000000 : ℝ)|^33 ≤ (12363313053379/100000000000000 : ℝ)^25
        have hw : |(-410443497/2000000000 : ℝ)|=(410443497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1255_s5_7 (p : ℝ) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4348946589/10000000000 : ℝ)*x 0 + (17492239/39062500 : ℝ)*x 1 + (131984663/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4348946589/10000000000 : ℝ)^33 ≤ (33317083528341/100000000000000 : ℝ)^25 := by
    have hnat : (4348946589 : ℕ)^33*100000000000000^25 ≤ 33317083528341^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348946589 10000000000 33317083528341 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17492239/39062500 : ℝ)^33 ≤ (4328552592357/12500000000000 : ℝ)^25 := by
    have hnat : (17492239 : ℕ)^33*12500000000000^25 ≤ 4328552592357^25*39062500^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17492239 39062500 4328552592357 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131984663/312500000 : ℝ)^33 ≤ (8013623929793/25000000000000 : ℝ)^25 := by
    have hnat : (131984663 : ℕ)^33*25000000000000^25 ≤ 8013623929793^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131984663 312500000 8013623929793 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4348946589/10000000000 : ℝ), (17492239/39062500 : ℝ), (131984663/312500000 : ℝ)] ![(33317083528341/100000000000000 : ℝ), (4328552592357/12500000000000 : ℝ), (8013623929793/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4348946589/10000000000 : ℝ)|^33 ≤ (33317083528341/100000000000000 : ℝ)^25
        have hw : |(4348946589/10000000000 : ℝ)|=(4348946589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17492239/39062500 : ℝ)|^33 ≤ (4328552592357/12500000000000 : ℝ)^25
        have hw : |(17492239/39062500 : ℝ)|=(17492239/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131984663/312500000 : ℝ)|^33 ≤ (8013623929793/25000000000000 : ℝ)^25
        have hw : |(131984663/312500000 : ℝ)|=(131984663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1255_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11471/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1767/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11373/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7119/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11373/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7119/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11373/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11373/100000 : ℝ) ^ (8447/2048 : ℝ) ≤ (6381393701299539/50000000000000000000 : ℝ) := by
    have hpowers : (11373/100000 : ℝ)^8447 ≤ (6381393701299539/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11373 : ℕ)^8447*50000000000000000000^2048 ≤ 6381393701299539^2048*100000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11373 100000 6381393701299539 50000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11373/100000 : ℝ)) (X := (6381393701299539/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7119/50000 : ℝ) ^ (8447/2048 : ℝ) ≤ (16119829253380013/50000000000000000000 : ℝ) := by
    have hpowers : (7119/50000 : ℝ)^8447 ≤ (16119829253380013/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7119 : ℕ)^8447*50000000000000000000^2048 ≤ 16119829253380013^2048*50000^8447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7119 50000 16119829253380013 50000000000000000000 8447 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7119/50000 : ℝ)) (X := (16119829253380013/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006381393701299539/25000000000000000000 : ℝ) ≤ (5000309407622003/5000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (25006381393701299539/25000000000000000000 : ℝ)^2048 ≤ (5000309407622003/5000000000000000 : ℝ)^8447 := by
      have hnat : (25006381393701299539 : ℕ)^2048*5000000000000000^8447 ≤ 5000309407622003^8447*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006381393701299539 25000000000000000000 5000309407622003 5000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000309407622003/5000000000000000 : ℝ)) (X := (25006381393701299539/25000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (195400395402166717/195312500000000000 : ℝ) ≤ (10001090911603641/10000000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (195400395402166717/195312500000000000 : ℝ)^2048 ≤ (10001090911603641/10000000000000000 : ℝ)^8447 := by
      have hnat : (195400395402166717 : ℕ)^2048*10000000000000000^8447 ≤ 10001090911603641^8447*195312500000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195400395402166717 195312500000000000 10001090911603641 10000000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001090911603641/10000000000000000 : ℝ)) (X := (195400395402166717/195312500000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016119829253380013/25000000000000000000 : ℝ) ≤ (2500390751990819/2500000000000000 : ℝ) ^ (8447/2048 : ℝ) := by
    have hpowers : (25016119829253380013/25000000000000000000 : ℝ)^2048 ≤ (2500390751990819/2500000000000000 : ℝ)^8447 := by
      have hnat : (25016119829253380013 : ℕ)^2048*2500000000000000^8447 ≤ 2500390751990819^8447*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016119829253380013 25000000000000000000 2500390751990819 2500000000000000 2048 8447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500390751990819/2500000000000000 : ℝ)) (X := (25016119829253380013/25000000000000000000 : ℝ)) (by norm_num) 8447 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6381393701299539/50000000000000000000 : ℝ) ≤ ((238675288348981829/238750000000000000 : ℝ)+2*(94419271927/57300000000000 : ℝ)*(11373/100000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (238675288348981829/238750000000000000 : ℝ)+2*(94419271927/57300000000000 : ℝ)*(11373/100000 : ℝ)=(5000309407622003/5000000000000000 : ℝ) by norm_num, show 1+2*(6381393701299539/50000000000000000000 : ℝ)=(25006381393701299539/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16119829253380013/50000000000000000000 : ℝ)+(6381393701299539/50000000000000000000 : ℝ) ≤ ((238675288348981829/238750000000000000 : ℝ)+(94419271927/57300000000000 : ℝ)*((7119/50000 : ℝ)+(11373/100000 : ℝ)))^(8447/2048 : ℝ) := by
    rw [show (238675288348981829/238750000000000000 : ℝ)+(94419271927/57300000000000 : ℝ)*((7119/50000 : ℝ)+(11373/100000 : ℝ))=(10001090911603641/10000000000000000 : ℝ) by norm_num, show 1+(16119829253380013/50000000000000000000 : ℝ)+(6381393701299539/50000000000000000000 : ℝ)=(195400395402166717/195312500000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16119829253380013/50000000000000000000 : ℝ) ≤ ((238675288348981829/238750000000000000 : ℝ)+2*(94419271927/57300000000000 : ℝ)*(7119/50000 : ℝ))^(8447/2048 : ℝ) := by
    rw [show (238675288348981829/238750000000000000 : ℝ)+2*(94419271927/57300000000000 : ℝ)*(7119/50000 : ℝ)=(2500390751990819/2500000000000000 : ℝ) by norm_num, show 1+2*(16119829253380013/50000000000000000000 : ℝ)=(25016119829253380013/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (238675288348981829/238750000000000000 : ℝ)*(X 1 0+X 2 0)+(94419271927/57300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (238675288348981829/238750000000000000 : ℝ)) (alpha := (94419271927/57300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (238675288348981829/238750000000000000 : ℝ)*(X 0 1+X 2 1)+(94419271927/57300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (238675288348981829/238750000000000000 : ℝ)) (alpha := (94419271927/57300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (238675288348981829/238750000000000000 : ℝ)*(X 0 2+X 1 2)+(94419271927/57300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8447/2048 : ℝ)) (lo := (11373/100000 : ℝ)) (hi := (7119/50000 : ℝ)) (c := (238675288348981829/238750000000000000 : ℝ)) (alpha := (94419271927/57300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1056946557/5000000000 : ℝ)*X 0 0+(67401241/125000000 : ℝ)*X 0 1+(5266306357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672264819/5000000000 : ℝ)*X 1 0+(-108884307/500000000 : ℝ)*X 1 1+(526630637/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672264833/5000000000 : ℝ)*X 2 0+(5266306377/10000000000 : ℝ)*X 2 1+(-1088843047/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4348936617/10000000000 : ℝ)*X 0 0+(527856233/1250000000 : ℝ)*X 0 1+(4478670153/10000000000 : ℝ)*X 0 2+(4348936617/10000000000 : ℝ)*X 1 0+(527856233/1250000000 : ℝ)*X 1 1+(4478670153/10000000000 : ℝ)*X 1 2+(4348936617/10000000000 : ℝ)*X 2 0+(527856233/1250000000 : ℝ)*X 2 1+(4478670153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1056948987/5000000000 : ℝ)*X 0 0+(329164341/625000000 : ℝ)*X 0 1+(1078355001/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062481051/2000000000 : ℝ)*X 1 0+(-1026108743/5000000000 : ℝ)*X 1 1+(1347943751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062481051/2000000000 : ℝ)*X 2 0+(1078355001/2000000000 : ℝ)*X 2 1+(-410443497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4348946589/10000000000 : ℝ)*X 0 0+(17492239/39062500 : ℝ)*X 0 1+(131984663/312500000 : ℝ)*X 0 2+(4348946589/10000000000 : ℝ)*X 1 0+(17492239/39062500 : ℝ)*X 1 1+(131984663/312500000 : ℝ)*X 1 2+(4348946589/10000000000 : ℝ)*X 2 0+(17492239/39062500 : ℝ)*X 2 1+(131984663/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1255_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9816221373932419761413699/2387500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (95217691/12500000000000 : ℝ)*(base19) + (158553697/20000000000000 : ℝ)*(base23) + (23128663/50000000000000 : ℝ)*(upper3) + (1419121/25000000000000 : ℝ)*(upper4) + (24266299/20000000000000 : ℝ)*(upper5) + (1185863425174823/20000000000000 : ℝ)*(major0) + (1185863425174823/20000000000000 : ℝ)*(major1) + (1185863425174823/20000000000000 : ℝ)*(major2) + (7949594191718357/100000000000000 : ℝ)*(sp0) + (3974809652972737/50000000000000 : ℝ)*(sp1) + (7949619274918517/100000000000000 : ℝ)*(sp2) + (977251167302569/25000000000000 : ℝ)*(sp3) + (6468992161/25000000000000 : ℝ)*(sp4) + (9377800731/100000000000000 : ℝ)*(sp7) + (3909014047011007/100000000000000 : ℝ)*(f.failure) + (3974810033843501/50000000000000 : ℝ)*(f.sum) + (29055153847/28650000000000000000000000 : ℝ)*base65 + (79068822819486301/14325000000000000000000000000000 : ℝ)*base67 + (327546445165161301/14325000000000000000000000000000 : ℝ)*base69 + (47054013957411301/14325000000000000000000000000000 : ℝ)*base71 + (370870688537/573000000000000000000000000 : ℝ)*base73 + (8994084769913699/14325000000000000000000000000000 : ℝ)*base76 + (73766859528338699/14325000000000000000000000000000 : ℝ)*base78 + (15075863586861301/14325000000000000000000000000000 : ℝ)*base79 + (2704804594523/573000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (21787421/2500000000000000000000 : ℝ)*base90 + (21787421/2500000000000000000000 : ℝ)*base92 + (21787421/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9678580945111101673449/955000000000000000000000000 : ℝ) := by norm_num
    linear_combination (452644333/25000000000000 : ℝ)*(base19) + (39356303/2000000000000 : ℝ)*(base23) + (101828487/50000000000000 : ℝ)*(upper3) + (17830173/25000000000000 : ℝ)*(lower4) + (103481263/50000000000000 : ℝ)*(upper5) + (5959952687541297/100000000000000 : ℝ)*(major0) + (5959952687541297/100000000000000 : ℝ)*(major1) + (5959952687541297/100000000000000 : ℝ)*(major2) + (50203681089/100000000000000 : ℝ)*(sp1) + (54004612701/100000000000000 : ℝ)*(sp2) + (3995346959463023/50000000000000 : ℝ)*(sp4) + (7990641904667623/100000000000000 : ℝ)*(sp5) + (3995318973249097/50000000000000 : ℝ)*(sp6) + (491151389791901/12500000000000 : ℝ)*(sp7) + (491151389791901/12500000000000 : ℝ)*(f.failure) + (3995346959463023/50000000000000 : ℝ)*(f.sum) + (4718794243633/955000000000000000000000000 : ℝ)*base65 + (304932161833745287/23875000000000000000000000000000 : ℝ)*base68 + (104405175184995287/23875000000000000000000000000000 : ℝ)*base70 + (440421775666129713/23875000000000000000000000000000 : ℝ)*base71 + (5620365542697/955000000000000000000000000 : ℝ)*base74 + (234561278731004713/23875000000000000000000000000000 : ℝ)*base75 + (209447321466254713/23875000000000000000000000000000 : ℝ)*base77 + (176702503803870287/23875000000000000000000000000000 : ℝ)*base80 + (4066346481747/955000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3059903/312500000000000000000 : ℝ)*base90 + (3059903/312500000000000000000 : ℝ)*base92 + (3059903/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1255_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7119/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11373/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1255_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1255_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (597/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1255_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1255_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1255_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8447/2048 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37920797/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (597/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1767/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1255_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
