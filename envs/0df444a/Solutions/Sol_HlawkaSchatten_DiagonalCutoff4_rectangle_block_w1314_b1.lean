-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:41:05.882971+00:00
-- url     : https://prove2.me/submissions/b2d53de7-253d-4e48-9509-7d502135b195

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
theorem support_rectangle_w1314_s3_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-258292211/1250000000 : ℝ)*x 0 + (543091307/1000000000 : ℝ)*x 1 + (522830463/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258292211/1250000000 : ℝ)^2137 ≤ (98226135713/781250000000 : ℝ)^1625 := by
    have hnat : (258292211 : ℕ)^2137*781250000000^1625 ≤ 98226135713^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258292211 1250000000 98226135713 781250000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543091307/1000000000 : ℝ)^2137 ≤ (22403063476691/50000000000000 : ℝ)^1625 := by
    have hnat : (543091307 : ℕ)^2137*50000000000000^1625 ≤ 22403063476691^1625*1000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543091307 1000000000 22403063476691 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522830463/1000000000 : ℝ)^2137 ≤ (42620927651989/100000000000000 : ℝ)^1625 := by
    have hnat : (522830463 : ℕ)^2137*100000000000000^1625 ≤ 42620927651989^1625*1000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522830463 1000000000 42620927651989 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258292211/1250000000 : ℝ), (543091307/1000000000 : ℝ), (522830463/1000000000 : ℝ)] ![(98226135713/781250000000 : ℝ), (22403063476691/50000000000000 : ℝ), (42620927651989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258292211/1250000000 : ℝ)|^2137 ≤ (98226135713/781250000000 : ℝ)^1625
        have hw : |(-258292211/1250000000 : ℝ)|=(258292211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543091307/1000000000 : ℝ)|^2137 ≤ (22403063476691/50000000000000 : ℝ)^1625
        have hw : |(543091307/1000000000 : ℝ)|=(543091307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522830463/1000000000 : ℝ)|^2137 ≤ (42620927651989/100000000000000 : ℝ)^1625
        have hw : |(522830463/1000000000 : ℝ)|=(522830463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s3_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5353717083/10000000000 : ℝ)*x 0 + (-1084981671/5000000000 : ℝ)*x 1 + (2614152317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353717083/10000000000 : ℝ)^2137 ≤ (43970459178519/100000000000000 : ℝ)^1625 := by
    have hnat : (5353717083 : ℕ)^2137*100000000000000^1625 ≤ 43970459178519^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353717083 10000000000 43970459178519 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084981671/5000000000 : ℝ)^2137 ≤ (838038319987/6250000000000 : ℝ)^1625 := by
    have hnat : (1084981671 : ℕ)^2137*6250000000000^1625 ≤ 838038319987^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084981671 5000000000 838038319987 6250000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614152317/5000000000 : ℝ)^2137 ≤ (42620927694871/100000000000000 : ℝ)^1625 := by
    have hnat : (2614152317 : ℕ)^2137*100000000000000^1625 ≤ 42620927694871^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614152317 5000000000 42620927694871 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353717083/10000000000 : ℝ), (-1084981671/5000000000 : ℝ), (2614152317/5000000000 : ℝ)] ![(43970459178519/100000000000000 : ℝ), (838038319987/6250000000000 : ℝ), (42620927694871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353717083/10000000000 : ℝ)|^2137 ≤ (43970459178519/100000000000000 : ℝ)^1625
        have hw : |(5353717083/10000000000 : ℝ)|=(5353717083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1084981671/5000000000 : ℝ)|^2137 ≤ (838038319987/6250000000000 : ℝ)^1625
        have hw : |(-1084981671/5000000000 : ℝ)|=(1084981671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614152317/5000000000 : ℝ)|^2137 ≤ (42620927694871/100000000000000 : ℝ)^1625
        have hw : |(2614152317/5000000000 : ℝ)|=(2614152317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s3_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338429303/2500000000 : ℝ)*x 0 + (5228304251/10000000000 : ℝ)*x 1 + (-86798547/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338429303/2500000000 : ℝ)^2137 ≤ (2748153785739/6250000000000 : ℝ)^1625 := by
    have hnat : (1338429303 : ℕ)^2137*6250000000000^1625 ≤ 2748153785739^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338429303 2500000000 2748153785739 6250000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228304251/10000000000 : ℝ)^2137 ≤ (42620923588937/100000000000000 : ℝ)^1625 := by
    have hnat : (5228304251 : ℕ)^2137*100000000000000^1625 ≤ 42620923588937^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228304251 10000000000 42620923588937 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (86798547/400000000 : ℝ)^2137 ≤ (6704307912893/50000000000000 : ℝ)^1625 := by
    have hnat : (86798547 : ℕ)^2137*50000000000000^1625 ≤ 6704307912893^1625*400000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86798547 400000000 6704307912893 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338429303/2500000000 : ℝ), (5228304251/10000000000 : ℝ), (-86798547/400000000 : ℝ)] ![(2748153785739/6250000000000 : ℝ), (42620923588937/100000000000000 : ℝ), (6704307912893/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338429303/2500000000 : ℝ)|^2137 ≤ (2748153785739/6250000000000 : ℝ)^1625
        have hw : |(1338429303/2500000000 : ℝ)|=(1338429303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228304251/10000000000 : ℝ)|^2137 ≤ (42620923588937/100000000000000 : ℝ)^1625
        have hw : |(5228304251/10000000000 : ℝ)|=(5228304251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-86798547/400000000 : ℝ)|^2137 ≤ (6704307912893/50000000000000 : ℝ)^1625
        have hw : |(-86798547/400000000 : ℝ)|=(86798547/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s3_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4332744333/10000000000 : ℝ)*x 0 + (2063799593/5000000000 : ℝ)*x 1 + (4547511299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332744333/10000000000 : ℝ)^2137 ≤ (33290129639973/100000000000000 : ℝ)^1625 := by
    have hnat : (4332744333 : ℕ)^2137*100000000000000^1625 ≤ 33290129639973^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332744333 10000000000 33290129639973 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063799593/5000000000 : ℝ)^2137 ≤ (31232926171961/100000000000000 : ℝ)^1625 := by
    have hnat : (2063799593 : ℕ)^2137*100000000000000^1625 ≤ 31232926171961^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063799593 5000000000 31232926171961 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4547511299/10000000000 : ℝ)^2137 ≤ (177384720863/500000000000 : ℝ)^1625 := by
    have hnat : (4547511299 : ℕ)^2137*500000000000^1625 ≤ 177384720863^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547511299 10000000000 177384720863 500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332744333/10000000000 : ℝ), (2063799593/5000000000 : ℝ), (4547511299/10000000000 : ℝ)] ![(33290129639973/100000000000000 : ℝ), (31232926171961/100000000000000 : ℝ), (177384720863/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332744333/10000000000 : ℝ)|^2137 ≤ (33290129639973/100000000000000 : ℝ)^1625
        have hw : |(4332744333/10000000000 : ℝ)|=(4332744333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063799593/5000000000 : ℝ)|^2137 ≤ (31232926171961/100000000000000 : ℝ)^1625
        have hw : |(2063799593/5000000000 : ℝ)|=(2063799593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4547511299/10000000000 : ℝ)|^2137 ≤ (177384720863/500000000000 : ℝ)^1625
        have hw : |(4547511299/10000000000 : ℝ)|=(4547511299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s3_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2066358727/10000000000 : ℝ)*x 0 + (1307290957/2500000000 : ℝ)*x 1 + (169689017/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066358727/10000000000 : ℝ)^2137 ≤ (12573113721093/100000000000000 : ℝ)^1625 := by
    have hnat : (2066358727 : ℕ)^2137*100000000000000^1625 ≤ 12573113721093^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066358727 10000000000 12573113721093 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1307290957/2500000000 : ℝ)^2137 ≤ (8526027776587/20000000000000 : ℝ)^1625 := by
    have hnat : (1307290957 : ℕ)^2137*20000000000000^1625 ≤ 8526027776587^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307290957 2500000000 8526027776587 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169689017/312500000 : ℝ)^2137 ≤ (22398373692243/50000000000000 : ℝ)^1625 := by
    have hnat : (169689017 : ℕ)^2137*50000000000000^1625 ≤ 22398373692243^1625*312500000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169689017 312500000 22398373692243 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2066358727/10000000000 : ℝ), (1307290957/2500000000 : ℝ), (169689017/312500000 : ℝ)] ![(12573113721093/100000000000000 : ℝ), (8526027776587/20000000000000 : ℝ), (22398373692243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2066358727/10000000000 : ℝ)|^2137 ≤ (12573113721093/100000000000000 : ℝ)^1625
        have hw : |(-2066358727/10000000000 : ℝ)|=(2066358727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1307290957/2500000000 : ℝ)|^2137 ≤ (8526027776587/20000000000000 : ℝ)^1625
        have hw : |(1307290957/2500000000 : ℝ)|=(1307290957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169689017/312500000 : ℝ)|^2137 ≤ (22398373692243/50000000000000 : ℝ)^1625
        have hw : |(169689017/312500000 : ℝ)|=(169689017/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s3_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5301699683/10000000000 : ℝ)*x 0 + (-1968219461/10000000000 : ℝ)*x 1 + (2715024253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301699683/10000000000 : ℝ)^2137 ≤ (43409490477797/100000000000000 : ℝ)^1625 := by
    have hnat : (5301699683 : ℕ)^2137*100000000000000^1625 ≤ 43409490477797^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301699683 10000000000 43409490477797 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968219461/10000000000 : ℝ)^2137 ≤ (11793762529759/100000000000000 : ℝ)^1625 := by
    have hnat : (1968219461 : ℕ)^2137*100000000000000^1625 ≤ 11793762529759^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968219461 10000000000 11793762529759 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715024253/5000000000 : ℝ)^2137 ≤ (2239837348611/5000000000000 : ℝ)^1625 := by
    have hnat : (2715024253 : ℕ)^2137*5000000000000^1625 ≤ 2239837348611^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715024253 5000000000 2239837348611 5000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301699683/10000000000 : ℝ), (-1968219461/10000000000 : ℝ), (2715024253/5000000000 : ℝ)] ![(43409490477797/100000000000000 : ℝ), (11793762529759/100000000000000 : ℝ), (2239837348611/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301699683/10000000000 : ℝ)|^2137 ≤ (43409490477797/100000000000000 : ℝ)^1625
        have hw : |(5301699683/10000000000 : ℝ)|=(5301699683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1968219461/10000000000 : ℝ)|^2137 ≤ (11793762529759/100000000000000 : ℝ)^1625
        have hw : |(-1968219461/10000000000 : ℝ)|=(1968219461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715024253/5000000000 : ℝ)|^2137 ≤ (2239837348611/5000000000000 : ℝ)^1625
        have hw : |(2715024253/5000000000 : ℝ)|=(2715024253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s3_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2650849911/5000000000 : ℝ)*x 0 + (5430048379/10000000000 : ℝ)*x 1 + (-984109723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650849911/5000000000 : ℝ)^2137 ≤ (43409491974499/100000000000000 : ℝ)^1625 := by
    have hnat : (2650849911 : ℕ)^2137*100000000000000^1625 ≤ 43409491974499^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650849911 5000000000 43409491974499 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430048379/10000000000 : ℝ)^2137 ≤ (44796745594383/100000000000000 : ℝ)^1625 := by
    have hnat : (5430048379 : ℕ)^2137*100000000000000^1625 ≤ 44796745594383^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430048379 10000000000 44796745594383 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (984109723/5000000000 : ℝ)^2137 ≤ (5896881205779/50000000000000 : ℝ)^1625 := by
    have hnat : (984109723 : ℕ)^2137*50000000000000^1625 ≤ 5896881205779^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984109723 5000000000 5896881205779 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650849911/5000000000 : ℝ), (5430048379/10000000000 : ℝ), (-984109723/5000000000 : ℝ)] ![(43409491974499/100000000000000 : ℝ), (44796745594383/100000000000000 : ℝ), (5896881205779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650849911/5000000000 : ℝ)|^2137 ≤ (43409491974499/100000000000000 : ℝ)^1625
        have hw : |(2650849911/5000000000 : ℝ)|=(2650849911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430048379/10000000000 : ℝ)|^2137 ≤ (44796745594383/100000000000000 : ℝ)^1625
        have hw : |(5430048379/10000000000 : ℝ)|=(5430048379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-984109723/5000000000 : ℝ)|^2137 ≤ (5896881205779/50000000000000 : ℝ)^1625
        have hw : |(-984109723/5000000000 : ℝ)|=(984109723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s3_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4332787523/10000000000 : ℝ)*x 0 + (284108147/625000000 : ℝ)*x 1 + (825878249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332787523/10000000000 : ℝ)^2137 ≤ (3329056604271/10000000000000 : ℝ)^1625 := by
    have hnat : (4332787523 : ℕ)^2137*10000000000000^1625 ≤ 3329056604271^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332787523 10000000000 3329056604271 10000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284108147/625000000 : ℝ)^2137 ≤ (35458673784531/100000000000000 : ℝ)^1625 := by
    have hnat : (284108147 : ℕ)^2137*100000000000000^1625 ≤ 35458673784531^1625*625000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284108147 625000000 35458673784531 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825878249/2000000000 : ℝ)^2137 ≤ (15625380076857/50000000000000 : ℝ)^1625 := by
    have hnat : (825878249 : ℕ)^2137*50000000000000^1625 ≤ 15625380076857^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825878249 2000000000 15625380076857 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332787523/10000000000 : ℝ), (284108147/625000000 : ℝ), (825878249/2000000000 : ℝ)] ![(3329056604271/10000000000000 : ℝ), (35458673784531/100000000000000 : ℝ), (15625380076857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332787523/10000000000 : ℝ)|^2137 ≤ (3329056604271/10000000000000 : ℝ)^1625
        have hw : |(4332787523/10000000000 : ℝ)|=(4332787523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284108147/625000000 : ℝ)|^2137 ≤ (35458673784531/100000000000000 : ℝ)^1625
        have hw : |(284108147/625000000 : ℝ)|=(284108147/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(825878249/2000000000 : ℝ)|^2137 ≤ (15625380076857/50000000000000 : ℝ)^1625
        have hw : |(825878249/2000000000 : ℝ)|=(825878249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4831/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (336/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15039/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (811/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4831/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (811/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4831/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (811/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4831/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (811/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4831/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (811/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4831/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (811/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4831/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4831/50000 : ℝ) ^ (4273/1024 : ℝ) ≤ (5818826170737897/100000000000000000000 : ℝ) := by
    have hpowers : (4831/50000 : ℝ)^4273 ≤ (5818826170737897/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4831 : ℕ)^4273*100000000000000000000^1024 ≤ 5818826170737897^1024*50000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4831 50000 5818826170737897 100000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4831/50000 : ℝ)) (X := (5818826170737897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (811/5000 : ℝ) ^ (4273/1024 : ℝ) ≤ (6317852284702227/12500000000000000000 : ℝ) := by
    have hpowers : (811/5000 : ℝ)^4273 ≤ (6317852284702227/12500000000000000000 : ℝ)^1024 := by
      have hnat : (811 : ℕ)^4273*12500000000000000000^1024 ≤ 6317852284702227^1024*5000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        811 5000 6317852284702227 12500000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (811/5000 : ℝ)) (X := (6317852284702227/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005818826170737897/50000000000000000000 : ℝ) ≤ (5000139438670519/5000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50005818826170737897/50000000000000000000 : ℝ)^1024 ≤ (5000139438670519/5000000000000000 : ℝ)^4273 := by
      have hnat : (50005818826170737897 : ℕ)^1024*5000000000000000^4273 ≤ 5000139438670519^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005818826170737897 50000000000000000000 5000139438670519 5000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139438670519/5000000000000000 : ℝ)) (X := (50005818826170737897/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100056361644448355713/100000000000000000000 : ℝ) ≤ (10001350385239783/10000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (100056361644448355713/100000000000000000000 : ℝ)^1024 ≤ (10001350385239783/10000000000000000 : ℝ)^4273 := by
      have hnat : (100056361644448355713 : ℕ)^1024*10000000000000000^4273 ≤ 10001350385239783^4273*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100056361644448355713 100000000000000000000 10001350385239783 10000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001350385239783/10000000000000000 : ℝ)) (X := (100056361644448355713/100000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6256317852284702227/6250000000000000000 : ℝ) ≤ (312575684160579/312500000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (6256317852284702227/6250000000000000000 : ℝ)^1024 ≤ (312575684160579/312500000000000 : ℝ)^4273 := by
      have hnat : (6256317852284702227 : ℕ)^1024*312500000000000^4273 ≤ 312575684160579^4273*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6256317852284702227 6250000000000000000 312575684160579 312500000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312575684160579/312500000000000 : ℝ)) (X := (6256317852284702227/6250000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5818826170737897/100000000000000000000 : ℝ) ≤ ((8195140382370897353/8197500000000000000 : ℝ)+2*(214301579749/131160000000000 : ℝ)*(4831/50000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (8195140382370897353/8197500000000000000 : ℝ)+2*(214301579749/131160000000000 : ℝ)*(4831/50000 : ℝ)=(5000139438670519/5000000000000000 : ℝ) by norm_num, show 1+2*(5818826170737897/100000000000000000000 : ℝ)=(50005818826170737897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6317852284702227/12500000000000000000 : ℝ)+(5818826170737897/100000000000000000000 : ℝ) ≤ ((8195140382370897353/8197500000000000000 : ℝ)+(214301579749/131160000000000 : ℝ)*((811/5000 : ℝ)+(4831/50000 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (8195140382370897353/8197500000000000000 : ℝ)+(214301579749/131160000000000 : ℝ)*((811/5000 : ℝ)+(4831/50000 : ℝ))=(10001350385239783/10000000000000000 : ℝ) by norm_num, show 1+(6317852284702227/12500000000000000000 : ℝ)+(5818826170737897/100000000000000000000 : ℝ)=(100056361644448355713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6317852284702227/12500000000000000000 : ℝ) ≤ ((8195140382370897353/8197500000000000000 : ℝ)+2*(214301579749/131160000000000 : ℝ)*(811/5000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (8195140382370897353/8197500000000000000 : ℝ)+2*(214301579749/131160000000000 : ℝ)*(811/5000 : ℝ)=(312575684160579/312500000000000 : ℝ) by norm_num, show 1+2*(6317852284702227/12500000000000000000 : ℝ)=(6256317852284702227/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8195140382370897353/8197500000000000000 : ℝ)*(X 1 0+X 2 0)+(214301579749/131160000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (4831/50000 : ℝ)) (hi := (811/5000 : ℝ)) (c := (8195140382370897353/8197500000000000000 : ℝ)) (alpha := (214301579749/131160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8195140382370897353/8197500000000000000 : ℝ)*(X 0 1+X 2 1)+(214301579749/131160000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (4831/50000 : ℝ)) (hi := (811/5000 : ℝ)) (c := (8195140382370897353/8197500000000000000 : ℝ)) (alpha := (214301579749/131160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8195140382370897353/8197500000000000000 : ℝ)*(X 0 2+X 1 2)+(214301579749/131160000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (4831/50000 : ℝ)) (hi := (811/5000 : ℝ)) (c := (8195140382370897353/8197500000000000000 : ℝ)) (alpha := (214301579749/131160000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-258292211/1250000000 : ℝ)*X 0 0+(543091307/1000000000 : ℝ)*X 0 1+(522830463/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353717083/10000000000 : ℝ)*X 1 0+(-1084981671/5000000000 : ℝ)*X 1 1+(2614152317/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338429303/2500000000 : ℝ)*X 2 0+(5228304251/10000000000 : ℝ)*X 2 1+(-86798547/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4332744333/10000000000 : ℝ)*X 0 0+(2063799593/5000000000 : ℝ)*X 0 1+(4547511299/10000000000 : ℝ)*X 0 2+(4332744333/10000000000 : ℝ)*X 1 0+(2063799593/5000000000 : ℝ)*X 1 1+(4547511299/10000000000 : ℝ)*X 1 2+(4332744333/10000000000 : ℝ)*X 2 0+(2063799593/5000000000 : ℝ)*X 2 1+(4547511299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2066358727/10000000000 : ℝ)*X 0 0+(1307290957/2500000000 : ℝ)*X 0 1+(169689017/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5301699683/10000000000 : ℝ)*X 1 0+(-1968219461/10000000000 : ℝ)*X 1 1+(2715024253/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2650849911/5000000000 : ℝ)*X 2 0+(5430048379/10000000000 : ℝ)*X 2 1+(-984109723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4332787523/10000000000 : ℝ)*X 0 0+(284108147/625000000 : ℝ)*X 0 1+(825878249/2000000000 : ℝ)*X 0 2+(4332787523/10000000000 : ℝ)*X 1 0+(284108147/625000000 : ℝ)*X 1 1+(825878249/2000000000 : ℝ)*X 1 2+(4332787523/10000000000 : ℝ)*X 2 0+(284108147/625000000 : ℝ)*X 2 1+(825878249/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (663173015756673324944806713/68312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1076404107/50000000000000 : ℝ)*(base19) + (2080046553/100000000000000 : ℝ)*(base23) + (125208299/100000000000000 : ℝ)*(lower2) + (470265831/100000000000000 : ℝ)*(upper3) + (4516663/20000000000000 : ℝ)*(lower4) + (1829295609182207/50000000000000 : ℝ)*(major0) + (1829295609182207/50000000000000 : ℝ)*(major1) + (1829295609182207/50000000000000 : ℝ)*(major2) + (4935668182999299/100000000000000 : ℝ)*(sp0) + (1233923434187261/25000000000000 : ℝ)*(sp1) + (987138761902141/20000000000000 : ℝ)*(sp2) + (1190732461038091/50000000000000 : ℝ)*(sp3) + (27706557959/100000000000000 : ℝ)*(sp4) + (21301497687/100000000000000 : ℝ)*(sp7) + (595371555893467/25000000000000 : ℝ)*(f.failure) + (2467847944778629/50000000000000 : ℝ)*(f.sum) + (1387595668703/655800000000000000000000000 : ℝ)*base66 + (1671157153749688143/136625000000000000000000000000000 : ℝ)*base68 + (1390176657263813143/136625000000000000000000000000000 : ℝ)*base70 + (482728129973813143/136625000000000000000000000000000 : ℝ)*base72 + (6557095035169/3279000000000000000000000000 : ℝ)*base74 + (2219798336787563143/136625000000000000000000000000000 : ℝ)*base76 + (1700061772241813143/136625000000000000000000000000000 : ℝ)*base78 + (3153984070810813143/136625000000000000000000000000000 : ℝ)*base80 + (4990884718339/3279000000000000000000000000 : ℝ)*base82 + (6889869/1250000000000000000000 : ℝ)*base90 + (6889869/1250000000000000000000 : ℝ)*base92 + (6889869/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11432647834100515198221/2186000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162490479/12500000000000 : ℝ)*(base19) + (1477867661/100000000000000 : ℝ)*(base23) + (135096477/100000000000000 : ℝ)*(upper3) + (2273883/12500000000000 : ℝ)*(lower4) + (70459313/50000000000000 : ℝ)*(upper5) + (3689934438177169/100000000000000 : ℝ)*(major0) + (3689934438177169/100000000000000 : ℝ)*(major1) + (3689934438177169/100000000000000 : ℝ)*(major2) + (436242329/2000000000000 : ℝ)*(sp1) + (23149270811/100000000000000 : ℝ)*(sp2) + (1244495060289627/25000000000000 : ℝ)*(sp4) + (2488978564559113/50000000000000 : ℝ)*(sp5) + (1244488903505009/25000000000000 : ℝ)*(sp6) + (2401888460864509/100000000000000 : ℝ)*(sp7) + (2401888460864509/100000000000000 : ℝ)*(f.failure) + (1244495060289627/25000000000000 : ℝ)*(f.sum) + (14754630189403/6558000000000000000000000000 : ℝ)*base65 + (469159373817851281/273250000000000000000000000000000 : ℝ)*base68 + (999747846270898719/273250000000000000000000000000000 : ℝ)*base69 + (45142725322398719/273250000000000000000000000000000 : ℝ)*base71 + (115364184913/262320000000000000000000000 : ℝ)*base73 + (1687033959547101281/273250000000000000000000000000000 : ℝ)*base76 + (2157660733149601281/273250000000000000000000000000000 : ℝ)*base78 + (74938599923898719/273250000000000000000000000000000 : ℝ)*base79 + (14055604227589/6558000000000000000000000000 : ℝ)*base81 + (26667237/5000000000000000000000 : ℝ)*base89 + (26667237/5000000000000000000000 : ℝ)*base91 + (26667237/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1314_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4831/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15039/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1314_s4_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034021439/5000000000 : ℝ)*x 0 + (677159313/1250000000 : ℝ)*x 1 + (5240824451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034021439/5000000000 : ℝ)^2137 ≤ (100692733671/800000000000 : ℝ)^1625 := by
    have hnat : (1034021439 : ℕ)^2137*800000000000^1625 ≤ 100692733671^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034021439 5000000000 100692733671 800000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677159313/1250000000 : ℝ)^2137 ≤ (44658211867369/100000000000000 : ℝ)^1625 := by
    have hnat : (677159313 : ℕ)^2137*100000000000000^1625 ≤ 44658211867369^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677159313 1250000000 44658211867369 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240824451/10000000000 : ℝ)^2137 ≤ (42755196420497/100000000000000 : ℝ)^1625 := by
    have hnat : (5240824451 : ℕ)^2137*100000000000000^1625 ≤ 42755196420497^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240824451 10000000000 42755196420497 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034021439/5000000000 : ℝ), (677159313/1250000000 : ℝ), (5240824451/10000000000 : ℝ)] ![(100692733671/800000000000 : ℝ), (44658211867369/100000000000000 : ℝ), (42755196420497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034021439/5000000000 : ℝ)|^2137 ≤ (100692733671/800000000000 : ℝ)^1625
        have hw : |(-1034021439/5000000000 : ℝ)|=(1034021439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677159313/1250000000 : ℝ)|^2137 ≤ (44658211867369/100000000000000 : ℝ)^1625
        have hw : |(677159313/1250000000 : ℝ)|=(677159313/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240824451/10000000000 : ℝ)|^2137 ≤ (42755196420497/100000000000000 : ℝ)^1625
        have hw : |(5240824451/10000000000 : ℝ)|=(5240824451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s4_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668782059/1250000000 : ℝ)*x 0 + (-431605793/2000000000 : ℝ)*x 1 + (5240824527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668782059/1250000000 : ℝ)^2137 ≤ (175732342191/400000000000 : ℝ)^1625 := by
    have hnat : (668782059 : ℕ)^2137*400000000000^1625 ≤ 175732342191^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668782059 1250000000 175732342191 400000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (431605793/2000000000 : ℝ)^2137 ≤ (13311717208979/100000000000000 : ℝ)^1625 := by
    have hnat : (431605793 : ℕ)^2137*100000000000000^1625 ≤ 13311717208979^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431605793 2000000000 13311717208979 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240824527/10000000000 : ℝ)^2137 ≤ (21377598617933/50000000000000 : ℝ)^1625 := by
    have hnat : (5240824527 : ℕ)^2137*50000000000000^1625 ≤ 21377598617933^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240824527 10000000000 21377598617933 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668782059/1250000000 : ℝ), (-431605793/2000000000 : ℝ), (5240824527/10000000000 : ℝ)] ![(175732342191/400000000000 : ℝ), (13311717208979/100000000000000 : ℝ), (21377598617933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668782059/1250000000 : ℝ)|^2137 ≤ (175732342191/400000000000 : ℝ)^1625
        have hw : |(668782059/1250000000 : ℝ)|=(668782059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-431605793/2000000000 : ℝ)|^2137 ≤ (13311717208979/100000000000000 : ℝ)^1625
        have hw : |(-431605793/2000000000 : ℝ)|=(431605793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240824527/10000000000 : ℝ)|^2137 ≤ (21377598617933/50000000000000 : ℝ)^1625
        have hw : |(5240824527/10000000000 : ℝ)|=(5240824527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s4_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2675128243/5000000000 : ℝ)*x 0 + (1048164861/2000000000 : ℝ)*x 1 + (-2158029239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675128243/5000000000 : ℝ)^2137 ≤ (43933085698931/100000000000000 : ℝ)^1625 := by
    have hnat : (2675128243 : ℕ)^2137*100000000000000^1625 ≤ 43933085698931^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675128243 5000000000 43933085698931 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048164861/2000000000 : ℝ)^2137 ≤ (42755194854131/100000000000000 : ℝ)^1625 := by
    have hnat : (1048164861 : ℕ)^2137*100000000000000^1625 ≤ 42755194854131^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048164861 2000000000 42755194854131 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158029239/10000000000 : ℝ)^2137 ≤ (13311719431667/100000000000000 : ℝ)^1625 := by
    have hnat : (2158029239 : ℕ)^2137*100000000000000^1625 ≤ 13311719431667^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158029239 10000000000 13311719431667 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675128243/5000000000 : ℝ), (1048164861/2000000000 : ℝ), (-2158029239/10000000000 : ℝ)] ![(43933085698931/100000000000000 : ℝ), (42755194854131/100000000000000 : ℝ), (13311719431667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675128243/5000000000 : ℝ)|^2137 ≤ (43933085698931/100000000000000 : ℝ)^1625
        have hw : |(2675128243/5000000000 : ℝ)|=(2675128243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048164861/2000000000 : ℝ)|^2137 ≤ (42755194854131/100000000000000 : ℝ)^1625
        have hw : |(1048164861/2000000000 : ℝ)|=(1048164861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2158029239/10000000000 : ℝ)|^2137 ≤ (13311719431667/100000000000000 : ℝ)^1625
        have hw : |(-2158029239/10000000000 : ℝ)|=(2158029239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s4_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4333776353/10000000000 : ℝ)*x 0 + (4154577353/10000000000 : ℝ)*x 1 + (4520275141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333776353/10000000000 : ℝ)^2137 ≤ (33300557807261/100000000000000 : ℝ)^1625 := by
    have hnat : (4333776353 : ℕ)^2137*100000000000000^1625 ≤ 33300557807261^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333776353 10000000000 33300557807261 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154577353/10000000000 : ℝ)^2137 ≤ (31501661672059/100000000000000 : ℝ)^1625 := by
    have hnat : (4154577353 : ℕ)^2137*100000000000000^1625 ≤ 31501661672059^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154577353 10000000000 31501661672059 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4520275141/10000000000 : ℝ)^2137 ≤ (8799445126929/25000000000000 : ℝ)^1625 := by
    have hnat : (4520275141 : ℕ)^2137*25000000000000^1625 ≤ 8799445126929^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4520275141 10000000000 8799445126929 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333776353/10000000000 : ℝ), (4154577353/10000000000 : ℝ), (4520275141/10000000000 : ℝ)] ![(33300557807261/100000000000000 : ℝ), (31501661672059/100000000000000 : ℝ), (8799445126929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333776353/10000000000 : ℝ)|^2137 ≤ (33300557807261/100000000000000 : ℝ)^1625
        have hw : |(4333776353/10000000000 : ℝ)|=(4333776353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154577353/10000000000 : ℝ)|^2137 ≤ (31501661672059/100000000000000 : ℝ)^1625
        have hw : |(4154577353/10000000000 : ℝ)|=(4154577353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4520275141/10000000000 : ℝ)|^2137 ≤ (8799445126929/25000000000000 : ℝ)^1625
        have hw : |(4520275141/10000000000 : ℝ)|=(4520275141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s4_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2068056487/10000000000 : ℝ)*x 0 + (655184639/1250000000 : ℝ)*x 1 + (5416618543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2068056487/10000000000 : ℝ)^2137 ≤ (3146675158397/25000000000000 : ℝ)^1625 := by
    have hnat : (2068056487 : ℕ)^2137*25000000000000^1625 ≤ 3146675158397^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068056487 10000000000 3146675158397 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655184639/1250000000 : ℝ)^2137 ≤ (42762198654697/100000000000000 : ℝ)^1625 := by
    have hnat : (655184639 : ℕ)^2137*100000000000000^1625 ≤ 42762198654697^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655184639 1250000000 42762198654697 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416618543/10000000000 : ℝ)^2137 ≤ (44651100692173/100000000000000 : ℝ)^1625 := by
    have hnat : (5416618543 : ℕ)^2137*100000000000000^1625 ≤ 44651100692173^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416618543 10000000000 44651100692173 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2068056487/10000000000 : ℝ), (655184639/1250000000 : ℝ), (5416618543/10000000000 : ℝ)] ![(3146675158397/25000000000000 : ℝ), (42762198654697/100000000000000 : ℝ), (44651100692173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2068056487/10000000000 : ℝ)|^2137 ≤ (3146675158397/25000000000000 : ℝ)^1625
        have hw : |(-2068056487/10000000000 : ℝ)|=(2068056487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655184639/1250000000 : ℝ)|^2137 ≤ (42762198654697/100000000000000 : ℝ)^1625
        have hw : |(655184639/1250000000 : ℝ)|=(655184639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416618543/10000000000 : ℝ)|^2137 ≤ (44651100692173/100000000000000 : ℝ)^1625
        have hw : |(5416618543/10000000000 : ℝ)|=(5416618543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s4_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652478911/5000000000 : ℝ)*x 0 + (-1982234939/10000000000 : ℝ)*x 1 + (5416617969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652478911/5000000000 : ℝ)^2137 ≤ (4344457635737/10000000000000 : ℝ)^1625 := by
    have hnat : (2652478911 : ℕ)^2137*10000000000000^1625 ≤ 4344457635737^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652478911 5000000000 4344457635737 10000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1982234939/10000000000 : ℝ)^2137 ≤ (5952164578769/50000000000000 : ℝ)^1625 := by
    have hnat : (1982234939 : ℕ)^2137*50000000000000^1625 ≤ 5952164578769^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982234939 10000000000 5952164578769 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416617969/10000000000 : ℝ)^2137 ≤ (11162773617411/25000000000000 : ℝ)^1625 := by
    have hnat : (5416617969 : ℕ)^2137*25000000000000^1625 ≤ 11162773617411^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416617969 10000000000 11162773617411 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652478911/5000000000 : ℝ), (-1982234939/10000000000 : ℝ), (5416617969/10000000000 : ℝ)] ![(4344457635737/10000000000000 : ℝ), (5952164578769/50000000000000 : ℝ), (11162773617411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652478911/5000000000 : ℝ)|^2137 ≤ (4344457635737/10000000000000 : ℝ)^1625
        have hw : |(2652478911/5000000000 : ℝ)|=(2652478911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1982234939/10000000000 : ℝ)|^2137 ≤ (5952164578769/50000000000000 : ℝ)^1625
        have hw : |(-1982234939/10000000000 : ℝ)|=(1982234939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416617969/10000000000 : ℝ)|^2137 ≤ (11162773617411/25000000000000 : ℝ)^1625
        have hw : |(5416617969/10000000000 : ℝ)|=(5416617969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s4_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (212198277/400000000 : ℝ)*x 0 + (338538691/625000000 : ℝ)*x 1 + (-198223467/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212198277/400000000 : ℝ)^2137 ≤ (43444566696923/100000000000000 : ℝ)^1625 := by
    have hnat : (212198277 : ℕ)^2137*100000000000000^1625 ≤ 43444566696923^1625*400000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212198277 400000000 43444566696923 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338538691/625000000 : ℝ)^2137 ≤ (2790694140839/6250000000000 : ℝ)^1625 := by
    have hnat : (338538691 : ℕ)^2137*6250000000000^1625 ≤ 2790694140839^1625*625000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338538691 625000000 2790694140839 6250000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198223467/1000000000 : ℝ)^2137 ≤ (2380865406611/20000000000000 : ℝ)^1625 := by
    have hnat : (198223467 : ℕ)^2137*20000000000000^1625 ≤ 2380865406611^1625*1000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198223467 1000000000 2380865406611 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212198277/400000000 : ℝ), (338538691/625000000 : ℝ), (-198223467/1000000000 : ℝ)] ![(43444566696923/100000000000000 : ℝ), (2790694140839/6250000000000 : ℝ), (2380865406611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212198277/400000000 : ℝ)|^2137 ≤ (43444566696923/100000000000000 : ℝ)^1625
        have hw : |(212198277/400000000 : ℝ)|=(212198277/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338538691/625000000 : ℝ)|^2137 ≤ (2790694140839/6250000000000 : ℝ)^1625
        have hw : |(338538691/625000000 : ℝ)|=(338538691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198223467/1000000000 : ℝ)|^2137 ≤ (2380865406611/20000000000000 : ℝ)^1625
        have hw : |(-198223467/1000000000 : ℝ)|=(198223467/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s4_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (866760961/2000000000 : ℝ)*x 0 + (4518923347/10000000000 : ℝ)*x 1 + (4155936591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866760961/2000000000 : ℝ)^2137 ≤ (832521132873/2500000000000 : ℝ)^1625 := by
    have hnat : (866760961 : ℕ)^2137*2500000000000^1625 ≤ 832521132873^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866760961 2000000000 832521132873 2500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518923347/10000000000 : ℝ)^2137 ≤ (17591969369037/50000000000000 : ℝ)^1625 := by
    have hnat : (4518923347 : ℕ)^2137*50000000000000^1625 ≤ 17591969369037^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518923347 10000000000 17591969369037 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155936591/10000000000 : ℝ)^2137 ≤ (31515215927303/100000000000000 : ℝ)^1625 := by
    have hnat : (4155936591 : ℕ)^2137*100000000000000^1625 ≤ 31515215927303^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155936591 10000000000 31515215927303 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866760961/2000000000 : ℝ), (4518923347/10000000000 : ℝ), (4155936591/10000000000 : ℝ)] ![(832521132873/2500000000000 : ℝ), (17591969369037/50000000000000 : ℝ), (31515215927303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866760961/2000000000 : ℝ)|^2137 ≤ (832521132873/2500000000000 : ℝ)^1625
        have hw : |(866760961/2000000000 : ℝ)|=(866760961/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518923347/10000000000 : ℝ)|^2137 ≤ (17591969369037/50000000000000 : ℝ)^1625
        have hw : |(4518923347/10000000000 : ℝ)|=(4518923347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155936591/10000000000 : ℝ)|^2137 ≤ (31515215927303/100000000000000 : ℝ)^1625
        have hw : |(4155936591/10000000000 : ℝ)|=(4155936591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (551/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7377/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (336/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15039/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (336/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (336/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15039/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (336/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (336/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15039/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (336/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (336/3125 : ℝ) ^ (4273/1024 : ℝ) ≤ (1817935301499359/20000000000000000000 : ℝ) := by
    have hpowers : (336/3125 : ℝ)^4273 ≤ (1817935301499359/20000000000000000000 : ℝ)^1024 := by
      have hnat : (336 : ℕ)^4273*20000000000000000000^1024 ≤ 1817935301499359^1024*3125^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        336 3125 1817935301499359 20000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (336/3125 : ℝ)) (X := (1817935301499359/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15039/100000 : ℝ) ^ (4273/1024 : ℝ) ≤ (9217154292781749/25000000000000000000 : ℝ) := by
    have hpowers : (15039/100000 : ℝ)^4273 ≤ (9217154292781749/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15039 : ℕ)^4273*25000000000000000000^1024 ≤ 9217154292781749^1024*100000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15039 100000 9217154292781749 25000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15039/100000 : ℝ)) (X := (9217154292781749/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001817935301499359/10000000000000000000 : ℝ) ≤ (10000435627686037/10000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (10001817935301499359/10000000000000000000 : ℝ)^1024 ≤ (10000435627686037/10000000000000000 : ℝ)^4273 := by
      have hnat : (10001817935301499359 : ℕ)^1024*10000000000000000^4273 ≤ 10000435627686037^4273*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001817935301499359 10000000000000000000 10000435627686037 10000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000435627686037/10000000000000000 : ℝ)) (X := (10001817935301499359/10000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045958293678623791/100000000000000000000 : ℝ) ≤ (10001101171828723/10000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (100045958293678623791/100000000000000000000 : ℝ)^1024 ≤ (10001101171828723/10000000000000000 : ℝ)^4273 := by
      have hnat : (100045958293678623791 : ℕ)^1024*10000000000000000^4273 ≤ 10001101171828723^4273*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045958293678623791 100000000000000000000 10001101171828723 10000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001101171828723/10000000000000000 : ℝ)) (X := (100045958293678623791/100000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509217154292781749/12500000000000000000 : ℝ) ≤ (10001766715971409/10000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (12509217154292781749/12500000000000000000 : ℝ)^1024 ≤ (10001766715971409/10000000000000000 : ℝ)^4273 := by
      have hnat : (12509217154292781749 : ℕ)^1024*10000000000000000^4273 ≤ 10001766715971409^4273*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509217154292781749 12500000000000000000 10001766715971409 10000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001766715971409/10000000000000000 : ℝ)) (X := (12509217154292781749/12500000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1817935301499359/20000000000000000000 : ℝ) ≤ ((114286815132388589/114320000000000000 : ℝ)+2*(110924023781/71450000000000 : ℝ)*(336/3125 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (114286815132388589/114320000000000000 : ℝ)+2*(110924023781/71450000000000 : ℝ)*(336/3125 : ℝ)=(10000435627686037/10000000000000000 : ℝ) by norm_num, show 1+2*(1817935301499359/20000000000000000000 : ℝ)=(10001817935301499359/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9217154292781749/25000000000000000000 : ℝ)+(1817935301499359/20000000000000000000 : ℝ) ≤ ((114286815132388589/114320000000000000 : ℝ)+(110924023781/71450000000000 : ℝ)*((15039/100000 : ℝ)+(336/3125 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (114286815132388589/114320000000000000 : ℝ)+(110924023781/71450000000000 : ℝ)*((15039/100000 : ℝ)+(336/3125 : ℝ))=(10001101171828723/10000000000000000 : ℝ) by norm_num, show 1+(9217154292781749/25000000000000000000 : ℝ)+(1817935301499359/20000000000000000000 : ℝ)=(100045958293678623791/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9217154292781749/25000000000000000000 : ℝ) ≤ ((114286815132388589/114320000000000000 : ℝ)+2*(110924023781/71450000000000 : ℝ)*(15039/100000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (114286815132388589/114320000000000000 : ℝ)+2*(110924023781/71450000000000 : ℝ)*(15039/100000 : ℝ)=(10001766715971409/10000000000000000 : ℝ) by norm_num, show 1+2*(9217154292781749/25000000000000000000 : ℝ)=(12509217154292781749/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (114286815132388589/114320000000000000 : ℝ)*(X 1 0+X 2 0)+(110924023781/71450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (15039/100000 : ℝ)) (c := (114286815132388589/114320000000000000 : ℝ)) (alpha := (110924023781/71450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (114286815132388589/114320000000000000 : ℝ)*(X 0 1+X 2 1)+(110924023781/71450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (15039/100000 : ℝ)) (c := (114286815132388589/114320000000000000 : ℝ)) (alpha := (110924023781/71450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (114286815132388589/114320000000000000 : ℝ)*(X 0 2+X 1 2)+(110924023781/71450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (336/3125 : ℝ)) (hi := (15039/100000 : ℝ)) (c := (114286815132388589/114320000000000000 : ℝ)) (alpha := (110924023781/71450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1034021439/5000000000 : ℝ)*X 0 0+(677159313/1250000000 : ℝ)*X 0 1+(5240824451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668782059/1250000000 : ℝ)*X 1 0+(-431605793/2000000000 : ℝ)*X 1 1+(5240824527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675128243/5000000000 : ℝ)*X 2 0+(1048164861/2000000000 : ℝ)*X 2 1+(-2158029239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4333776353/10000000000 : ℝ)*X 0 0+(4154577353/10000000000 : ℝ)*X 0 1+(4520275141/10000000000 : ℝ)*X 0 2+(4333776353/10000000000 : ℝ)*X 1 0+(4154577353/10000000000 : ℝ)*X 1 1+(4520275141/10000000000 : ℝ)*X 1 2+(4333776353/10000000000 : ℝ)*X 2 0+(4154577353/10000000000 : ℝ)*X 2 1+(4520275141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2068056487/10000000000 : ℝ)*X 0 0+(655184639/1250000000 : ℝ)*X 0 1+(5416618543/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652478911/5000000000 : ℝ)*X 1 0+(-1982234939/10000000000 : ℝ)*X 1 1+(5416617969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212198277/400000000 : ℝ)*X 2 0+(338538691/625000000 : ℝ)*X 2 1+(-198223467/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866760961/2000000000 : ℝ)*X 0 0+(4518923347/10000000000 : ℝ)*X 0 1+(4155936591/10000000000 : ℝ)*X 0 2+(866760961/2000000000 : ℝ)*X 1 0+(4518923347/10000000000 : ℝ)*X 1 1+(4155936591/10000000000 : ℝ)*X 1 2+(866760961/2000000000 : ℝ)*X 2 0+(4518923347/10000000000 : ℝ)*X 2 1+(4155936591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12059781441193328181232641/2858000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102781129/10000000000000 : ℝ)*(base19) + (1103894451/100000000000000 : ℝ)*(base23) + (2033807/25000000000000 : ℝ)*(lower2) + (273062553/100000000000000 : ℝ)*(upper3) + (255671/625000000000 : ℝ)*(lower4) + (2100471222730423/50000000000000 : ℝ)*(major0) + (2100471222730423/50000000000000 : ℝ)*(major1) + (2100471222730423/50000000000000 : ℝ)*(major2) + (708418897847/12500000000 : ℝ)*(sp0) + (1416841224343659/25000000000000 : ℝ)*(sp1) + (226694592851659/4000000000000 : ℝ)*(sp2) + (1367253355369417/50000000000000 : ℝ)*(sp3) + (7371204963/50000000000000 : ℝ)*(sp4) + (6057170837/50000000000000 : ℝ)*(sp7) + (683629706270127/25000000000000 : ℝ)*(f.failure) + (2833682962592963/50000000000000 : ℝ)*(f.sum) + (28932221788001/3572500000000000000000000000 : ℝ)*base65 + (69205297634948053/5716000000000000000000000000000 : ℝ)*base68 + (39727003964812053/5716000000000000000000000000000 : ℝ)*base70 + (4426652913899947/5716000000000000000000000000000 : ℝ)*base71 + (740715891769/893125000000000000000000000 : ℝ)*base73 + (15272031696276053/5716000000000000000000000000000 : ℝ)*base76 + (12421901039228053/5716000000000000000000000000000 : ℝ)*base78 + (33250674721343947/5716000000000000000000000000000 : ℝ)*base79 + (32565689133017/7145000000000000000000000000 : ℝ)*base81 + (385511/1250000000000000000000 : ℝ)*base89 + (385511/1250000000000000000000 : ℝ)*base91 + (385511/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9278285922870011966427171/2858000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (150029803/12500000000000 : ℝ)*(base19) + (526927943/100000000000000 : ℝ)*(base23) + (29300099/100000000000000 : ℝ)*(upper3) + (110494569/100000000000000 : ℝ)*(lower4) + (2116147092413787/50000000000000 : ℝ)*(major0) + (2116147092413787/50000000000000 : ℝ)*(major1) + (2116147092413787/50000000000000 : ℝ)*(major2) + (5491685121/50000000000000 : ℝ)*(sp1) + (5200207653/25000000000000 : ℝ)*(sp2) + (2129919637/50000000000000 : ℝ)*(sp3) + (285483082671891/5000000000000 : ℝ)*(sp4) + (2854824734914577/50000000000000 : ℝ)*(sp5) + (2854820162839633/50000000000000 : ℝ)*(sp6) + (1377461174081921/50000000000000 : ℝ)*(sp7) + (688731652000779/25000000000000 : ℝ)*(f.failure) + (285483082671891/5000000000000 : ℝ)*(f.sum) + (456027186813/1786250000000000000000000000 : ℝ)*base66 + (269172591935743/5716000000000000000000000000000 : ℝ)*base67 + (3055895329455743/5716000000000000000000000000000 : ℝ)*base69 + (25174124076607743/5716000000000000000000000000000 : ℝ)*base71 + (4413112459847/1786250000000000000000000000 : ℝ)*base73 + (78492819619455743/5716000000000000000000000000000 : ℝ)*base75 + (79927783725112257/5716000000000000000000000000000 : ℝ)*base78 + (81310389456720257/5716000000000000000000000000000 : ℝ)*base80 + (10485819425557/1786250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1522653/1250000000000000000000 : ℝ)*base90 + (1522653/1250000000000000000000 : ℝ)*base92 + (1522653/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1314_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15039/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (336/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1314_s5_0 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-16546793/80000000 : ℝ)*x 0 + (5414646361/10000000000 : ℝ)*x 1 + (52432513/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16546793/80000000 : ℝ)^2137 ≤ (12589042925743/100000000000000 : ℝ)^1625 := by
    have hnat : (16546793 : ℕ)^2137*100000000000000^1625 ≤ 12589042925743^1625*80000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16546793 80000000 12589042925743 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414646361/10000000000 : ℝ)^2137 ≤ (11157430549019/25000000000000 : ℝ)^1625 := by
    have hnat : (5414646361 : ℕ)^2137*25000000000000^1625 ≤ 11157430549019^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414646361 10000000000 11157430549019 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52432513/100000000 : ℝ)^2137 ≤ (8556246971157/20000000000000 : ℝ)^1625 := by
    have hnat : (52432513 : ℕ)^2137*20000000000000^1625 ≤ 8556246971157^1625*100000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52432513 100000000 8556246971157 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16546793/80000000 : ℝ), (5414646361/10000000000 : ℝ), (52432513/100000000 : ℝ)] ![(12589042925743/100000000000000 : ℝ), (11157430549019/25000000000000 : ℝ), (8556246971157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16546793/80000000 : ℝ)|^2137 ≤ (12589042925743/100000000000000 : ℝ)^1625
        have hw : |(-16546793/80000000 : ℝ)|=(16546793/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414646361/10000000000 : ℝ)|^2137 ≤ (11157430549019/25000000000000 : ℝ)^1625
        have hw : |(5414646361/10000000000 : ℝ)|=(5414646361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52432513/100000000 : ℝ)|^2137 ≤ (8556246971157/20000000000000 : ℝ)^1625
        have hw : |(52432513/100000000 : ℝ)|=(52432513/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s5_1 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069917637/2000000000 : ℝ)*x 0 + (-2155708423/10000000000 : ℝ)*x 1 + (5243251287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069917637/2000000000 : ℝ)^2137 ≤ (43925869112343/100000000000000 : ℝ)^1625 := by
    have hnat : (1069917637 : ℕ)^2137*100000000000000^1625 ≤ 43925869112343^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069917637 2000000000 43925869112343 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2155708423/10000000000 : ℝ)^2137 ≤ (6646448080347/50000000000000 : ℝ)^1625 := by
    have hnat : (2155708423 : ℕ)^2137*50000000000000^1625 ≤ 6646448080347^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155708423 10000000000 6646448080347 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243251287/10000000000 : ℝ)^2137 ≤ (21390617358147/50000000000000 : ℝ)^1625 := by
    have hnat : (5243251287 : ℕ)^2137*50000000000000^1625 ≤ 21390617358147^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243251287 10000000000 21390617358147 50000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069917637/2000000000 : ℝ), (-2155708423/10000000000 : ℝ), (5243251287/10000000000 : ℝ)] ![(43925869112343/100000000000000 : ℝ), (6646448080347/50000000000000 : ℝ), (21390617358147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069917637/2000000000 : ℝ)|^2137 ≤ (43925869112343/100000000000000 : ℝ)^1625
        have hw : |(1069917637/2000000000 : ℝ)|=(1069917637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2155708423/10000000000 : ℝ)|^2137 ≤ (6646448080347/50000000000000 : ℝ)^1625
        have hw : |(-2155708423/10000000000 : ℝ)|=(2155708423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243251287/10000000000 : ℝ)|^2137 ≤ (21390617358147/50000000000000 : ℝ)^1625
        have hw : |(5243251287/10000000000 : ℝ)|=(5243251287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s5_2 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674794037/5000000000 : ℝ)*x 0 + (1310812821/2500000000 : ℝ)*x 1 + (-1077854287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674794037/5000000000 : ℝ)^2137 ≤ (2745366744609/6250000000000 : ℝ)^1625 := by
    have hnat : (2674794037 : ℕ)^2137*6250000000000^1625 ≤ 2745366744609^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674794037 5000000000 2745366744609 6250000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310812821/2500000000 : ℝ)^2137 ≤ (5347654335513/12500000000000 : ℝ)^1625 := by
    have hnat : (1310812821 : ℕ)^2137*12500000000000^1625 ≤ 5347654335513^1625*2500000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310812821 2500000000 5347654335513 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077854287/5000000000 : ℝ)^2137 ≤ (13292897385191/100000000000000 : ℝ)^1625 := by
    have hnat : (1077854287 : ℕ)^2137*100000000000000^1625 ≤ 13292897385191^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077854287 5000000000 13292897385191 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674794037/5000000000 : ℝ), (1310812821/2500000000 : ℝ), (-1077854287/5000000000 : ℝ)] ![(2745366744609/6250000000000 : ℝ), (5347654335513/12500000000000 : ℝ), (13292897385191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674794037/5000000000 : ℝ)|^2137 ≤ (2745366744609/6250000000000 : ℝ)^1625
        have hw : |(2674794037/5000000000 : ℝ)|=(2674794037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310812821/2500000000 : ℝ)|^2137 ≤ (5347654335513/12500000000000 : ℝ)^1625
        have hw : |(1310812821/2500000000 : ℝ)|=(1310812821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077854287/5000000000 : ℝ)|^2137 ≤ (13292897385191/100000000000000 : ℝ)^1625
        have hw : |(-1077854287/5000000000 : ℝ)|=(1077854287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s5_3 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4333959061/10000000000 : ℝ)*x 0 + (831958597/2000000000 : ℝ)*x 1 + (141094189/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333959061/10000000000 : ℝ)^2137 ≤ (33302404083233/100000000000000 : ℝ)^1625 := by
    have hnat : (4333959061 : ℕ)^2137*100000000000000^1625 ≤ 33302404083233^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333959061 10000000000 33302404083233 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831958597/2000000000 : ℝ)^2137 ≤ (31553679303127/100000000000000 : ℝ)^1625 := by
    have hnat : (831958597 : ℕ)^2137*100000000000000^1625 ≤ 31553679303127^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831958597 2000000000 31553679303127 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141094189/312500000 : ℝ)^2137 ≤ (1757195829831/5000000000000 : ℝ)^1625 := by
    have hnat : (141094189 : ℕ)^2137*5000000000000^1625 ≤ 1757195829831^1625*312500000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141094189 312500000 1757195829831 5000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333959061/10000000000 : ℝ), (831958597/2000000000 : ℝ), (141094189/312500000 : ℝ)] ![(33302404083233/100000000000000 : ℝ), (31553679303127/100000000000000 : ℝ), (1757195829831/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333959061/10000000000 : ℝ)|^2137 ≤ (33302404083233/100000000000000 : ℝ)^1625
        have hw : |(4333959061/10000000000 : ℝ)|=(4333959061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831958597/2000000000 : ℝ)|^2137 ≤ (31553679303127/100000000000000 : ℝ)^1625
        have hw : |(831958597/2000000000 : ℝ)|=(831958597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141094189/312500000 : ℝ)|^2137 ≤ (1757195829831/5000000000000 : ℝ)^1625
        have hw : |(141094189/312500000 : ℝ)|=(141094189/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s5_4 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-20683619/100000000 : ℝ)*x 0 + (655483373/1250000000 : ℝ)*x 1 + (5414027429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20683619/100000000 : ℝ)^2137 ≤ (12589145179991/100000000000000 : ℝ)^1625 := by
    have hnat : (20683619 : ℕ)^2137*100000000000000^1625 ≤ 12589145179991^1625*100000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20683619 100000000 12589145179991 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655483373/1250000000 : ℝ)^2137 ≤ (42787841329341/100000000000000 : ℝ)^1625 := by
    have hnat : (655483373 : ℕ)^2137*100000000000000^1625 ≤ 42787841329341^1625*1250000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655483373 1250000000 42787841329341 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414027429/10000000000 : ℝ)^2137 ≤ (44623013465373/100000000000000 : ℝ)^1625 := by
    have hnat : (5414027429 : ℕ)^2137*100000000000000^1625 ≤ 44623013465373^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414027429 10000000000 44623013465373 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20683619/100000000 : ℝ), (655483373/1250000000 : ℝ), (5414027429/10000000000 : ℝ)] ![(12589145179991/100000000000000 : ℝ), (42787841329341/100000000000000 : ℝ), (44623013465373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20683619/100000000 : ℝ)|^2137 ≤ (12589145179991/100000000000000 : ℝ)^1625
        have hw : |(-20683619/100000000 : ℝ)|=(20683619/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655483373/1250000000 : ℝ)|^2137 ≤ (42787841329341/100000000000000 : ℝ)^1625
        have hw : |(655483373/1250000000 : ℝ)|=(655483373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414027429/10000000000 : ℝ)|^2137 ≤ (44623013465373/100000000000000 : ℝ)^1625
        have hw : |(5414027429/10000000000 : ℝ)|=(5414027429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s5_5 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1061117323/2000000000 : ℝ)*x 0 + (-992466207/5000000000 : ℝ)*x 1 + (5414027477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061117323/2000000000 : ℝ)^2137 ≤ (43451348414227/100000000000000 : ℝ)^1625 := by
    have hnat : (1061117323 : ℕ)^2137*100000000000000^1625 ≤ 43451348414227^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061117323 2000000000 43451348414227 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992466207/5000000000 : ℝ)^2137 ≤ (1490704698437/12500000000000 : ℝ)^1625 := by
    have hnat : (992466207 : ℕ)^2137*12500000000000^1625 ≤ 1490704698437^1625*5000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992466207 5000000000 1490704698437 12500000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414027477/10000000000 : ℝ)^2137 ≤ (8924602797129/20000000000000 : ℝ)^1625 := by
    have hnat : (5414027477 : ℕ)^2137*20000000000000^1625 ≤ 8924602797129^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414027477 10000000000 8924602797129 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061117323/2000000000 : ℝ), (-992466207/5000000000 : ℝ), (5414027477/10000000000 : ℝ)] ![(43451348414227/100000000000000 : ℝ), (1490704698437/12500000000000 : ℝ), (8924602797129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061117323/2000000000 : ℝ)|^2137 ≤ (43451348414227/100000000000000 : ℝ)^1625
        have hw : |(1061117323/2000000000 : ℝ)|=(1061117323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992466207/5000000000 : ℝ)|^2137 ≤ (1490704698437/12500000000000 : ℝ)^1625
        have hw : |(-992466207/5000000000 : ℝ)|=(992466207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414027477/10000000000 : ℝ)|^2137 ≤ (8924602797129/20000000000000 : ℝ)^1625
        have hw : |(5414027477/10000000000 : ℝ)|=(5414027477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s5_6 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305586783/10000000000 : ℝ)*x 0 + (1082805481/2000000000 : ℝ)*x 1 + (-1984932283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305586783/10000000000 : ℝ)^2137 ≤ (43451350223609/100000000000000 : ℝ)^1625 := by
    have hnat : (5305586783 : ℕ)^2137*100000000000000^1625 ≤ 43451350223609^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305586783 10000000000 43451350223609 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082805481/2000000000 : ℝ)^2137 ≤ (11155753301309/25000000000000 : ℝ)^1625 := by
    have hnat : (1082805481 : ℕ)^2137*25000000000000^1625 ≤ 11155753301309^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082805481 2000000000 11155753301309 25000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1984932283/10000000000 : ℝ)^2137 ≤ (11925636552453/100000000000000 : ℝ)^1625 := by
    have hnat : (1984932283 : ℕ)^2137*100000000000000^1625 ≤ 11925636552453^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984932283 10000000000 11925636552453 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305586783/10000000000 : ℝ), (1082805481/2000000000 : ℝ), (-1984932283/10000000000 : ℝ)] ![(43451350223609/100000000000000 : ℝ), (11155753301309/25000000000000 : ℝ), (11925636552453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305586783/10000000000 : ℝ)|^2137 ≤ (43451350223609/100000000000000 : ℝ)^1625
        have hw : |(5305586783/10000000000 : ℝ)|=(5305586783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082805481/2000000000 : ℝ)|^2137 ≤ (11155753301309/25000000000000 : ℝ)^1625
        have hw : |(1082805481/2000000000 : ℝ)|=(1082805481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1984932283/10000000000 : ℝ)|^2137 ≤ (11925636552453/100000000000000 : ℝ)^1625
        have hw : |(-1984932283/10000000000 : ℝ)|=(1984932283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1314_s5_7 (p : ℝ) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ)) (x : Fin 3 → ℝ) :
    (866797117/2000000000 : ℝ)*x 0 + (4513737901/10000000000 : ℝ)*x 1 + (13003361/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866797117/2000000000 : ℝ)^2137 ≤ (1665133605599/5000000000000 : ℝ)^1625 := by
    have hnat : (866797117 : ℕ)^2137*5000000000000^1625 ≤ 1665133605599^1625*2000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866797117 2000000000 1665133605599 5000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4513737901/10000000000 : ℝ)^2137 ≤ (7026170835739/20000000000000 : ℝ)^1625 := by
    have hnat : (4513737901 : ℕ)^2137*20000000000000^1625 ≤ 7026170835739^1625*10000000000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513737901 10000000000 7026170835739 20000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13003361/31250000 : ℝ)^2137 ≤ (31566473698409/100000000000000 : ℝ)^1625 := by
    have hnat : (13003361 : ℕ)^2137*100000000000000^1625 ≤ 31566473698409^1625*31250000^2137 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13003361 31250000 31566473698409 100000000000000 2137 1625 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2137/512 : ℝ)) 2137 1625 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866797117/2000000000 : ℝ), (4513737901/10000000000 : ℝ), (13003361/31250000 : ℝ)] ![(1665133605599/5000000000000 : ℝ), (7026170835739/20000000000000 : ℝ), (31566473698409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866797117/2000000000 : ℝ)|^2137 ≤ (1665133605599/5000000000000 : ℝ)^1625
        have hw : |(866797117/2000000000 : ℝ)|=(866797117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4513737901/10000000000 : ℝ)|^2137 ≤ (7026170835739/20000000000000 : ℝ)^1625
        have hw : |(4513737901/10000000000 : ℝ)|=(4513737901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13003361/31250000 : ℝ)|^2137 ≤ (31566473698409/100000000000000 : ℝ)^1625
        have hw : |(13003361/31250000 : ℝ)|=(13003361/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1314_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (346/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14699/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (551/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7377/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (551/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7377/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (551/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (551/5000 : ℝ) ^ (4273/1024 : ℝ) ≤ (5036582758198897/50000000000000000000 : ℝ) := by
    have hpowers : (551/5000 : ℝ)^4273 ≤ (5036582758198897/50000000000000000000 : ℝ)^1024 := by
      have hnat : (551 : ℕ)^4273*50000000000000000000^1024 ≤ 5036582758198897^1024*5000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        551 5000 5036582758198897 50000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (551/5000 : ℝ)) (X := (5036582758198897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7377/50000 : ℝ) ^ (4273/1024 : ℝ) ≤ (8509888736789701/25000000000000000000 : ℝ) := by
    have hpowers : (7377/50000 : ℝ)^4273 ≤ (8509888736789701/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7377 : ℕ)^4273*25000000000000000000^1024 ≤ 8509888736789701^1024*50000^4273 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7377 50000 8509888736789701 25000000000000000000 4273 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7377/50000 : ℝ)) (X := (8509888736789701/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25005036582758198897/25000000000000000000 : ℝ) ≤ (10000482758321687/10000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (25005036582758198897/25000000000000000000 : ℝ)^1024 ≤ (10000482758321687/10000000000000000 : ℝ)^4273 := by
      have hnat : (25005036582758198897 : ℕ)^1024*10000000000000000^4273 ≤ 10000482758321687^4273*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005036582758198897 25000000000000000000 10000482758321687 10000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000482758321687/10000000000000000 : ℝ)) (X := (25005036582758198897/25000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022056360231778299/50000000000000000000 : ℝ) ≤ (10001056958861687/10000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (50022056360231778299/50000000000000000000 : ℝ)^1024 ≤ (10001056958861687/10000000000000000 : ℝ)^4273 := by
      have hnat : (50022056360231778299 : ℕ)^1024*10000000000000000^4273 ≤ 10001056958861687^4273*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022056360231778299 50000000000000000000 10001056958861687 10000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001056958861687/10000000000000000 : ℝ)) (X := (50022056360231778299/50000000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508509888736789701/12500000000000000000 : ℝ) ≤ (10001631159401687/10000000000000000 : ℝ) ^ (4273/1024 : ℝ) := by
    have hpowers : (12508509888736789701/12500000000000000000 : ℝ)^1024 ≤ (10001631159401687/10000000000000000 : ℝ)^4273 := by
      have hnat : (12508509888736789701 : ℕ)^1024*10000000000000000^4273 ≤ 10001631159401687^4273*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508509888736789701 12500000000000000000 10001631159401687 10000000000000000 1024 4273 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001631159401687/10000000000000000 : ℝ)) (X := (12508509888736789701/12500000000000000000 : ℝ)) (by norm_num) 4273 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5036582758198897/50000000000000000000 : ℝ) ≤ ((18664573619835789629/18670000000000000000 : ℝ)+2*(28710027/18670000000 : ℝ)*(551/5000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (18664573619835789629/18670000000000000000 : ℝ)+2*(28710027/18670000000 : ℝ)*(551/5000 : ℝ)=(10000482758321687/10000000000000000 : ℝ) by norm_num, show 1+2*(5036582758198897/50000000000000000000 : ℝ)=(25005036582758198897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8509888736789701/25000000000000000000 : ℝ)+(5036582758198897/50000000000000000000 : ℝ) ≤ ((18664573619835789629/18670000000000000000 : ℝ)+(28710027/18670000000 : ℝ)*((7377/50000 : ℝ)+(551/5000 : ℝ)))^(4273/1024 : ℝ) := by
    rw [show (18664573619835789629/18670000000000000000 : ℝ)+(28710027/18670000000 : ℝ)*((7377/50000 : ℝ)+(551/5000 : ℝ))=(10001056958861687/10000000000000000 : ℝ) by norm_num, show 1+(8509888736789701/25000000000000000000 : ℝ)+(5036582758198897/50000000000000000000 : ℝ)=(50022056360231778299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8509888736789701/25000000000000000000 : ℝ) ≤ ((18664573619835789629/18670000000000000000 : ℝ)+2*(28710027/18670000000 : ℝ)*(7377/50000 : ℝ))^(4273/1024 : ℝ) := by
    rw [show (18664573619835789629/18670000000000000000 : ℝ)+2*(28710027/18670000000 : ℝ)*(7377/50000 : ℝ)=(10001631159401687/10000000000000000 : ℝ) by norm_num, show 1+2*(8509888736789701/25000000000000000000 : ℝ)=(12508509888736789701/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18664573619835789629/18670000000000000000 : ℝ)*(X 1 0+X 2 0)+(28710027/18670000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (18664573619835789629/18670000000000000000 : ℝ)) (alpha := (28710027/18670000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18664573619835789629/18670000000000000000 : ℝ)*(X 0 1+X 2 1)+(28710027/18670000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (18664573619835789629/18670000000000000000 : ℝ)) (alpha := (28710027/18670000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18664573619835789629/18670000000000000000 : ℝ)*(X 0 2+X 1 2)+(28710027/18670000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4273/1024 : ℝ)) (lo := (551/5000 : ℝ)) (hi := (7377/50000 : ℝ)) (c := (18664573619835789629/18670000000000000000 : ℝ)) (alpha := (28710027/18670000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-16546793/80000000 : ℝ)*X 0 0+(5414646361/10000000000 : ℝ)*X 0 1+(52432513/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069917637/2000000000 : ℝ)*X 1 0+(-2155708423/10000000000 : ℝ)*X 1 1+(5243251287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674794037/5000000000 : ℝ)*X 2 0+(1310812821/2500000000 : ℝ)*X 2 1+(-1077854287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4333959061/10000000000 : ℝ)*X 0 0+(831958597/2000000000 : ℝ)*X 0 1+(141094189/312500000 : ℝ)*X 0 2+(4333959061/10000000000 : ℝ)*X 1 0+(831958597/2000000000 : ℝ)*X 1 1+(141094189/312500000 : ℝ)*X 1 2+(4333959061/10000000000 : ℝ)*X 2 0+(831958597/2000000000 : ℝ)*X 2 1+(141094189/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-20683619/100000000 : ℝ)*X 0 0+(655483373/1250000000 : ℝ)*X 0 1+(5414027429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061117323/2000000000 : ℝ)*X 1 0+(-992466207/5000000000 : ℝ)*X 1 1+(5414027477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305586783/10000000000 : ℝ)*X 2 0+(1082805481/2000000000 : ℝ)*X 2 1+(-1984932283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866797117/2000000000 : ℝ)*X 0 0+(4513737901/10000000000 : ℝ)*X 0 1+(13003361/31250000 : ℝ)*X 0 2+(866797117/2000000000 : ℝ)*X 1 0+(4513737901/10000000000 : ℝ)*X 1 1+(13003361/31250000 : ℝ)*X 1 2+(866797117/2000000000 : ℝ)*X 2 0+(4513737901/10000000000 : ℝ)*X 2 1+(13003361/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1314_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1366314165263966854421435193/466750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (309301309/50000000000000 : ℝ)*(base19) + (495094471/100000000000000 : ℝ)*(base23) + (2128361/4000000000000 : ℝ)*(upper3) + (15643769/100000000000000 : ℝ)*(lower4) + (2162417048567387/50000000000000 : ℝ)*(major0) + (2162417048567387/50000000000000 : ℝ)*(major1) + (2162417048567387/50000000000000 : ℝ)*(major2) + (2917245413585641/50000000000000 : ℝ)*(sp0) + (5834503879088167/100000000000000 : ℝ)*(sp1) + (5834500149857699/100000000000000 : ℝ)*(sp2) + (703788975371093/25000000000000 : ℝ)*(sp3) + (13670519503/100000000000000 : ℝ)*(sp4) + (481592327/12500000000000 : ℝ)*(sp6) + (7697517933/100000000000000 : ℝ)*(sp7) + (1407581799501153/50000000000000 : ℝ)*(f.failure) + (2917252248845393/50000000000000 : ℝ)*(f.sum) + (10288757867249/1867000000000000000000000000 : ℝ)*base66 + (7268140493027729423/933500000000000000000000000000000 : ℝ)*base67 + (8708932775161729423/933500000000000000000000000000000 : ℝ)*base69 + (12808468047930229423/933500000000000000000000000000000 : ℝ)*base71 + (547498849801/466750000000000000000000000 : ℝ)*base74 + (12052163568204729423/933500000000000000000000000000000 : ℝ)*base75 + (10928130985003729423/933500000000000000000000000000000 : ℝ)*base77 + (10899443131620729423/933500000000000000000000000000000 : ℝ)*base79 + (2538121534277/933500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (19111529/2500000000000000000000 : ℝ)*base89 + (19111529/2500000000000000000000 : ℝ)*base91 + (19111529/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48153147725753526912825423/18670000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (576812783/100000000000000 : ℝ)*(base19) + (109439089/12500000000000 : ℝ)*(base23) + (92425573/100000000000000 : ℝ)*(upper3) + (833283/3125000000000 : ℝ)*(lower4) + (58650387/100000000000000 : ℝ)*(upper5) + (87123809209043/2000000000000 : ℝ)*(major0) + (87123809209043/2000000000000 : ℝ)*(major1) + (87123809209043/2000000000000 : ℝ)*(major2) + (11729261189/100000000000000 : ℝ)*(sp1) + (1924785237/10000000000000 : ℝ)*(sp2) + (2938403221569737/50000000000000 : ℝ)*(sp4) + (2938397068532751/50000000000000 : ℝ)*(sp5) + (734598289971799/12500000000000 : ℝ)*(sp6) + (708893597948101/25000000000000 : ℝ)*(sp7) + (708893597948101/25000000000000 : ℝ)*(f.failure) + (2938403221569737/50000000000000 : ℝ)*(f.sum) + (750223078329/93350000000000000000000000 : ℝ)*base66 + (364687733050384953/37340000000000000000000000000000 : ℝ)*base68 + (557995120954424953/37340000000000000000000000000000 : ℝ)*base70 + (425222355834484953/37340000000000000000000000000000 : ℝ)*base72 + (7466582536543/1867000000000000000000000000 : ℝ)*base74 + (1142424608500764953/37340000000000000000000000000000 : ℝ)*base76 + (281791522942624953/37340000000000000000000000000000 : ℝ)*base78 + (138199327742544953/37340000000000000000000000000000 : ℝ)*base80 + (2496854067597/466750000000000000000000000 : ℝ)*base82 + (11096493/1250000000000000000000 : ℝ)*base89 + (11096493/1250000000000000000000 : ℝ)*base91 + (11096493/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1314_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7377/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (551/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1314_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1314_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4831/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1314_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1314_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1314_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4273/1024 : ℝ) ≤ p) (hpb : p ≤ (2137/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76813193/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (811/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4831/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (346/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14699/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1314_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
