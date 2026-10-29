-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1376_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:06.075239+00:00
-- url     : https://prove2.me/submissions/4fbd31c7-3390-4d74-91af-42b978ffc65c

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
theorem support_rectangle_w1376_s3_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006757349/5000000000 : ℝ)*x 0 + (542302397/1000000000 : ℝ)*x 1 + (5234472163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006757349/5000000000 : ℝ)^271 ≤ (6133698564203/50000000000000 : ℝ)^207 := by
    have hnat : (1006757349 : ℕ)^271*50000000000000^207 ≤ 6133698564203^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006757349 5000000000 6133698564203 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542302397/1000000000 : ℝ)^271 ≤ (22441126641043/50000000000000 : ℝ)^207 := by
    have hnat : (542302397 : ℕ)^271*50000000000000^207 ≤ 22441126641043^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542302397 1000000000 22441126641043 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234472163/10000000000 : ℝ)^271 ≤ (535629369617/1250000000000 : ℝ)^207 := by
    have hnat : (5234472163 : ℕ)^271*1250000000000^207 ≤ 535629369617^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234472163 10000000000 535629369617 1250000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006757349/5000000000 : ℝ), (542302397/1000000000 : ℝ), (5234472163/10000000000 : ℝ)] ![(6133698564203/50000000000000 : ℝ), (22441126641043/50000000000000 : ℝ), (535629369617/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006757349/5000000000 : ℝ)|^271 ≤ (6133698564203/50000000000000 : ℝ)^207
        have hw : |(-1006757349/5000000000 : ℝ)|=(1006757349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542302397/1000000000 : ℝ)|^271 ≤ (22441126641043/50000000000000 : ℝ)^207
        have hw : |(542302397/1000000000 : ℝ)|=(542302397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234472163/10000000000 : ℝ)|^271 ≤ (535629369617/1250000000000 : ℝ)^207
        have hw : |(5234472163/10000000000 : ℝ)|=(5234472163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (107029583/200000000 : ℝ)*x 0 + (-2109800183/10000000000 : ℝ)*x 1 + (2617236021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107029583/200000000 : ℝ)^271 ≤ (22054322665617/50000000000000 : ℝ)^207 := by
    have hnat : (107029583 : ℕ)^271*50000000000000^207 ≤ 22054322665617^207*200000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107029583 200000000 22054322665617 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109800183/10000000000 : ℝ)^271 ≤ (13041006383947/100000000000000 : ℝ)^207 := by
    have hnat : (2109800183 : ℕ)^271*100000000000000^207 ≤ 13041006383947^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109800183 10000000000 13041006383947 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2617236021/5000000000 : ℝ)^271 ≤ (21425174136291/50000000000000 : ℝ)^207 := by
    have hnat : (2617236021 : ℕ)^271*50000000000000^207 ≤ 21425174136291^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617236021 5000000000 21425174136291 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107029583/200000000 : ℝ), (-2109800183/10000000000 : ℝ), (2617236021/5000000000 : ℝ)] ![(22054322665617/50000000000000 : ℝ), (13041006383947/100000000000000 : ℝ), (21425174136291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107029583/200000000 : ℝ)|^271 ≤ (22054322665617/50000000000000 : ℝ)^207
        have hw : |(107029583/200000000 : ℝ)|=(107029583/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109800183/10000000000 : ℝ)|^271 ≤ (13041006383947/100000000000000 : ℝ)^207
        have hw : |(-2109800183/10000000000 : ℝ)|=(2109800183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2617236021/5000000000 : ℝ)|^271 ≤ (21425174136291/50000000000000 : ℝ)^207
        have hw : |(2617236021/5000000000 : ℝ)|=(2617236021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2675739583/5000000000 : ℝ)*x 0 + (163577253/312500000 : ℝ)*x 1 + (-210980009/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675739583/5000000000 : ℝ)^271 ≤ (8821729100777/20000000000000 : ℝ)^207 := by
    have hnat : (2675739583 : ℕ)^271*20000000000000^207 ≤ 8821729100777^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675739583 5000000000 8821729100777 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163577253/312500000 : ℝ)^271 ≤ (42850348851309/100000000000000 : ℝ)^207 := by
    have hnat : (163577253 : ℕ)^271*100000000000000^207 ≤ 42850348851309^207*312500000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163577253 312500000 42850348851309 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210980009/1000000000 : ℝ)^271 ≤ (13041005631369/100000000000000 : ℝ)^207 := by
    have hnat : (210980009 : ℕ)^271*100000000000000^207 ≤ 13041005631369^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210980009 1000000000 13041005631369 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675739583/5000000000 : ℝ), (163577253/312500000 : ℝ), (-210980009/1000000000 : ℝ)] ![(8821729100777/20000000000000 : ℝ), (42850348851309/100000000000000 : ℝ), (13041005631369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675739583/5000000000 : ℝ)|^271 ≤ (8821729100777/20000000000000 : ℝ)^207
        have hw : |(2675739583/5000000000 : ℝ)|=(2675739583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163577253/312500000 : ℝ)|^271 ≤ (42850348851309/100000000000000 : ℝ)^207
        have hw : |(163577253/312500000 : ℝ)|=(163577253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-210980009/1000000000 : ℝ)|^271 ≤ (13041005631369/100000000000000 : ℝ)^207
        have hw : |(-210980009/1000000000 : ℝ)|=(210980009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4316930699/10000000000 : ℝ)*x 0 + (1030299149/2500000000 : ℝ)*x 1 + (4521190613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316930699/10000000000 : ℝ)^271 ≤ (16647497934557/50000000000000 : ℝ)^207 := by
    have hnat : (4316930699 : ℕ)^271*50000000000000^207 ≤ 16647497934557^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316930699 10000000000 16647497934557 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030299149/2500000000 : ℝ)^271 ≤ (783315532951/2500000000000 : ℝ)^207 := by
    have hnat : (1030299149 : ℕ)^271*2500000000000^207 ≤ 783315532951^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030299149 2500000000 783315532951 2500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4521190613/10000000000 : ℝ)^271 ≤ (1768619139929/5000000000000 : ℝ)^207 := by
    have hnat : (4521190613 : ℕ)^271*5000000000000^207 ≤ 1768619139929^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521190613 10000000000 1768619139929 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316930699/10000000000 : ℝ), (1030299149/2500000000 : ℝ), (4521190613/10000000000 : ℝ)] ![(16647497934557/50000000000000 : ℝ), (783315532951/2500000000000 : ℝ), (1768619139929/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316930699/10000000000 : ℝ)|^271 ≤ (16647497934557/50000000000000 : ℝ)^207
        have hw : |(4316930699/10000000000 : ℝ)|=(4316930699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030299149/2500000000 : ℝ)|^271 ≤ (783315532951/2500000000000 : ℝ)^207
        have hw : |(1030299149/2500000000 : ℝ)|=(1030299149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4521190613/10000000000 : ℝ)|^271 ≤ (1768619139929/5000000000000 : ℝ)^207
        have hw : |(4521190613/10000000000 : ℝ)|=(4521190613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013532693/10000000000 : ℝ)*x 0 + (2617621669/5000000000 : ℝ)*x 1 + (2711123953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013532693/10000000000 : ℝ)^271 ≤ (12267540660499/100000000000000 : ℝ)^207 := by
    have hnat : (2013532693 : ℕ)^271*100000000000000^207 ≤ 12267540660499^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013532693 10000000000 12267540660499 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617621669/5000000000 : ℝ)^271 ≤ (10714653644219/25000000000000 : ℝ)^207 := by
    have hnat : (2617621669 : ℕ)^271*25000000000000^207 ≤ 10714653644219^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617621669 5000000000 10714653644219 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711123953/5000000000 : ℝ)^271 ≤ (44873844753531/100000000000000 : ℝ)^207 := by
    have hnat : (2711123953 : ℕ)^271*100000000000000^207 ≤ 44873844753531^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711123953 5000000000 44873844753531 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013532693/10000000000 : ℝ), (2617621669/5000000000 : ℝ), (2711123953/5000000000 : ℝ)] ![(12267540660499/100000000000000 : ℝ), (10714653644219/25000000000000 : ℝ), (44873844753531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013532693/10000000000 : ℝ)|^271 ≤ (12267540660499/100000000000000 : ℝ)^207
        have hw : |(-2013532693/10000000000 : ℝ)|=(2013532693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617621669/5000000000 : ℝ)|^271 ≤ (10714653644219/25000000000000 : ℝ)^207
        have hw : |(2617621669/5000000000 : ℝ)|=(2617621669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711123953/5000000000 : ℝ)|^271 ≤ (44873844753531/100000000000000 : ℝ)^207
        have hw : |(2711123953/5000000000 : ℝ)|=(2711123953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2651363563/5000000000 : ℝ)*x 0 + (-76880949/400000000 : ℝ)*x 1 + (2711124339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651363563/5000000000 : ℝ)^271 ≤ (43583320250613/100000000000000 : ℝ)^207 := by
    have hnat : (2651363563 : ℕ)^271*100000000000000^207 ≤ 43583320250613^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651363563 5000000000 43583320250613 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76880949/400000000 : ℝ)^271 ≤ (5771413309971/50000000000000 : ℝ)^207 := by
    have hnat : (76880949 : ℕ)^271*50000000000000^207 ≤ 5771413309971^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76880949 400000000 5771413309971 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711124339/5000000000 : ℝ)^271 ≤ (22436926558921/50000000000000 : ℝ)^207 := by
    have hnat : (2711124339 : ℕ)^271*50000000000000^207 ≤ 22436926558921^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711124339 5000000000 22436926558921 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651363563/5000000000 : ℝ), (-76880949/400000000 : ℝ), (2711124339/5000000000 : ℝ)] ![(43583320250613/100000000000000 : ℝ), (5771413309971/50000000000000 : ℝ), (22436926558921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651363563/5000000000 : ℝ)|^271 ≤ (43583320250613/100000000000000 : ℝ)^207
        have hw : |(2651363563/5000000000 : ℝ)|=(2651363563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76880949/400000000 : ℝ)|^271 ≤ (5771413309971/50000000000000 : ℝ)^207
        have hw : |(-76880949/400000000 : ℝ)|=(76880949/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711124339/5000000000 : ℝ)|^271 ≤ (22436926558921/50000000000000 : ℝ)^207
        have hw : |(2711124339/5000000000 : ℝ)|=(2711124339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2651364287/5000000000 : ℝ)*x 0 + (5422247591/10000000000 : ℝ)*x 1 + (-961011621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651364287/5000000000 : ℝ)^271 ≤ (4358333583137/10000000000000 : ℝ)^207 := by
    have hnat : (2651364287 : ℕ)^271*10000000000000^207 ≤ 4358333583137^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651364287 5000000000 4358333583137 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422247591/10000000000 : ℝ)^271 ≤ (5609230167579/12500000000000 : ℝ)^207 := by
    have hnat : (5422247591 : ℕ)^271*12500000000000^207 ≤ 5609230167579^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422247591 10000000000 5609230167579 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961011621/5000000000 : ℝ)^271 ≤ (2885705705607/25000000000000 : ℝ)^207 := by
    have hnat : (961011621 : ℕ)^271*25000000000000^207 ≤ 2885705705607^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961011621 5000000000 2885705705607 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651364287/5000000000 : ℝ), (5422247591/10000000000 : ℝ), (-961011621/5000000000 : ℝ)] ![(4358333583137/10000000000000 : ℝ), (5609230167579/12500000000000 : ℝ), (2885705705607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651364287/5000000000 : ℝ)|^271 ≤ (4358333583137/10000000000000 : ℝ)^207
        have hw : |(2651364287/5000000000 : ℝ)|=(2651364287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422247591/10000000000 : ℝ)|^271 ≤ (5609230167579/12500000000000 : ℝ)^207
        have hw : |(5422247591/10000000000 : ℝ)|=(5422247591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-961011621/5000000000 : ℝ)|^271 ≤ (2885705705607/25000000000000 : ℝ)^207
        have hw : |(-961011621/5000000000 : ℝ)|=(961011621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2158484837/5000000000 : ℝ)*x 0 + (451955357/1000000000 : ℝ)*x 1 + (1030710367/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158484837/5000000000 : ℝ)^271 ≤ (8323847352433/25000000000000 : ℝ)^207 := by
    have hnat : (2158484837 : ℕ)^271*25000000000000^207 ≤ 8323847352433^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158484837 5000000000 8323847352433 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451955357/1000000000 : ℝ)^271 ≤ (35355616151629/100000000000000 : ℝ)^207 := by
    have hnat : (451955357 : ℕ)^271*100000000000000^207 ≤ 35355616151629^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451955357 1000000000 35355616151629 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030710367/2500000000 : ℝ)^271 ≤ (15674497215227/50000000000000 : ℝ)^207 := by
    have hnat : (1030710367 : ℕ)^271*50000000000000^207 ≤ 15674497215227^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030710367 2500000000 15674497215227 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158484837/5000000000 : ℝ), (451955357/1000000000 : ℝ), (1030710367/2500000000 : ℝ)] ![(8323847352433/25000000000000 : ℝ), (35355616151629/100000000000000 : ℝ), (15674497215227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158484837/5000000000 : ℝ)|^271 ≤ (8323847352433/25000000000000 : ℝ)^207
        have hw : |(2158484837/5000000000 : ℝ)|=(2158484837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451955357/1000000000 : ℝ)|^271 ≤ (35355616151629/100000000000000 : ℝ)^207
        have hw : |(451955357/1000000000 : ℝ)|=(451955357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030710367/2500000000 : ℝ)|^271 ≤ (15674497215227/50000000000000 : ℝ)^207
        have hw : |(1030710367/2500000000 : ℝ)|=(1030710367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_8 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-16601723/2000000000 : ℝ)*x 0 + (1429025567/2500000000 : ℝ)*x 1 + (1511014183/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16601723/2000000000 : ℝ)^271 ≤ (1179343451/625000000000 : ℝ)^207 := by
    have hnat : (16601723 : ℕ)^271*625000000000^207 ≤ 1179343451^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16601723 2000000000 1179343451 625000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429025567/2500000000 : ℝ)^271 ≤ (2404199345871/5000000000000 : ℝ)^207 := by
    have hnat : (1429025567 : ℕ)^271*5000000000000^207 ≤ 2404199345871^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429025567 2500000000 2404199345871 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1511014183/2500000000 : ℝ)^271 ≤ (6465914765537/12500000000000 : ℝ)^207 := by
    have hnat : (1511014183 : ℕ)^271*12500000000000^207 ≤ 6465914765537^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511014183 2500000000 6465914765537 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-16601723/2000000000 : ℝ), (1429025567/2500000000 : ℝ), (1511014183/2500000000 : ℝ)] ![(1179343451/625000000000 : ℝ), (2404199345871/5000000000000 : ℝ), (6465914765537/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-16601723/2000000000 : ℝ)|^271 ≤ (1179343451/625000000000 : ℝ)^207
        have hw : |(-16601723/2000000000 : ℝ)|=(16601723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1429025567/2500000000 : ℝ)|^271 ≤ (2404199345871/5000000000000 : ℝ)^207
        have hw : |(1429025567/2500000000 : ℝ)|=(1429025567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1511014183/2500000000 : ℝ)|^271 ≤ (6465914765537/12500000000000 : ℝ)^207
        have hw : |(1511014183/2500000000 : ℝ)|=(1511014183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_9 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (51346191/500000000 : ℝ)*x 0 + (-2115323031/5000000000 : ℝ)*x 1 + (279323347/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51346191/500000000 : ℝ)^271 ≤ (635092335297/12500000000000 : ℝ)^207 := by
    have hnat : (51346191 : ℕ)^271*12500000000000^207 ≤ 635092335297^207*500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51346191 500000000 635092335297 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115323031/5000000000 : ℝ)^271 ≤ (16213231680979/50000000000000 : ℝ)^207 := by
    have hnat : (2115323031 : ℕ)^271*50000000000000^207 ≤ 16213231680979^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115323031 5000000000 16213231680979 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279323347/400000000 : ℝ)^271 ≤ (12498559588089/20000000000000 : ℝ)^207 := by
    have hnat : (279323347 : ℕ)^271*20000000000000^207 ≤ 12498559588089^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279323347 400000000 12498559588089 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(51346191/500000000 : ℝ), (-2115323031/5000000000 : ℝ), (279323347/400000000 : ℝ)] ![(635092335297/12500000000000 : ℝ), (16213231680979/50000000000000 : ℝ), (12498559588089/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(51346191/500000000 : ℝ)|^271 ≤ (635092335297/12500000000000 : ℝ)^207
        have hw : |(51346191/500000000 : ℝ)|=(51346191/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2115323031/5000000000 : ℝ)|^271 ≤ (16213231680979/50000000000000 : ℝ)^207
        have hw : |(-2115323031/5000000000 : ℝ)|=(2115323031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279323347/400000000 : ℝ)|^271 ≤ (12498559588089/20000000000000 : ℝ)^207
        have hw : |(279323347/400000000 : ℝ)|=(279323347/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_10 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (513469027/5000000000 : ℝ)*x 0 + (279324601/400000000 : ℝ)*x 1 + (-423060027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (513469027/5000000000 : ℝ)^271 ≤ (635103859887/12500000000000 : ℝ)^207 := by
    have hnat : (513469027 : ℕ)^271*12500000000000^207 ≤ 635103859887^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513469027 5000000000 635103859887 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279324601/400000000 : ℝ)^271 ≤ (249972660957/400000000000 : ℝ)^207 := by
    have hnat : (279324601 : ℕ)^271*400000000000^207 ≤ 249972660957^207*400000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279324601 400000000 249972660957 400000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423060027/1000000000 : ℝ)^271 ≤ (32426003867031/100000000000000 : ℝ)^207 := by
    have hnat : (423060027 : ℕ)^271*100000000000000^207 ≤ 32426003867031^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423060027 1000000000 32426003867031 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(513469027/5000000000 : ℝ), (279324601/400000000 : ℝ), (-423060027/1000000000 : ℝ)] ![(635103859887/12500000000000 : ℝ), (249972660957/400000000000 : ℝ), (32426003867031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(513469027/5000000000 : ℝ)|^271 ≤ (635103859887/12500000000000 : ℝ)^207
        have hw : |(513469027/5000000000 : ℝ)|=(513469027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(279324601/400000000 : ℝ)|^271 ≤ (249972660957/400000000000 : ℝ)^207
        have hw : |(279324601/400000000 : ℝ)|=(279324601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-423060027/1000000000 : ℝ)|^271 ≤ (32426003867031/100000000000000 : ℝ)^207
        have hw : |(-423060027/1000000000 : ℝ)|=(423060027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s3_11 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (192506561/2000000000 : ℝ)*x 0 + (5835785333/10000000000 : ℝ)*x 1 + (5519087579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (192506561/2000000000 : ℝ)^271 ≤ (4667767690591/100000000000000 : ℝ)^207 := by
    have hnat : (192506561 : ℕ)^271*100000000000000^207 ≤ 4667767690591^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192506561 2000000000 4667767690591 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5835785333/10000000000 : ℝ)^271 ≤ (24703141748299/50000000000000 : ℝ)^207 := by
    have hnat : (5835785333 : ℕ)^271*50000000000000^207 ≤ 24703141748299^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835785333 10000000000 24703141748299 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519087579/10000000000 : ℝ)^271 ≤ (45925948796847/100000000000000 : ℝ)^207 := by
    have hnat : (5519087579 : ℕ)^271*100000000000000^207 ≤ 45925948796847^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519087579 10000000000 45925948796847 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(192506561/2000000000 : ℝ), (5835785333/10000000000 : ℝ), (5519087579/10000000000 : ℝ)] ![(4667767690591/100000000000000 : ℝ), (24703141748299/50000000000000 : ℝ), (45925948796847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(192506561/2000000000 : ℝ)|^271 ≤ (4667767690591/100000000000000 : ℝ)^207
        have hw : |(192506561/2000000000 : ℝ)|=(192506561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5835785333/10000000000 : ℝ)|^271 ≤ (24703141748299/50000000000000 : ℝ)^207
        have hw : |(5835785333/10000000000 : ℝ)|=(5835785333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519087579/10000000000 : ℝ)|^271 ≤ (45925948796847/100000000000000 : ℝ)^207
        have hw : |(5519087579/10000000000 : ℝ)|=(5519087579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1997/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5033/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10989/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (749/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1997/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5033/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1997/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5033/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1997/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5033/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1997/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5033/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1997/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5033/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1997/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5033/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5033/50000 : ℝ) ^ (4335/1024 : ℝ) ≤ (93867682314381/1562500000000000000 : ℝ) := by
    have hpowers : (5033/50000 : ℝ)^4335 ≤ (93867682314381/1562500000000000000 : ℝ)^1024 := by
      have hnat : (5033 : ℕ)^4335*1562500000000000000^1024 ≤ 93867682314381^1024*50000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5033 50000 93867682314381 1562500000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5033/50000 : ℝ)) (X := (93867682314381/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1997/12500 : ℝ) ^ (4335/1024 : ℝ) ≤ (42458328742503383/100000000000000000000 : ℝ) := by
    have hpowers : (1997/12500 : ℝ)^4335 ≤ (42458328742503383/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1997 : ℕ)^4335*100000000000000000000^1024 ≤ 42458328742503383^1024*12500^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1997 12500 42458328742503383 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1997/12500 : ℝ)) (X := (42458328742503383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781343867682314381/781250000000000000 : ℝ) ≤ (500014190150357/500000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (781343867682314381/781250000000000000 : ℝ)^1024 ≤ (500014190150357/500000000000000 : ℝ)^4335 := by
      have hnat : (781343867682314381 : ℕ)^1024*500000000000000^4335 ≤ 500014190150357^4335*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781343867682314381 781250000000000000 500014190150357 500000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014190150357/500000000000000 : ℝ)) (X := (781343867682314381/781250000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048465860410623767/100000000000000000000 : ℝ) ≤ (2000228926680437/2000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (100048465860410623767/100000000000000000000 : ℝ)^1024 ≤ (2000228926680437/2000000000000000 : ℝ)^4335 := by
      have hnat : (100048465860410623767 : ℕ)^1024*2000000000000000^4335 ≤ 2000228926680437^4335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048465860410623767 100000000000000000000 2000228926680437 2000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000228926680437/2000000000000000 : ℝ)) (X := (100048465860410623767/100000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042458328742503383/50000000000000000000 : ℝ) ≤ (1000200546379723/1000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50042458328742503383/50000000000000000000 : ℝ)^1024 ≤ (1000200546379723/1000000000000000 : ℝ)^4335 := by
      have hnat : (50042458328742503383 : ℕ)^1024*1000000000000000^4335 ≤ 1000200546379723^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042458328742503383 50000000000000000000 1000200546379723 1000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000200546379723/1000000000000000 : ℝ)) (X := (50042458328742503383/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(93867682314381/1562500000000000000 : ℝ) ≤ ((984739117304319191/985000000000000000 : ℝ)+2*(57388693003/39400000000000 : ℝ)*(5033/50000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (984739117304319191/985000000000000000 : ℝ)+2*(57388693003/39400000000000 : ℝ)*(5033/50000 : ℝ)=(500014190150357/500000000000000 : ℝ) by norm_num, show 1+2*(93867682314381/1562500000000000000 : ℝ)=(781343867682314381/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42458328742503383/100000000000000000000 : ℝ)+(93867682314381/1562500000000000000 : ℝ) ≤ ((984739117304319191/985000000000000000 : ℝ)+(57388693003/39400000000000 : ℝ)*((1997/12500 : ℝ)+(5033/50000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (984739117304319191/985000000000000000 : ℝ)+(57388693003/39400000000000 : ℝ)*((1997/12500 : ℝ)+(5033/50000 : ℝ))=(2000228926680437/2000000000000000 : ℝ) by norm_num, show 1+(42458328742503383/100000000000000000000 : ℝ)+(93867682314381/1562500000000000000 : ℝ)=(100048465860410623767/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42458328742503383/100000000000000000000 : ℝ) ≤ ((984739117304319191/985000000000000000 : ℝ)+2*(57388693003/39400000000000 : ℝ)*(1997/12500 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (984739117304319191/985000000000000000 : ℝ)+2*(57388693003/39400000000000 : ℝ)*(1997/12500 : ℝ)=(1000200546379723/1000000000000000 : ℝ) by norm_num, show 1+2*(42458328742503383/100000000000000000000 : ℝ)=(50042458328742503383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (984739117304319191/985000000000000000 : ℝ)*(X 1 0+X 2 0)+(57388693003/39400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (5033/50000 : ℝ)) (hi := (1997/12500 : ℝ)) (c := (984739117304319191/985000000000000000 : ℝ)) (alpha := (57388693003/39400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (984739117304319191/985000000000000000 : ℝ)*(X 0 1+X 2 1)+(57388693003/39400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (5033/50000 : ℝ)) (hi := (1997/12500 : ℝ)) (c := (984739117304319191/985000000000000000 : ℝ)) (alpha := (57388693003/39400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (984739117304319191/985000000000000000 : ℝ)*(X 0 2+X 1 2)+(57388693003/39400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (5033/50000 : ℝ)) (hi := (1997/12500 : ℝ)) (c := (984739117304319191/985000000000000000 : ℝ)) (alpha := (57388693003/39400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1006757349/5000000000 : ℝ)*X 0 0+(542302397/1000000000 : ℝ)*X 0 1+(5234472163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107029583/200000000 : ℝ)*X 1 0+(-2109800183/10000000000 : ℝ)*X 1 1+(2617236021/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675739583/5000000000 : ℝ)*X 2 0+(163577253/312500000 : ℝ)*X 2 1+(-210980009/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4316930699/10000000000 : ℝ)*X 0 0+(1030299149/2500000000 : ℝ)*X 0 1+(4521190613/10000000000 : ℝ)*X 0 2+(4316930699/10000000000 : ℝ)*X 1 0+(1030299149/2500000000 : ℝ)*X 1 1+(4521190613/10000000000 : ℝ)*X 1 2+(4316930699/10000000000 : ℝ)*X 2 0+(1030299149/2500000000 : ℝ)*X 2 1+(4521190613/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2013532693/10000000000 : ℝ)*X 0 0+(2617621669/5000000000 : ℝ)*X 0 1+(2711123953/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651363563/5000000000 : ℝ)*X 1 0+(-76880949/400000000 : ℝ)*X 1 1+(2711124339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651364287/5000000000 : ℝ)*X 2 0+(5422247591/10000000000 : ℝ)*X 2 1+(-961011621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158484837/5000000000 : ℝ)*X 0 0+(451955357/1000000000 : ℝ)*X 0 1+(1030710367/2500000000 : ℝ)*X 0 2+(2158484837/5000000000 : ℝ)*X 1 0+(451955357/1000000000 : ℝ)*X 1 1+(1030710367/2500000000 : ℝ)*X 1 2+(2158484837/5000000000 : ℝ)*X 2 0+(451955357/1000000000 : ℝ)*X 2 1+(1030710367/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-16601723/2000000000 : ℝ)*X 0 0+(1429025567/2500000000 : ℝ)*X 0 1+(1511014183/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((51346191/500000000 : ℝ)*X 1 0+(-2115323031/5000000000 : ℝ)*X 1 1+(279323347/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((513469027/5000000000 : ℝ)*X 2 0+(279324601/400000000 : ℝ)*X 2 1+(-423060027/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((192506561/2000000000 : ℝ)*X 0 0+(5835785333/10000000000 : ℝ)*X 0 1+(5519087579/10000000000 : ℝ)*X 0 2+(192506561/2000000000 : ℝ)*X 1 0+(5835785333/10000000000 : ℝ)*X 1 1+(5519087579/10000000000 : ℝ)*X 1 2+(192506561/2000000000 : ℝ)*X 2 0+(5835785333/10000000000 : ℝ)*X 2 1+(5519087579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (599268659191589327657194749/49250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (323892389/50000000000000 : ℝ)*(lower2) + (41815367/100000000000000 : ℝ)*(lower4) + (3901807031640943/100000000000000 : ℝ)*(major0) + (3901807031640943/100000000000000 : ℝ)*(major1) + (243862939477559/6250000000000 : ℝ)*(major2) + (2651786031917329/50000000000000 : ℝ)*(sp0) + (5303568970983157/100000000000000 : ℝ)*(sp1) + (1060715061915973/20000000000000 : ℝ)*(sp2) + (1250017449287189/50000000000000 : ℝ)*(sp3) + (5013508321/100000000000000 : ℝ)*(sp5) + (1718933443/50000000000000 : ℝ)*(sp7) + (1628704787/50000000000000 : ℝ)*(sp8) + (668376377/50000000000000 : ℝ)*(sp9) + (11664367/100000000000000 : ℝ)*(sp10) + (156252396027579/6250000000000 : ℝ)*(f.failure) + (662946915155529/12500000000000 : ℝ)*(f.sum) + (7002458894181/3940000000000000000000000000 : ℝ)*base65 + (1042907851647037113/98500000000000000000000000000000 : ℝ)*base67 + (106386517912785163/12312500000000000000000000000000 : ℝ)*base69 + (616105117659962887/98500000000000000000000000000000 : ℝ)*base72 + (230396153099/3940000000000000000000000000 : ℝ)*base74 + (66115288367785163/12312500000000000000000000000000 : ℝ)*base75 + (791461085012962113/98500000000000000000000000000000 : ℝ)*base77 + (343729164706462113/98500000000000000000000000000000 : ℝ)*base79 + (4916539159511/1970000000000000000000000000 : ℝ)*base82 + (355697/39062500000000000000 : ℝ)*base89 + (355697/39062500000000000000 : ℝ)*base91 + (2183/2441406250000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (140715515247156113830115523/49250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (118614319/100000000000000 : ℝ)*(lower4) + (78681895516261/2000000000000 : ℝ)*(major0) + (78681895516261/2000000000000 : ℝ)*(major1) + (3934094775813051/100000000000000 : ℝ)*(major2) + (13766538789/100000000000000 : ℝ)*(sp1) + (980790067/100000000000000 : ℝ)*(sp2) + (1262784033/50000000000000 : ℝ)*(sp3) + (1336865158615767/25000000000000 : ℝ)*(sp4) + (2673724674863781/50000000000000 : ℝ)*(sp5) + (1069492038585239/20000000000000 : ℝ)*(sp6) + (1260361072050153/50000000000000 : ℝ)*(sp7) + (2481803283/100000000000000 : ℝ)*(sp8) + (1942550089/100000000000000 : ℝ)*(sp10) + (1670452441/100000000000000 : ℝ)*(sp11) + (630181585030203/25000000000000 : ℝ)*(f.failure) + (5347463116266351/100000000000000 : ℝ)*(f.sum) + (18735007571857/3940000000000000000000000000 : ℝ)*base66 + (17809050994948649/1970000000000000000000000000000 : ℝ)*base68 + (1018626122470188259/98500000000000000000000000000000 : ℝ)*base70 + (40738809077708649/1970000000000000000000000000000 : ℝ)*base72 + (1628895989623/3940000000000000000000000000 : ℝ)*base73 + (706431693355188259/98500000000000000000000000000000 : ℝ)*base76 + (29219423895330149/1970000000000000000000000000000 : ℝ)*base78 + (22754504977230149/1970000000000000000000000000000 : ℝ)*base80 + (6444527359/9850000000000000000000000 : ℝ)*base81 + (68963/19531250000000000000 : ℝ)*base89 + (68963/19531250000000000000 : ℝ)*base91 + (252699/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1376_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1997/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5033/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (749/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1376_s4_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-503681997/2500000000 : ℝ)*x 0 + (541296229/1000000000 : ℝ)*x 1 + (1310934003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503681997/2500000000 : ℝ)^271 ≤ (3069268871319/25000000000000 : ℝ)^207 := by
    have hnat : (503681997 : ℕ)^271*25000000000000^207 ≤ 3069268871319^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503681997 2500000000 3069268871319 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541296229/1000000000 : ℝ)^271 ≤ (1790930618749/4000000000000 : ℝ)^207 := by
    have hnat : (541296229 : ℕ)^271*4000000000000^207 ≤ 1790930618749^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541296229 1000000000 1790930618749 4000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310934003/2500000000 : ℝ)^271 ≤ (42949659034069/100000000000000 : ℝ)^207 := by
    have hnat : (1310934003 : ℕ)^271*100000000000000^207 ≤ 42949659034069^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310934003 2500000000 42949659034069 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503681997/2500000000 : ℝ), (541296229/1000000000 : ℝ), (1310934003/2500000000 : ℝ)] ![(3069268871319/25000000000000 : ℝ), (1790930618749/4000000000000 : ℝ), (42949659034069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503681997/2500000000 : ℝ)|^271 ≤ (3069268871319/25000000000000 : ℝ)^207
        have hw : |(-503681997/2500000000 : ℝ)|=(503681997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541296229/1000000000 : ℝ)|^271 ≤ (1790930618749/4000000000000 : ℝ)^207
        have hw : |(541296229/1000000000 : ℝ)|=(541296229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310934003/2500000000 : ℝ)|^271 ≤ (42949659034069/100000000000000 : ℝ)^207
        have hw : |(1310934003/2500000000 : ℝ)|=(1310934003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s4_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348900581/10000000000 : ℝ)*x 0 + (-42019197/200000000 : ℝ)*x 1 + (655467041/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348900581/10000000000 : ℝ)^271 ≤ (8816164578043/20000000000000 : ℝ)^207 := by
    have hnat : (5348900581 : ℕ)^271*20000000000000^207 ≤ 8816164578043^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348900581 10000000000 8816164578043 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42019197/200000000 : ℝ)^271 ≤ (12969514675673/100000000000000 : ℝ)^207 := by
    have hnat : (42019197 : ℕ)^271*100000000000000^207 ≤ 12969514675673^207*200000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42019197 200000000 12969514675673 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655467041/1250000000 : ℝ)^271 ≤ (42949662422549/100000000000000 : ℝ)^207 := by
    have hnat : (655467041 : ℕ)^271*100000000000000^207 ≤ 42949662422549^207*1250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655467041 1250000000 42949662422549 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348900581/10000000000 : ℝ), (-42019197/200000000 : ℝ), (655467041/1250000000 : ℝ)] ![(8816164578043/20000000000000 : ℝ), (12969514675673/100000000000000 : ℝ), (42949662422549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348900581/10000000000 : ℝ)|^271 ≤ (8816164578043/20000000000000 : ℝ)^207
        have hw : |(5348900581/10000000000 : ℝ)|=(5348900581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42019197/200000000 : ℝ)|^271 ≤ (12969514675673/100000000000000 : ℝ)^207
        have hw : |(-42019197/200000000 : ℝ)|=(42019197/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655467041/1250000000 : ℝ)|^271 ≤ (42949662422549/100000000000000 : ℝ)^207
        have hw : |(655467041/1250000000 : ℝ)|=(655467041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s4_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348900649/10000000000 : ℝ)*x 0 + (327733493/625000000 : ℝ)*x 1 + (-1050480171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348900649/10000000000 : ℝ)^271 ≤ (688762869123/1562500000000 : ℝ)^207 := by
    have hnat : (5348900649 : ℕ)^271*1562500000000^207 ≤ 688762869123^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348900649 10000000000 688762869123 1562500000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (327733493/625000000 : ℝ)^271 ≤ (10737414426103/25000000000000 : ℝ)^207 := by
    have hnat : (327733493 : ℕ)^271*25000000000000^207 ≤ 10737414426103^207*625000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327733493 625000000 10737414426103 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050480171/5000000000 : ℝ)^271 ≤ (1296951865189/10000000000000 : ℝ)^207 := by
    have hnat : (1050480171 : ℕ)^271*10000000000000^207 ≤ 1296951865189^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050480171 5000000000 1296951865189 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348900649/10000000000 : ℝ), (327733493/625000000 : ℝ), (-1050480171/5000000000 : ℝ)] ![(688762869123/1562500000000 : ℝ), (10737414426103/25000000000000 : ℝ), (1296951865189/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348900649/10000000000 : ℝ)|^271 ≤ (688762869123/1562500000000 : ℝ)^207
        have hw : |(5348900649/10000000000 : ℝ)|=(5348900649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(327733493/625000000 : ℝ)|^271 ≤ (10737414426103/25000000000000 : ℝ)^207
        have hw : |(327733493/625000000 : ℝ)|=(327733493/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1050480171/5000000000 : ℝ)|^271 ≤ (1296951865189/10000000000000 : ℝ)^207
        have hw : |(-1050480171/5000000000 : ℝ)|=(1050480171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s4_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4317669001/10000000000 : ℝ)*x 0 + (258850277/625000000 : ℝ)*x 1 + (900120289/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317669001/10000000000 : ℝ)^271 ≤ (6660490176269/20000000000000 : ℝ)^207 := by
    have hnat : (4317669001 : ℕ)^271*20000000000000^207 ≤ 6660490176269^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317669001 10000000000 6660490176269 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258850277/625000000 : ℝ)^271 ≤ (3153590440723/10000000000000 : ℝ)^207 := by
    have hnat : (258850277 : ℕ)^271*10000000000000^207 ≤ 3153590440723^207*625000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258850277 625000000 3153590440723 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900120289/2000000000 : ℝ)^271 ≤ (8790411172931/25000000000000 : ℝ)^207 := by
    have hnat : (900120289 : ℕ)^271*25000000000000^207 ≤ 8790411172931^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900120289 2000000000 8790411172931 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317669001/10000000000 : ℝ), (258850277/625000000 : ℝ), (900120289/2000000000 : ℝ)] ![(6660490176269/20000000000000 : ℝ), (3153590440723/10000000000000 : ℝ), (8790411172931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317669001/10000000000 : ℝ)|^271 ≤ (6660490176269/20000000000000 : ℝ)^207
        have hw : |(4317669001/10000000000 : ℝ)|=(4317669001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258850277/625000000 : ℝ)|^271 ≤ (3153590440723/10000000000000 : ℝ)^207
        have hw : |(258850277/625000000 : ℝ)|=(258850277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(900120289/2000000000 : ℝ)|^271 ≤ (8790411172931/25000000000000 : ℝ)^207
        have hw : |(900120289/2000000000 : ℝ)|=(900120289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s4_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-503685209/2500000000 : ℝ)*x 0 + (5244357671/10000000000 : ℝ)*x 1 + (5412337217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503685209/2500000000 : ℝ)^271 ≤ (1534647247851/12500000000000 : ℝ)^207 := by
    have hnat : (503685209 : ℕ)^271*12500000000000^207 ≤ 1534647247851^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503685209 2500000000 1534647247851 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244357671/10000000000 : ℝ)^271 ≤ (42956325229333/100000000000000 : ℝ)^207 := by
    have hnat : (5244357671 : ℕ)^271*100000000000000^207 ≤ 42956325229333^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244357671 10000000000 42956325229333 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412337217/10000000000 : ℝ)^271 ≤ (8953299352389/20000000000000 : ℝ)^207 := by
    have hnat : (5412337217 : ℕ)^271*20000000000000^207 ≤ 8953299352389^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412337217 10000000000 8953299352389 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503685209/2500000000 : ℝ), (5244357671/10000000000 : ℝ), (5412337217/10000000000 : ℝ)] ![(1534647247851/12500000000000 : ℝ), (42956325229333/100000000000000 : ℝ), (8953299352389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503685209/2500000000 : ℝ)|^271 ≤ (1534647247851/12500000000000 : ℝ)^207
        have hw : |(-503685209/2500000000 : ℝ)|=(503685209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244357671/10000000000 : ℝ)|^271 ≤ (42956325229333/100000000000000 : ℝ)^207
        have hw : |(5244357671/10000000000 : ℝ)|=(5244357671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412337217/10000000000 : ℝ)|^271 ≤ (8953299352389/20000000000000 : ℝ)^207
        have hw : |(5412337217/10000000000 : ℝ)|=(5412337217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s4_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1061029149/2000000000 : ℝ)*x 0 + (-1932358541/10000000000 : ℝ)*x 1 + (5412337801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061029149/2000000000 : ℝ)^271 ≤ (21804673443853/50000000000000 : ℝ)^207 := by
    have hnat : (1061029149 : ℕ)^271*50000000000000^207 ≤ 21804673443853^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061029149 2000000000 21804673443853 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932358541/10000000000 : ℝ)^271 ≤ (11624150019949/100000000000000 : ℝ)^207 := by
    have hnat : (1932358541 : ℕ)^271*100000000000000^207 ≤ 11624150019949^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932358541 10000000000 11624150019949 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412337801/10000000000 : ℝ)^271 ≤ (44766503085773/100000000000000 : ℝ)^207 := by
    have hnat : (5412337801 : ℕ)^271*100000000000000^207 ≤ 44766503085773^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412337801 10000000000 44766503085773 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061029149/2000000000 : ℝ), (-1932358541/10000000000 : ℝ), (5412337801/10000000000 : ℝ)] ![(21804673443853/50000000000000 : ℝ), (11624150019949/100000000000000 : ℝ), (44766503085773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061029149/2000000000 : ℝ)|^271 ≤ (21804673443853/50000000000000 : ℝ)^207
        have hw : |(1061029149/2000000000 : ℝ)|=(1061029149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1932358541/10000000000 : ℝ)|^271 ≤ (11624150019949/100000000000000 : ℝ)^207
        have hw : |(-1932358541/10000000000 : ℝ)|=(1932358541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412337801/10000000000 : ℝ)|^271 ≤ (44766503085773/100000000000000 : ℝ)^207
        have hw : |(5412337801/10000000000 : ℝ)|=(5412337801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s4_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1061029281/2000000000 : ℝ)*x 0 + (676542151/1250000000 : ℝ)*x 1 + (-966179227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061029281/2000000000 : ℝ)^271 ≤ (21804676995217/50000000000000 : ℝ)^207 := by
    have hnat : (1061029281 : ℕ)^271*50000000000000^207 ≤ 21804676995217^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061029281 2000000000 21804676995217 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676542151/1250000000 : ℝ)^271 ≤ (44766496664489/100000000000000 : ℝ)^207 := by
    have hnat : (676542151 : ℕ)^271*100000000000000^207 ≤ 44766496664489^207*1250000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676542151 1250000000 44766496664489 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966179227/5000000000 : ℝ)^271 ≤ (1162414933479/10000000000000 : ℝ)^207 := by
    have hnat : (966179227 : ℕ)^271*10000000000000^207 ≤ 1162414933479^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966179227 5000000000 1162414933479 10000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061029281/2000000000 : ℝ), (676542151/1250000000 : ℝ), (-966179227/5000000000 : ℝ)] ![(21804676995217/50000000000000 : ℝ), (44766496664489/100000000000000 : ℝ), (1162414933479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061029281/2000000000 : ℝ)|^271 ≤ (21804676995217/50000000000000 : ℝ)^207
        have hw : |(1061029281/2000000000 : ℝ)|=(1061029281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676542151/1250000000 : ℝ)|^271 ≤ (44766496664489/100000000000000 : ℝ)^207
        have hw : |(676542151/1250000000 : ℝ)|=(676542151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966179227/5000000000 : ℝ)|^271 ≤ (1162414933479/10000000000000 : ℝ)^207
        have hw : |(-966179227/5000000000 : ℝ)|=(966179227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s4_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2158847393/5000000000 : ℝ)*x 0 + (1124820779/2500000000 : ℝ)*x 1 + (4142930837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158847393/5000000000 : ℝ)^271 ≤ (16651355626389/50000000000000 : ℝ)^207 := by
    have hnat : (2158847393 : ℕ)^271*50000000000000^207 ≤ 16651355626389^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158847393 5000000000 16651355626389 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124820779/2500000000 : ℝ)^271 ≤ (35148161220613/100000000000000 : ℝ)^207 := by
    have hnat : (1124820779 : ℕ)^271*100000000000000^207 ≤ 35148161220613^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124820779 2500000000 35148161220613 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4142930837/10000000000 : ℝ)^271 ≤ (1261965100273/4000000000000 : ℝ)^207 := by
    have hnat : (4142930837 : ℕ)^271*4000000000000^207 ≤ 1261965100273^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142930837 10000000000 1261965100273 4000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158847393/5000000000 : ℝ), (1124820779/2500000000 : ℝ), (4142930837/10000000000 : ℝ)] ![(16651355626389/50000000000000 : ℝ), (35148161220613/100000000000000 : ℝ), (1261965100273/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158847393/5000000000 : ℝ)|^271 ≤ (16651355626389/50000000000000 : ℝ)^207
        have hw : |(2158847393/5000000000 : ℝ)|=(2158847393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124820779/2500000000 : ℝ)|^271 ≤ (35148161220613/100000000000000 : ℝ)^207
        have hw : |(1124820779/2500000000 : ℝ)|=(1124820779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4142930837/10000000000 : ℝ)|^271 ≤ (1261965100273/4000000000000 : ℝ)^207
        have hw : |(4142930837/10000000000 : ℝ)|=(4142930837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (749/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11187/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (749/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (749/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (749/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (749/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (749/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (749/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10989/100000 : ℝ) ^ (4335/1024 : ℝ) ≤ (435475607860653/5000000000000000000 : ℝ) := by
    have hpowers : (10989/100000 : ℝ)^4335 ≤ (435475607860653/5000000000000000000 : ℝ)^1024 := by
      have hnat : (10989 : ℕ)^4335*5000000000000000000^1024 ≤ 435475607860653^1024*100000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10989 100000 435475607860653 5000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10989/100000 : ℝ)) (X := (435475607860653/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (749/5000 : ℝ) ^ (4335/1024 : ℝ) ≤ (32330543014322269/100000000000000000000 : ℝ) := by
    have hpowers : (749/5000 : ℝ)^4335 ≤ (32330543014322269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (749 : ℕ)^4335*100000000000000000000^1024 ≤ 32330543014322269^1024*5000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        749 5000 32330543014322269 100000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (749/5000 : ℝ)) (X := (32330543014322269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500435475607860653/2500000000000000000 : ℝ) ≤ (2000082287863737/2000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (2500435475607860653/2500000000000000000 : ℝ)^1024 ≤ (2000082287863737/2000000000000000 : ℝ)^4335 := by
      have hnat : (2500435475607860653 : ℕ)^1024*2000000000000000^4335 ≤ 2000082287863737^4335*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500435475607860653 2500000000000000000 2000082287863737 2000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000082287863737/2000000000000000 : ℝ)) (X := (2500435475607860653/2500000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041040055171535329/100000000000000000000 : ℝ) ≤ (2500242320827947/2500000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (100041040055171535329/100000000000000000000 : ℝ)^1024 ≤ (2500242320827947/2500000000000000 : ℝ)^4335 := by
      have hnat : (100041040055171535329 : ℕ)^1024*2500000000000000^4335 ≤ 2500242320827947^4335*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041040055171535329 100000000000000000000 2500242320827947 2500000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500242320827947/2500000000000000 : ℝ)) (X := (100041040055171535329/100000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032330543014322269/50000000000000000000 : ℝ) ≤ (10001527127304891/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (50032330543014322269/50000000000000000000 : ℝ)^1024 ≤ (10001527127304891/10000000000000000 : ℝ)^4335 := by
      have hnat : (50032330543014322269 : ℕ)^1024*10000000000000000^4335 ≤ 10001527127304891^4335*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032330543014322269 50000000000000000000 10001527127304891 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001527127304891/10000000000000000 : ℝ)) (X := (50032330543014322269/50000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(435475607860653/5000000000000000000 : ℝ) ≤ ((39899381759040454101/39910000000000000000 : ℝ)+2*(557843993103/399100000000000 : ℝ)*(10989/100000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (39899381759040454101/39910000000000000000 : ℝ)+2*(557843993103/399100000000000 : ℝ)*(10989/100000 : ℝ)=(2000082287863737/2000000000000000 : ℝ) by norm_num, show 1+2*(435475607860653/5000000000000000000 : ℝ)=(2500435475607860653/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32330543014322269/100000000000000000000 : ℝ)+(435475607860653/5000000000000000000 : ℝ) ≤ ((39899381759040454101/39910000000000000000 : ℝ)+(557843993103/399100000000000 : ℝ)*((749/5000 : ℝ)+(10989/100000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (39899381759040454101/39910000000000000000 : ℝ)+(557843993103/399100000000000 : ℝ)*((749/5000 : ℝ)+(10989/100000 : ℝ))=(2500242320827947/2500000000000000 : ℝ) by norm_num, show 1+(32330543014322269/100000000000000000000 : ℝ)+(435475607860653/5000000000000000000 : ℝ)=(100041040055171535329/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32330543014322269/100000000000000000000 : ℝ) ≤ ((39899381759040454101/39910000000000000000 : ℝ)+2*(557843993103/399100000000000 : ℝ)*(749/5000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (39899381759040454101/39910000000000000000 : ℝ)+2*(557843993103/399100000000000 : ℝ)*(749/5000 : ℝ)=(10001527127304891/10000000000000000 : ℝ) by norm_num, show 1+2*(32330543014322269/100000000000000000000 : ℝ)=(50032330543014322269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39899381759040454101/39910000000000000000 : ℝ)*(X 1 0+X 2 0)+(557843993103/399100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (749/5000 : ℝ)) (c := (39899381759040454101/39910000000000000000 : ℝ)) (alpha := (557843993103/399100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39899381759040454101/39910000000000000000 : ℝ)*(X 0 1+X 2 1)+(557843993103/399100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (749/5000 : ℝ)) (c := (39899381759040454101/39910000000000000000 : ℝ)) (alpha := (557843993103/399100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39899381759040454101/39910000000000000000 : ℝ)*(X 0 2+X 1 2)+(557843993103/399100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (749/5000 : ℝ)) (c := (39899381759040454101/39910000000000000000 : ℝ)) (alpha := (557843993103/399100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-503681997/2500000000 : ℝ)*X 0 0+(541296229/1000000000 : ℝ)*X 0 1+(1310934003/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348900581/10000000000 : ℝ)*X 1 0+(-42019197/200000000 : ℝ)*X 1 1+(655467041/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348900649/10000000000 : ℝ)*X 2 0+(327733493/625000000 : ℝ)*X 2 1+(-1050480171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317669001/10000000000 : ℝ)*X 0 0+(258850277/625000000 : ℝ)*X 0 1+(900120289/2000000000 : ℝ)*X 0 2+(4317669001/10000000000 : ℝ)*X 1 0+(258850277/625000000 : ℝ)*X 1 1+(900120289/2000000000 : ℝ)*X 1 2+(4317669001/10000000000 : ℝ)*X 2 0+(258850277/625000000 : ℝ)*X 2 1+(900120289/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-503685209/2500000000 : ℝ)*X 0 0+(5244357671/10000000000 : ℝ)*X 0 1+(5412337217/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061029149/2000000000 : ℝ)*X 1 0+(-1932358541/10000000000 : ℝ)*X 1 1+(5412337801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061029281/2000000000 : ℝ)*X 2 0+(676542151/1250000000 : ℝ)*X 2 1+(-966179227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158847393/5000000000 : ℝ)*X 0 0+(1124820779/2500000000 : ℝ)*X 0 1+(4142930837/10000000000 : ℝ)*X 0 2+(2158847393/5000000000 : ℝ)*X 1 0+(1124820779/2500000000 : ℝ)*X 1 1+(4142930837/10000000000 : ℝ)*X 1 2+(2158847393/5000000000 : ℝ)*X 2 0+(1124820779/2500000000 : ℝ)*X 2 1+(4142930837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (320727405116370761639652201/49887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (148254611/12500000000000 : ℝ)*(base19) + (343454391/25000000000000 : ℝ)*(base23) + (484457007/100000000000000 : ℝ)*(upper3) + (62459383/100000000000000 : ℝ)*(lower4) + (108685835408133/2500000000000 : ℝ)*(major0) + (108685835408133/2500000000000 : ℝ)*(major1) + (108685835408133/2500000000000 : ℝ)*(major2) + (5909282460616589/100000000000000 : ℝ)*(sp0) + (1181859414884281/20000000000000 : ℝ)*(sp1) + (5909296383698361/100000000000000 : ℝ)*(sp2) + (348193749266403/12500000000000 : ℝ)*(sp3) + (1974980213/12500000000000 : ℝ)*(sp4) + (15716949/3125000000000 : ℝ)*(sp6) + (18363760671/100000000000000 : ℝ)*(sp7) + (348196044736487/12500000000000 : ℝ)*(f.failure) + (5909298260458293/100000000000000 : ℝ)*(f.sum) + (1526265991011/1995500000000000000000000000 : ℝ)*base66 + (16970595413053433/99775000000000000000000000000000 : ℝ)*base67 + (248188984634321567/99775000000000000000000000000000 : ℝ)*base70 + (609838816731121567/99775000000000000000000000000000 : ℝ)*base72 + (7696944587389/1995500000000000000000000000 : ℝ)*base73 + (325766702466578433/99775000000000000000000000000000 : ℝ)*base75 + (562798097949278433/99775000000000000000000000000000 : ℝ)*base77 + (198065421394603433/99775000000000000000000000000000 : ℝ)*base79 + (9666499472451/3991000000000000000000000000 : ℝ)*base82 + (60951/4882812500000000000 : ℝ)*base89 + (60951/4882812500000000000 : ℝ)*base91 + (60951/4882812500000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1504359973985080864236496221/249437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (525090883/100000000000000 : ℝ)*(base19) + (2134851699/100000000000000 : ℝ)*(base23) + (176406389/50000000000000 : ℝ)*(upper2) + (1672469/781250000000 : ℝ)*(upper3) + (1263347/2500000000000 : ℝ)*(upper5) + (547457065366707/12500000000000 : ℝ)*(major0) + (547457065366707/12500000000000 : ℝ)*(major1) + (547457065366707/12500000000000 : ℝ)*(major2) + (1388180509/6250000000000 : ℝ)*(sp1) + (23479762609/50000000000000 : ℝ)*(sp2) + (1488274474760921/25000000000000 : ℝ)*(sp4) + (372067197691541/6250000000000 : ℝ)*(sp5) + (2976524402333383/50000000000000 : ℝ)*(sp6) + (701553736447491/25000000000000 : ℝ)*(sp7) + (701553736447491/25000000000000 : ℝ)*(f.failure) + (1488274474760921/25000000000000 : ℝ)*(f.sum) + (4747122554427/1247187500000000000000000000 : ℝ)*base66 + (1569361824189384593/498875000000000000000000000000000 : ℝ)*base68 + (2510120098742884593/498875000000000000000000000000000 : ℝ)*base70 + (5781303733851884593/498875000000000000000000000000000 : ℝ)*base72 + (650075983959/2494375000000000000000000000 : ℝ)*base74 + (5027297836674615407/498875000000000000000000000000000 : ℝ)*base75 + (4411414100232884593/498875000000000000000000000000000 : ℝ)*base78 + (1932265273877115407/498875000000000000000000000000000 : ℝ)*base79 + (10854970246443/4988750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (74709/4882812500000000000 : ℝ)*base89 + (74709/4882812500000000000 : ℝ)*base91 + (74709/4882812500000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1376_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (749/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1376_s5_0 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014924101/10000000000 : ℝ)*x 0 + (33820257/62500000 : ℝ)*x 1 + (2622664051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014924101/10000000000 : ℝ)^271 ≤ (6139320019301/50000000000000 : ℝ)^207 := by
    have hnat : (2014924101 : ℕ)^271*50000000000000^207 ≤ 6139320019301^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014924101 10000000000 6139320019301 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33820257/62500000 : ℝ)^271 ≤ (44754628077067/100000000000000 : ℝ)^207 := by
    have hnat : (33820257 : ℕ)^271*100000000000000^207 ≤ 44754628077067^207*62500000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33820257 62500000 44754628077067 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622664051/5000000000 : ℝ)^271 ≤ (21483365938461/50000000000000 : ℝ)^207 := by
    have hnat : (2622664051 : ℕ)^271*50000000000000^207 ≤ 21483365938461^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622664051 5000000000 21483365938461 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014924101/10000000000 : ℝ), (33820257/62500000 : ℝ), (2622664051/5000000000 : ℝ)] ![(6139320019301/50000000000000 : ℝ), (44754628077067/100000000000000 : ℝ), (21483365938461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014924101/10000000000 : ℝ)|^271 ≤ (6139320019301/50000000000000 : ℝ)^207
        have hw : |(-2014924101/10000000000 : ℝ)|=(2014924101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33820257/62500000 : ℝ)|^271 ≤ (44754628077067/100000000000000 : ℝ)^207
        have hw : |(33820257/62500000 : ℝ)|=(33820257/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622664051/5000000000 : ℝ)|^271 ≤ (21483365938461/50000000000000 : ℝ)^207
        have hw : |(2622664051/5000000000 : ℝ)|=(2622664051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s5_1 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5348459109/10000000000 : ℝ)*x 0 + (-32803703/156250000 : ℝ)*x 1 + (5245328057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348459109/10000000000 : ℝ)^271 ≤ (44076059877559/100000000000000 : ℝ)^207 := by
    have hnat : (5348459109 : ℕ)^271*100000000000000^207 ≤ 44076059877559^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348459109 10000000000 44076059877559 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32803703/156250000 : ℝ)^271 ≤ (2591441742269/20000000000000 : ℝ)^207 := by
    have hnat : (32803703 : ℕ)^271*20000000000000^207 ≤ 2591441742269^207*156250000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32803703 156250000 2591441742269 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245328057/10000000000 : ℝ)^271 ≤ (2148336569717/5000000000000 : ℝ)^207 := by
    have hnat : (5245328057 : ℕ)^271*5000000000000^207 ≤ 2148336569717^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245328057 10000000000 2148336569717 5000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348459109/10000000000 : ℝ), (-32803703/156250000 : ℝ), (5245328057/10000000000 : ℝ)] ![(44076059877559/100000000000000 : ℝ), (2591441742269/20000000000000 : ℝ), (2148336569717/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348459109/10000000000 : ℝ)|^271 ≤ (44076059877559/100000000000000 : ℝ)^207
        have hw : |(5348459109/10000000000 : ℝ)|=(5348459109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32803703/156250000 : ℝ)|^271 ≤ (2591441742269/20000000000000 : ℝ)^207
        have hw : |(-32803703/156250000 : ℝ)|=(32803703/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245328057/10000000000 : ℝ)|^271 ≤ (2148336569717/5000000000000 : ℝ)^207
        have hw : |(5245328057/10000000000 : ℝ)|=(5245328057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s5_2 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2674229597/5000000000 : ℝ)*x 0 + (524532809/1000000000 : ℝ)*x 1 + (-419887367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674229597/5000000000 : ℝ)^271 ≤ (44076060794607/100000000000000 : ℝ)^207 := by
    have hnat : (2674229597 : ℕ)^271*100000000000000^207 ≤ 44076060794607^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674229597 5000000000 44076060794607 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524532809/1000000000 : ℝ)^271 ≤ (42966731748233/100000000000000 : ℝ)^207 := by
    have hnat : (524532809 : ℕ)^271*100000000000000^207 ≤ 42966731748233^207*1000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524532809 1000000000 42966731748233 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (419887367/2000000000 : ℝ)^271 ≤ (3239301860699/25000000000000 : ℝ)^207 := by
    have hnat : (419887367 : ℕ)^271*25000000000000^207 ≤ 3239301860699^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419887367 2000000000 3239301860699 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674229597/5000000000 : ℝ), (524532809/1000000000 : ℝ), (-419887367/2000000000 : ℝ)] ![(44076060794607/100000000000000 : ℝ), (42966731748233/100000000000000 : ℝ), (3239301860699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674229597/5000000000 : ℝ)|^271 ≤ (44076060794607/100000000000000 : ℝ)^207
        have hw : |(2674229597/5000000000 : ℝ)|=(2674229597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524532809/1000000000 : ℝ)|^271 ≤ (42966731748233/100000000000000 : ℝ)^207
        have hw : |(524532809/1000000000 : ℝ)|=(524532809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-419887367/2000000000 : ℝ)|^271 ≤ (3239301860699/25000000000000 : ℝ)^207
        have hw : |(-419887367/2000000000 : ℝ)|=(419887367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s5_3 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1079446693/2500000000 : ℝ)*x 0 + (1036276381/2500000000 : ℝ)*x 1 + (2248536023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079446693/2500000000 : ℝ)^271 ≤ (1040738753491/3125000000000 : ℝ)^207 := by
    have hnat : (1079446693 : ℕ)^271*3125000000000^207 ≤ 1040738753491^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079446693 2500000000 1040738753491 3125000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036276381/2500000000 : ℝ)^271 ≤ (31570810069459/100000000000000 : ℝ)^207 := by
    have hnat : (1036276381 : ℕ)^271*100000000000000^207 ≤ 31570810069459^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036276381 2500000000 31570810069459 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248536023/5000000000 : ℝ)^271 ≤ (35125549806321/100000000000000 : ℝ)^207 := by
    have hnat : (2248536023 : ℕ)^271*100000000000000^207 ≤ 35125549806321^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248536023 5000000000 35125549806321 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079446693/2500000000 : ℝ), (1036276381/2500000000 : ℝ), (2248536023/5000000000 : ℝ)] ![(1040738753491/3125000000000 : ℝ), (31570810069459/100000000000000 : ℝ), (35125549806321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079446693/2500000000 : ℝ)|^271 ≤ (1040738753491/3125000000000 : ℝ)^207
        have hw : |(1079446693/2500000000 : ℝ)|=(1079446693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036276381/2500000000 : ℝ)|^271 ≤ (31570810069459/100000000000000 : ℝ)^207
        have hw : |(1036276381/2500000000 : ℝ)|=(1036276381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248536023/5000000000 : ℝ)|^271 ≤ (35125549806321/100000000000000 : ℝ)^207
        have hw : |(2248536023/5000000000 : ℝ)|=(2248536023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s5_4 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014936061/10000000000 : ℝ)*x 0 + (5245925763/10000000000 : ℝ)*x 1 + (169082511/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014936061/10000000000 : ℝ)^271 ≤ (6139367727399/50000000000000 : ℝ)^207 := by
    have hnat : (2014936061 : ℕ)^271*50000000000000^207 ≤ 6139367727399^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014936061 10000000000 6139367727399 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245925763/10000000000 : ℝ)^271 ≤ (5371642666623/12500000000000 : ℝ)^207 := by
    have hnat : (5245925763 : ℕ)^271*12500000000000^207 ≤ 5371642666623^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245925763 10000000000 5371642666623 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169082511/312500000 : ℝ)^271 ≤ (11187030799041/25000000000000 : ℝ)^207 := by
    have hnat : (169082511 : ℕ)^271*25000000000000^207 ≤ 11187030799041^207*312500000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169082511 312500000 11187030799041 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014936061/10000000000 : ℝ), (5245925763/10000000000 : ℝ), (169082511/312500000 : ℝ)] ![(6139367727399/50000000000000 : ℝ), (5371642666623/12500000000000 : ℝ), (11187030799041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014936061/10000000000 : ℝ)|^271 ≤ (6139367727399/50000000000000 : ℝ)^207
        have hw : |(-2014936061/10000000000 : ℝ)|=(2014936061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245925763/10000000000 : ℝ)|^271 ≤ (5371642666623/12500000000000 : ℝ)^207
        have hw : |(5245925763/10000000000 : ℝ)|=(5245925763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169082511/312500000 : ℝ)|^271 ≤ (11187030799041/25000000000000 : ℝ)^207
        have hw : |(169082511/312500000 : ℝ)|=(169082511/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s5_5 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1326390287/2500000000 : ℝ)*x 0 + (-1934124567/10000000000 : ℝ)*x 1 + (1352660071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326390287/2500000000 : ℝ)^271 ≤ (10903454346913/25000000000000 : ℝ)^207 := by
    have hnat : (1326390287 : ℕ)^271*25000000000000^207 ≤ 10903454346913^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326390287 2500000000 10903454346913 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934124567/10000000000 : ℝ)^271 ≤ (2909515034973/25000000000000 : ℝ)^207 := by
    have hnat : (1934124567 : ℕ)^271*25000000000000^207 ≤ 2909515034973^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934124567 10000000000 2909515034973 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352660071/2500000000 : ℝ)^271 ≤ (44748122459899/100000000000000 : ℝ)^207 := by
    have hnat : (1352660071 : ℕ)^271*100000000000000^207 ≤ 44748122459899^207*2500000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352660071 2500000000 44748122459899 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326390287/2500000000 : ℝ), (-1934124567/10000000000 : ℝ), (1352660071/2500000000 : ℝ)] ![(10903454346913/25000000000000 : ℝ), (2909515034973/25000000000000 : ℝ), (44748122459899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326390287/2500000000 : ℝ)|^271 ≤ (10903454346913/25000000000000 : ℝ)^207
        have hw : |(1326390287/2500000000 : ℝ)|=(1326390287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1934124567/10000000000 : ℝ)|^271 ≤ (2909515034973/25000000000000 : ℝ)^207
        have hw : |(-1934124567/10000000000 : ℝ)|=(1934124567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352660071/2500000000 : ℝ)|^271 ≤ (44748122459899/100000000000000 : ℝ)^207
        have hw : |(1352660071/2500000000 : ℝ)|=(1352660071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s5_6 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305561197/10000000000 : ℝ)*x 0 + (5410639991/10000000000 : ℝ)*x 1 + (-967062451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305561197/10000000000 : ℝ)^271 ≤ (43613817914989/100000000000000 : ℝ)^207 := by
    have hnat : (5305561197 : ℕ)^271*100000000000000^207 ≤ 43613817914989^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305561197 10000000000 43613817914989 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410639991/10000000000 : ℝ)^271 ≤ (5593514910933/12500000000000 : ℝ)^207 := by
    have hnat : (5410639991 : ℕ)^271*12500000000000^207 ≤ 5593514910933^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410639991 10000000000 5593514910933 12500000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967062451/5000000000 : ℝ)^271 ≤ (2327612555779/20000000000000 : ℝ)^207 := by
    have hnat : (967062451 : ℕ)^271*20000000000000^207 ≤ 2327612555779^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967062451 5000000000 2327612555779 20000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305561197/10000000000 : ℝ), (5410639991/10000000000 : ℝ), (-967062451/5000000000 : ℝ)] ![(43613817914989/100000000000000 : ℝ), (5593514910933/12500000000000 : ℝ), (2327612555779/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305561197/10000000000 : ℝ)|^271 ≤ (43613817914989/100000000000000 : ℝ)^207
        have hw : |(5305561197/10000000000 : ℝ)|=(5305561197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410639991/10000000000 : ℝ)|^271 ≤ (5593514910933/12500000000000 : ℝ)^207
        have hw : |(5410639991/10000000000 : ℝ)|=(5410639991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-967062451/5000000000 : ℝ)|^271 ≤ (2327612555779/20000000000000 : ℝ)^207
        have hw : |(-967062451/5000000000 : ℝ)|=(967062451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1376_s5_7 (p : ℝ) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4317813017/10000000000 : ℝ)*x 0 + (899160791/2000000000 : ℝ)*x 1 + (2073189639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317813017/10000000000 : ℝ)^271 ≤ (16651952565183/50000000000000 : ℝ)^207 := by
    have hnat : (4317813017 : ℕ)^271*50000000000000^207 ≤ 16651952565183^207*10000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317813017 10000000000 16651952565183 50000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (899160791/2000000000 : ℝ)^271 ≤ (35112583277847/100000000000000 : ℝ)^207 := by
    have hnat : (899160791 : ℕ)^271*100000000000000^207 ≤ 35112583277847^207*2000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899160791 2000000000 35112583277847 100000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073189639/5000000000 : ℝ)^271 ≤ (7895877894243/25000000000000 : ℝ)^207 := by
    have hnat : (2073189639 : ℕ)^271*25000000000000^207 ≤ 7895877894243^207*5000000000^271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073189639 5000000000 7895877894243 25000000000000 271 207 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (271/64 : ℝ)) 271 207 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317813017/10000000000 : ℝ), (899160791/2000000000 : ℝ), (2073189639/5000000000 : ℝ)] ![(16651952565183/50000000000000 : ℝ), (35112583277847/100000000000000 : ℝ), (7895877894243/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317813017/10000000000 : ℝ)|^271 ≤ (16651952565183/50000000000000 : ℝ)^207
        have hw : |(4317813017/10000000000 : ℝ)|=(4317813017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(899160791/2000000000 : ℝ)|^271 ≤ (35112583277847/100000000000000 : ℝ)^207
        have hw : |(899160791/2000000000 : ℝ)|=(899160791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2073189639/5000000000 : ℝ)|^271 ≤ (7895877894243/25000000000000 : ℝ)^207
        have hw : |(2073189639/5000000000 : ℝ)|=(2073189639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1376_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11221/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7367/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11187/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11187/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11187/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11187/100000 : ℝ) ^ (4335/1024 : ℝ) ≤ (4696732287013151/50000000000000000000 : ℝ) := by
    have hpowers : (11187/100000 : ℝ)^4335 ≤ (4696732287013151/50000000000000000000 : ℝ)^1024 := by
      have hnat : (11187 : ℕ)^4335*50000000000000000000^1024 ≤ 4696732287013151^1024*100000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11187 100000 4696732287013151 50000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11187/100000 : ℝ)) (X := (4696732287013151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (4335/1024 : ℝ) ≤ (15227432780177549/50000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^4335 ≤ (15227432780177549/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1477 : ℕ)^4335*50000000000000000000^1024 ≤ 15227432780177549^1024*10000^4335 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 15227432780177549 50000000000000000000 4335 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (15227432780177549/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004696732287013151/25000000000000000000 : ℝ) ≤ (10000443747067347/10000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (25004696732287013151/25000000000000000000 : ℝ)^1024 ≤ (10000443747067347/10000000000000000 : ℝ)^4335 := by
      have hnat : (25004696732287013151 : ℕ)^1024*10000000000000000^4335 ≤ 10000443747067347^4335*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004696732287013151 25000000000000000000 10000443747067347 10000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000443747067347/10000000000000000 : ℝ)) (X := (25004696732287013151/25000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (500199241650671907/500000000000000000 : ℝ) ≤ (2500235285363089/2500000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (500199241650671907/500000000000000000 : ℝ)^1024 ≤ (2500235285363089/2500000000000000 : ℝ)^4335 := by
      have hnat : (500199241650671907 : ℕ)^1024*2500000000000000^4335 ≤ 2500235285363089^4335*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500199241650671907 500000000000000000 2500235285363089 2500000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500235285363089/2500000000000000 : ℝ)) (X := (500199241650671907/500000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015227432780177549/25000000000000000000 : ℝ) ≤ (2000287707167473/2000000000000000 : ℝ) ^ (4335/1024 : ℝ) := by
    have hpowers : (25015227432780177549/25000000000000000000 : ℝ)^1024 ≤ (2000287707167473/2000000000000000 : ℝ)^4335 := by
      have hnat : (25015227432780177549 : ℕ)^1024*2000000000000000^4335 ≤ 2000287707167473^4335*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015227432780177549 25000000000000000000 2000287707167473 2000000000000000 1024 4335 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000287707167473/2000000000000000 : ℝ)) (X := (25015227432780177549/25000000000000000000 : ℝ)) (by norm_num) 4335 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4696732287013151/50000000000000000000 : ℝ) ≤ ((7164092248754422587/7166000000000000000 : ℝ)+2*(497394385009/358300000000000 : ℝ)*(11187/100000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (7164092248754422587/7166000000000000000 : ℝ)+2*(497394385009/358300000000000 : ℝ)*(11187/100000 : ℝ)=(10000443747067347/10000000000000000 : ℝ) by norm_num, show 1+2*(4696732287013151/50000000000000000000 : ℝ)=(25004696732287013151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15227432780177549/50000000000000000000 : ℝ)+(4696732287013151/50000000000000000000 : ℝ) ≤ ((7164092248754422587/7166000000000000000 : ℝ)+(497394385009/358300000000000 : ℝ)*((1477/10000 : ℝ)+(11187/100000 : ℝ)))^(4335/1024 : ℝ) := by
    rw [show (7164092248754422587/7166000000000000000 : ℝ)+(497394385009/358300000000000 : ℝ)*((1477/10000 : ℝ)+(11187/100000 : ℝ))=(2500235285363089/2500000000000000 : ℝ) by norm_num, show 1+(15227432780177549/50000000000000000000 : ℝ)+(4696732287013151/50000000000000000000 : ℝ)=(500199241650671907/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15227432780177549/50000000000000000000 : ℝ) ≤ ((7164092248754422587/7166000000000000000 : ℝ)+2*(497394385009/358300000000000 : ℝ)*(1477/10000 : ℝ))^(4335/1024 : ℝ) := by
    rw [show (7164092248754422587/7166000000000000000 : ℝ)+2*(497394385009/358300000000000 : ℝ)*(1477/10000 : ℝ)=(2000287707167473/2000000000000000 : ℝ) by norm_num, show 1+2*(15227432780177549/50000000000000000000 : ℝ)=(25015227432780177549/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7164092248754422587/7166000000000000000 : ℝ)*(X 1 0+X 2 0)+(497394385009/358300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (7164092248754422587/7166000000000000000 : ℝ)) (alpha := (497394385009/358300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7164092248754422587/7166000000000000000 : ℝ)*(X 0 1+X 2 1)+(497394385009/358300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (7164092248754422587/7166000000000000000 : ℝ)) (alpha := (497394385009/358300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7164092248754422587/7166000000000000000 : ℝ)*(X 0 2+X 1 2)+(497394385009/358300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4335/1024 : ℝ)) (lo := (11187/100000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (7164092248754422587/7166000000000000000 : ℝ)) (alpha := (497394385009/358300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2014924101/10000000000 : ℝ)*X 0 0+(33820257/62500000 : ℝ)*X 0 1+(2622664051/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348459109/10000000000 : ℝ)*X 1 0+(-32803703/156250000 : ℝ)*X 1 1+(5245328057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674229597/5000000000 : ℝ)*X 2 0+(524532809/1000000000 : ℝ)*X 2 1+(-419887367/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079446693/2500000000 : ℝ)*X 0 0+(1036276381/2500000000 : ℝ)*X 0 1+(2248536023/5000000000 : ℝ)*X 0 2+(1079446693/2500000000 : ℝ)*X 1 0+(1036276381/2500000000 : ℝ)*X 1 1+(2248536023/5000000000 : ℝ)*X 1 2+(1079446693/2500000000 : ℝ)*X 2 0+(1036276381/2500000000 : ℝ)*X 2 1+(2248536023/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2014936061/10000000000 : ℝ)*X 0 0+(5245925763/10000000000 : ℝ)*X 0 1+(169082511/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326390287/2500000000 : ℝ)*X 1 0+(-1934124567/10000000000 : ℝ)*X 1 1+(1352660071/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305561197/10000000000 : ℝ)*X 2 0+(5410639991/10000000000 : ℝ)*X 2 1+(-967062451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317813017/10000000000 : ℝ)*X 0 0+(899160791/2000000000 : ℝ)*X 0 1+(2073189639/5000000000 : ℝ)*X 0 2+(4317813017/10000000000 : ℝ)*X 1 0+(899160791/2000000000 : ℝ)*X 1 1+(2073189639/5000000000 : ℝ)*X 1 2+(4317813017/10000000000 : ℝ)*X 2 0+(899160791/2000000000 : ℝ)*X 2 1+(2073189639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1376_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (313399071861633195432567117/44787500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1047475321/100000000000000 : ℝ)*(base19) + (575836363/50000000000000 : ℝ)*(base23) + (148099/3125000000000 : ℝ)*(lower2) + (16906959/12500000000000 : ℝ)*(upper5) + (4434253580082941/100000000000000 : ℝ)*(major0) + (4434253580082941/100000000000000 : ℝ)*(major1) + (2217126790041471/50000000000000 : ℝ)*(major2) + (6027278900016071/100000000000000 : ℝ)*(sp0) + (6027306339071807/100000000000000 : ℝ)*(sp1) + (1506827097007699/25000000000000 : ℝ)*(sp2) + (2841189090508139/100000000000000 : ℝ)*(sp3) + (30639687451/100000000000000 : ℝ)*(sp4) + (2153156393/100000000000000 : ℝ)*(sp5) + (8296705301/100000000000000 : ℝ)*(sp7) + (4439370917521/156250000000 : ℝ)*(f.failure) + (6027309539703521/100000000000000 : ℝ)*(f.sum) + (111010033743/35830000000000000000000000000 : ℝ)*base66 + (1883598215814948367/716600000000000000000000000000000 : ℝ)*base67 + (1961820291555995477/358300000000000000000000000000000 : ℝ)*base69 + (4879964641390148367/716600000000000000000000000000000 : ℝ)*base71 + (31502115237667/35830000000000000000000000000 : ℝ)*base73 + (4901250926284895477/358300000000000000000000000000000 : ℝ)*base75 + (6734266489459768367/716600000000000000000000000000000 : ℝ)*base77 + (7234448931098568367/716600000000000000000000000000000 : ℝ)*base79 + (23597602590489/17915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (88199/7812500000000000000 : ℝ)*base89 + (88199/7812500000000000000 : ℝ)*base91 + (5037/3906250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1877221492397490851778539283/358300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1368495441/100000000000000 : ℝ)*(base19) + (1825089001/100000000000000 : ℝ)*(base23) + (24961333/25000000000000 : ℝ)*(upper3) + (60625231/25000000000000 : ℝ)*(lower4) + (241450443/100000000000000 : ℝ)*(upper5) + (4466475269663997/100000000000000 : ℝ)*(major0) + (4466475269663997/100000000000000 : ℝ)*(major1) + (4466475269663997/100000000000000 : ℝ)*(major2) + (2945474351/10000000000000 : ℝ)*(sp1) + (11230595131/50000000000000 : ℝ)*(sp2) + (3035553648759521/50000000000000 : ℝ)*(sp4) + (607107647428009/10000000000000 : ℝ)*(sp5) + (6071083011239779/100000000000000 : ℝ)*(sp6) + (1430921533583723/50000000000000 : ℝ)*(sp7) + (1430921533583723/50000000000000 : ℝ)*(f.failure) + (3035553648759521/50000000000000 : ℝ)*(f.sum) + (64374309502327/17915000000000000000000000000 : ℝ)*base66 + (176707380055360239/716600000000000000000000000000000 : ℝ)*base67 + (60515021158239761/716600000000000000000000000000000 : ℝ)*base70 + (1491962016910239761/716600000000000000000000000000000 : ℝ)*base72 + (46650589439273/17915000000000000000000000000 : ℝ)*base73 + (13224372687398160239/716600000000000000000000000000000 : ℝ)*base75 + (1940302333265160239/716600000000000000000000000000000 : ℝ)*base77 + (1294902544073560239/716600000000000000000000000000000 : ℝ)*base79 + (48308612298573/17915000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (290883/39062500000000000000 : ℝ)*base89 + (290883/39062500000000000000 : ℝ)*base91 + (290883/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1376_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11187/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1376_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1376_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1997/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5033/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1376_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1376_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1376_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4335/1024 : ℝ) ≤ p) (hpb : p ≤ (271/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (609648/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1997/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5033/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1376_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
