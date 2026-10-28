-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:01.919476+00:00
-- url     : https://prove2.me/submissions/5de2ab01-0afd-4aed-986a-6755aa3c3f3b

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
theorem support_rectangle_w1216_s9_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-532999221/2500000000 : ℝ)*x 0 + (5391632351/10000000000 : ℝ)*x 1 + (5266902587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532999221/2500000000 : ℝ)^8409 ≤ (3240569829411/25000000000000 : ℝ)^6361 := by
    have hnat : (532999221 : ℕ)^8409*25000000000000^6361 ≤ 3240569829411^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532999221 2500000000 3240569829411 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391632351/10000000000 : ℝ)^8409 ≤ (44192076036329/100000000000000 : ℝ)^6361 := by
    have hnat : (5391632351 : ℕ)^8409*100000000000000^6361 ≤ 44192076036329^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391632351 10000000000 44192076036329 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266902587/10000000000 : ℝ)^8409 ≤ (21422822315527/50000000000000 : ℝ)^6361 := by
    have hnat : (5266902587 : ℕ)^8409*50000000000000^6361 ≤ 21422822315527^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266902587 10000000000 21422822315527 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532999221/2500000000 : ℝ), (5391632351/10000000000 : ℝ), (5266902587/10000000000 : ℝ)] ![(3240569829411/25000000000000 : ℝ), (44192076036329/100000000000000 : ℝ), (21422822315527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532999221/2500000000 : ℝ)|^8409 ≤ (3240569829411/25000000000000 : ℝ)^6361
        have hw : |(-532999221/2500000000 : ℝ)|=(532999221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391632351/10000000000 : ℝ)|^8409 ≤ (44192076036329/100000000000000 : ℝ)^6361
        have hw : |(5391632351/10000000000 : ℝ)|=(5391632351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266902587/10000000000 : ℝ)|^8409 ≤ (21422822315527/50000000000000 : ℝ)^6361
        have hw : |(5266902587/10000000000 : ℝ)|=(5266902587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s9_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344428533/10000000000 : ℝ)*x 0 + (-2195243497/10000000000 : ℝ)*x 1 + (5266902591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344428533/10000000000 : ℝ)^8409 ≤ (10920332066903/25000000000000 : ℝ)^6361 := by
    have hnat : (5344428533 : ℕ)^8409*25000000000000^6361 ≤ 10920332066903^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344428533 10000000000 10920332066903 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195243497/10000000000 : ℝ)^8409 ≤ (13473027038131/100000000000000 : ℝ)^6361 := by
    have hnat : (2195243497 : ℕ)^8409*100000000000000^6361 ≤ 13473027038131^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195243497 10000000000 13473027038131 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266902591/10000000000 : ℝ)^8409 ≤ (4284564467407/10000000000000 : ℝ)^6361 := by
    have hnat : (5266902591 : ℕ)^8409*10000000000000^6361 ≤ 4284564467407^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266902591 10000000000 4284564467407 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344428533/10000000000 : ℝ), (-2195243497/10000000000 : ℝ), (5266902591/10000000000 : ℝ)] ![(10920332066903/25000000000000 : ℝ), (13473027038131/100000000000000 : ℝ), (4284564467407/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344428533/10000000000 : ℝ)|^8409 ≤ (10920332066903/25000000000000 : ℝ)^6361
        have hw : |(5344428533/10000000000 : ℝ)|=(5344428533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195243497/10000000000 : ℝ)|^8409 ≤ (13473027038131/100000000000000 : ℝ)^6361
        have hw : |(-2195243497/10000000000 : ℝ)|=(2195243497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266902591/10000000000 : ℝ)|^8409 ≤ (4284564467407/10000000000000 : ℝ)^6361
        have hw : |(5266902591/10000000000 : ℝ)|=(5266902591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s9_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672214277/5000000000 : ℝ)*x 0 + (658362823/1250000000 : ℝ)*x 1 + (-1097621739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672214277/5000000000 : ℝ)^8409 ≤ (43681328494511/100000000000000 : ℝ)^6361 := by
    have hnat : (2672214277 : ℕ)^8409*100000000000000^6361 ≤ 43681328494511^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672214277 5000000000 43681328494511 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658362823/1250000000 : ℝ)^8409 ≤ (5355705574849/12500000000000 : ℝ)^6361 := by
    have hnat : (658362823 : ℕ)^8409*12500000000000^6361 ≤ 5355705574849^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658362823 1250000000 5355705574849 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097621739/5000000000 : ℝ)^8409 ≤ (13473026883977/100000000000000 : ℝ)^6361 := by
    have hnat : (1097621739 : ℕ)^8409*100000000000000^6361 ≤ 13473026883977^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097621739 5000000000 13473026883977 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672214277/5000000000 : ℝ), (658362823/1250000000 : ℝ), (-1097621739/5000000000 : ℝ)] ![(43681328494511/100000000000000 : ℝ), (5355705574849/12500000000000 : ℝ), (13473026883977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672214277/5000000000 : ℝ)|^8409 ≤ (43681328494511/100000000000000 : ℝ)^6361
        have hw : |(2672214277/5000000000 : ℝ)|=(2672214277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658362823/1250000000 : ℝ)|^8409 ≤ (5355705574849/12500000000000 : ℝ)^6361
        have hw : |(658362823/1250000000 : ℝ)|=(658362823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097621739/5000000000 : ℝ)|^8409 ≤ (13473026883977/100000000000000 : ℝ)^6361
        have hw : |(-1097621739/5000000000 : ℝ)|=(1097621739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s9_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354353741/10000000000 : ℝ)*x 0 + (4230256587/10000000000 : ℝ)*x 1 + (179280403/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354353741/10000000000 : ℝ)^8409 ≤ (3331738276997/10000000000000 : ℝ)^6361 := by
    have hnat : (4354353741 : ℕ)^8409*10000000000000^6361 ≤ 3331738276997^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354353741 10000000000 3331738276997 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230256587/10000000000 : ℝ)^8409 ≤ (32067935821517/100000000000000 : ℝ)^6361 := by
    have hnat : (4230256587 : ℕ)^8409*100000000000000^6361 ≤ 32067935821517^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230256587 10000000000 32067935821517 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179280403/400000000 : ℝ)^8409 ≤ (8653670350859/25000000000000 : ℝ)^6361 := by
    have hnat : (179280403 : ℕ)^8409*25000000000000^6361 ≤ 8653670350859^6361*400000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179280403 400000000 8653670350859 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354353741/10000000000 : ℝ), (4230256587/10000000000 : ℝ), (179280403/400000000 : ℝ)] ![(3331738276997/10000000000000 : ℝ), (32067935821517/100000000000000 : ℝ), (8653670350859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354353741/10000000000 : ℝ)|^8409 ≤ (3331738276997/10000000000000 : ℝ)^6361
        have hw : |(4354353741/10000000000 : ℝ)|=(4354353741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230256587/10000000000 : ℝ)|^8409 ≤ (32067935821517/100000000000000 : ℝ)^6361
        have hw : |(4230256587/10000000000 : ℝ)|=(4230256587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179280403/400000000 : ℝ)|^8409 ≤ (8653670350859/25000000000000 : ℝ)^6361
        have hw : |(179280403/400000000 : ℝ)|=(179280403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s9_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132001593/10000000000 : ℝ)*x 0 + (2633608189/5000000000 : ℝ)*x 1 + (5391317417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132001593/10000000000 : ℝ)^8409 ≤ (2592463433123/20000000000000 : ℝ)^6361 := by
    have hnat : (2132001593 : ℕ)^8409*20000000000000^6361 ≤ 2592463433123^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132001593 10000000000 2592463433123 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633608189/5000000000 : ℝ)^8409 ≤ (535612739679/1250000000000 : ℝ)^6361 := by
    have hnat : (2633608189 : ℕ)^8409*1250000000000^6361 ≤ 535612739679^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633608189 5000000000 535612739679 1250000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391317417/10000000000 : ℝ)^8409 ≤ (2761791477947/6250000000000 : ℝ)^6361 := by
    have hnat : (5391317417 : ℕ)^8409*6250000000000^6361 ≤ 2761791477947^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391317417 10000000000 2761791477947 6250000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132001593/10000000000 : ℝ), (2633608189/5000000000 : ℝ), (5391317417/10000000000 : ℝ)] ![(2592463433123/20000000000000 : ℝ), (535612739679/1250000000000 : ℝ), (2761791477947/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132001593/10000000000 : ℝ)|^8409 ≤ (2592463433123/20000000000000 : ℝ)^6361
        have hw : |(-2132001593/10000000000 : ℝ)|=(2132001593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633608189/5000000000 : ℝ)|^8409 ≤ (535612739679/1250000000000 : ℝ)^6361
        have hw : |(2633608189/5000000000 : ℝ)|=(2633608189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391317417/10000000000 : ℝ)|^8409 ≤ (2761791477947/6250000000000 : ℝ)^6361
        have hw : |(5391317417/10000000000 : ℝ)|=(5391317417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s9_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4354363293/10000000000 : ℝ)*x 0 + (4481376201/10000000000 : ℝ)*x 1 + (4230892697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354363293/10000000000 : ℝ)^8409 ≤ (16658739694269/50000000000000 : ℝ)^6361 := by
    have hnat : (4354363293 : ℕ)^8409*50000000000000^6361 ≤ 16658739694269^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354363293 10000000000 16658739694269 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481376201/10000000000 : ℝ)^8409 ≤ (34608209984467/100000000000000 : ℝ)^6361 := by
    have hnat : (4481376201 : ℕ)^8409*100000000000000^6361 ≤ 34608209984467^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481376201 10000000000 34608209984467 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230892697/10000000000 : ℝ)^8409 ≤ (16037155306529/50000000000000 : ℝ)^6361 := by
    have hnat : (4230892697 : ℕ)^8409*50000000000000^6361 ≤ 16037155306529^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230892697 10000000000 16037155306529 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354363293/10000000000 : ℝ), (4481376201/10000000000 : ℝ), (4230892697/10000000000 : ℝ)] ![(16658739694269/50000000000000 : ℝ), (34608209984467/100000000000000 : ℝ), (16037155306529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354363293/10000000000 : ℝ)|^8409 ≤ (16658739694269/50000000000000 : ℝ)^6361
        have hw : |(4354363293/10000000000 : ℝ)|=(4354363293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481376201/10000000000 : ℝ)|^8409 ≤ (34608209984467/100000000000000 : ℝ)^6361
        have hw : |(4481376201/10000000000 : ℝ)|=(4481376201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230892697/10000000000 : ℝ)|^8409 ≤ (16037155306529/50000000000000 : ℝ)^6361
        have hw : |(4230892697/10000000000 : ℝ)|=(4230892697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1431/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11447/100000 : ℝ) ^ (1051/256 : ℝ) ≤ (273223540895677/2000000000000000000 : ℝ) := by
    have hpowers : (11447/100000 : ℝ)^1051 ≤ (273223540895677/2000000000000000000 : ℝ)^256 := by
      have hnat : (11447 : ℕ)^1051*2000000000000000000^256 ≤ 273223540895677^256*100000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11447 100000 273223540895677 2000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11447/100000 : ℝ)) (X := (273223540895677/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (1051/256 : ℝ) ≤ (32053885315081191/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^1051 ≤ (32053885315081191/100000000000000000000 : ℝ)^256 := by
      have hnat : (1409 : ℕ)^1051*100000000000000000000^256 ≤ 32053885315081191^256*10000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 32053885315081191 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (32053885315081191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000273223540895677/1000000000000000000 : ℝ) ≤ (10000665442433403/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (1000273223540895677/1000000000000000000 : ℝ)^256 ≤ (10000665442433403/10000000000000000 : ℝ)^1051 := by
      have hnat : (1000273223540895677 : ℕ)^256*10000000000000000^1051 ≤ 10000665442433403^1051*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000273223540895677 1000000000000000000 10000665442433403 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665442433403/10000000000000000 : ℝ)) (X := (1000273223540895677/1000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045715062359865041/100000000000000000000 : ℝ) ≤ (2000222664758383/2000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (100045715062359865041/100000000000000000000 : ℝ)^256 ≤ (2000222664758383/2000000000000000 : ℝ)^1051 := by
      have hnat : (100045715062359865041 : ℕ)^256*2000000000000000^1051 ≤ 2000222664758383^1051*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045715062359865041 100000000000000000000 2000222664758383 2000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000222664758383/2000000000000000 : ℝ)) (X := (100045715062359865041/100000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032053885315081191/50000000000000000000 : ℝ) ≤ (10001561205150427/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50032053885315081191/50000000000000000000 : ℝ)^256 ≤ (10001561205150427/10000000000000000 : ℝ)^1051 := by
      have hnat : (50032053885315081191 : ℕ)^256*10000000000000000^1051 ≤ 10001561205150427^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032053885315081191 50000000000000000000 10001561205150427 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001561205150427/10000000000000000 : ℝ)) (X := (50032053885315081191/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(273223540895677/2000000000000000000 : ℝ) ≤ ((26421504968529710401/26430000000000000000 : ℝ)+2*(27992584907/16518750000000 : ℝ)*(11447/100000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (26421504968529710401/26430000000000000000 : ℝ)+2*(27992584907/16518750000000 : ℝ)*(11447/100000 : ℝ)=(10000665442433403/10000000000000000 : ℝ) by norm_num, show 1+2*(273223540895677/2000000000000000000 : ℝ)=(1000273223540895677/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32053885315081191/100000000000000000000 : ℝ)+(273223540895677/2000000000000000000 : ℝ) ≤ ((26421504968529710401/26430000000000000000 : ℝ)+(27992584907/16518750000000 : ℝ)*((1409/10000 : ℝ)+(11447/100000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (26421504968529710401/26430000000000000000 : ℝ)+(27992584907/16518750000000 : ℝ)*((1409/10000 : ℝ)+(11447/100000 : ℝ))=(2000222664758383/2000000000000000 : ℝ) by norm_num, show 1+(32053885315081191/100000000000000000000 : ℝ)+(273223540895677/2000000000000000000 : ℝ)=(100045715062359865041/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32053885315081191/100000000000000000000 : ℝ) ≤ ((26421504968529710401/26430000000000000000 : ℝ)+2*(27992584907/16518750000000 : ℝ)*(1409/10000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (26421504968529710401/26430000000000000000 : ℝ)+2*(27992584907/16518750000000 : ℝ)*(1409/10000 : ℝ)=(10001561205150427/10000000000000000 : ℝ) by norm_num, show 1+2*(32053885315081191/100000000000000000000 : ℝ)=(50032053885315081191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26421504968529710401/26430000000000000000 : ℝ)*(X 1 0+X 2 0)+(27992584907/16518750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (26421504968529710401/26430000000000000000 : ℝ)) (alpha := (27992584907/16518750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26421504968529710401/26430000000000000000 : ℝ)*(X 0 1+X 2 1)+(27992584907/16518750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (26421504968529710401/26430000000000000000 : ℝ)) (alpha := (27992584907/16518750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26421504968529710401/26430000000000000000 : ℝ)*(X 0 2+X 1 2)+(27992584907/16518750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (26421504968529710401/26430000000000000000 : ℝ)) (alpha := (27992584907/16518750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-532999221/2500000000 : ℝ)*X 0 0+(5391632351/10000000000 : ℝ)*X 0 1+(5266902587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344428533/10000000000 : ℝ)*X 1 0+(-2195243497/10000000000 : ℝ)*X 1 1+(5266902591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672214277/5000000000 : ℝ)*X 2 0+(658362823/1250000000 : ℝ)*X 2 1+(-1097621739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354353741/10000000000 : ℝ)*X 0 0+(4230256587/10000000000 : ℝ)*X 0 1+(179280403/400000000 : ℝ)*X 0 2+(4354353741/10000000000 : ℝ)*X 1 0+(4230256587/10000000000 : ℝ)*X 1 1+(179280403/400000000 : ℝ)*X 1 2+(4354353741/10000000000 : ℝ)*X 2 0+(4230256587/10000000000 : ℝ)*X 2 1+(179280403/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132001593/10000000000 : ℝ)*X 0 0+(2633608189/5000000000 : ℝ)*X 0 1+(5391317417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4354363293/10000000000 : ℝ)*X 0 0+(4481376201/10000000000 : ℝ)*X 0 1+(4230892697/10000000000 : ℝ)*X 0 2+(4354363293/10000000000 : ℝ)*X 1 0+(4481376201/10000000000 : ℝ)*X 1 1+(4230892697/10000000000 : ℝ)*X 1 2+(4354363293/10000000000 : ℝ)*X 2 0+(4481376201/10000000000 : ℝ)*X 2 1+(4230892697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286267885157543887848777721/110125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57374757/12500000000000 : ℝ)*(base19) + (406002083/100000000000000 : ℝ)*(base23) + (11289943/25000000000000 : ℝ)*(lower2) + (7372767/12500000000000 : ℝ)*(upper3) + (16729369/50000000000000 : ℝ)*(upper5) + (1498688810864321/25000000000000 : ℝ)*(major0) + (1498688810864321/25000000000000 : ℝ)*(major1) + (1498688810864321/25000000000000 : ℝ)*(major2) + (16034690147179/200000000000 : ℝ)*(sp0) + (8017357593193719/100000000000000 : ℝ)*(sp1) + (8017357646189693/100000000000000 : ℝ)*(sp2) + (1986072689905079/50000000000000 : ℝ)*(sp3) + (519144091/4000000000000 : ℝ)*(sp4) + (3484131623/50000000000000 : ℝ)*(sp5) + (993038087018351/25000000000000 : ℝ)*(f.failure) + (250542439130993/3125000000000 : ℝ)*(f.sum) + (20673560689007/13215000000000000000000000000 : ℝ)*base66 + (2198974324427599093/220250000000000000000000000000000 : ℝ)*base68 + (2265671056038849093/220250000000000000000000000000000 : ℝ)*base70 + (1713922317632849093/220250000000000000000000000000000 : ℝ)*base72 + (35775160636873/13215000000000000000000000000 : ℝ)*base73 + (792133311642650907/220250000000000000000000000000000 : ℝ)*base75 + (1336604122043400907/220250000000000000000000000000000 : ℝ)*base77 + (4730504095133099093/220250000000000000000000000000000 : ℝ)*base80 + (17718652762531/6607500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1502907/250000000000000000000 : ℝ)*base89 + (1502907/250000000000000000000 : ℝ)*base91 + (1502907/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1216_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1216_box_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-401497937/2000000000 : ℝ)*x 0 + (5375230769/10000000000 : ℝ)*x 1 + (1075046211/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401497937/2000000000 : ℝ)^8409 ≤ (2992776127927/25000000000000 : ℝ)^6361 := by
    have hnat : (401497937 : ℕ)^8409*25000000000000^6361 ≤ 2992776127927^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401497937 2000000000 2992776127927 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375230769/10000000000 : ℝ)^8409 ≤ (1375451443277/3125000000000 : ℝ)^6361 := by
    have hnat : (5375230769 : ℕ)^8409*3125000000000^6361 ≤ 1375451443277^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375230769 10000000000 1375451443277 3125000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075046211/2000000000 : ℝ)^8409 ≤ (44014449280737/100000000000000 : ℝ)^6361 := by
    have hnat : (1075046211 : ℕ)^8409*100000000000000^6361 ≤ 44014449280737^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075046211 2000000000 44014449280737 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401497937/2000000000 : ℝ), (5375230769/10000000000 : ℝ), (1075046211/2000000000 : ℝ)] ![(2992776127927/25000000000000 : ℝ), (1375451443277/3125000000000 : ℝ), (44014449280737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401497937/2000000000 : ℝ)|^8409 ≤ (2992776127927/25000000000000 : ℝ)^6361
        have hw : |(-401497937/2000000000 : ℝ)|=(401497937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375230769/10000000000 : ℝ)|^8409 ≤ (1375451443277/3125000000000 : ℝ)^6361
        have hw : |(5375230769/10000000000 : ℝ)|=(5375230769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075046211/2000000000 : ℝ)|^8409 ≤ (44014449280737/100000000000000 : ℝ)^6361
        have hw : |(1075046211/2000000000 : ℝ)|=(1075046211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296608411/10000000000 : ℝ)*x 0 + (-2114291007/10000000000 : ℝ)*x 1 + (5375230909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296608411/10000000000 : ℝ)^8409 ≤ (10791347744731/25000000000000 : ℝ)^6361 := by
    have hnat : (5296608411 : ℕ)^8409*25000000000000^6361 ≤ 10791347744731^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296608411 10000000000 10791347744731 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2114291007/10000000000 : ℝ)^8409 ≤ (8012600819/62500000000 : ℝ)^6361 := by
    have hnat : (2114291007 : ℕ)^8409*62500000000^6361 ≤ 8012600819^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114291007 10000000000 8012600819 62500000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375230909/10000000000 : ℝ)^8409 ≤ (44014447700327/100000000000000 : ℝ)^6361 := by
    have hnat : (5375230909 : ℕ)^8409*100000000000000^6361 ≤ 44014447700327^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375230909 10000000000 44014447700327 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296608411/10000000000 : ℝ), (-2114291007/10000000000 : ℝ), (5375230909/10000000000 : ℝ)] ![(10791347744731/25000000000000 : ℝ), (8012600819/62500000000 : ℝ), (44014447700327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296608411/10000000000 : ℝ)|^8409 ≤ (10791347744731/25000000000000 : ℝ)^6361
        have hw : |(5296608411/10000000000 : ℝ)|=(5296608411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2114291007/10000000000 : ℝ)|^8409 ≤ (8012600819/62500000000 : ℝ)^6361
        have hw : |(-2114291007/10000000000 : ℝ)|=(2114291007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375230909/10000000000 : ℝ)|^8409 ≤ (44014447700327/100000000000000 : ℝ)^6361
        have hw : |(5375230909/10000000000 : ℝ)|=(5375230909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (132415211/250000000 : ℝ)*x 0 + (2687615409/5000000000 : ℝ)*x 1 + (-211429109/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132415211/250000000 : ℝ)^8409 ≤ (8633078258271/20000000000000 : ℝ)^6361 := by
    have hnat : (132415211 : ℕ)^8409*20000000000000^6361 ≤ 8633078258271^6361*250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132415211 250000000 8633078258271 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687615409/5000000000 : ℝ)^8409 ≤ (11003611678819/25000000000000 : ℝ)^6361 := by
    have hnat : (2687615409 : ℕ)^8409*25000000000000^6361 ≤ 11003611678819^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687615409 5000000000 11003611678819 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211429109/1000000000 : ℝ)^8409 ≤ (400630061741/3125000000000 : ℝ)^6361 := by
    have hnat : (211429109 : ℕ)^8409*3125000000000^6361 ≤ 400630061741^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211429109 1000000000 400630061741 3125000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132415211/250000000 : ℝ), (2687615409/5000000000 : ℝ), (-211429109/1000000000 : ℝ)] ![(8633078258271/20000000000000 : ℝ), (11003611678819/25000000000000 : ℝ), (400630061741/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132415211/250000000 : ℝ)|^8409 ≤ (8633078258271/20000000000000 : ℝ)^6361
        have hw : |(132415211/250000000 : ℝ)|=(132415211/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687615409/5000000000 : ℝ)|^8409 ≤ (11003611678819/25000000000000 : ℝ)^6361
        have hw : |(2687615409/5000000000 : ℝ)|=(2687615409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211429109/1000000000 : ℝ)|^8409 ≤ (400630061741/3125000000000 : ℝ)^6361
        have hw : |(-211429109/1000000000 : ℝ)|=(211429109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4461132839/10000000000 : ℝ)*x 0 + (430302233/1000000000 : ℝ)*x 1 + (860604451/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4461132839/10000000000 : ℝ)^8409 ≤ (34401694281107/100000000000000 : ℝ)^6361 := by
    have hnat : (4461132839 : ℕ)^8409*100000000000000^6361 ≤ 34401694281107^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4461132839 10000000000 34401694281107 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430302233/1000000000 : ℝ)^8409 ≤ (32799153232293/100000000000000 : ℝ)^6361 := by
    have hnat : (430302233 : ℕ)^8409*100000000000000^6361 ≤ 32799153232293^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430302233 1000000000 32799153232293 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (860604451/2000000000 : ℝ)^8409 ≤ (16399576238279/50000000000000 : ℝ)^6361 := by
    have hnat : (860604451 : ℕ)^8409*50000000000000^6361 ≤ 16399576238279^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860604451 2000000000 16399576238279 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4461132839/10000000000 : ℝ), (430302233/1000000000 : ℝ), (860604451/2000000000 : ℝ)] ![(34401694281107/100000000000000 : ℝ), (32799153232293/100000000000000 : ℝ), (16399576238279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4461132839/10000000000 : ℝ)|^8409 ≤ (34401694281107/100000000000000 : ℝ)^6361
        have hw : |(4461132839/10000000000 : ℝ)|=(4461132839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(430302233/1000000000 : ℝ)|^8409 ≤ (32799153232293/100000000000000 : ℝ)^6361
        have hw : |(430302233/1000000000 : ℝ)|=(430302233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(860604451/2000000000 : ℝ)|^8409 ≤ (16399576238279/50000000000000 : ℝ)^6361
        have hw : |(860604451/2000000000 : ℝ)|=(860604451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-112893959/500000000 : ℝ)*x 0 + (1320503621/2500000000 : ℝ)*x 1 + (1056402911/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112893959/500000000 : ℝ)^8409 ≤ (873970813261/6250000000000 : ℝ)^6361 := by
    have hnat : (112893959 : ℕ)^8409*6250000000000^6361 ≤ 873970813261^6361*500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112893959 500000000 873970813261 6250000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320503621/2500000000 : ℝ)^8409 ≤ (43008233105847/100000000000000 : ℝ)^6361 := by
    have hnat : (1320503621 : ℕ)^8409*100000000000000^6361 ≤ 43008233105847^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320503621 2500000000 43008233105847 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056402911/2000000000 : ℝ)^8409 ≤ (43008233870087/100000000000000 : ℝ)^6361 := by
    have hnat : (1056402911 : ℕ)^8409*100000000000000^6361 ≤ 43008233870087^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056402911 2000000000 43008233870087 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-112893959/500000000 : ℝ), (1320503621/2500000000 : ℝ), (1056402911/2000000000 : ℝ)] ![(873970813261/6250000000000 : ℝ), (43008233105847/100000000000000 : ℝ), (43008233870087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-112893959/500000000 : ℝ)|^8409 ≤ (873970813261/6250000000000 : ℝ)^6361
        have hw : |(-112893959/500000000 : ℝ)|=(112893959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320503621/2500000000 : ℝ)|^8409 ≤ (43008233105847/100000000000000 : ℝ)^6361
        have hw : |(1320503621/2500000000 : ℝ)|=(1320503621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056402911/2000000000 : ℝ)|^8409 ≤ (43008233870087/100000000000000 : ℝ)^6361
        have hw : |(1056402911/2000000000 : ℝ)|=(1056402911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2681178753/5000000000 : ℝ)*x 0 + (-215117193/1000000000 : ℝ)*x 1 + (1320503567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681178753/5000000000 : ℝ)^8409 ≤ (5484393792299/12500000000000 : ℝ)^6361 := by
    have hnat : (2681178753 : ℕ)^8409*12500000000000^6361 ≤ 5484393792299^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681178753 5000000000 5484393792299 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215117193/1000000000 : ℝ)^8409 ≤ (13116618874711/100000000000000 : ℝ)^6361 := by
    have hnat : (215117193 : ℕ)^8409*100000000000000^6361 ≤ 13116618874711^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215117193 1000000000 13116618874711 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320503567/2500000000 : ℝ)^8409 ≤ (21504115390419/50000000000000 : ℝ)^6361 := by
    have hnat : (1320503567 : ℕ)^8409*50000000000000^6361 ≤ 21504115390419^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320503567 2500000000 21504115390419 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681178753/5000000000 : ℝ), (-215117193/1000000000 : ℝ), (1320503567/2500000000 : ℝ)] ![(5484393792299/12500000000000 : ℝ), (13116618874711/100000000000000 : ℝ), (21504115390419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681178753/5000000000 : ℝ)|^8409 ≤ (5484393792299/12500000000000 : ℝ)^6361
        have hw : |(2681178753/5000000000 : ℝ)|=(2681178753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215117193/1000000000 : ℝ)|^8409 ≤ (13116618874711/100000000000000 : ℝ)^6361
        have hw : |(-215117193/1000000000 : ℝ)|=(215117193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320503567/2500000000 : ℝ)|^8409 ≤ (21504115390419/50000000000000 : ℝ)^6361
        have hw : |(1320503567/2500000000 : ℝ)|=(1320503567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362356879/10000000000 : ℝ)*x 0 + (5282014747/10000000000 : ℝ)*x 1 + (-2151172131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362356879/10000000000 : ℝ)^8409 ≤ (10968785889131/25000000000000 : ℝ)^6361 := by
    have hnat : (5362356879 : ℕ)^8409*25000000000000^6361 ≤ 10968785889131^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362356879 10000000000 10968785889131 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282014747/10000000000 : ℝ)^8409 ≤ (21504117968381/50000000000000 : ℝ)^6361 := by
    have hnat : (5282014747 : ℕ)^8409*50000000000000^6361 ≤ 21504117968381^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282014747 10000000000 21504117968381 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151172131/10000000000 : ℝ)^8409 ≤ (2623324098977/20000000000000 : ℝ)^6361 := by
    have hnat : (2151172131 : ℕ)^8409*20000000000000^6361 ≤ 2623324098977^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151172131 10000000000 2623324098977 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362356879/10000000000 : ℝ), (5282014747/10000000000 : ℝ), (-2151172131/10000000000 : ℝ)] ![(10968785889131/25000000000000 : ℝ), (21504117968381/50000000000000 : ℝ), (2623324098977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362356879/10000000000 : ℝ)|^8409 ≤ (10968785889131/25000000000000 : ℝ)^6361
        have hw : |(5362356879/10000000000 : ℝ)|=(5362356879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282014747/10000000000 : ℝ)|^8409 ≤ (21504117968381/50000000000000 : ℝ)^6361
        have hw : |(5282014747/10000000000 : ℝ)|=(5282014747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2151172131/10000000000 : ℝ)|^8409 ≤ (2623324098977/20000000000000 : ℝ)^6361
        have hw : |(-2151172131/10000000000 : ℝ)|=(2151172131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4247182151/10000000000 : ℝ)*x 0 + (881995481/2000000000 : ℝ)*x 1 + (4409977299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247182151/10000000000 : ℝ)^8409 ≤ (3223766080957/10000000000000 : ℝ)^6361 := by
    have hnat : (4247182151 : ℕ)^8409*10000000000000^6361 ≤ 3223766080957^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247182151 10000000000 3223766080957 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881995481/2000000000 : ℝ)^8409 ≤ (33881170127759/100000000000000 : ℝ)^6361 := by
    have hnat : (881995481 : ℕ)^8409*100000000000000^6361 ≤ 33881170127759^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881995481 2000000000 33881170127759 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4409977299/10000000000 : ℝ)^8409 ≤ (16940584525589/50000000000000 : ℝ)^6361 := by
    have hnat : (4409977299 : ℕ)^8409*50000000000000^6361 ≤ 16940584525589^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4409977299 10000000000 16940584525589 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247182151/10000000000 : ℝ), (881995481/2000000000 : ℝ), (4409977299/10000000000 : ℝ)] ![(3223766080957/10000000000000 : ℝ), (33881170127759/100000000000000 : ℝ), (16940584525589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247182151/10000000000 : ℝ)|^8409 ≤ (3223766080957/10000000000000 : ℝ)^6361
        have hw : |(4247182151/10000000000 : ℝ)|=(4247182151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(881995481/2000000000 : ℝ)|^8409 ≤ (33881170127759/100000000000000 : ℝ)^6361
        have hw : |(881995481/2000000000 : ℝ)|=(881995481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4409977299/10000000000 : ℝ)|^8409 ≤ (16940584525589/50000000000000 : ℝ)^6361
        have hw : |(4409977299/10000000000 : ℝ)|=(4409977299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_8 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205437717/10000000000 : ℝ)*x 0 + (5218479371/10000000000 : ℝ)*x 1 + (673105403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205437717/10000000000 : ℝ)^8409 ≤ (13555798312287/100000000000000 : ℝ)^6361 := by
    have hnat : (2205437717 : ℕ)^8409*100000000000000^6361 ≤ 13555798312287^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205437717 10000000000 13555798312287 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218479371/10000000000 : ℝ)^8409 ≤ (5290709163817/12500000000000 : ℝ)^6361 := by
    have hnat : (5218479371 : ℕ)^8409*12500000000000^6361 ≤ 5290709163817^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218479371 10000000000 5290709163817 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673105403/1250000000 : ℝ)^8409 ≤ (8823705672041/20000000000000 : ℝ)^6361 := by
    have hnat : (673105403 : ℕ)^8409*20000000000000^6361 ≤ 8823705672041^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673105403 1250000000 8823705672041 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205437717/10000000000 : ℝ), (5218479371/10000000000 : ℝ), (673105403/1250000000 : ℝ)] ![(13555798312287/100000000000000 : ℝ), (5290709163817/12500000000000 : ℝ), (8823705672041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205437717/10000000000 : ℝ)|^8409 ≤ (13555798312287/100000000000000 : ℝ)^6361
        have hw : |(-2205437717/10000000000 : ℝ)|=(2205437717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218479371/10000000000 : ℝ)|^8409 ≤ (5290709163817/12500000000000 : ℝ)^6361
        have hw : |(5218479371/10000000000 : ℝ)|=(5218479371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673105403/1250000000 : ℝ)|^8409 ≤ (8823705672041/20000000000000 : ℝ)^6361
        have hw : |(673105403/1250000000 : ℝ)|=(673105403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_9 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289825493/10000000000 : ℝ)*x 0 + (-422084013/2000000000 : ℝ)*x 1 + (5384843191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289825493/10000000000 : ℝ)^8409 ≤ (43092330288861/100000000000000 : ℝ)^6361 := by
    have hnat : (5289825493 : ℕ)^8409*100000000000000^6361 ≤ 43092330288861^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289825493 10000000000 43092330288861 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422084013/2000000000 : ℝ)^8409 ≤ (12789141704481/100000000000000 : ℝ)^6361 := by
    have hnat : (422084013 : ℕ)^8409*100000000000000^6361 ≤ 12789141704481^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422084013 2000000000 12789141704481 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384843191/10000000000 : ℝ)^8409 ≤ (44118528002783/100000000000000 : ℝ)^6361 := by
    have hnat : (5384843191 : ℕ)^8409*100000000000000^6361 ≤ 44118528002783^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384843191 10000000000 44118528002783 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289825493/10000000000 : ℝ), (-422084013/2000000000 : ℝ), (5384843191/10000000000 : ℝ)] ![(43092330288861/100000000000000 : ℝ), (12789141704481/100000000000000 : ℝ), (44118528002783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289825493/10000000000 : ℝ)|^8409 ≤ (43092330288861/100000000000000 : ℝ)^6361
        have hw : |(5289825493/10000000000 : ℝ)|=(5289825493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422084013/2000000000 : ℝ)|^8409 ≤ (12789141704481/100000000000000 : ℝ)^6361
        have hw : |(-422084013/2000000000 : ℝ)|=(422084013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384843191/10000000000 : ℝ)|^8409 ≤ (44118528002783/100000000000000 : ℝ)^6361
        have hw : |(5384843191/10000000000 : ℝ)|=(5384843191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_10 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289825519/10000000000 : ℝ)*x 0 + (1076968647/2000000000 : ℝ)*x 1 + (-2110419969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289825519/10000000000 : ℝ)^8409 ≤ (5386541321107/12500000000000 : ℝ)^6361 := by
    have hnat : (5289825519 : ℕ)^8409*12500000000000^6361 ≤ 5386541321107^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289825519 10000000000 5386541321107 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076968647/2000000000 : ℝ)^8409 ≤ (8823705695869/20000000000000 : ℝ)^6361 := by
    have hnat : (1076968647 : ℕ)^8409*20000000000000^6361 ≤ 8823705695869^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076968647 2000000000 8823705695869 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110419969/10000000000 : ℝ)^8409 ≤ (12789140935417/100000000000000 : ℝ)^6361 := by
    have hnat : (2110419969 : ℕ)^8409*100000000000000^6361 ≤ 12789140935417^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110419969 10000000000 12789140935417 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289825519/10000000000 : ℝ), (1076968647/2000000000 : ℝ), (-2110419969/10000000000 : ℝ)] ![(5386541321107/12500000000000 : ℝ), (8823705695869/20000000000000 : ℝ), (12789140935417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289825519/10000000000 : ℝ)|^8409 ≤ (5386541321107/12500000000000 : ℝ)^6361
        have hw : |(5289825519/10000000000 : ℝ)|=(5289825519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076968647/2000000000 : ℝ)|^8409 ≤ (8823705695869/20000000000000 : ℝ)^6361
        have hw : |(1076968647/2000000000 : ℝ)|=(1076968647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110419969/10000000000 : ℝ)|^8409 ≤ (12789140935417/100000000000000 : ℝ)^6361
        have hw : |(-2110419969/10000000000 : ℝ)|=(2110419969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_11 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (112073061/250000000 : ℝ)*x 0 + (4291986923/10000000000 : ℝ)*x 1 + (4291987/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112073061/250000000 : ℝ)^8409 ≤ (34623996541893/100000000000000 : ℝ)^6361 := by
    have hnat : (112073061 : ℕ)^8409*100000000000000^6361 ≤ 34623996541893^6361*250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112073061 250000000 34623996541893 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4291986923/10000000000 : ℝ)^8409 ≤ (8172000332123/25000000000000 : ℝ)^6361 := by
    have hnat : (4291986923 : ℕ)^8409*25000000000000^6361 ≤ 8172000332123^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291986923 10000000000 8172000332123 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4291987/10000000 : ℝ)^8409 ≤ (16344001051869/50000000000000 : ℝ)^6361 := by
    have hnat : (4291987 : ℕ)^8409*50000000000000^6361 ≤ 16344001051869^6361*10000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291987 10000000 16344001051869 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112073061/250000000 : ℝ), (4291986923/10000000000 : ℝ), (4291987/10000000 : ℝ)] ![(34623996541893/100000000000000 : ℝ), (8172000332123/25000000000000 : ℝ), (16344001051869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112073061/250000000 : ℝ)|^8409 ≤ (34623996541893/100000000000000 : ℝ)^6361
        have hw : |(112073061/250000000 : ℝ)|=(112073061/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4291986923/10000000000 : ℝ)|^8409 ≤ (8172000332123/25000000000000 : ℝ)^6361
        have hw : |(4291986923/10000000000 : ℝ)|=(4291986923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4291987/10000000 : ℝ)|^8409 ≤ (16344001051869/50000000000000 : ℝ)^6361
        have hw : |(4291987/10000000 : ℝ)|=(4291987/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_12 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060206047/10000000000 : ℝ)*x 0 + (339846261/625000000 : ℝ)*x 1 + (527394489/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060206047/10000000000 : ℝ)^8409 ≤ (6194211004641/50000000000000 : ℝ)^6361 := by
    have hnat : (2060206047 : ℕ)^8409*50000000000000^6361 ≤ 6194211004641^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060206047 10000000000 6194211004641 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339846261/625000000 : ℝ)^8409 ≤ (5586273008707/12500000000000 : ℝ)^6361 := by
    have hnat : (339846261 : ℕ)^8409*12500000000000^6361 ≤ 5586273008707^6361*625000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339846261 625000000 5586273008707 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527394489/1000000000 : ℝ)^8409 ≤ (42921393909593/100000000000000 : ℝ)^6361 := by
    have hnat : (527394489 : ℕ)^8409*100000000000000^6361 ≤ 42921393909593^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527394489 1000000000 42921393909593 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060206047/10000000000 : ℝ), (339846261/625000000 : ℝ), (527394489/1000000000 : ℝ)] ![(6194211004641/50000000000000 : ℝ), (5586273008707/12500000000000 : ℝ), (42921393909593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060206047/10000000000 : ℝ)|^8409 ≤ (6194211004641/50000000000000 : ℝ)^6361
        have hw : |(-2060206047/10000000000 : ℝ)|=(2060206047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339846261/625000000 : ℝ)|^8409 ≤ (5586273008707/12500000000000 : ℝ)^6361
        have hw : |(339846261/625000000 : ℝ)|=(339846261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527394489/1000000000 : ℝ)|^8409 ≤ (42921393909593/100000000000000 : ℝ)^6361
        have hw : |(527394489/1000000000 : ℝ)|=(527394489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_13 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (214721871/400000000 : ℝ)*x 0 + (-1077154179/5000000000 : ℝ)*x 1 + (1318486263/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214721871/400000000 : ℝ)^8409 ≤ (8787339624719/20000000000000 : ℝ)^6361 := by
    have hnat : (214721871 : ℕ)^8409*20000000000000^6361 ≤ 8787339624719^6361*400000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214721871 400000000 8787339624719 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1077154179/5000000000 : ℝ)^8409 ≤ (13141906202897/100000000000000 : ℝ)^6361 := by
    have hnat : (1077154179 : ℕ)^8409*100000000000000^6361 ≤ 13141906202897^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077154179 5000000000 13141906202897 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318486263/2500000000 : ℝ)^8409 ≤ (10730348913123/25000000000000 : ℝ)^6361 := by
    have hnat : (1318486263 : ℕ)^8409*25000000000000^6361 ≤ 10730348913123^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318486263 2500000000 10730348913123 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214721871/400000000 : ℝ), (-1077154179/5000000000 : ℝ), (1318486263/2500000000 : ℝ)] ![(8787339624719/20000000000000 : ℝ), (13141906202897/100000000000000 : ℝ), (10730348913123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214721871/400000000 : ℝ)|^8409 ≤ (8787339624719/20000000000000 : ℝ)^6361
        have hw : |(214721871/400000000 : ℝ)|=(214721871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1077154179/5000000000 : ℝ)|^8409 ≤ (13141906202897/100000000000000 : ℝ)^6361
        have hw : |(-1077154179/5000000000 : ℝ)|=(1077154179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318486263/2500000000 : ℝ)|^8409 ≤ (10730348913123/25000000000000 : ℝ)^6361
        have hw : |(1318486263/2500000000 : ℝ)|=(1318486263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_14 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368047023/10000000000 : ℝ)*x 0 + (2636972479/5000000000 : ℝ)*x 1 + (-269288519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368047023/10000000000 : ℝ)^8409 ≤ (10984175201743/25000000000000 : ℝ)^6361 := by
    have hnat : (5368047023 : ℕ)^8409*25000000000000^6361 ≤ 10984175201743^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368047023 10000000000 10984175201743 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636972479/5000000000 : ℝ)^8409 ≤ (2146069732059/5000000000000 : ℝ)^6361 := by
    have hnat : (2636972479 : ℕ)^8409*5000000000000^6361 ≤ 2146069732059^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636972479 5000000000 2146069732059 5000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269288519/1250000000 : ℝ)^8409 ≤ (328547613541/2500000000000 : ℝ)^6361 := by
    have hnat : (269288519 : ℕ)^8409*2500000000000^6361 ≤ 328547613541^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269288519 1250000000 328547613541 2500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368047023/10000000000 : ℝ), (2636972479/5000000000 : ℝ), (-269288519/1250000000 : ℝ)] ![(10984175201743/25000000000000 : ℝ), (2146069732059/5000000000000 : ℝ), (328547613541/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368047023/10000000000 : ℝ)|^8409 ≤ (10984175201743/25000000000000 : ℝ)^6361
        have hw : |(5368047023/10000000000 : ℝ)|=(5368047023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636972479/5000000000 : ℝ)|^8409 ≤ (2146069732059/5000000000000 : ℝ)^6361
        have hw : |(2636972479/5000000000 : ℝ)|=(2636972479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269288519/1250000000 : ℝ)|^8409 ≤ (328547613541/2500000000000 : ℝ)^6361
        have hw : |(-269288519/1250000000 : ℝ)|=(269288519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_box_15 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2114214677/5000000000 : ℝ)*x 0 + (2209615719/5000000000 : ℝ)*x 1 + (4419230901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114214677/5000000000 : ℝ)^8409 ≤ (16024812939523/50000000000000 : ℝ)^6361 := by
    have hnat : (2114214677 : ℕ)^8409*50000000000000^6361 ≤ 16024812939523^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114214677 5000000000 16024812939523 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209615719/5000000000 : ℝ)^8409 ≤ (2123449361391/6250000000000 : ℝ)^6361 := by
    have hnat : (2209615719 : ℕ)^8409*6250000000000^6361 ≤ 2123449361391^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209615719 5000000000 2123449361391 6250000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4419230901/10000000000 : ℝ)^8409 ≤ (8493796081143/25000000000000 : ℝ)^6361 := by
    have hnat : (4419230901 : ℕ)^8409*25000000000000^6361 ≤ 8493796081143^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419230901 10000000000 8493796081143 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2114214677/5000000000 : ℝ), (2209615719/5000000000 : ℝ), (4419230901/10000000000 : ℝ)] ![(16024812939523/50000000000000 : ℝ), (2123449361391/6250000000000 : ℝ), (8493796081143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2114214677/5000000000 : ℝ)|^8409 ≤ (16024812939523/50000000000000 : ℝ)^6361
        have hw : |(2114214677/5000000000 : ℝ)|=(2114214677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209615719/5000000000 : ℝ)|^8409 ≤ (2123449361391/6250000000000 : ℝ)^6361
        have hw : |(2209615719/5000000000 : ℝ)|=(2209615719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4419230901/10000000000 : ℝ)|^8409 ≤ (8493796081143/25000000000000 : ℝ)^6361
        have hw : |(4419230901/10000000000 : ℝ)|=(4419230901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(31121/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59357/100000 : ℝ) ∧ (2501/3125 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83289/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1431/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1431/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1431/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1431/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1431/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1431/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1431/12500 : ℝ) ^ (1051/256 : ℝ) ≤ (13666077293203887/100000000000000000000 : ℝ) := by
    have hpowers : (1431/12500 : ℝ)^1051 ≤ (13666077293203887/100000000000000000000 : ℝ)^256 := by
      have hnat : (1431 : ℕ)^1051*100000000000000000000^256 ≤ 13666077293203887^256*12500^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1431 12500 13666077293203887 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1431/12500 : ℝ)) (X := (13666077293203887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (1051/256 : ℝ) ≤ (32053885315081191/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^1051 ≤ (32053885315081191/100000000000000000000 : ℝ)^256 := by
      have hnat : (1409 : ℕ)^1051*100000000000000000000^256 ≤ 32053885315081191^256*10000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 32053885315081191 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (32053885315081191/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013666077293203887/50000000000000000000 : ℝ) ≤ (5000332840551083/5000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50013666077293203887/50000000000000000000 : ℝ)^256 ≤ (5000332840551083/5000000000000000 : ℝ)^1051 := by
      have hnat : (50013666077293203887 : ℕ)^256*5000000000000000^1051 ≤ 5000332840551083^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013666077293203887 50000000000000000000 5000332840551083 5000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000332840551083/5000000000000000 : ℝ)) (X := (50013666077293203887/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022859981304142539/50000000000000000000 : ℝ) ≤ (1250139180388713/1250000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50022859981304142539/50000000000000000000 : ℝ)^256 ≤ (1250139180388713/1250000000000000 : ℝ)^1051 := by
      have hnat : (50022859981304142539 : ℕ)^256*1250000000000000^1051 ≤ 1250139180388713^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022859981304142539 50000000000000000000 1250139180388713 1250000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250139180388713/1250000000000000 : ℝ)) (X := (50022859981304142539/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032053885315081191/50000000000000000000 : ℝ) ≤ (5000780602558621/5000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50032053885315081191/50000000000000000000 : ℝ)^256 ≤ (5000780602558621/5000000000000000 : ℝ)^1051 := by
      have hnat : (50032053885315081191 : ℕ)^256*5000000000000000^1051 ≤ 5000780602558621^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032053885315081191 50000000000000000000 5000780602558621 5000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000780602558621/5000000000000000 : ℝ)) (X := (50032053885315081191/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13666077293203887/100000000000000000000 : ℝ) ≤ ((6602876692636833131/6605000000000000000 : ℝ)+2*(223881003769/132100000000000 : ℝ)*(1431/12500 : ℝ))^(1051/256 : ℝ) := by
    rw [show (6602876692636833131/6605000000000000000 : ℝ)+2*(223881003769/132100000000000 : ℝ)*(1431/12500 : ℝ)=(5000332840551083/5000000000000000 : ℝ) by norm_num, show 1+2*(13666077293203887/100000000000000000000 : ℝ)=(50013666077293203887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32053885315081191/100000000000000000000 : ℝ)+(13666077293203887/100000000000000000000 : ℝ) ≤ ((6602876692636833131/6605000000000000000 : ℝ)+(223881003769/132100000000000 : ℝ)*((1409/10000 : ℝ)+(1431/12500 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (6602876692636833131/6605000000000000000 : ℝ)+(223881003769/132100000000000 : ℝ)*((1409/10000 : ℝ)+(1431/12500 : ℝ))=(1250139180388713/1250000000000000 : ℝ) by norm_num, show 1+(32053885315081191/100000000000000000000 : ℝ)+(13666077293203887/100000000000000000000 : ℝ)=(50022859981304142539/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32053885315081191/100000000000000000000 : ℝ) ≤ ((6602876692636833131/6605000000000000000 : ℝ)+2*(223881003769/132100000000000 : ℝ)*(1409/10000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (6602876692636833131/6605000000000000000 : ℝ)+2*(223881003769/132100000000000 : ℝ)*(1409/10000 : ℝ)=(5000780602558621/5000000000000000 : ℝ) by norm_num, show 1+2*(32053885315081191/100000000000000000000 : ℝ)=(50032053885315081191/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6602876692636833131/6605000000000000000 : ℝ)*(X 1 0+X 2 0)+(223881003769/132100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6602876692636833131/6605000000000000000 : ℝ)) (alpha := (223881003769/132100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6602876692636833131/6605000000000000000 : ℝ)*(X 0 1+X 2 1)+(223881003769/132100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6602876692636833131/6605000000000000000 : ℝ)) (alpha := (223881003769/132100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6602876692636833131/6605000000000000000 : ℝ)*(X 0 2+X 1 2)+(223881003769/132100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (1431/12500 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (6602876692636833131/6605000000000000000 : ℝ)) (alpha := (223881003769/132100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-401497937/2000000000 : ℝ)*X 0 0+(5375230769/10000000000 : ℝ)*X 0 1+(1075046211/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296608411/10000000000 : ℝ)*X 1 0+(-2114291007/10000000000 : ℝ)*X 1 1+(5375230909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((132415211/250000000 : ℝ)*X 2 0+(2687615409/5000000000 : ℝ)*X 2 1+(-211429109/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4461132839/10000000000 : ℝ)*X 0 0+(430302233/1000000000 : ℝ)*X 0 1+(860604451/2000000000 : ℝ)*X 0 2+(4461132839/10000000000 : ℝ)*X 1 0+(430302233/1000000000 : ℝ)*X 1 1+(860604451/2000000000 : ℝ)*X 1 2+(4461132839/10000000000 : ℝ)*X 2 0+(430302233/1000000000 : ℝ)*X 2 1+(860604451/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-112893959/500000000 : ℝ)*X 0 0+(1320503621/2500000000 : ℝ)*X 0 1+(1056402911/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681178753/5000000000 : ℝ)*X 1 0+(-215117193/1000000000 : ℝ)*X 1 1+(1320503567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362356879/10000000000 : ℝ)*X 2 0+(5282014747/10000000000 : ℝ)*X 2 1+(-2151172131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4247182151/10000000000 : ℝ)*X 0 0+(881995481/2000000000 : ℝ)*X 0 1+(4409977299/10000000000 : ℝ)*X 0 2+(4247182151/10000000000 : ℝ)*X 1 0+(881995481/2000000000 : ℝ)*X 1 1+(4409977299/10000000000 : ℝ)*X 1 2+(4247182151/10000000000 : ℝ)*X 2 0+(881995481/2000000000 : ℝ)*X 2 1+(4409977299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2205437717/10000000000 : ℝ)*X 0 0+(5218479371/10000000000 : ℝ)*X 0 1+(673105403/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289825493/10000000000 : ℝ)*X 1 0+(-422084013/2000000000 : ℝ)*X 1 1+(5384843191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289825519/10000000000 : ℝ)*X 2 0+(1076968647/2000000000 : ℝ)*X 2 1+(-2110419969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((112073061/250000000 : ℝ)*X 0 0+(4291986923/10000000000 : ℝ)*X 0 1+(4291987/10000000 : ℝ)*X 0 2+(112073061/250000000 : ℝ)*X 1 0+(4291986923/10000000000 : ℝ)*X 1 1+(4291987/10000000 : ℝ)*X 1 2+(112073061/250000000 : ℝ)*X 2 0+(4291986923/10000000000 : ℝ)*X 2 1+(4291987/10000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2060206047/10000000000 : ℝ)*X 0 0+(339846261/625000000 : ℝ)*X 0 1+(527394489/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((214721871/400000000 : ℝ)*X 1 0+(-1077154179/5000000000 : ℝ)*X 1 1+(1318486263/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5368047023/10000000000 : ℝ)*X 2 0+(2636972479/5000000000 : ℝ)*X 2 1+(-269288519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2114214677/5000000000 : ℝ)*X 0 0+(2209615719/5000000000 : ℝ)*X 0 1+(4419230901/10000000000 : ℝ)*X 0 2+(2114214677/5000000000 : ℝ)*X 1 0+(2209615719/5000000000 : ℝ)*X 1 1+(4419230901/10000000000 : ℝ)*X 1 2+(2114214677/5000000000 : ℝ)*X 2 0+(2209615719/5000000000 : ℝ)*X 2 1+(4419230901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31121/50000 : ℝ) ≤ (-102772694945827878093799470233079/165125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (192208333/100000000000000 : ℝ)*(upper1) + (3633809/1250000000000 : ℝ)*(lower4) + (806559/2500000000000 : ℝ)*(upper5) + (1990963707294303/50000000000000 : ℝ)*(major0) + (1990963707294303/50000000000000 : ℝ)*(major1) + (1990963707294303/50000000000000 : ℝ)*(major2) + (4467134093/50000000000000 : ℝ)*(sp3) + (1336539372653779/25000000000000 : ℝ)*(sp4) + (668263679916353/12500000000000 : ℝ)*(sp5) + (5346031242470747/100000000000000 : ℝ)*(sp6) + (1319217226443687/50000000000000 : ℝ)*(sp7) + (394998923/100000000000000 : ℝ)*(sp12) + (3027892701/6250000000000 : ℝ)*(sp13) + (126643143293/100000000000000 : ℝ)*(sp14) + (65961084678889/2500000000000 : ℝ)*(f.failure) + (5346157885614039/100000000000000 : ℝ)*(f.sum) + (57381788952521/6605000000000000000000000000 : ℝ)*base66 + (2278706312947802693/330250000000000000000000000000000 : ℝ)*base67 + (3535102588661802693/330250000000000000000000000000000 : ℝ)*base69 + (5039193275559697307/330250000000000000000000000000000 : ℝ)*base72 + (3363047779549/1651250000000000000000000000 : ℝ)*base74 + (1082112188738302693/330250000000000000000000000000000 : ℝ)*base75 + (1870045586201697307/330250000000000000000000000000000 : ℝ)*base78 + (1060611515790052693/330250000000000000000000000000000 : ℝ)*base79 + (18138614630899/6605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (95773/25000000000000000000 : ℝ)*base89 + (95773/25000000000000000000 : ℝ)*base91 + (95773/25000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59357/100000 : ℝ) ≤ (153150958882440996263854136529/258007812500000000000000000000 : ℝ) := by norm_num
    linear_combination (9234711/25000000000000 : ℝ)*(upper1) + (68426607/50000000000000 : ℝ)*(upper2) + (438627/1000000000000 : ℝ)*(upper3) + (102639129/100000000000000 : ℝ)*(upper4) + (5547313/12500000000000 : ℝ)*(upper5) + (25295595181999/625000000000 : ℝ)*(major0) + (25295595181999/625000000000 : ℝ)*(major1) + (25295595181999/625000000000 : ℝ)*(major2) + (2696519626575999/50000000000000 : ℝ)*(sp0) + (337065481913157/6250000000000 : ℝ)*(sp1) + (2696487105707007/50000000000000 : ℝ)*(sp2) + (1340878200593813/50000000000000 : ℝ)*(sp3) + (36749598249/50000000000000 : ℝ)*(sp10) + (4228729257/50000000000000 : ℝ)*(sp12) + (1340878200593813/50000000000000 : ℝ)*(f.failure) + (337065481913157/6250000000000 : ℝ)*(f.sum) + (3910890751177/660500000000000000000000000 : ℝ)*base66 + (37862672104897381/4128125000000000000000000000000 : ℝ)*base68 + (4201128082121369/4128125000000000000000000000000 : ℝ)*base69 + (40231774723459881/4128125000000000000000000000000 : ℝ)*base72 + (226239060581/330250000000000000000000000 : ℝ)*base74 + (48558472794809881/4128125000000000000000000000000 : ℝ)*base76 + (230892073446369/4128125000000000000000000000000 : ℝ)*base77 + (33689920240759881/4128125000000000000000000000000 : ℝ)*base80 + (1046588052003/165125000000000000000000000 : ℝ)*base81 + (262041/500000000000000000000 : ℝ)*base89 + (262041/500000000000000000000 : ℝ)*base91 + (262041/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (2501/3125 : ℝ) ≤ (66078280969778667372135285078999/82562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (173749/10000000000000 : ℝ)*(upper0) + (1504017/12500000000000 : ℝ)*(lower1) + (5545883/10000000000000 : ℝ)*(lower3) + (7158707/20000000000000 : ℝ)*(upper4) + (1128611967285743/25000000000000 : ℝ)*(major0) + (1128611967285743/25000000000000 : ℝ)*(major1) + (1128611967285743/25000000000000 : ℝ)*(major2) + (24542190029/100000000000000 : ℝ)*(sp1) + (54271456929/100000000000000 : ℝ)*(sp2) + (24896765659/100000000000000 : ℝ)*(sp3) + (150273094207673/2500000000000 : ℝ)*(sp8) + (6010899226116891/100000000000000 : ℝ)*(sp9) + (601086949684999/10000000000000 : ℝ)*(sp10) + (1495634494271119/50000000000000 : ℝ)*(sp11) + (1495646942653949/50000000000000 : ℝ)*(f.failure) + (150273094207673/2500000000000 : ℝ)*(f.sum) + (15412833511963/6605000000000000000000000000 : ℝ)*base65 + (644241003686701333/165125000000000000000000000000000 : ℝ)*base67 + (9503841710923667/165125000000000000000000000000000 : ℝ)*base70 + (204628038040673667/165125000000000000000000000000000 : ℝ)*base72 + (3375395914869/3302500000000000000000000000 : ℝ)*base73 + (701300884873673667/165125000000000000000000000000000 : ℝ)*base76 + (1044014454484173667/165125000000000000000000000000000 : ℝ)*base78 + (749060991075201333/165125000000000000000000000000000 : ℝ)*base79 + (97470452965843/6605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (4188193/500000000000000000000 : ℝ)*base89 + (4188193/500000000000000000000 : ℝ)*base91 + (4188193/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83289/100000 : ℝ) ≤ (-275052724887780574385627264476137/330250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5669043/10000000000000 : ℝ)*(lower0) + (200821997/100000000000000 : ℝ)*(lower2) + (140862459/100000000000000 : ℝ)*(upper3) + (134449347/100000000000000 : ℝ)*(upper5) + (4549795346028791/100000000000000 : ℝ)*(major0) + (4549795346028791/100000000000000 : ℝ)*(major1) + (4549795346028791/100000000000000 : ℝ)*(major2) + (2762891047/100000000000000 : ℝ)*(sp0) + (86528846803/100000000000000 : ℝ)*(sp5) + (25406424859/20000000000000 : ℝ)*(sp7) + (6112634715034517/100000000000000 : ℝ)*(sp12) + (152813773726969/2500000000000 : ℝ)*(sp13) + (6112637477925563/100000000000000 : ℝ)*(sp14) + (1507294126829623/50000000000000 : ℝ)*(sp15) + (3014715285783541/100000000000000 : ℝ)*(f.failure) + (6112637477925563/100000000000000 : ℝ)*(f.sum) + (3123506891651/1651250000000000000000000000 : ℝ)*base65 + (9762735050406375379/660500000000000000000000000000000 : ℝ)*base68 + (12999556388790375379/660500000000000000000000000000000 : ℝ)*base70 + (8011645187059124621/660500000000000000000000000000000 : ℝ)*base71 + (370050150644143/3302500000000000000000000000 : ℝ)*base74 + (8224701498734875379/660500000000000000000000000000000 : ℝ)*base76 + (1243107612283624621/660500000000000000000000000000000 : ℝ)*base77 + (92087376595555875379/660500000000000000000000000000000 : ℝ)*base80 + (2507127805863/825625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2079737/1000000000000000000000 : ℝ)*base89 + (2079737/1000000000000000000000 : ℝ)*base91 + (2079737/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1216_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1431/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59357/100000 : ℝ) else (2501/3125 : ℝ) ≤ X j i ∧ X j i ≤ (83289/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1216_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1216_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59357/100000 : ℝ) else (2501/3125 : ℝ) ≤ X j i ∧ X j i ≤ (83289/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1216_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1216_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59357/100000 : ℝ) else (2501/3125 : ℝ) ≤ X j i ∧ X j i ≤ (83289/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
