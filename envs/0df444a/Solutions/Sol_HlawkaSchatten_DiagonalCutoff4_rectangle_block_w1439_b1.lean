-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1439_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:38.3937+00:00
-- url     : https://prove2.me/submissions/a17101a4-cf32-4e09-969d-4363c08a8310

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
theorem support_rectangle_w1439_s3_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962050071/10000000000 : ℝ)*x 0 + (5416282309/10000000000 : ℝ)*x 1 + (523920267/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962050071/10000000000 : ℝ)^4399 ≤ (11970521947717/100000000000000 : ℝ)^3375 := by
    have hnat : (1962050071 : ℕ)^4399*100000000000000^3375 ≤ 11970521947717^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962050071 10000000000 11970521947717 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416282309/10000000000 : ℝ)^4399 ≤ (5621009319109/12500000000000 : ℝ)^3375 := by
    have hnat : (5416282309 : ℕ)^4399*12500000000000^3375 ≤ 5621009319109^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416282309 10000000000 5621009319109 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523920267/1000000000 : ℝ)^4399 ≤ (43061403485449/100000000000000 : ℝ)^3375 := by
    have hnat : (523920267 : ℕ)^4399*100000000000000^3375 ≤ 43061403485449^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523920267 1000000000 43061403485449 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962050071/10000000000 : ℝ), (5416282309/10000000000 : ℝ), (523920267/1000000000 : ℝ)] ![(11970521947717/100000000000000 : ℝ), (5621009319109/12500000000000 : ℝ), (43061403485449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962050071/10000000000 : ℝ)|^4399 ≤ (11970521947717/100000000000000 : ℝ)^3375
        have hw : |(-1962050071/10000000000 : ℝ)|=(1962050071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416282309/10000000000 : ℝ)|^4399 ≤ (5621009319109/12500000000000 : ℝ)^3375
        have hw : |(5416282309/10000000000 : ℝ)|=(5416282309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523920267/1000000000 : ℝ)|^4399 ≤ (43061403485449/100000000000000 : ℝ)^3375
        have hw : |(523920267/1000000000 : ℝ)|=(523920267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s3_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349332563/10000000000 : ℝ)*x 0 + (-2052361841/10000000000 : ℝ)*x 1 + (261960107/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349332563/10000000000 : ℝ)^4399 ≤ (44244947486199/100000000000000 : ℝ)^3375 := by
    have hnat : (5349332563 : ℕ)^4399*100000000000000^3375 ≤ 44244947486199^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349332563 10000000000 44244947486199 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052361841/10000000000 : ℝ)^4399 ≤ (6346827342403/50000000000000 : ℝ)^3375 := by
    have hnat : (2052361841 : ℕ)^4399*50000000000000^3375 ≤ 6346827342403^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052361841 10000000000 6346827342403 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261960107/500000000 : ℝ)^4399 ≤ (43061397807663/100000000000000 : ℝ)^3375 := by
    have hnat : (261960107 : ℕ)^4399*100000000000000^3375 ≤ 43061397807663^3375*500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261960107 500000000 43061397807663 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349332563/10000000000 : ℝ), (-2052361841/10000000000 : ℝ), (261960107/500000000 : ℝ)] ![(44244947486199/100000000000000 : ℝ), (6346827342403/50000000000000 : ℝ), (43061397807663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349332563/10000000000 : ℝ)|^4399 ≤ (44244947486199/100000000000000 : ℝ)^3375
        have hw : |(5349332563/10000000000 : ℝ)|=(5349332563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2052361841/10000000000 : ℝ)|^4399 ≤ (6346827342403/50000000000000 : ℝ)^3375
        have hw : |(-2052361841/10000000000 : ℝ)|=(2052361841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261960107/500000000 : ℝ)|^4399 ≤ (43061397807663/100000000000000 : ℝ)^3375
        have hw : |(261960107/500000000 : ℝ)|=(261960107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s3_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349332501/10000000000 : ℝ)*x 0 + (5239202191/10000000000 : ℝ)*x 1 + (-2052361857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349332501/10000000000 : ℝ)^4399 ≤ (221224734089/500000000000 : ℝ)^3375 := by
    have hnat : (5349332501 : ℕ)^4399*500000000000^3375 ≤ 221224734089^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349332501 10000000000 221224734089 500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239202191/10000000000 : ℝ)^4399 ≤ (1345668698563/3125000000000 : ℝ)^3375 := by
    have hnat : (5239202191 : ℕ)^4399*3125000000000^3375 ≤ 1345668698563^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239202191 10000000000 1345668698563 3125000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2052361857/10000000000 : ℝ)^4399 ≤ (12693654813789/100000000000000 : ℝ)^3375 := by
    have hnat : (2052361857 : ℕ)^4399*100000000000000^3375 ≤ 12693654813789^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052361857 10000000000 12693654813789 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349332501/10000000000 : ℝ), (5239202191/10000000000 : ℝ), (-2052361857/10000000000 : ℝ)] ![(221224734089/500000000000 : ℝ), (1345668698563/3125000000000 : ℝ), (12693654813789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349332501/10000000000 : ℝ)|^4399 ≤ (221224734089/500000000000 : ℝ)^3375
        have hw : |(5349332501/10000000000 : ℝ)|=(5349332501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239202191/10000000000 : ℝ)|^4399 ≤ (1345668698563/3125000000000 : ℝ)^3375
        have hw : |(5239202191/10000000000 : ℝ)|=(5239202191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2052361857/10000000000 : ℝ)|^4399 ≤ (12693654813789/100000000000000 : ℝ)^3375
        have hw : |(-2052361857/10000000000 : ℝ)|=(2052361857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s3_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075317297/2500000000 : ℝ)*x 0 + (411287283/1000000000 : ℝ)*x 1 + (4497359053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075317297/2500000000 : ℝ)^4399 ≤ (6659737632571/20000000000000 : ℝ)^3375 := by
    have hnat : (1075317297 : ℕ)^4399*20000000000000^3375 ≤ 6659737632571^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075317297 2500000000 6659737632571 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (411287283/1000000000 : ℝ)^4399 ≤ (31410445889769/100000000000000 : ℝ)^3375 := by
    have hnat : (411287283 : ℕ)^4399*100000000000000^3375 ≤ 31410445889769^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411287283 1000000000 31410445889769 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497359053/10000000000 : ℝ)^4399 ≤ (35290865944443/100000000000000 : ℝ)^3375 := by
    have hnat : (4497359053 : ℕ)^4399*100000000000000^3375 ≤ 35290865944443^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497359053 10000000000 35290865944443 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075317297/2500000000 : ℝ), (411287283/1000000000 : ℝ), (4497359053/10000000000 : ℝ)] ![(6659737632571/20000000000000 : ℝ), (31410445889769/100000000000000 : ℝ), (35290865944443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075317297/2500000000 : ℝ)|^4399 ≤ (6659737632571/20000000000000 : ℝ)^3375
        have hw : |(1075317297/2500000000 : ℝ)|=(1075317297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(411287283/1000000000 : ℝ)|^4399 ≤ (31410445889769/100000000000000 : ℝ)^3375
        have hw : |(411287283/1000000000 : ℝ)|=(411287283/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497359053/10000000000 : ℝ)|^4399 ≤ (35290865944443/100000000000000 : ℝ)^3375
        have hw : |(4497359053/10000000000 : ℝ)|=(4497359053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s3_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962064651/10000000000 : ℝ)*x 0 + (1047981429/2000000000 : ℝ)*x 1 + (5415574161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962064651/10000000000 : ℝ)^4399 ≤ (11970637889827/100000000000000 : ℝ)^3375 := by
    have hnat : (1962064651 : ℕ)^4399*100000000000000^3375 ≤ 11970637889827^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962064651 10000000000 11970637889827 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1047981429/2000000000 : ℝ)^4399 ≤ (8613790108423/20000000000000 : ℝ)^3375 := by
    have hnat : (1047981429 : ℕ)^4399*20000000000000^3375 ≤ 8613790108423^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047981429 2000000000 8613790108423 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415574161/10000000000 : ℝ)^4399 ≤ (22480205778399/50000000000000 : ℝ)^3375 := by
    have hnat : (5415574161 : ℕ)^4399*50000000000000^3375 ≤ 22480205778399^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415574161 10000000000 22480205778399 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962064651/10000000000 : ℝ), (1047981429/2000000000 : ℝ), (5415574161/10000000000 : ℝ)] ![(11970637889827/100000000000000 : ℝ), (8613790108423/20000000000000 : ℝ), (22480205778399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962064651/10000000000 : ℝ)|^4399 ≤ (11970637889827/100000000000000 : ℝ)^3375
        have hw : |(-1962064651/10000000000 : ℝ)|=(1962064651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1047981429/2000000000 : ℝ)|^4399 ≤ (8613790108423/20000000000000 : ℝ)^3375
        have hw : |(1047981429/2000000000 : ℝ)|=(1047981429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415574161/10000000000 : ℝ)|^4399 ≤ (22480205778399/50000000000000 : ℝ)^3375
        have hw : |(5415574161/10000000000 : ℝ)|=(5415574161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s3_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325813077/2500000000 : ℝ)*x 0 + (-58624699/312500000 : ℝ)*x 1 + (2707787049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325813077/2500000000 : ℝ)^4399 ≤ (5468602956269/12500000000000 : ℝ)^3375 := by
    have hnat : (1325813077 : ℕ)^4399*12500000000000^3375 ≤ 5468602956269^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325813077 2500000000 5468602956269 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58624699/312500000 : ℝ)^4399 ≤ (11290765461469/100000000000000 : ℝ)^3375 := by
    have hnat : (58624699 : ℕ)^4399*100000000000000^3375 ≤ 11290765461469^3375*312500000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58624699 312500000 11290765461469 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707787049/5000000000 : ℝ)^4399 ≤ (44960410875077/100000000000000 : ℝ)^3375 := by
    have hnat : (2707787049 : ℕ)^4399*100000000000000^3375 ≤ 44960410875077^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707787049 5000000000 44960410875077 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325813077/2500000000 : ℝ), (-58624699/312500000 : ℝ), (2707787049/5000000000 : ℝ)] ![(5468602956269/12500000000000 : ℝ), (11290765461469/100000000000000 : ℝ), (44960410875077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325813077/2500000000 : ℝ)|^4399 ≤ (5468602956269/12500000000000 : ℝ)^3375
        have hw : |(1325813077/2500000000 : ℝ)|=(1325813077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58624699/312500000 : ℝ)|^4399 ≤ (11290765461469/100000000000000 : ℝ)^3375
        have hw : |(-58624699/312500000 : ℝ)|=(58624699/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707787049/5000000000 : ℝ)|^4399 ≤ (44960410875077/100000000000000 : ℝ)^3375
        have hw : |(2707787049/5000000000 : ℝ)|=(2707787049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s3_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325812747/2500000000 : ℝ)*x 0 + (5415575183/10000000000 : ℝ)*x 1 + (-46899767/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325812747/2500000000 : ℝ)^4399 ≤ (43748809457021/100000000000000 : ℝ)^3375 := by
    have hnat : (1325812747 : ℕ)^4399*100000000000000^3375 ≤ 43748809457021^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325812747 2500000000 43748809457021 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415575183/10000000000 : ℝ)^4399 ≤ (44960422615823/100000000000000 : ℝ)^3375 := by
    have hnat : (5415575183 : ℕ)^4399*100000000000000^3375 ≤ 44960422615823^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415575183 10000000000 44960422615823 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46899767/250000000 : ℝ)^4399 ≤ (11290767908997/100000000000000 : ℝ)^3375 := by
    have hnat : (46899767 : ℕ)^4399*100000000000000^3375 ≤ 11290767908997^3375*250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46899767 250000000 11290767908997 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325812747/2500000000 : ℝ), (5415575183/10000000000 : ℝ), (-46899767/250000000 : ℝ)] ![(43748809457021/100000000000000 : ℝ), (44960422615823/100000000000000 : ℝ), (11290767908997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325812747/2500000000 : ℝ)|^4399 ≤ (43748809457021/100000000000000 : ℝ)^3375
        have hw : |(1325812747/2500000000 : ℝ)|=(1325812747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415575183/10000000000 : ℝ)|^4399 ≤ (44960422615823/100000000000000 : ℝ)^3375
        have hw : |(5415575183/10000000000 : ℝ)|=(5415575183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46899767/250000000 : ℝ)|^4399 ≤ (11290767908997/100000000000000 : ℝ)^3375
        have hw : |(-46899767/250000000 : ℝ)|=(46899767/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s3_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301300989/10000000000 : ℝ)*x 0 + (4495830343/10000000000 : ℝ)*x 1 + (4114411153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301300989/10000000000 : ℝ)^4399 ≤ (33299009049727/100000000000000 : ℝ)^3375 := by
    have hnat : (4301300989 : ℕ)^4399*100000000000000^3375 ≤ 33299009049727^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301300989 10000000000 33299009049727 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495830343/10000000000 : ℝ)^4399 ≤ (7055046262603/20000000000000 : ℝ)^3375 := by
    have hnat : (4495830343 : ℕ)^4399*20000000000000^3375 ≤ 7055046262603^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495830343 10000000000 7055046262603 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4114411153/10000000000 : ℝ)^4399 ≤ (7856439906637/25000000000000 : ℝ)^3375 := by
    have hnat : (4114411153 : ℕ)^4399*25000000000000^3375 ≤ 7856439906637^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114411153 10000000000 7856439906637 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301300989/10000000000 : ℝ), (4495830343/10000000000 : ℝ), (4114411153/10000000000 : ℝ)] ![(33299009049727/100000000000000 : ℝ), (7055046262603/20000000000000 : ℝ), (7856439906637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301300989/10000000000 : ℝ)|^4399 ≤ (33299009049727/100000000000000 : ℝ)^3375
        have hw : |(4301300989/10000000000 : ℝ)|=(4301300989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495830343/10000000000 : ℝ)|^4399 ≤ (7055046262603/20000000000000 : ℝ)^3375
        have hw : |(4495830343/10000000000 : ℝ)|=(4495830343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4114411153/10000000000 : ℝ)|^4399 ≤ (7856439906637/25000000000000 : ℝ)^3375
        have hw : |(4114411153/10000000000 : ℝ)|=(4114411153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11191/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7471/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (521/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15769/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (521/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (521/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15769/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (521/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (521/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15769/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (521/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (521/5000 : ℝ) ^ (2199/512 : ℝ) ≤ (47272504557237/781250000000000000 : ℝ) := by
    have hpowers : (521/5000 : ℝ)^2199 ≤ (47272504557237/781250000000000000 : ℝ)^512 := by
      have hnat : (521 : ℕ)^2199*781250000000000000^512 ≤ 47272504557237^512*5000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        521 5000 47272504557237 781250000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (521/5000 : ℝ)) (X := (47272504557237/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15769/100000 : ℝ) ^ (2199/512 : ℝ) ≤ (3586175254024867/10000000000000000000 : ℝ) := by
    have hpowers : (15769/100000 : ℝ)^2199 ≤ (3586175254024867/10000000000000000000 : ℝ)^512 := by
      have hnat : (15769 : ℕ)^2199*10000000000000000000^512 ≤ 3586175254024867^512*100000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15769 100000 3586175254024867 10000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15769/100000 : ℝ)) (X := (3586175254024867/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (390672272504557237/390625000000000000 : ℝ) ≤ (1250035219498139/1250000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (390672272504557237/390625000000000000 : ℝ)^512 ≤ (1250035219498139/1250000000000000 : ℝ)^2199 := by
      have hnat : (390672272504557237 : ℕ)^512*1250000000000000^2199 ≤ 1250035219498139^2199*390625000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390672272504557237 390625000000000000 1250035219498139 1250000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035219498139/1250000000000000 : ℝ)) (X := (390672272504557237/390625000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020956316561787503/50000000000000000000 : ℝ) ≤ (10000975708003907/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (50020956316561787503/50000000000000000000 : ℝ)^512 ≤ (10000975708003907/10000000000000000 : ℝ)^2199 := by
      have hnat : (50020956316561787503 : ℕ)^512*10000000000000000^2199 ≤ 10000975708003907^2199*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020956316561787503 50000000000000000000 10000975708003907 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000975708003907/10000000000000000 : ℝ)) (X := (50020956316561787503/50000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003586175254024867/5000000000000000000 : ℝ) ≤ (5000834830011351/5000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (5003586175254024867/5000000000000000000 : ℝ)^512 ≤ (5000834830011351/5000000000000000 : ℝ)^2199 := by
      have hnat : (5003586175254024867 : ℕ)^512*5000000000000000^2199 ≤ 5000834830011351^2199*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003586175254024867 5000000000000000000 5000834830011351 5000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000834830011351/5000000000000000 : ℝ)) (X := (5003586175254024867/5000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47272504557237/781250000000000000 : ℝ) ≤ ((835578830510823067/835781250000000000 : ℝ)+2*(138790403759/106980000000000 : ℝ)*(521/5000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (835578830510823067/835781250000000000 : ℝ)+2*(138790403759/106980000000000 : ℝ)*(521/5000 : ℝ)=(1250035219498139/1250000000000000 : ℝ) by norm_num, show 1+2*(47272504557237/781250000000000000 : ℝ)=(390672272504557237/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3586175254024867/10000000000000000000 : ℝ)+(47272504557237/781250000000000000 : ℝ) ≤ ((835578830510823067/835781250000000000 : ℝ)+(138790403759/106980000000000 : ℝ)*((15769/100000 : ℝ)+(521/5000 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (835578830510823067/835781250000000000 : ℝ)+(138790403759/106980000000000 : ℝ)*((15769/100000 : ℝ)+(521/5000 : ℝ))=(10000975708003907/10000000000000000 : ℝ) by norm_num, show 1+(3586175254024867/10000000000000000000 : ℝ)+(47272504557237/781250000000000000 : ℝ)=(50020956316561787503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3586175254024867/10000000000000000000 : ℝ) ≤ ((835578830510823067/835781250000000000 : ℝ)+2*(138790403759/106980000000000 : ℝ)*(15769/100000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (835578830510823067/835781250000000000 : ℝ)+2*(138790403759/106980000000000 : ℝ)*(15769/100000 : ℝ)=(5000834830011351/5000000000000000 : ℝ) by norm_num, show 1+2*(3586175254024867/10000000000000000000 : ℝ)=(5003586175254024867/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (835578830510823067/835781250000000000 : ℝ)*(X 1 0+X 2 0)+(138790403759/106980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (521/5000 : ℝ)) (hi := (15769/100000 : ℝ)) (c := (835578830510823067/835781250000000000 : ℝ)) (alpha := (138790403759/106980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (835578830510823067/835781250000000000 : ℝ)*(X 0 1+X 2 1)+(138790403759/106980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (521/5000 : ℝ)) (hi := (15769/100000 : ℝ)) (c := (835578830510823067/835781250000000000 : ℝ)) (alpha := (138790403759/106980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (835578830510823067/835781250000000000 : ℝ)*(X 0 2+X 1 2)+(138790403759/106980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (521/5000 : ℝ)) (hi := (15769/100000 : ℝ)) (c := (835578830510823067/835781250000000000 : ℝ)) (alpha := (138790403759/106980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1962050071/10000000000 : ℝ)*X 0 0+(5416282309/10000000000 : ℝ)*X 0 1+(523920267/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349332563/10000000000 : ℝ)*X 1 0+(-2052361841/10000000000 : ℝ)*X 1 1+(261960107/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349332501/10000000000 : ℝ)*X 2 0+(5239202191/10000000000 : ℝ)*X 2 1+(-2052361857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075317297/2500000000 : ℝ)*X 0 0+(411287283/1000000000 : ℝ)*X 0 1+(4497359053/10000000000 : ℝ)*X 0 2+(1075317297/2500000000 : ℝ)*X 1 0+(411287283/1000000000 : ℝ)*X 1 1+(4497359053/10000000000 : ℝ)*X 1 2+(1075317297/2500000000 : ℝ)*X 2 0+(411287283/1000000000 : ℝ)*X 2 1+(4497359053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1962064651/10000000000 : ℝ)*X 0 0+(1047981429/2000000000 : ℝ)*X 0 1+(5415574161/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325813077/2500000000 : ℝ)*X 1 0+(-58624699/312500000 : ℝ)*X 1 1+(2707787049/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325812747/2500000000 : ℝ)*X 2 0+(5415575183/10000000000 : ℝ)*X 2 1+(-46899767/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301300989/10000000000 : ℝ)*X 0 0+(4495830343/10000000000 : ℝ)*X 0 1+(4114411153/10000000000 : ℝ)*X 0 2+(4301300989/10000000000 : ℝ)*X 1 0+(4495830343/10000000000 : ℝ)*X 1 1+(4114411153/10000000000 : ℝ)*X 1 2+(4301300989/10000000000 : ℝ)*X 2 0+(4495830343/10000000000 : ℝ)*X 2 1+(4114411153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (497476240754483474639/55718750000000000000000000 : ℝ) := by norm_num
    linear_combination (284340887/20000000000000 : ℝ)*(base19) + (663154269/50000000000000 : ℝ)*(base23) + (8008887/50000000000000 : ℝ)*(lower2) + (1439779/1000000000000 : ℝ)*(upper3) + (92262397/100000000000000 : ℝ)*(upper5) + (20620225235579/500000000000 : ℝ)*(major0) + (20620225235579/500000000000 : ℝ)*(major1) + (20620225235579/500000000000 : ℝ)*(major2) + (5647191754905227/100000000000000 : ℝ)*(sp0) + (2823601787993047/50000000000000 : ℝ)*(sp1) + (705900458922749/12500000000000 : ℝ)*(sp2) + (325109848498707/12500000000000 : ℝ)*(sp3) + (6621392651/50000000000000 : ℝ)*(sp4) + (751367487/12500000000000 : ℝ)*(sp7) + (162555299933097/6250000000000 : ℝ)*(f.failure) + (564720499769053/10000000000000 : ℝ)*(f.sum) + (8734214290597/5349000000000000000000000000 : ℝ)*base66 + (6447165663713219/3343125000000000000000000000000 : ℝ)*base67 + (1693582036200289/835781250000000000000000000000 : ℝ)*base70 + (4428390500326297/1671562500000000000000000000000 : ℝ)*base71 + (13371310840027/2674500000000000000000000000 : ℝ)*base73 + (3138985847650961/835781250000000000000000000000 : ℝ)*base75 + (11093400543810289/835781250000000000000000000000 : ℝ)*base78 + (13316793310807789/835781250000000000000000000000 : ℝ)*base80 + (5375962577/20894531250000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (892771/625000000000000000000 : ℝ)*base90 + (892771/625000000000000000000 : ℝ)*base92 + (892771/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (487681402238937659880689787/27859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (434949919/100000000000000 : ℝ)*(base21) + (209326727/100000000000000 : ℝ)*(upper2) + (318847283/100000000000000 : ℝ)*(lower4) + (44344487/50000000000000 : ℝ)*(upper5) + (2078590803643753/50000000000000 : ℝ)*(major0) + (2078590803643753/50000000000000 : ℝ)*(major1) + (2078590803643753/50000000000000 : ℝ)*(major2) + (508348209/25000000000000 : ℝ)*(sp0) + (2057383311/50000000000000 : ℝ)*(sp2) + (278059487/25000000000000 : ℝ)*(sp3) + (355786111175389/6250000000000 : ℝ)*(sp4) + (284628990609953/5000000000000 : ℝ)*(sp5) + (5692575262482519/100000000000000 : ℝ)*(sp6) + (52435634132687/2000000000000 : ℝ)*(sp7) + (2621782818872297/100000000000000 : ℝ)*(f.failure) + (284628990609953/5000000000000 : ℝ)*(f.sum) + (35572438578413/1337250000000000000000000000 : ℝ)*base66 + (1143525247754283473/83578125000000000000000000000000 : ℝ)*base68 + (1641697282349845973/83578125000000000000000000000000 : ℝ)*base70 + (369374938392408473/83578125000000000000000000000000 : ℝ)*base72 + (9980604904409/1337250000000000000000000000 : ℝ)*base74 + (1483358331973345973/83578125000000000000000000000000 : ℝ)*base76 + (2192517226048439723/83578125000000000000000000000000 : ℝ)*base78 + (175591325142770087/20894531250000000000000000000000 : ℝ)*base80 + (11945219831563/2674500000000000000000000000 : ℝ)*base82 + (7838371/10000000000000000000000 : ℝ)*base90 + (7838371/10000000000000000000000 : ℝ)*base92 + (7838371/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1439_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7471/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1439_s4_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-490724953/2500000000 : ℝ)*x 0 + (5408985829/10000000000 : ℝ)*x 1 + (1049187897/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490724953/2500000000 : ℝ)^4399 ≤ (1497159954761/12500000000000 : ℝ)^3375 := by
    have hnat : (490724953 : ℕ)^4399*12500000000000^3375 ≤ 1497159954761^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490724953 2500000000 1497159954761 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408985829/10000000000 : ℝ)^4399 ≤ (44889132613959/100000000000000 : ℝ)^3375 := by
    have hnat : (5408985829 : ℕ)^4399*100000000000000^3375 ≤ 44889132613959^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408985829 10000000000 44889132613959 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049187897/2000000000 : ℝ)^4399 ≤ (8626717547847/20000000000000 : ℝ)^3375 := by
    have hnat : (1049187897 : ℕ)^4399*20000000000000^3375 ≤ 8626717547847^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049187897 2000000000 8626717547847 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490724953/2500000000 : ℝ), (5408985829/10000000000 : ℝ), (1049187897/2000000000 : ℝ)] ![(1497159954761/12500000000000 : ℝ), (44889132613959/100000000000000 : ℝ), (8626717547847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490724953/2500000000 : ℝ)|^4399 ≤ (1497159954761/12500000000000 : ℝ)^3375
        have hw : |(-490724953/2500000000 : ℝ)|=(490724953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408985829/10000000000 : ℝ)|^4399 ≤ (44889132613959/100000000000000 : ℝ)^3375
        have hw : |(5408985829/10000000000 : ℝ)|=(5408985829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049187897/2000000000 : ℝ)|^4399 ≤ (8626717547847/20000000000000 : ℝ)^3375
        have hw : |(1049187897/2000000000 : ℝ)|=(1049187897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s4_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668430863/1250000000 : ℝ)*x 0 + (-2045925067/10000000000 : ℝ)*x 1 + (5245939727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668430863/1250000000 : ℝ)^4399 ≤ (44224619975339/100000000000000 : ℝ)^3375 := by
    have hnat : (668430863 : ℕ)^4399*100000000000000^3375 ≤ 44224619975339^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668430863 1250000000 44224619975339 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2045925067/10000000000 : ℝ)^4399 ≤ (12641789687037/100000000000000 : ℝ)^3375 := by
    have hnat : (2045925067 : ℕ)^4399*100000000000000^3375 ≤ 12641789687037^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2045925067 10000000000 12641789687037 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245939727/10000000000 : ℝ)^4399 ≤ (8626718066549/20000000000000 : ℝ)^3375 := by
    have hnat : (5245939727 : ℕ)^4399*20000000000000^3375 ≤ 8626718066549^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245939727 10000000000 8626718066549 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668430863/1250000000 : ℝ), (-2045925067/10000000000 : ℝ), (5245939727/10000000000 : ℝ)] ![(44224619975339/100000000000000 : ℝ), (12641789687037/100000000000000 : ℝ), (8626718066549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668430863/1250000000 : ℝ)|^4399 ≤ (44224619975339/100000000000000 : ℝ)^3375
        have hw : |(668430863/1250000000 : ℝ)|=(668430863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2045925067/10000000000 : ℝ)|^4399 ≤ (12641789687037/100000000000000 : ℝ)^3375
        have hw : |(-2045925067/10000000000 : ℝ)|=(2045925067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245939727/10000000000 : ℝ)|^4399 ≤ (8626718066549/20000000000000 : ℝ)^3375
        have hw : |(5245939727/10000000000 : ℝ)|=(5245939727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s4_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347447093/10000000000 : ℝ)*x 0 + (655742457/1250000000 : ℝ)*x 1 + (-1022962453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347447093/10000000000 : ℝ)^4399 ≤ (44224622012661/100000000000000 : ℝ)^3375 := by
    have hnat : (5347447093 : ℕ)^4399*100000000000000^3375 ≤ 44224622012661^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347447093 10000000000 44224622012661 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655742457/1250000000 : ℝ)^4399 ≤ (43133589571839/100000000000000 : ℝ)^3375 := by
    have hnat : (655742457 : ℕ)^4399*100000000000000^3375 ≤ 43133589571839^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655742457 1250000000 43133589571839 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1022962453/5000000000 : ℝ)^4399 ≤ (12641788390381/100000000000000 : ℝ)^3375 := by
    have hnat : (1022962453 : ℕ)^4399*100000000000000^3375 ≤ 12641788390381^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022962453 5000000000 12641788390381 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347447093/10000000000 : ℝ), (655742457/1250000000 : ℝ), (-1022962453/5000000000 : ℝ)] ![(44224622012661/100000000000000 : ℝ), (43133589571839/100000000000000 : ℝ), (12641788390381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347447093/10000000000 : ℝ)|^4399 ≤ (44224622012661/100000000000000 : ℝ)^3375
        have hw : |(5347447093/10000000000 : ℝ)|=(5347447093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655742457/1250000000 : ℝ)|^4399 ≤ (43133589571839/100000000000000 : ℝ)^3375
        have hw : |(655742457/1250000000 : ℝ)|=(655742457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1022962453/5000000000 : ℝ)|^4399 ≤ (12641788390381/100000000000000 : ℝ)^3375
        have hw : |(-1022962453/5000000000 : ℝ)|=(1022962453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s4_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4301791649/10000000000 : ℝ)*x 0 + (129001411/312500000 : ℝ)*x 1 + (4482060993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301791649/10000000000 : ℝ)^4399 ≤ (2081497508027/6250000000000 : ℝ)^3375 := by
    have hnat : (4301791649 : ℕ)^4399*6250000000000^3375 ≤ 2081497508027^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301791649 10000000000 2081497508027 6250000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129001411/312500000 : ℝ)^4399 ≤ (3156155958501/10000000000000 : ℝ)^3375 := by
    have hnat : (129001411 : ℕ)^4399*10000000000000^3375 ≤ 3156155958501^3375*312500000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129001411 312500000 3156155958501 10000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482060993/10000000000 : ℝ)^4399 ≤ (7026896054967/20000000000000 : ℝ)^3375 := by
    have hnat : (4482060993 : ℕ)^4399*20000000000000^3375 ≤ 7026896054967^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482060993 10000000000 7026896054967 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301791649/10000000000 : ℝ), (129001411/312500000 : ℝ), (4482060993/10000000000 : ℝ)] ![(2081497508027/6250000000000 : ℝ), (3156155958501/10000000000000 : ℝ), (7026896054967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301791649/10000000000 : ℝ)|^4399 ≤ (2081497508027/6250000000000 : ℝ)^3375
        have hw : |(4301791649/10000000000 : ℝ)|=(4301791649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129001411/312500000 : ℝ)|^4399 ≤ (3156155958501/10000000000000 : ℝ)^3375
        have hw : |(129001411/312500000 : ℝ)|=(129001411/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482060993/10000000000 : ℝ)|^4399 ≤ (7026896054967/20000000000000 : ℝ)^3375
        have hw : |(4482060993/10000000000 : ℝ)|=(4482060993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s4_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-981455851/5000000000 : ℝ)*x 0 + (5246537151/10000000000 : ℝ)*x 1 + (216335397/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981455851/5000000000 : ℝ)^4399 ≤ (11977374201361/100000000000000 : ℝ)^3375 := by
    have hnat : (981455851 : ℕ)^4399*100000000000000^3375 ≤ 11977374201361^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981455851 5000000000 11977374201361 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246537151/10000000000 : ℝ)^4399 ≤ (10784998256389/25000000000000 : ℝ)^3375 := by
    have hnat : (5246537151 : ℕ)^4399*25000000000000^3375 ≤ 10784998256389^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246537151 10000000000 10784998256389 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216335397/400000000 : ℝ)^4399 ≤ (2244131638201/5000000000000 : ℝ)^3375 := by
    have hnat : (216335397 : ℕ)^4399*5000000000000^3375 ≤ 2244131638201^3375*400000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216335397 400000000 2244131638201 5000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981455851/5000000000 : ℝ), (5246537151/10000000000 : ℝ), (216335397/400000000 : ℝ)] ![(11977374201361/100000000000000 : ℝ), (10784998256389/25000000000000 : ℝ), (2244131638201/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981455851/5000000000 : ℝ)|^4399 ≤ (11977374201361/100000000000000 : ℝ)^3375
        have hw : |(-981455851/5000000000 : ℝ)|=(981455851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246537151/10000000000 : ℝ)|^4399 ≤ (10784998256389/25000000000000 : ℝ)^3375
        have hw : |(5246537151/10000000000 : ℝ)|=(5246537151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216335397/400000000 : ℝ)|^4399 ≤ (2244131638201/5000000000000 : ℝ)^3375
        have hw : |(216335397/400000000 : ℝ)|=(216335397/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s4_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305018483/10000000000 : ℝ)*x 0 + (-235434967/1250000000 : ℝ)*x 1 + (5408384893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305018483/10000000000 : ℝ)^4399 ≤ (43767815179881/100000000000000 : ℝ)^3375 := by
    have hnat : (5305018483 : ℕ)^4399*100000000000000^3375 ≤ 43767815179881^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305018483 10000000000 43767815179881 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235434967/1250000000 : ℝ)^4399 ≤ (2837388099813/25000000000000 : ℝ)^3375 := by
    have hnat : (235434967 : ℕ)^4399*25000000000000^3375 ≤ 2837388099813^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235434967 1250000000 2837388099813 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408384893/10000000000 : ℝ)^4399 ≤ (44882632417889/100000000000000 : ℝ)^3375 := by
    have hnat : (5408384893 : ℕ)^4399*100000000000000^3375 ≤ 44882632417889^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408384893 10000000000 44882632417889 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305018483/10000000000 : ℝ), (-235434967/1250000000 : ℝ), (5408384893/10000000000 : ℝ)] ![(43767815179881/100000000000000 : ℝ), (2837388099813/25000000000000 : ℝ), (44882632417889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305018483/10000000000 : ℝ)|^4399 ≤ (43767815179881/100000000000000 : ℝ)^3375
        have hw : |(5305018483/10000000000 : ℝ)|=(5305018483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-235434967/1250000000 : ℝ)|^4399 ≤ (2837388099813/25000000000000 : ℝ)^3375
        have hw : |(-235434967/1250000000 : ℝ)|=(235434967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408384893/10000000000 : ℝ)|^4399 ≤ (44882632417889/100000000000000 : ℝ)^3375
        have hw : |(5408384893/10000000000 : ℝ)|=(5408384893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s4_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305018437/10000000000 : ℝ)*x 0 + (270419247/500000000 : ℝ)*x 1 + (-1883479733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305018437/10000000000 : ℝ)^4399 ≤ (21883907342611/50000000000000 : ℝ)^3375 := by
    have hnat : (5305018437 : ℕ)^4399*50000000000000^3375 ≤ 21883907342611^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305018437 10000000000 21883907342611 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270419247/500000000 : ℝ)^4399 ≤ (44882632926269/100000000000000 : ℝ)^3375 := by
    have hnat : (270419247 : ℕ)^4399*100000000000000^3375 ≤ 44882632926269^3375*500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270419247 500000000 44882632926269 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1883479733/10000000000 : ℝ)^4399 ≤ (11349552375689/100000000000000 : ℝ)^3375 := by
    have hnat : (1883479733 : ℕ)^4399*100000000000000^3375 ≤ 11349552375689^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883479733 10000000000 11349552375689 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305018437/10000000000 : ℝ), (270419247/500000000 : ℝ), (-1883479733/10000000000 : ℝ)] ![(21883907342611/50000000000000 : ℝ), (44882632926269/100000000000000 : ℝ), (11349552375689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305018437/10000000000 : ℝ)|^4399 ≤ (21883907342611/50000000000000 : ℝ)^3375
        have hw : |(5305018437/10000000000 : ℝ)|=(5305018437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270419247/500000000 : ℝ)|^4399 ≤ (44882632926269/100000000000000 : ℝ)^3375
        have hw : |(270419247/500000000 : ℝ)|=(270419247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1883479733/10000000000 : ℝ)|^4399 ≤ (11349552375689/100000000000000 : ℝ)^3375
        have hw : |(-1883479733/10000000000 : ℝ)|=(1883479733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s4_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075454307/2500000000 : ℝ)*x 0 + (140023859/312500000 : ℝ)*x 1 + (4129349433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075454307/2500000000 : ℝ)^4399 ≤ (33304218241887/100000000000000 : ℝ)^3375 := by
    have hnat : (1075454307 : ℕ)^4399*100000000000000^3375 ≤ 33304218241887^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075454307 2500000000 33304218241887 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140023859/312500000 : ℝ)^4399 ≤ (3512122386501/10000000000000 : ℝ)^3375 := by
    have hnat : (140023859 : ℕ)^4399*10000000000000^3375 ≤ 3512122386501^3375*312500000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140023859 312500000 3512122386501 10000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4129349433/10000000000 : ℝ)^4399 ≤ (31574557873853/100000000000000 : ℝ)^3375 := by
    have hnat : (4129349433 : ℕ)^4399*100000000000000^3375 ≤ 31574557873853^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129349433 10000000000 31574557873853 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075454307/2500000000 : ℝ), (140023859/312500000 : ℝ), (4129349433/10000000000 : ℝ)] ![(33304218241887/100000000000000 : ℝ), (3512122386501/10000000000000 : ℝ), (31574557873853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075454307/2500000000 : ℝ)|^4399 ≤ (33304218241887/100000000000000 : ℝ)^3375
        have hw : |(1075454307/2500000000 : ℝ)|=(1075454307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140023859/312500000 : ℝ)|^4399 ≤ (3512122386501/10000000000000 : ℝ)^3375
        have hw : |(140023859/312500000 : ℝ)|=(140023859/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4129349433/10000000000 : ℝ)|^4399 ≤ (31574557873853/100000000000000 : ℝ)^3375
        have hw : |(4129349433/10000000000 : ℝ)|=(4129349433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7471/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2267/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14789/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7471/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7471/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7471/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7471/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7471/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7471/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11191/100000 : ℝ) ^ (2199/512 : ℝ) ≤ (8221786865599127/100000000000000000000 : ℝ) := by
    have hpowers : (11191/100000 : ℝ)^2199 ≤ (8221786865599127/100000000000000000000 : ℝ)^512 := by
      have hnat : (11191 : ℕ)^2199*100000000000000000000^512 ≤ 8221786865599127^512*100000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11191 100000 8221786865599127 100000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11191/100000 : ℝ)) (X := (8221786865599127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7471/50000 : ℝ) ^ (2199/512 : ℝ) ≤ (7113609356482889/25000000000000000000 : ℝ) := by
    have hpowers : (7471/50000 : ℝ)^2199 ≤ (7113609356482889/25000000000000000000 : ℝ)^512 := by
      have hnat : (7471 : ℕ)^2199*25000000000000000000^512 ≤ 7113609356482889^512*50000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7471 50000 7113609356482889 25000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7471/50000 : ℝ)) (X := (7113609356482889/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008221786865599127/50000000000000000000 : ℝ) ≤ (5000191418343973/5000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (50008221786865599127/50000000000000000000 : ℝ)^512 ≤ (5000191418343973/5000000000000000 : ℝ)^2199 := by
      have hnat : (50008221786865599127 : ℕ)^512*5000000000000000^2199 ≤ 5000191418343973^2199*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008221786865599127 50000000000000000000 5000191418343973 5000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000191418343973/5000000000000000 : ℝ)) (X := (50008221786865599127/50000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036676224291530683/100000000000000000000 : ℝ) ≤ (312526681994107/312500000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (100036676224291530683/100000000000000000000 : ℝ)^512 ≤ (312526681994107/312500000000000 : ℝ)^2199 := by
      have hnat : (100036676224291530683 : ℕ)^512*312500000000000^2199 ≤ 312526681994107^2199*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036676224291530683 100000000000000000000 312526681994107 312500000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312526681994107/312500000000000 : ℝ)) (X := (100036676224291530683/100000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507113609356482889/12500000000000000000 : ℝ) ≤ (5000662405467451/5000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (12507113609356482889/12500000000000000000 : ℝ)^512 ≤ (5000662405467451/5000000000000000 : ℝ)^2199 := by
      have hnat : (12507113609356482889 : ℕ)^512*5000000000000000^2199 ≤ 5000662405467451^2199*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507113609356482889 12500000000000000000 5000662405467451 5000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000662405467451/5000000000000000 : ℝ)) (X := (12507113609356482889/12500000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8221786865599127/100000000000000000000 : ℝ) ≤ ((24194125410721807/24200000000000000 : ℝ)+2*(235493561739/187550000000000 : ℝ)*(11191/100000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (24194125410721807/24200000000000000 : ℝ)+2*(235493561739/187550000000000 : ℝ)*(11191/100000 : ℝ)=(5000191418343973/5000000000000000 : ℝ) by norm_num, show 1+2*(8221786865599127/100000000000000000000 : ℝ)=(50008221786865599127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7113609356482889/25000000000000000000 : ℝ)+(8221786865599127/100000000000000000000 : ℝ) ≤ ((24194125410721807/24200000000000000 : ℝ)+(235493561739/187550000000000 : ℝ)*((7471/50000 : ℝ)+(11191/100000 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (24194125410721807/24200000000000000 : ℝ)+(235493561739/187550000000000 : ℝ)*((7471/50000 : ℝ)+(11191/100000 : ℝ))=(312526681994107/312500000000000 : ℝ) by norm_num, show 1+(7113609356482889/25000000000000000000 : ℝ)+(8221786865599127/100000000000000000000 : ℝ)=(100036676224291530683/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7113609356482889/25000000000000000000 : ℝ) ≤ ((24194125410721807/24200000000000000 : ℝ)+2*(235493561739/187550000000000 : ℝ)*(7471/50000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (24194125410721807/24200000000000000 : ℝ)+2*(235493561739/187550000000000 : ℝ)*(7471/50000 : ℝ)=(5000662405467451/5000000000000000 : ℝ) by norm_num, show 1+2*(7113609356482889/25000000000000000000 : ℝ)=(12507113609356482889/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24194125410721807/24200000000000000 : ℝ)*(X 1 0+X 2 0)+(235493561739/187550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (7471/50000 : ℝ)) (c := (24194125410721807/24200000000000000 : ℝ)) (alpha := (235493561739/187550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24194125410721807/24200000000000000 : ℝ)*(X 0 1+X 2 1)+(235493561739/187550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (7471/50000 : ℝ)) (c := (24194125410721807/24200000000000000 : ℝ)) (alpha := (235493561739/187550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24194125410721807/24200000000000000 : ℝ)*(X 0 2+X 1 2)+(235493561739/187550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (7471/50000 : ℝ)) (c := (24194125410721807/24200000000000000 : ℝ)) (alpha := (235493561739/187550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-490724953/2500000000 : ℝ)*X 0 0+(5408985829/10000000000 : ℝ)*X 0 1+(1049187897/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668430863/1250000000 : ℝ)*X 1 0+(-2045925067/10000000000 : ℝ)*X 1 1+(5245939727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347447093/10000000000 : ℝ)*X 2 0+(655742457/1250000000 : ℝ)*X 2 1+(-1022962453/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301791649/10000000000 : ℝ)*X 0 0+(129001411/312500000 : ℝ)*X 0 1+(4482060993/10000000000 : ℝ)*X 0 2+(4301791649/10000000000 : ℝ)*X 1 0+(129001411/312500000 : ℝ)*X 1 1+(4482060993/10000000000 : ℝ)*X 1 2+(4301791649/10000000000 : ℝ)*X 2 0+(129001411/312500000 : ℝ)*X 2 1+(4482060993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-981455851/5000000000 : ℝ)*X 0 0+(5246537151/10000000000 : ℝ)*X 0 1+(216335397/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305018483/10000000000 : ℝ)*X 1 0+(-235434967/1250000000 : ℝ)*X 1 1+(5408384893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305018437/10000000000 : ℝ)*X 2 0+(270419247/500000000 : ℝ)*X 2 1+(-1883479733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075454307/2500000000 : ℝ)*X 0 0+(140023859/312500000 : ℝ)*X 0 1+(4129349433/10000000000 : ℝ)*X 0 2+(1075454307/2500000000 : ℝ)*X 1 0+(140023859/312500000 : ℝ)*X 1 1+(4129349433/10000000000 : ℝ)*X 1 2+(1075454307/2500000000 : ℝ)*X 2 0+(140023859/312500000 : ℝ)*X 2 1+(4129349433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72504008087625815457994257/9377500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201703891/20000000000000 : ℝ)*(base19) + (490852207/50000000000000 : ℝ)*(base23) + (65129143/50000000000000 : ℝ)*(lower2) + (77078923/100000000000000 : ℝ)*(upper3) + (1075593/781250000000 : ℝ)*(upper5) + (1119755135228593/25000000000000 : ℝ)*(major0) + (1119755135228593/25000000000000 : ℝ)*(major1) + (1119755135228593/25000000000000 : ℝ)*(major2) + (383328251310653/6250000000000 : ℝ)*(sp0) + (6133284919393811/100000000000000 : ℝ)*(sp1) + (6133284946208853/100000000000000 : ℝ)*(sp2) + (282474312064667/10000000000000 : ℝ)*(sp3) + (33906942819/100000000000000 : ℝ)*(sp4) + (1471943187/12500000000000 : ℝ)*(sp7) + (1412377448096083/50000000000000 : ℝ)*(f.failure) + (3066642963956633/50000000000000 : ℝ)*(f.sum) + (4555728074949/4688750000000000000000000000 : ℝ)*base65 + (167452524475267081/18755000000000000000000000000000 : ℝ)*base67 + (46480996454652919/18755000000000000000000000000000 : ℝ)*base70 + (99654491450952081/18755000000000000000000000000000 : ℝ)*base71 + (70568242076811/18755000000000000000000000000 : ℝ)*base73 + (148854452699137081/18755000000000000000000000000000 : ℝ)*base75 + (53330103283722919/18755000000000000000000000000000 : ℝ)*base78 + (16755639846482081/18755000000000000000000000000000 : ℝ)*base79 + (5935561294879/4688750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (40185969/5000000000000000000000 : ℝ)*base90 + (40185969/5000000000000000000000 : ℝ)*base92 + (40185969/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5468799820957995746218059/682000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255012627/20000000000000 : ℝ)*(base19) + (1360669133/100000000000000 : ℝ)*(base23) + (1522899/1000000000000 : ℝ)*(upper3) + (16300967/25000000000000 : ℝ)*(lower4) + (167495147/100000000000000 : ℝ)*(upper5) + (902428953764767/20000000000000 : ℝ)*(major0) + (902428953764767/20000000000000 : ℝ)*(major1) + (902428953764767/20000000000000 : ℝ)*(major2) + (12724243047/50000000000000 : ℝ)*(sp1) + (27482826159/100000000000000 : ℝ)*(sp2) + (6178644131728493/100000000000000 : ℝ)*(sp4) + (96540897002801/1562500000000 : ℝ)*(sp5) + (15446538220583/250000000000 : ℝ)*(sp6) + (2845645138626897/100000000000000 : ℝ)*(sp7) + (2845645138626897/100000000000000 : ℝ)*(f.failure) + (6178644131728493/100000000000000 : ℝ)*(f.sum) + (182035807167/42625000000000000000000000 : ℝ)*base65 + (12088231363993549/1364000000000000000000000000000 : ℝ)*base67 + (8038532759085549/1364000000000000000000000000000 : ℝ)*base69 + (7721534278693549/1364000000000000000000000000000 : ℝ)*base71 + (12976472973/5328125000000000000000000 : ℝ)*base73 + (17803480962425549/1364000000000000000000000000000 : ℝ)*base75 + (6657989789257549/1364000000000000000000000000000 : ℝ)*base77 + (28223634089589549/1364000000000000000000000000000 : ℝ)*base79 + (794003681761/341000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (66566171/10000000000000000000000 : ℝ)*base90 + (66566171/10000000000000000000000 : ℝ)*base92 + (66566171/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1439_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7471/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1439_s5_0 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-981513081/5000000000 : ℝ)*x 0 + (337991907/625000000 : ℝ)*x 1 + (41975771/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981513081/5000000000 : ℝ)^4399 ≤ (1497285566359/12500000000000 : ℝ)^3375 := by
    have hnat : (981513081 : ℕ)^4399*12500000000000^3375 ≤ 1497285566359^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981513081 5000000000 1497285566359 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337991907/625000000 : ℝ)^4399 ≤ (22438534321393/50000000000000 : ℝ)^3375 := by
    have hnat : (337991907 : ℕ)^4399*50000000000000^3375 ≤ 22438534321393^3375*625000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337991907 625000000 22438534321393 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41975771/80000000 : ℝ)^4399 ≤ (21572323407763/50000000000000 : ℝ)^3375 := by
    have hnat : (41975771 : ℕ)^4399*50000000000000^3375 ≤ 21572323407763^3375*80000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41975771 80000000 21572323407763 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981513081/5000000000 : ℝ), (337991907/625000000 : ℝ), (41975771/80000000 : ℝ)] ![(1497285566359/12500000000000 : ℝ), (22438534321393/50000000000000 : ℝ), (21572323407763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981513081/5000000000 : ℝ)|^4399 ≤ (1497285566359/12500000000000 : ℝ)^3375
        have hw : |(-981513081/5000000000 : ℝ)|=(981513081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337991907/625000000 : ℝ)|^4399 ≤ (22438534321393/50000000000000 : ℝ)^3375
        have hw : |(337991907/625000000 : ℝ)|=(337991907/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41975771/80000000 : ℝ)|^4399 ≤ (21572323407763/50000000000000 : ℝ)^3375
        have hw : |(41975771/80000000 : ℝ)|=(41975771/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s5_1 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673579173/5000000000 : ℝ)*x 0 + (-204493823/1000000000 : ℝ)*x 1 + (5246971483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673579173/5000000000 : ℝ)^4399 ≤ (11055377373899/25000000000000 : ℝ)^3375 := by
    have hnat : (2673579173 : ℕ)^4399*25000000000000^3375 ≤ 11055377373899^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673579173 5000000000 11055377373899 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (204493823/1000000000 : ℝ)^4399 ≤ (3158460628527/25000000000000 : ℝ)^3375 := by
    have hnat : (204493823 : ℕ)^4399*25000000000000^3375 ≤ 3158460628527^3375*1000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204493823 1000000000 3158460628527 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246971483/10000000000 : ℝ)^4399 ≤ (43144647973029/100000000000000 : ℝ)^3375 := by
    have hnat : (5246971483 : ℕ)^4399*100000000000000^3375 ≤ 43144647973029^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246971483 10000000000 43144647973029 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673579173/5000000000 : ℝ), (-204493823/1000000000 : ℝ), (5246971483/10000000000 : ℝ)] ![(11055377373899/25000000000000 : ℝ), (3158460628527/25000000000000 : ℝ), (43144647973029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673579173/5000000000 : ℝ)|^4399 ≤ (11055377373899/25000000000000 : ℝ)^3375
        have hw : |(2673579173/5000000000 : ℝ)|=(2673579173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-204493823/1000000000 : ℝ)|^4399 ≤ (3158460628527/25000000000000 : ℝ)^3375
        have hw : |(-204493823/1000000000 : ℝ)|=(204493823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246971483/10000000000 : ℝ)|^4399 ≤ (43144647973029/100000000000000 : ℝ)^3375
        have hw : |(5246971483/10000000000 : ℝ)|=(5246971483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s5_2 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069431667/2000000000 : ℝ)*x 0 + (1049394319/2000000000 : ℝ)*x 1 + (-127808631/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069431667/2000000000 : ℝ)^4399 ≤ (43185067751/97656250000 : ℝ)^3375 := by
    have hnat : (1069431667 : ℕ)^4399*97656250000^3375 ≤ 43185067751^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069431667 2000000000 43185067751 97656250000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049394319/2000000000 : ℝ)^4399 ≤ (43144649173403/100000000000000 : ℝ)^3375 := by
    have hnat : (1049394319 : ℕ)^4399*100000000000000^3375 ≤ 43144649173403^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049394319 2000000000 43144649173403 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127808631/625000000 : ℝ)^4399 ≤ (12633841435061/100000000000000 : ℝ)^3375 := by
    have hnat : (127808631 : ℕ)^4399*100000000000000^3375 ≤ 12633841435061^3375*625000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127808631 625000000 12633841435061 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069431667/2000000000 : ℝ), (1049394319/2000000000 : ℝ), (-127808631/625000000 : ℝ)] ![(43185067751/97656250000 : ℝ), (43144649173403/100000000000000 : ℝ), (12633841435061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069431667/2000000000 : ℝ)|^4399 ≤ (43185067751/97656250000 : ℝ)^3375
        have hw : |(1069431667/2000000000 : ℝ)|=(1069431667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049394319/2000000000 : ℝ)|^4399 ≤ (43144649173403/100000000000000 : ℝ)^3375
        have hw : |(1049394319/2000000000 : ℝ)|=(1049394319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127808631/625000000 : ℝ)|^4399 ≤ (12633841435061/100000000000000 : ℝ)^3375
        have hw : |(-127808631/625000000 : ℝ)|=(127808631/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s5_3 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075466899/2500000000 : ℝ)*x 0 + (4130367573/10000000000 : ℝ)*x 1 + (2239860223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075466899/2500000000 : ℝ)^4399 ≤ (33304726498399/100000000000000 : ℝ)^3375 := by
    have hnat : (1075466899 : ℕ)^4399*100000000000000^3375 ≤ 33304726498399^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075466899 2500000000 33304726498399 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130367573/10000000000 : ℝ)^4399 ≤ (31584705385791/100000000000000 : ℝ)^3375 := by
    have hnat : (4130367573 : ℕ)^4399*100000000000000^3375 ≤ 31584705385791^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130367573 10000000000 31584705385791 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2239860223/5000000000 : ℝ)^4399 ≤ (35110568109089/100000000000000 : ℝ)^3375 := by
    have hnat : (2239860223 : ℕ)^4399*100000000000000^3375 ≤ 35110568109089^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239860223 5000000000 35110568109089 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075466899/2500000000 : ℝ), (4130367573/10000000000 : ℝ), (2239860223/5000000000 : ℝ)] ![(33304726498399/100000000000000 : ℝ), (31584705385791/100000000000000 : ℝ), (35110568109089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075466899/2500000000 : ℝ)|^4399 ≤ (33304726498399/100000000000000 : ℝ)^3375
        have hw : |(1075466899/2500000000 : ℝ)|=(1075466899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130367573/10000000000 : ℝ)|^4399 ≤ (31584705385791/100000000000000 : ℝ)^3375
        have hw : |(4130367573/10000000000 : ℝ)|=(4130367573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2239860223/5000000000 : ℝ)|^4399 ≤ (35110568109089/100000000000000 : ℝ)^3375
        have hw : |(2239860223/5000000000 : ℝ)|=(2239860223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s5_4 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-392607483/2000000000 : ℝ)*x 0 + (655944207/1250000000 : ℝ)*x 1 + (5407285249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392607483/2000000000 : ℝ)^4399 ≤ (2395674805943/20000000000000 : ℝ)^3375 := by
    have hnat : (392607483 : ℕ)^4399*20000000000000^3375 ≤ 2395674805943^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392607483 2000000000 2395674805943 20000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655944207/1250000000 : ℝ)^4399 ≤ (10787721896961/25000000000000 : ℝ)^3375 := by
    have hnat : (655944207 : ℕ)^4399*25000000000000^3375 ≤ 10787721896961^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655944207 1250000000 10787721896961 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407285249/10000000000 : ℝ)^4399 ≤ (22435369185763/50000000000000 : ℝ)^3375 := by
    have hnat : (5407285249 : ℕ)^4399*50000000000000^3375 ≤ 22435369185763^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407285249 10000000000 22435369185763 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-392607483/2000000000 : ℝ), (655944207/1250000000 : ℝ), (5407285249/10000000000 : ℝ)] ![(2395674805943/20000000000000 : ℝ), (10787721896961/25000000000000 : ℝ), (22435369185763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-392607483/2000000000 : ℝ)|^4399 ≤ (2395674805943/20000000000000 : ℝ)^3375
        have hw : |(-392607483/2000000000 : ℝ)|=(392607483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655944207/1250000000 : ℝ)|^4399 ≤ (10787721896961/25000000000000 : ℝ)^3375
        have hw : |(655944207/1250000000 : ℝ)|=(655944207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407285249/10000000000 : ℝ)|^4399 ≤ (22435369185763/50000000000000 : ℝ)^3375
        have hw : |(5407285249/10000000000 : ℝ)|=(5407285249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s5_5 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305288221/10000000000 : ℝ)*x 0 + (-942312331/5000000000 : ℝ)*x 1 + (1081457053/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305288221/10000000000 : ℝ)^4399 ≤ (21885357909281/50000000000000 : ℝ)^3375 := by
    have hnat : (5305288221 : ℕ)^4399*50000000000000^3375 ≤ 21885357909281^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305288221 10000000000 21885357909281 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942312331/5000000000 : ℝ)^4399 ≤ (11358545623583/100000000000000 : ℝ)^3375 := by
    have hnat : (942312331 : ℕ)^4399*100000000000000^3375 ≤ 11358545623583^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942312331 5000000000 11358545623583 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081457053/2000000000 : ℝ)^4399 ≤ (44870738544581/100000000000000 : ℝ)^3375 := by
    have hnat : (1081457053 : ℕ)^4399*100000000000000^3375 ≤ 44870738544581^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081457053 2000000000 44870738544581 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305288221/10000000000 : ℝ), (-942312331/5000000000 : ℝ), (1081457053/2000000000 : ℝ)] ![(21885357909281/50000000000000 : ℝ), (11358545623583/100000000000000 : ℝ), (44870738544581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305288221/10000000000 : ℝ)|^4399 ≤ (21885357909281/50000000000000 : ℝ)^3375
        have hw : |(5305288221/10000000000 : ℝ)|=(5305288221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942312331/5000000000 : ℝ)|^4399 ≤ (11358545623583/100000000000000 : ℝ)^3375
        have hw : |(-942312331/5000000000 : ℝ)|=(942312331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081457053/2000000000 : ℝ)|^4399 ≤ (44870738544581/100000000000000 : ℝ)^3375
        have hw : |(1081457053/2000000000 : ℝ)|=(1081457053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s5_6 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663160999/1250000000 : ℝ)*x 0 + (2703642729/5000000000 : ℝ)*x 1 + (-1884624709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663160999/1250000000 : ℝ)^4399 ≤ (43770713355983/100000000000000 : ℝ)^3375 := by
    have hnat : (663160999 : ℕ)^4399*100000000000000^3375 ≤ 43770713355983^3375*1250000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663160999 1250000000 43770713355983 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703642729/5000000000 : ℝ)^4399 ≤ (5608842579007/12500000000000 : ℝ)^3375 := by
    have hnat : (2703642729 : ℕ)^4399*12500000000000^3375 ≤ 5608842579007^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703642729 5000000000 5608842579007 12500000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1884624709/10000000000 : ℝ)^4399 ≤ (2839636498199/25000000000000 : ℝ)^3375 := by
    have hnat : (1884624709 : ℕ)^4399*25000000000000^3375 ≤ 2839636498199^3375*10000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884624709 10000000000 2839636498199 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663160999/1250000000 : ℝ), (2703642729/5000000000 : ℝ), (-1884624709/10000000000 : ℝ)] ![(43770713355983/100000000000000 : ℝ), (5608842579007/12500000000000 : ℝ), (2839636498199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663160999/1250000000 : ℝ)|^4399 ≤ (43770713355983/100000000000000 : ℝ)^3375
        have hw : |(663160999/1250000000 : ℝ)|=(663160999/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703642729/5000000000 : ℝ)|^4399 ≤ (5608842579007/12500000000000 : ℝ)^3375
        have hw : |(2703642729/5000000000 : ℝ)|=(2703642729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1884624709/10000000000 : ℝ)|^4399 ≤ (2839636498199/25000000000000 : ℝ)^3375
        have hw : |(-1884624709/10000000000 : ℝ)|=(1884624709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1439_s5_7 (p : ℝ) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2150946141/5000000000 : ℝ)*x 0 + (895691399/2000000000 : ℝ)*x 1 + (1032909357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2150946141/5000000000 : ℝ)^4399 ≤ (16652487801033/50000000000000 : ℝ)^3375 := by
    have hnat : (2150946141 : ℕ)^4399*50000000000000^3375 ≤ 16652487801033^3375*5000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150946141 5000000000 16652487801033 50000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895691399/2000000000 : ℝ)^4399 ≤ (8774415413693/25000000000000 : ℝ)^3375 := by
    have hnat : (895691399 : ℕ)^4399*25000000000000^3375 ≤ 8774415413693^3375*2000000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895691399 2000000000 8774415413693 25000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032909357/2500000000 : ℝ)^4399 ≤ (31597362733177/100000000000000 : ℝ)^3375 := by
    have hnat : (1032909357 : ℕ)^4399*100000000000000^3375 ≤ 31597362733177^3375*2500000000^4399 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032909357 2500000000 31597362733177 100000000000000 4399 3375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4399/1024 : ℝ)) 4399 3375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2150946141/5000000000 : ℝ), (895691399/2000000000 : ℝ), (1032909357/2500000000 : ℝ)] ![(16652487801033/50000000000000 : ℝ), (8774415413693/25000000000000 : ℝ), (31597362733177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2150946141/5000000000 : ℝ)|^4399 ≤ (16652487801033/50000000000000 : ℝ)^3375
        have hw : |(2150946141/5000000000 : ℝ)|=(2150946141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895691399/2000000000 : ℝ)|^4399 ≤ (8774415413693/25000000000000 : ℝ)^3375
        have hw : |(895691399/2000000000 : ℝ)|=(895691399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1032909357/2500000000 : ℝ)|^4399 ≤ (31597362733177/100000000000000 : ℝ)^3375
        have hw : |(1032909357/2500000000 : ℝ)|=(1032909357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1439_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7383/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14789/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14789/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2267/20000 : ℝ) ^ (2199/512 : ℝ) ≤ (1085736239559321/12500000000000000000 : ℝ) := by
    have hpowers : (2267/20000 : ℝ)^2199 ≤ (1085736239559321/12500000000000000000 : ℝ)^512 := by
      have hnat : (2267 : ℕ)^2199*12500000000000000000^512 ≤ 1085736239559321^512*20000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2267 20000 1085736239559321 12500000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2267/20000 : ℝ)) (X := (1085736239559321/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14789/100000 : ℝ) ^ (2199/512 : ℝ) ≤ (27224006070966731/100000000000000000000 : ℝ) := by
    have hpowers : (14789/100000 : ℝ)^2199 ≤ (27224006070966731/100000000000000000000 : ℝ)^512 := by
      have hnat : (14789 : ℕ)^2199*100000000000000000000^512 ≤ 27224006070966731^512*100000^2199 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14789 100000 27224006070966731 100000000000000000000 2199 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14789/100000 : ℝ)) (X := (27224006070966731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251085736239559321/6250000000000000000 : ℝ) ≤ (10000404445596071/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (6251085736239559321/6250000000000000000 : ℝ)^512 ≤ (10000404445596071/10000000000000000 : ℝ)^2199 := by
      have hnat : (6251085736239559321 : ℕ)^512*10000000000000000^2199 ≤ 10000404445596071^2199*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251085736239559321 6250000000000000000 10000404445596071 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000404445596071/10000000000000000 : ℝ)) (X := (6251085736239559321/6250000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035909895987441299/100000000000000000000 : ℝ) ≤ (10000835986117811/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (100035909895987441299/100000000000000000000 : ℝ)^512 ≤ (10000835986117811/10000000000000000 : ℝ)^2199 := by
      have hnat : (100035909895987441299 : ℕ)^512*10000000000000000^2199 ≤ 10000835986117811^2199*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035909895987441299 100000000000000000000 10000835986117811 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000835986117811/10000000000000000 : ℝ)) (X := (100035909895987441299/100000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027224006070966731/50000000000000000000 : ℝ) ≤ (10001267526639551/10000000000000000 : ℝ) ^ (2199/512 : ℝ) := by
    have hpowers : (50027224006070966731/50000000000000000000 : ℝ)^512 ≤ (10001267526639551/10000000000000000 : ℝ)^2199 := by
      have hnat : (50027224006070966731 : ℕ)^512*10000000000000000^2199 ≤ 10001267526639551^2199*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027224006070966731 50000000000000000000 10001267526639551 10000000000000000 512 2199 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001267526639551/10000000000000000 : ℝ)) (X := (50027224006070966731/50000000000000000000 : ℝ)) (by norm_num) 2199 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1085736239559321/12500000000000000000 : ℝ) ≤ ((17265806965730491717/17270000000000000000 : ℝ)+2*(21577026087/17270000000000 : ℝ)*(2267/20000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (17265806965730491717/17270000000000000000 : ℝ)+2*(21577026087/17270000000000 : ℝ)*(2267/20000 : ℝ)=(10000404445596071/10000000000000000 : ℝ) by norm_num, show 1+2*(1085736239559321/12500000000000000000 : ℝ)=(6251085736239559321/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27224006070966731/100000000000000000000 : ℝ)+(1085736239559321/12500000000000000000 : ℝ) ≤ ((17265806965730491717/17270000000000000000 : ℝ)+(21577026087/17270000000000 : ℝ)*((14789/100000 : ℝ)+(2267/20000 : ℝ)))^(2199/512 : ℝ) := by
    rw [show (17265806965730491717/17270000000000000000 : ℝ)+(21577026087/17270000000000 : ℝ)*((14789/100000 : ℝ)+(2267/20000 : ℝ))=(10000835986117811/10000000000000000 : ℝ) by norm_num, show 1+(27224006070966731/100000000000000000000 : ℝ)+(1085736239559321/12500000000000000000 : ℝ)=(100035909895987441299/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27224006070966731/100000000000000000000 : ℝ) ≤ ((17265806965730491717/17270000000000000000 : ℝ)+2*(21577026087/17270000000000 : ℝ)*(14789/100000 : ℝ))^(2199/512 : ℝ) := by
    rw [show (17265806965730491717/17270000000000000000 : ℝ)+2*(21577026087/17270000000000 : ℝ)*(14789/100000 : ℝ)=(10001267526639551/10000000000000000 : ℝ) by norm_num, show 1+2*(27224006070966731/100000000000000000000 : ℝ)=(50027224006070966731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17265806965730491717/17270000000000000000 : ℝ)*(X 1 0+X 2 0)+(21577026087/17270000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (17265806965730491717/17270000000000000000 : ℝ)) (alpha := (21577026087/17270000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17265806965730491717/17270000000000000000 : ℝ)*(X 0 1+X 2 1)+(21577026087/17270000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (17265806965730491717/17270000000000000000 : ℝ)) (alpha := (21577026087/17270000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17265806965730491717/17270000000000000000 : ℝ)*(X 0 2+X 1 2)+(21577026087/17270000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2199/512 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (14789/100000 : ℝ)) (c := (17265806965730491717/17270000000000000000 : ℝ)) (alpha := (21577026087/17270000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-981513081/5000000000 : ℝ)*X 0 0+(337991907/625000000 : ℝ)*X 0 1+(41975771/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673579173/5000000000 : ℝ)*X 1 0+(-204493823/1000000000 : ℝ)*X 1 1+(5246971483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069431667/2000000000 : ℝ)*X 2 0+(1049394319/2000000000 : ℝ)*X 2 1+(-127808631/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1075466899/2500000000 : ℝ)*X 0 0+(4130367573/10000000000 : ℝ)*X 0 1+(2239860223/5000000000 : ℝ)*X 0 2+(1075466899/2500000000 : ℝ)*X 1 0+(4130367573/10000000000 : ℝ)*X 1 1+(2239860223/5000000000 : ℝ)*X 1 2+(1075466899/2500000000 : ℝ)*X 2 0+(4130367573/10000000000 : ℝ)*X 2 1+(2239860223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-392607483/2000000000 : ℝ)*X 0 0+(655944207/1250000000 : ℝ)*X 0 1+(5407285249/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305288221/10000000000 : ℝ)*X 1 0+(-942312331/5000000000 : ℝ)*X 1 1+(1081457053/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663160999/1250000000 : ℝ)*X 2 0+(2703642729/5000000000 : ℝ)*X 2 1+(-1884624709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2150946141/5000000000 : ℝ)*X 0 0+(895691399/2000000000 : ℝ)*X 0 1+(1032909357/2500000000 : ℝ)*X 0 2+(2150946141/5000000000 : ℝ)*X 1 0+(895691399/2000000000 : ℝ)*X 1 1+(1032909357/2500000000 : ℝ)*X 1 2+(2150946141/5000000000 : ℝ)*X 2 0+(895691399/2000000000 : ℝ)*X 2 1+(1032909357/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1439_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5606402913015838885653/863500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1535793009/100000000000000 : ℝ)*(base19) + (71861831/5000000000000 : ℝ)*(base23) + (32546939/50000000000000 : ℝ)*(upper3) + (22931493/50000000000000 : ℝ)*(upper4) + (86927979/50000000000000 : ℝ)*(upper5) + (226940555537439/5000000000000 : ℝ)*(major0) + (226940555537439/5000000000000 : ℝ)*(major1) + (226940555537439/5000000000000 : ℝ)*(major2) + (1243022743390947/20000000000000 : ℝ)*(sp0) + (12430315682759/200000000000 : ℝ)*(sp1) + (6215157939935889/100000000000000 : ℝ)*(sp2) + (2862449575703533/100000000000000 : ℝ)*(sp3) + (22830108887/50000000000000 : ℝ)*(sp4) + (6526099929/50000000000000 : ℝ)*(sp7) + (2862462627903391/100000000000000 : ℝ)*(f.failure) + (6215159377172509/100000000000000 : ℝ)*(f.sum) + (987582235829/215875000000000000000000000 : ℝ)*base65 + (25604971748741567/7850000000000000000000000000000 : ℝ)*base68 + (55785797737758433/7850000000000000000000000000000 : ℝ)*base69 + (65442299939408433/7850000000000000000000000000000 : ℝ)*base71 + (1584433296793/1727000000000000000000000000 : ℝ)*base74 + (42540711368108433/7850000000000000000000000000000 : ℝ)*base75 + (96689070908341567/7850000000000000000000000000000 : ℝ)*base78 + (73873969343091567/7850000000000000000000000000000 : ℝ)*base80 + (4928180301987/863500000000000000000000000 : ℝ)*base81 + (32034613/10000000000000000000000 : ℝ)*base90 + (32034613/10000000000000000000000 : ℝ)*base92 + (32034613/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2652682317628819922610622341/215875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1781623457/100000000000000 : ℝ)*(base19) + (822152807/50000000000000 : ℝ)*(base23) + (274482803/100000000000000 : ℝ)*(upper3) + (8039751/12500000000000 : ℝ)*(lower4) + (213135043/100000000000000 : ℝ)*(upper5) + (1142979981947897/25000000000000 : ℝ)*(major0) + (1142979981947897/25000000000000 : ℝ)*(major1) + (1142979981947897/25000000000000 : ℝ)*(major2) + (17271840703/50000000000000 : ℝ)*(sp1) + (36023366439/100000000000000 : ℝ)*(sp2) + (782562036839373/12500000000000 : ℝ)*(sp4) + (6260459969410121/100000000000000 : ℝ)*(sp5) + (1565114656760733/25000000000000 : ℝ)*(sp6) + (720835787816647/25000000000000 : ℝ)*(sp7) + (720835787816647/25000000000000 : ℝ)*(f.failure) + (782562036839373/12500000000000 : ℝ)*(f.sum) + (11213855721/8635000000000000000000000 : ℝ)*base66 + (470419648471266441/39250000000000000000000000000000 : ℝ)*base68 + (182150461524266441/39250000000000000000000000000000 : ℝ)*base70 + (698470330879516441/39250000000000000000000000000000 : ℝ)*base72 + (561215957447/863500000000000000000000000 : ℝ)*base74 + (319605576544016441/39250000000000000000000000000000 : ℝ)*base76 + (531610432265516441/39250000000000000000000000000000 : ℝ)*base78 + (301150159583516441/39250000000000000000000000000000 : ℝ)*base80 + (1611812218037/431750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14525421/2500000000000000000000 : ℝ)*base90 + (14525421/2500000000000000000000 : ℝ)*base92 + (14525421/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1439_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14789/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1439_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1439_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1439_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1439_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1439_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2199/512 : ℝ) ≤ p) (hpb : p ≤ (4399/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158563157/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15769/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (521/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1439_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
