-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1422_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:52:07.456753+00:00
-- url     : https://prove2.me/submissions/cff84f27-3709-427d-b588-f0d331c35c39

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
theorem support_rectangle_w1422_s3_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-987861453/5000000000 : ℝ)*x 0 + (169312239/312500000 : ℝ)*x 1 + (163689421/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987861453/5000000000 : ℝ)^2191 ≤ (12049314064273/100000000000000 : ℝ)^1679 := by
    have hnat : (987861453 : ℕ)^2191*100000000000000^1679 ≤ 12049314064273^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987861453 5000000000 12049314064273 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169312239/312500000 : ℝ)^2191 ≤ (44944244247103/100000000000000 : ℝ)^1679 := by
    have hnat : (169312239 : ℕ)^2191*100000000000000^1679 ≤ 44944244247103^1679*312500000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169312239 312500000 44944244247103 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163689421/312500000 : ℝ)^2191 ≤ (43006441669489/100000000000000 : ℝ)^1679 := by
    have hnat : (163689421 : ℕ)^2191*100000000000000^1679 ≤ 43006441669489^1679*312500000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163689421 312500000 43006441669489 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987861453/5000000000 : ℝ), (169312239/312500000 : ℝ), (163689421/312500000 : ℝ)] ![(12049314064273/100000000000000 : ℝ), (44944244247103/100000000000000 : ℝ), (43006441669489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987861453/5000000000 : ℝ)|^2191 ≤ (12049314064273/100000000000000 : ℝ)^1679
        have hw : |(-987861453/5000000000 : ℝ)|=(987861453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169312239/312500000 : ℝ)|^2191 ≤ (44944244247103/100000000000000 : ℝ)^1679
        have hw : |(169312239/312500000 : ℝ)|=(169312239/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163689421/312500000 : ℝ)|^2191 ≤ (43006441669489/100000000000000 : ℝ)^1679
        have hw : |(163689421/312500000 : ℝ)|=(163689421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s3_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349901417/10000000000 : ℝ)*x 0 + (-2067517189/10000000000 : ℝ)*x 1 + (1309515359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349901417/10000000000 : ℝ)^2191 ≤ (22104292400889/50000000000000 : ℝ)^1679 := by
    have hnat : (5349901417 : ℕ)^2191*50000000000000^1679 ≤ 22104292400889^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349901417 10000000000 22104292400889 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067517189/10000000000 : ℝ)^2191 ≤ (6392486953143/50000000000000 : ℝ)^1679 := by
    have hnat : (2067517189 : ℕ)^2191*50000000000000^1679 ≤ 6392486953143^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067517189 10000000000 6392486953143 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309515359/2500000000 : ℝ)^2191 ≤ (43006441283783/100000000000000 : ℝ)^1679 := by
    have hnat : (1309515359 : ℕ)^2191*100000000000000^1679 ≤ 43006441283783^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309515359 2500000000 43006441283783 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349901417/10000000000 : ℝ), (-2067517189/10000000000 : ℝ), (1309515359/2500000000 : ℝ)] ![(22104292400889/50000000000000 : ℝ), (6392486953143/50000000000000 : ℝ), (43006441283783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349901417/10000000000 : ℝ)|^2191 ≤ (22104292400889/50000000000000 : ℝ)^1679
        have hw : |(5349901417/10000000000 : ℝ)|=(5349901417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067517189/10000000000 : ℝ)|^2191 ≤ (6392486953143/50000000000000 : ℝ)^1679
        have hw : |(-2067517189/10000000000 : ℝ)|=(2067517189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309515359/2500000000 : ℝ)|^2191 ≤ (43006441283783/100000000000000 : ℝ)^1679
        have hw : |(1309515359/2500000000 : ℝ)|=(1309515359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s3_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (213996057/400000000 : ℝ)*x 0 + (5238061441/10000000000 : ℝ)*x 1 + (-2067517171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213996057/400000000 : ℝ)^2191 ≤ (11052146222011/25000000000000 : ℝ)^1679 := by
    have hnat : (213996057 : ℕ)^2191*25000000000000^1679 ≤ 11052146222011^1679*400000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213996057 400000000 11052146222011 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238061441/10000000000 : ℝ)^2191 ≤ (43006441337353/100000000000000 : ℝ)^1679 := by
    have hnat : (5238061441 : ℕ)^2191*100000000000000^1679 ≤ 43006441337353^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238061441 10000000000 43006441337353 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067517171/10000000000 : ℝ)^2191 ≤ (3196243440259/25000000000000 : ℝ)^1679 := by
    have hnat : (2067517171 : ℕ)^2191*25000000000000^1679 ≤ 3196243440259^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067517171 10000000000 3196243440259 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213996057/400000000 : ℝ), (5238061441/10000000000 : ℝ), (-2067517171/10000000000 : ℝ)] ![(11052146222011/25000000000000 : ℝ), (43006441337353/100000000000000 : ℝ), (3196243440259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213996057/400000000 : ℝ)|^2191 ≤ (11052146222011/25000000000000 : ℝ)^1679
        have hw : |(213996057/400000000 : ℝ)|=(213996057/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238061441/10000000000 : ℝ)|^2191 ≤ (43006441337353/100000000000000 : ℝ)^1679
        have hw : |(5238061441/10000000000 : ℝ)|=(5238061441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067517171/10000000000 : ℝ)|^2191 ≤ (3196243440259/25000000000000 : ℝ)^1679
        have hw : |(-2067517171/10000000000 : ℝ)|=(2067517171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s3_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (215272731/500000000 : ℝ)*x 0 + (4115276099/10000000000 : ℝ)*x 1 + (4503527039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215272731/500000000 : ℝ)^2191 ≤ (1331911948563/4000000000000 : ℝ)^1679 := by
    have hnat : (215272731 : ℕ)^2191*4000000000000^1679 ≤ 1331911948563^1679*500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215272731 500000000 1331911948563 4000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4115276099/10000000000 : ℝ)^2191 ≤ (31391530038757/100000000000000 : ℝ)^1679 := by
    have hnat : (4115276099 : ℕ)^2191*100000000000000^1679 ≤ 31391530038757^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4115276099 10000000000 31391530038757 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503527039/10000000000 : ℝ)^2191 ≤ (8827667807341/25000000000000 : ℝ)^1679 := by
    have hnat : (4503527039 : ℕ)^2191*25000000000000^1679 ≤ 8827667807341^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503527039 10000000000 8827667807341 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215272731/500000000 : ℝ), (4115276099/10000000000 : ℝ), (4503527039/10000000000 : ℝ)] ![(1331911948563/4000000000000 : ℝ), (31391530038757/100000000000000 : ℝ), (8827667807341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215272731/500000000 : ℝ)|^2191 ≤ (1331911948563/4000000000000 : ℝ)^1679
        have hw : |(215272731/500000000 : ℝ)|=(215272731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4115276099/10000000000 : ℝ)|^2191 ≤ (31391530038757/100000000000000 : ℝ)^1679
        have hw : |(4115276099/10000000000 : ℝ)|=(4115276099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503527039/10000000000 : ℝ)|^2191 ≤ (8827667807341/25000000000000 : ℝ)^1679
        have hw : |(4503527039/10000000000 : ℝ)|=(4503527039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s3_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-197573823/1000000000 : ℝ)*x 0 + (130969553/250000000 : ℝ)*x 1 + (338579193/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197573823/1000000000 : ℝ)^2191 ≤ (12049436019559/100000000000000 : ℝ)^1679 := by
    have hnat : (197573823 : ℕ)^2191*100000000000000^1679 ≤ 12049436019559^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197573823 1000000000 12049436019559 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130969553/250000000 : ℝ)^2191 ≤ (10753540726683/25000000000000 : ℝ)^1679 := by
    have hnat : (130969553 : ℕ)^2191*25000000000000^1679 ≤ 10753540726683^1679*250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130969553 250000000 10753540726683 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338579193/625000000 : ℝ)^2191 ≤ (1797456042143/4000000000000 : ℝ)^1679 := by
    have hnat : (338579193 : ℕ)^2191*4000000000000^1679 ≤ 1797456042143^1679*625000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338579193 625000000 1797456042143 4000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197573823/1000000000 : ℝ), (130969553/250000000 : ℝ), (338579193/625000000 : ℝ)] ![(12049436019559/100000000000000 : ℝ), (10753540726683/25000000000000 : ℝ), (1797456042143/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197573823/1000000000 : ℝ)|^2191 ≤ (12049436019559/100000000000000 : ℝ)^1679
        have hw : |(-197573823/1000000000 : ℝ)|=(197573823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130969553/250000000 : ℝ)|^2191 ≤ (10753540726683/25000000000000 : ℝ)^1679
        have hw : |(130969553/250000000 : ℝ)|=(130969553/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338579193/625000000 : ℝ)|^2191 ≤ (1797456042143/4000000000000 : ℝ)^1679
        have hw : |(338579193/625000000 : ℝ)|=(338579193/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s3_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33144733/62500000 : ℝ)*x 0 + (-188831163/1000000000 : ℝ)*x 1 + (5417267077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33144733/62500000 : ℝ)^2191 ≤ (43705200660597/100000000000000 : ℝ)^1679 := by
    have hnat : (33144733 : ℕ)^2191*100000000000000^1679 ≤ 43705200660597^1679*62500000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33144733 62500000 43705200660597 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188831163/1000000000 : ℝ)^2191 ≤ (11358398392141/100000000000000 : ℝ)^1679 := by
    have hnat : (188831163 : ℕ)^2191*100000000000000^1679 ≤ 11358398392141^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188831163 1000000000 11358398392141 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5417267077/10000000000 : ℝ)^2191 ≤ (8987280186901/20000000000000 : ℝ)^1679 := by
    have hnat : (5417267077 : ℕ)^2191*20000000000000^1679 ≤ 8987280186901^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417267077 10000000000 8987280186901 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33144733/62500000 : ℝ), (-188831163/1000000000 : ℝ), (5417267077/10000000000 : ℝ)] ![(43705200660597/100000000000000 : ℝ), (11358398392141/100000000000000 : ℝ), (8987280186901/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33144733/62500000 : ℝ)|^2191 ≤ (43705200660597/100000000000000 : ℝ)^1679
        have hw : |(33144733/62500000 : ℝ)|=(33144733/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188831163/1000000000 : ℝ)|^2191 ≤ (11358398392141/100000000000000 : ℝ)^1679
        have hw : |(-188831163/1000000000 : ℝ)|=(188831163/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5417267077/10000000000 : ℝ)|^2191 ≤ (8987280186901/20000000000000 : ℝ)^1679
        have hw : |(5417267077/10000000000 : ℝ)|=(5417267077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s3_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (662894631/1250000000 : ℝ)*x 0 + (2708633667/5000000000 : ℝ)*x 1 + (-1888311593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662894631/1250000000 : ℝ)^2191 ≤ (43705198165553/100000000000000 : ℝ)^1679 := by
    have hnat : (662894631 : ℕ)^2191*100000000000000^1679 ≤ 43705198165553^1679*1250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662894631 1250000000 43705198165553 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708633667/5000000000 : ℝ)^2191 ≤ (22468201858207/50000000000000 : ℝ)^1679 := by
    have hnat : (2708633667 : ℕ)^2191*50000000000000^1679 ≤ 22468201858207^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708633667 5000000000 22468201858207 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1888311593/10000000000 : ℝ)^2191 ≤ (5679199050857/50000000000000 : ℝ)^1679 := by
    have hnat : (1888311593 : ℕ)^2191*50000000000000^1679 ≤ 5679199050857^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888311593 10000000000 5679199050857 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662894631/1250000000 : ℝ), (2708633667/5000000000 : ℝ), (-1888311593/10000000000 : ℝ)] ![(43705198165553/100000000000000 : ℝ), (22468201858207/50000000000000 : ℝ), (5679199050857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662894631/1250000000 : ℝ)|^2191 ≤ (43705198165553/100000000000000 : ℝ)^1679
        have hw : |(662894631/1250000000 : ℝ)|=(662894631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708633667/5000000000 : ℝ)|^2191 ≤ (22468201858207/50000000000000 : ℝ)^1679
        have hw : |(2708633667/5000000000 : ℝ)|=(2708633667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1888311593/10000000000 : ℝ)|^2191 ≤ (5679199050857/50000000000000 : ℝ)^1679
        have hw : |(-1888311593/10000000000 : ℝ)|=(1888311593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s3_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1076372011/2500000000 : ℝ)*x 0 + (4501972517/10000000000 : ℝ)*x 1 + (4116839889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076372011/2500000000 : ℝ)^2191 ≤ (6659627207597/20000000000000 : ℝ)^1679 := by
    have hnat : (1076372011 : ℕ)^2191*20000000000000^1679 ≤ 6659627207597^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076372011 2500000000 6659627207597 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501972517/10000000000 : ℝ)^2191 ≤ (17647383385319/50000000000000 : ℝ)^1679 := by
    have hnat : (4501972517 : ℕ)^2191*50000000000000^1679 ≤ 17647383385319^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501972517 10000000000 17647383385319 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4116839889/10000000000 : ℝ)^2191 ≤ (31407097176873/100000000000000 : ℝ)^1679 := by
    have hnat : (4116839889 : ℕ)^2191*100000000000000^1679 ≤ 31407097176873^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4116839889 10000000000 31407097176873 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076372011/2500000000 : ℝ), (4501972517/10000000000 : ℝ), (4116839889/10000000000 : ℝ)] ![(6659627207597/20000000000000 : ℝ), (17647383385319/50000000000000 : ℝ), (31407097176873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076372011/2500000000 : ℝ)|^2191 ≤ (6659627207597/20000000000000 : ℝ)^1679
        have hw : |(1076372011/2500000000 : ℝ)|=(1076372011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501972517/10000000000 : ℝ)|^2191 ≤ (17647383385319/50000000000000 : ℝ)^1679
        have hw : |(4501972517/10000000000 : ℝ)|=(4501972517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4116839889/10000000000 : ℝ)|^2191 ≤ (31407097176873/100000000000000 : ℝ)^1679
        have hw : |(4116839889/10000000000 : ℝ)|=(4116839889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1033/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (557/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (299/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1033/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15821/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1033/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1033/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15821/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1033/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1033/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15821/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1033/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1033/10000 : ℝ) ^ (4381/1024 : ℝ) ≤ (1513370932421997/25000000000000000000 : ℝ) := by
    have hpowers : (1033/10000 : ℝ)^4381 ≤ (1513370932421997/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1033 : ℕ)^4381*25000000000000000000^1024 ≤ 1513370932421997^1024*10000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1033 10000 1513370932421997 25000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1033/10000 : ℝ)) (X := (1513370932421997/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15821/100000 : ℝ) ^ (4381/1024 : ℝ) ≤ (7500604310071013/20000000000000000000 : ℝ) := by
    have hpowers : (15821/100000 : ℝ)^4381 ≤ (7500604310071013/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15821 : ℕ)^4381*20000000000000000000^1024 ≤ 7500604310071013^1024*100000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15821 100000 7500604310071013 20000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15821/100000 : ℝ)) (X := (7500604310071013/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501513370932421997/12500000000000000000 : ℝ) ≤ (250007074275081/250000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (12501513370932421997/12500000000000000000 : ℝ)^1024 ≤ (250007074275081/250000000000000 : ℝ)^4381 := by
      have hnat : (12501513370932421997 : ℕ)^1024*250000000000000^4381 ≤ 250007074275081^4381*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501513370932421997 12500000000000000000 250007074275081 250000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250007074275081/250000000000000 : ℝ)) (X := (12501513370932421997/12500000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100043556505280043053/100000000000000000000 : ℝ) ≤ (10001017905049319/10000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (100043556505280043053/100000000000000000000 : ℝ)^1024 ≤ (10001017905049319/10000000000000000 : ℝ)^4381 := by
      have hnat : (100043556505280043053 : ℕ)^1024*10000000000000000^4381 ≤ 10001017905049319^4381*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100043556505280043053 100000000000000000000 10001017905049319 10000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001017905049319/10000000000000000 : ℝ)) (X := (100043556505280043053/100000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007500604310071013/10000000000000000000 : ℝ) ≤ (5000876419547699/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (10007500604310071013/10000000000000000000 : ℝ)^1024 ≤ (5000876419547699/5000000000000000 : ℝ)^4381 := by
      have hnat : (10007500604310071013 : ℕ)^1024*5000000000000000^4381 ≤ 5000876419547699^4381*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007500604310071013 10000000000000000000 5000876419547699 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000876419547699/5000000000000000 : ℝ)) (X := (10007500604310071013/10000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1513370932421997/25000000000000000000 : ℝ) ≤ ((548963700563867987/549100000000000000 : ℝ)+2*(734934046079/549100000000000 : ℝ)*(1033/10000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (548963700563867987/549100000000000000 : ℝ)+2*(734934046079/549100000000000 : ℝ)*(1033/10000 : ℝ)=(250007074275081/250000000000000 : ℝ) by norm_num, show 1+2*(1513370932421997/25000000000000000000 : ℝ)=(12501513370932421997/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7500604310071013/20000000000000000000 : ℝ)+(1513370932421997/25000000000000000000 : ℝ) ≤ ((548963700563867987/549100000000000000 : ℝ)+(734934046079/549100000000000 : ℝ)*((15821/100000 : ℝ)+(1033/10000 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (548963700563867987/549100000000000000 : ℝ)+(734934046079/549100000000000 : ℝ)*((15821/100000 : ℝ)+(1033/10000 : ℝ))=(10001017905049319/10000000000000000 : ℝ) by norm_num, show 1+(7500604310071013/20000000000000000000 : ℝ)+(1513370932421997/25000000000000000000 : ℝ)=(100043556505280043053/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7500604310071013/20000000000000000000 : ℝ) ≤ ((548963700563867987/549100000000000000 : ℝ)+2*(734934046079/549100000000000 : ℝ)*(15821/100000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (548963700563867987/549100000000000000 : ℝ)+2*(734934046079/549100000000000 : ℝ)*(15821/100000 : ℝ)=(5000876419547699/5000000000000000 : ℝ) by norm_num, show 1+2*(7500604310071013/20000000000000000000 : ℝ)=(10007500604310071013/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (548963700563867987/549100000000000000 : ℝ)*(X 1 0+X 2 0)+(734934046079/549100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (1033/10000 : ℝ)) (hi := (15821/100000 : ℝ)) (c := (548963700563867987/549100000000000000 : ℝ)) (alpha := (734934046079/549100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (548963700563867987/549100000000000000 : ℝ)*(X 0 1+X 2 1)+(734934046079/549100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (1033/10000 : ℝ)) (hi := (15821/100000 : ℝ)) (c := (548963700563867987/549100000000000000 : ℝ)) (alpha := (734934046079/549100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (548963700563867987/549100000000000000 : ℝ)*(X 0 2+X 1 2)+(734934046079/549100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (1033/10000 : ℝ)) (hi := (15821/100000 : ℝ)) (c := (548963700563867987/549100000000000000 : ℝ)) (alpha := (734934046079/549100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-987861453/5000000000 : ℝ)*X 0 0+(169312239/312500000 : ℝ)*X 0 1+(163689421/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349901417/10000000000 : ℝ)*X 1 0+(-2067517189/10000000000 : ℝ)*X 1 1+(1309515359/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213996057/400000000 : ℝ)*X 2 0+(5238061441/10000000000 : ℝ)*X 2 1+(-2067517171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215272731/500000000 : ℝ)*X 0 0+(4115276099/10000000000 : ℝ)*X 0 1+(4503527039/10000000000 : ℝ)*X 0 2+(215272731/500000000 : ℝ)*X 1 0+(4115276099/10000000000 : ℝ)*X 1 1+(4503527039/10000000000 : ℝ)*X 1 2+(215272731/500000000 : ℝ)*X 2 0+(4115276099/10000000000 : ℝ)*X 2 1+(4503527039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-197573823/1000000000 : ℝ)*X 0 0+(130969553/250000000 : ℝ)*X 0 1+(338579193/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((33144733/62500000 : ℝ)*X 1 0+(-188831163/1000000000 : ℝ)*X 1 1+(5417267077/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((662894631/1250000000 : ℝ)*X 2 0+(2708633667/5000000000 : ℝ)*X 2 1+(-1888311593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1076372011/2500000000 : ℝ)*X 0 0+(4501972517/10000000000 : ℝ)*X 0 1+(4116839889/10000000000 : ℝ)*X 0 2+(1076372011/2500000000 : ℝ)*X 1 0+(4501972517/10000000000 : ℝ)*X 1 1+(4116839889/10000000000 : ℝ)*X 1 2+(1076372011/2500000000 : ℝ)*X 2 0+(4501972517/10000000000 : ℝ)*X 2 1+(4116839889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52372563482372695147347063/6863750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1446266803/100000000000000 : ℝ)*(base19) + (1418984699/100000000000000 : ℝ)*(base23) + (50184437/25000000000000 : ℝ)*(upper3) + (9520933/50000000000000 : ℝ)*(upper4) + (197367873/100000000000000 : ℝ)*(upper5) + (2033360082045117/50000000000000 : ℝ)*(major0) + (2033360082045117/50000000000000 : ℝ)*(major1) + (2033360082045117/50000000000000 : ℝ)*(major2) + (27788684882139/500000000000 : ℝ)*(sp0) + (694720205381503/12500000000000 : ℝ)*(sp1) + (347360104395883/6250000000000 : ℝ)*(sp2) + (51513304678701/2000000000000 : ℝ)*(sp3) + (26112891027/100000000000000 : ℝ)*(sp4) + (11750582801/100000000000000 : ℝ)*(sp7) + (643919246129463/25000000000000 : ℝ)*(f.failure) + (5557763089318827/100000000000000 : ℝ)*(f.sum) + (7045922868373/3431875000000000000000000000 : ℝ)*base66 + (496829105546527479/27455000000000000000000000000000 : ℝ)*base67 + (20859774684612521/27455000000000000000000000000000 : ℝ)*base70 + (408869365593552479/27455000000000000000000000000000 : ℝ)*base71 + (91337873218881/27455000000000000000000000000 : ℝ)*base73 + (259488570642347479/27455000000000000000000000000000 : ℝ)*base75 + (403075965461192479/27455000000000000000000000000000 : ℝ)*base77 + (430055613132887479/27455000000000000000000000000000 : ℝ)*base79 + (168788494823219/27455000000000000000000000000 : ℝ)*base82 + (150831/250000000000000000000 : ℝ)*base89 + (150831/250000000000000000000 : ℝ)*base91 + (150831/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43081711086052940617851/6863750000000000000000000000 : ℝ) := by norm_num
    linear_combination (234672009/100000000000000 : ℝ)*(base19) + (33512053/25000000000000 : ℝ)*(base23) + (37730609/100000000000000 : ℝ)*(upper3) + (64456331/100000000000000 : ℝ)*(lower4) + (9337439/25000000000000 : ℝ)*(upper5) + (256225531516063/6250000000000 : ℝ)*(major0) + (256225531516063/6250000000000 : ℝ)*(major1) + (256225531516063/6250000000000 : ℝ)*(major2) + (355180363/10000000000000 : ℝ)*(sp1) + (6154056293/100000000000000 : ℝ)*(sp2) + (5602709824655783/100000000000000 : ℝ)*(sp4) + (350169127386259/6250000000000 : ℝ)*(sp5) + (5602703536551277/100000000000000 : ℝ)*(sp6) + (64912674365871/2500000000000 : ℝ)*(sp7) + (64912674365871/2500000000000 : ℝ)*(f.failure) + (5602709824655783/100000000000000 : ℝ)*(f.sum) + (8038742172891/13727500000000000000000000000 : ℝ)*base65 + (21041059449697819/3431875000000000000000000000000 : ℝ)*base68 + (4652176161062819/3431875000000000000000000000000 : ℝ)*base70 + (26638485268895931/3431875000000000000000000000000 : ℝ)*base71 + (6246816668159/13727500000000000000000000000 : ℝ)*base74 + (4066976341922181/3431875000000000000000000000000 : ℝ)*base75 + (3907183980671097/1715937500000000000000000000000 : ℝ)*base78 + (2564595655300389/857968750000000000000000000000 : ℝ)*base79 + (3862860248613/6863750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (169127/25000000000000000000 : ℝ)*base89 + (169127/25000000000000000000 : ℝ)*base91 + (169127/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1422_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1033/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (299/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1422_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1422_s4_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976660547/10000000000 : ℝ)*x 0 + (5410024469/10000000000 : ℝ)*x 1 + (5245411221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976660547/10000000000 : ℝ)^2191 ≤ (12056776764237/100000000000000 : ℝ)^1679 := by
    have hnat : (1976660547 : ℕ)^2191*100000000000000^1679 ≤ 12056776764237^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976660547 10000000000 12056776764237 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410024469/10000000000 : ℝ)^2191 ≤ (22429009485921/50000000000000 : ℝ)^1679 := by
    have hnat : (5410024469 : ℕ)^2191*50000000000000^1679 ≤ 22429009485921^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410024469 10000000000 22429009485921 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245411221/10000000000 : ℝ)^2191 ≤ (1346412633069/3125000000000 : ℝ)^1679 := by
    have hnat : (5245411221 : ℕ)^2191*3125000000000^1679 ≤ 1346412633069^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245411221 10000000000 1346412633069 3125000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976660547/10000000000 : ℝ), (5410024469/10000000000 : ℝ), (5245411221/10000000000 : ℝ)] ![(12056776764237/100000000000000 : ℝ), (22429009485921/50000000000000 : ℝ), (1346412633069/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976660547/10000000000 : ℝ)|^2191 ≤ (12056776764237/100000000000000 : ℝ)^1679
        have hw : |(-1976660547/10000000000 : ℝ)|=(1976660547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410024469/10000000000 : ℝ)|^2191 ≤ (22429009485921/50000000000000 : ℝ)^1679
        have hw : |(5410024469/10000000000 : ℝ)|=(5410024469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245411221/10000000000 : ℝ)|^2191 ≤ (1346412633069/3125000000000 : ℝ)^1679
        have hw : |(5245411221/10000000000 : ℝ)|=(5245411221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s4_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336961633/2500000000 : ℝ)*x 0 + (-1030249221/5000000000 : ℝ)*x 1 + (5245411417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336961633/2500000000 : ℝ)^2191 ≤ (1767457104639/4000000000000 : ℝ)^1679 := by
    have hnat : (1336961633 : ℕ)^2191*4000000000000^1679 ≤ 1767457104639^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336961633 2500000000 1767457104639 4000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030249221/5000000000 : ℝ)^2191 ≤ (6364183008783/50000000000000 : ℝ)^1679 := by
    have hnat : (1030249221 : ℕ)^2191*50000000000000^1679 ≤ 6364183008783^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030249221 5000000000 6364183008783 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245411417/10000000000 : ℝ)^2191 ≤ (5385650794883/12500000000000 : ℝ)^1679 := by
    have hnat : (5245411417 : ℕ)^2191*12500000000000^1679 ≤ 5385650794883^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245411417 10000000000 5385650794883 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336961633/2500000000 : ℝ), (-1030249221/5000000000 : ℝ), (5245411417/10000000000 : ℝ)] ![(1767457104639/4000000000000 : ℝ), (6364183008783/50000000000000 : ℝ), (5385650794883/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336961633/2500000000 : ℝ)|^2191 ≤ (1767457104639/4000000000000 : ℝ)^1679
        have hw : |(1336961633/2500000000 : ℝ)|=(1336961633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1030249221/5000000000 : ℝ)|^2191 ≤ (6364183008783/50000000000000 : ℝ)^1679
        have hw : |(-1030249221/5000000000 : ℝ)|=(1030249221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245411417/10000000000 : ℝ)|^2191 ≤ (5385650794883/12500000000000 : ℝ)^1679
        have hw : |(5245411417/10000000000 : ℝ)|=(5245411417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s4_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347846537/10000000000 : ℝ)*x 0 + (5245411463/10000000000 : ℝ)*x 1 + (-1030249187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347846537/10000000000 : ℝ)^2191 ≤ (8837285533977/20000000000000 : ℝ)^1679 := by
    have hnat : (5347846537 : ℕ)^2191*20000000000000^1679 ≤ 8837285533977^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347846537 10000000000 8837285533977 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245411463/10000000000 : ℝ)^2191 ≤ (43085206852123/100000000000000 : ℝ)^1679 := by
    have hnat : (5245411463 : ℕ)^2191*100000000000000^1679 ≤ 43085206852123^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245411463 10000000000 43085206852123 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030249187/5000000000 : ℝ)^2191 ≤ (6364182734707/50000000000000 : ℝ)^1679 := by
    have hnat : (1030249187 : ℕ)^2191*50000000000000^1679 ≤ 6364182734707^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030249187 5000000000 6364182734707 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347846537/10000000000 : ℝ), (5245411463/10000000000 : ℝ), (-1030249187/5000000000 : ℝ)] ![(8837285533977/20000000000000 : ℝ), (43085206852123/100000000000000 : ℝ), (6364182734707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347846537/10000000000 : ℝ)|^2191 ≤ (8837285533977/20000000000000 : ℝ)^1679
        have hw : |(5347846537/10000000000 : ℝ)|=(5347846537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245411463/10000000000 : ℝ)|^2191 ≤ (43085206852123/100000000000000 : ℝ)^1679
        have hw : |(5245411463/10000000000 : ℝ)|=(5245411463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1030249187/5000000000 : ℝ)|^2191 ≤ (6364182734707/50000000000000 : ℝ)^1679
        have hw : |(-1030249187/5000000000 : ℝ)|=(1030249187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s4_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2153014009/5000000000 : ℝ)*x 0 + (4131732247/10000000000 : ℝ)*x 1 + (2243466231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153014009/5000000000 : ℝ)^2191 ≤ (33303585710063/100000000000000 : ℝ)^1679 := by
    have hnat : (2153014009 : ℕ)^2191*100000000000000^1679 ≤ 33303585710063^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153014009 5000000000 33303585710063 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4131732247/10000000000 : ℝ)^2191 ≤ (31555437165531/100000000000000 : ℝ)^1679 := by
    have hnat : (4131732247 : ℕ)^2191*100000000000000^1679 ≤ 31555437165531^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131732247 10000000000 31555437165531 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243466231/5000000000 : ℝ)^2191 ≤ (702819542211/2000000000000 : ℝ)^1679 := by
    have hnat : (2243466231 : ℕ)^2191*2000000000000^1679 ≤ 702819542211^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243466231 5000000000 702819542211 2000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153014009/5000000000 : ℝ), (4131732247/10000000000 : ℝ), (2243466231/5000000000 : ℝ)] ![(33303585710063/100000000000000 : ℝ), (31555437165531/100000000000000 : ℝ), (702819542211/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153014009/5000000000 : ℝ)|^2191 ≤ (33303585710063/100000000000000 : ℝ)^1679
        have hw : |(2153014009/5000000000 : ℝ)|=(2153014009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4131732247/10000000000 : ℝ)|^2191 ≤ (31555437165531/100000000000000 : ℝ)^1679
        have hw : |(4131732247/10000000000 : ℝ)|=(4131732247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243466231/5000000000 : ℝ)|^2191 ≤ (702819542211/2000000000000 : ℝ)^1679
        have hw : |(2243466231/5000000000 : ℝ)|=(2243466231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s4_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976672561/10000000000 : ℝ)*x 0 + (131150369/250000000 : ℝ)*x 1 + (5409417731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976672561/10000000000 : ℝ)^2191 ≤ (753554524429/6250000000000 : ℝ)^1679 := by
    have hnat : (1976672561 : ℕ)^2191*6250000000000^1679 ≤ 753554524429^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976672561 10000000000 753554524429 6250000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131150369/250000000 : ℝ)^2191 ≤ (43091673498077/100000000000000 : ℝ)^1679 := by
    have hnat : (131150369 : ℕ)^2191*100000000000000^1679 ≤ 43091673498077^1679*250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131150369 250000000 43091673498077 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409417731/10000000000 : ℝ)^2191 ≤ (11212863524777/25000000000000 : ℝ)^1679 := by
    have hnat : (5409417731 : ℕ)^2191*25000000000000^1679 ≤ 11212863524777^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409417731 10000000000 11212863524777 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976672561/10000000000 : ℝ), (131150369/250000000 : ℝ), (5409417731/10000000000 : ℝ)] ![(753554524429/6250000000000 : ℝ), (43091673498077/100000000000000 : ℝ), (11212863524777/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976672561/10000000000 : ℝ)|^2191 ≤ (753554524429/6250000000000 : ℝ)^1679
        have hw : |(-1976672561/10000000000 : ℝ)|=(1976672561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131150369/250000000 : ℝ)|^2191 ≤ (43091673498077/100000000000000 : ℝ)^1679
        have hw : |(131150369/250000000 : ℝ)|=(131150369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409417731/10000000000 : ℝ)|^2191 ≤ (11212863524777/25000000000000 : ℝ)^1679
        have hw : |(5409417731/10000000000 : ℝ)|=(5409417731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s4_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305081351/10000000000 : ℝ)*x 0 + (-118530749/625000000 : ℝ)*x 1 + (676177219/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305081351/10000000000 : ℝ)^2191 ≤ (43725894230023/100000000000000 : ℝ)^1679 := by
    have hnat : (5305081351 : ℕ)^2191*100000000000000^1679 ≤ 43725894230023^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305081351 10000000000 43725894230023 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118530749/625000000 : ℝ)^2191 ≤ (2855662858329/25000000000000 : ℝ)^1679 := by
    have hnat : (118530749 : ℕ)^2191*25000000000000^1679 ≤ 2855662858329^1679*625000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118530749 625000000 2855662858329 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676177219/1250000000 : ℝ)^2191 ≤ (44851454326323/100000000000000 : ℝ)^1679 := by
    have hnat : (676177219 : ℕ)^2191*100000000000000^1679 ≤ 44851454326323^1679*1250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676177219 1250000000 44851454326323 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305081351/10000000000 : ℝ), (-118530749/625000000 : ℝ), (676177219/1250000000 : ℝ)] ![(43725894230023/100000000000000 : ℝ), (2855662858329/25000000000000 : ℝ), (44851454326323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305081351/10000000000 : ℝ)|^2191 ≤ (43725894230023/100000000000000 : ℝ)^1679
        have hw : |(5305081351/10000000000 : ℝ)|=(5305081351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-118530749/625000000 : ℝ)|^2191 ≤ (2855662858329/25000000000000 : ℝ)^1679
        have hw : |(-118530749/625000000 : ℝ)|=(118530749/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676177219/1250000000 : ℝ)|^2191 ≤ (44851454326323/100000000000000 : ℝ)^1679
        have hw : |(676177219/1250000000 : ℝ)|=(676177219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s4_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652540681/5000000000 : ℝ)*x 0 + (676177219/1250000000 : ℝ)*x 1 + (-29632687/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652540681/5000000000 : ℝ)^2191 ≤ (2732868396771/6250000000000 : ℝ)^1679 := by
    have hnat : (2652540681 : ℕ)^2191*6250000000000^1679 ≤ 2732868396771^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652540681 5000000000 2732868396771 6250000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676177219/1250000000 : ℝ)^2191 ≤ (44851454326323/100000000000000 : ℝ)^1679 := by
    have hnat : (676177219 : ℕ)^2191*100000000000000^1679 ≤ 44851454326323^1679*1250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676177219 1250000000 44851454326323 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29632687/156250000 : ℝ)^2191 ≤ (11422651307561/100000000000000 : ℝ)^1679 := by
    have hnat : (29632687 : ℕ)^2191*100000000000000^1679 ≤ 11422651307561^1679*156250000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29632687 156250000 11422651307561 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652540681/5000000000 : ℝ), (676177219/1250000000 : ℝ), (-29632687/156250000 : ℝ)] ![(2732868396771/6250000000000 : ℝ), (44851454326323/100000000000000 : ℝ), (11422651307561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652540681/5000000000 : ℝ)|^2191 ≤ (2732868396771/6250000000000 : ℝ)^1679
        have hw : |(2652540681/5000000000 : ℝ)|=(2652540681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676177219/1250000000 : ℝ)|^2191 ≤ (44851454326323/100000000000000 : ℝ)^1679
        have hw : |(676177219/1250000000 : ℝ)|=(676177219/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29632687/156250000 : ℝ)|^2191 ≤ (11422651307561/100000000000000 : ℝ)^1679
        have hw : |(-29632687/156250000 : ℝ)|=(29632687/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s4_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2153026977/5000000000 : ℝ)*x 0 + (4485630197/10000000000 : ℝ)*x 1 + (4133041291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2153026977/5000000000 : ℝ)^2191 ≤ (33303847473643/100000000000000 : ℝ)^1679 := by
    have hnat : (2153026977 : ℕ)^2191*100000000000000^1679 ≤ 33303847473643^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153026977 5000000000 33303847473643 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485630197/10000000000 : ℝ)^2191 ≤ (274434909339/781250000000 : ℝ)^1679 := by
    have hnat : (4485630197 : ℕ)^2191*781250000000^1679 ≤ 274434909339^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485630197 10000000000 274434909339 781250000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4133041291/10000000000 : ℝ)^2191 ≤ (31568484113633/100000000000000 : ℝ)^1679 := by
    have hnat : (4133041291 : ℕ)^2191*100000000000000^1679 ≤ 31568484113633^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4133041291 10000000000 31568484113633 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2153026977/5000000000 : ℝ), (4485630197/10000000000 : ℝ), (4133041291/10000000000 : ℝ)] ![(33303847473643/100000000000000 : ℝ), (274434909339/781250000000 : ℝ), (31568484113633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2153026977/5000000000 : ℝ)|^2191 ≤ (33303847473643/100000000000000 : ℝ)^1679
        have hw : |(2153026977/5000000000 : ℝ)|=(2153026977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485630197/10000000000 : ℝ)|^2191 ≤ (274434909339/781250000000 : ℝ)^1679
        have hw : |(4485630197/10000000000 : ℝ)|=(4485630197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4133041291/10000000000 : ℝ)|^2191 ≤ (31568484113633/100000000000000 : ℝ)^1679
        have hw : |(4133041291/10000000000 : ℝ)|=(4133041291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (299/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11297/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (462/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (299/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (557/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (299/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (557/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (299/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (557/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (299/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (557/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (299/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (557/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (299/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (557/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (557/5000 : ℝ) ^ (4381/1024 : ℝ) ≤ (104515226198849/1250000000000000000 : ℝ) := by
    have hpowers : (557/5000 : ℝ)^4381 ≤ (104515226198849/1250000000000000000 : ℝ)^1024 := by
      have hnat : (557 : ℕ)^4381*1250000000000000000^1024 ≤ 104515226198849^1024*5000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        557 5000 104515226198849 1250000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (557/5000 : ℝ)) (X := (104515226198849/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (299/2000 : ℝ) ^ (4381/1024 : ℝ) ≤ (29434092438671921/100000000000000000000 : ℝ) := by
    have hpowers : (299/2000 : ℝ)^4381 ≤ (29434092438671921/100000000000000000000 : ℝ)^1024 := by
      have hnat : (299 : ℕ)^4381*100000000000000000000^1024 ≤ 29434092438671921^1024*2000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        299 2000 29434092438671921 100000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (299/2000 : ℝ)) (X := (29434092438671921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (625104515226198849/625000000000000000 : ℝ) ≤ (250009770987027/250000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (625104515226198849/625000000000000000 : ℝ)^1024 ≤ (250009770987027/250000000000000 : ℝ)^4381 := by
      have hnat : (625104515226198849 : ℕ)^1024*250000000000000^4381 ≤ 250009770987027^4381*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625104515226198849 625000000000000000 250009770987027 250000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250009770987027/250000000000000 : ℝ)) (X := (625104515226198849/625000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037795310534579841/100000000000000000000 : ℝ) ≤ (1250110410850553/1250000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (100037795310534579841/100000000000000000000 : ℝ)^1024 ≤ (1250110410850553/1250000000000000 : ℝ)^4381 := by
      have hnat : (100037795310534579841 : ℕ)^1024*1250000000000000^4381 ≤ 1250110410850553^4381*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037795310534579841 100000000000000000000 1250110410850553 1250000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250110410850553/1250000000000000 : ℝ)) (X := (100037795310534579841/100000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029434092438671921/50000000000000000000 : ℝ) ≤ (1250171966765971/1250000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (50029434092438671921/50000000000000000000 : ℝ)^1024 ≤ (1250171966765971/1250000000000000 : ℝ)^4381 := by
      have hnat : (50029434092438671921 : ℕ)^1024*1250000000000000^4381 ≤ 1250171966765971^4381*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029434092438671921 50000000000000000000 1250171966765971 1250000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250171966765971/1250000000000000 : ℝ)) (X := (50029434092438671921/50000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(104515226198849/1250000000000000000 : ℝ) ≤ ((476131467150735131/476250000000000000 : ℝ)+2*(30777957709/23812500000000 : ℝ)*(557/5000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (476131467150735131/476250000000000000 : ℝ)+2*(30777957709/23812500000000 : ℝ)*(557/5000 : ℝ)=(250009770987027/250000000000000 : ℝ) by norm_num, show 1+2*(104515226198849/1250000000000000000 : ℝ)=(625104515226198849/625000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29434092438671921/100000000000000000000 : ℝ)+(104515226198849/1250000000000000000 : ℝ) ≤ ((476131467150735131/476250000000000000 : ℝ)+(30777957709/23812500000000 : ℝ)*((299/2000 : ℝ)+(557/5000 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (476131467150735131/476250000000000000 : ℝ)+(30777957709/23812500000000 : ℝ)*((299/2000 : ℝ)+(557/5000 : ℝ))=(1250110410850553/1250000000000000 : ℝ) by norm_num, show 1+(29434092438671921/100000000000000000000 : ℝ)+(104515226198849/1250000000000000000 : ℝ)=(100037795310534579841/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29434092438671921/100000000000000000000 : ℝ) ≤ ((476131467150735131/476250000000000000 : ℝ)+2*(30777957709/23812500000000 : ℝ)*(299/2000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (476131467150735131/476250000000000000 : ℝ)+2*(30777957709/23812500000000 : ℝ)*(299/2000 : ℝ)=(1250171966765971/1250000000000000 : ℝ) by norm_num, show 1+2*(29434092438671921/100000000000000000000 : ℝ)=(50029434092438671921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (476131467150735131/476250000000000000 : ℝ)*(X 1 0+X 2 0)+(30777957709/23812500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (476131467150735131/476250000000000000 : ℝ)) (alpha := (30777957709/23812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (476131467150735131/476250000000000000 : ℝ)*(X 0 1+X 2 1)+(30777957709/23812500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (476131467150735131/476250000000000000 : ℝ)) (alpha := (30777957709/23812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (476131467150735131/476250000000000000 : ℝ)*(X 0 2+X 1 2)+(30777957709/23812500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (299/2000 : ℝ)) (c := (476131467150735131/476250000000000000 : ℝ)) (alpha := (30777957709/23812500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1976660547/10000000000 : ℝ)*X 0 0+(5410024469/10000000000 : ℝ)*X 0 1+(5245411221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336961633/2500000000 : ℝ)*X 1 0+(-1030249221/5000000000 : ℝ)*X 1 1+(5245411417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347846537/10000000000 : ℝ)*X 2 0+(5245411463/10000000000 : ℝ)*X 2 1+(-1030249187/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2153014009/5000000000 : ℝ)*X 0 0+(4131732247/10000000000 : ℝ)*X 0 1+(2243466231/5000000000 : ℝ)*X 0 2+(2153014009/5000000000 : ℝ)*X 1 0+(4131732247/10000000000 : ℝ)*X 1 1+(2243466231/5000000000 : ℝ)*X 1 2+(2153014009/5000000000 : ℝ)*X 2 0+(4131732247/10000000000 : ℝ)*X 2 1+(2243466231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1976672561/10000000000 : ℝ)*X 0 0+(131150369/250000000 : ℝ)*X 0 1+(5409417731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305081351/10000000000 : ℝ)*X 1 0+(-118530749/625000000 : ℝ)*X 1 1+(676177219/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652540681/5000000000 : ℝ)*X 2 0+(676177219/1250000000 : ℝ)*X 2 1+(-29632687/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2153026977/5000000000 : ℝ)*X 0 0+(4485630197/10000000000 : ℝ)*X 0 1+(4133041291/10000000000 : ℝ)*X 0 2+(2153026977/5000000000 : ℝ)*X 1 0+(4485630197/10000000000 : ℝ)*X 1 1+(4133041291/10000000000 : ℝ)*X 1 2+(2153026977/5000000000 : ℝ)*X 2 0+(4485630197/10000000000 : ℝ)*X 2 1+(4133041291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64174995997721668227022599/7937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1074812013/100000000000000 : ℝ)*(base19) + (984203157/100000000000000 : ℝ)*(base23) + (51493677/100000000000000 : ℝ)*(lower2) + (27218111/20000000000000 : ℝ)*(upper3) + (3033147/2000000000000 : ℝ)*(upper5) + (4445121454964829/100000000000000 : ℝ)*(major0) + (4445121454964829/100000000000000 : ℝ)*(major1) + (4445121454964829/100000000000000 : ℝ)*(major2) + (30374366188767/500000000000 : ℝ)*(sp0) + (1518725571022443/25000000000000 : ℝ)*(sp1) + (6074902374698629/100000000000000 : ℝ)*(sp2) + (1407663149548659/50000000000000 : ℝ)*(sp3) + (15060574193/50000000000000 : ℝ)*(sp4) + (12982429253/100000000000000 : ℝ)*(sp7) + (2815339281526571/100000000000000 : ℝ)*(f.failure) + (3037451679450893/50000000000000 : ℝ)*(f.sum) + (3088732069951/793750000000000000000000000 : ℝ)*base66 + (38571205696982467/15875000000000000000000000000000 : ℝ)*base68 + (73910031355232467/15875000000000000000000000000000 : ℝ)*base70 + (69417617520392533/15875000000000000000000000000000 : ℝ)*base71 + (3270635497829/3175000000000000000000000000 : ℝ)*base74 + (153291275913482467/15875000000000000000000000000000 : ℝ)*base76 + (13070462800017533/15875000000000000000000000000000 : ℝ)*base77 + (197842894185607467/15875000000000000000000000000000 : ℝ)*base80 + (6503722239421/3175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3345027/1000000000000000000000 : ℝ)*base89 + (3345027/1000000000000000000000 : ℝ)*base91 + (3345027/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41639612442126899266969/3875732421875000000000000000 : ℝ) := by norm_num
    linear_combination (882144009/50000000000000 : ℝ)*(base19) + (1944077473/100000000000000 : ℝ)*(base23) + (44344203/20000000000000 : ℝ)*(upper3) + (36250673/50000000000000 : ℝ)*(lower4) + (107627211/50000000000000 : ℝ)*(upper5) + (1119500280987271/25000000000000 : ℝ)*(major0) + (1119500280987271/25000000000000 : ℝ)*(major1) + (1119500280987271/25000000000000 : ℝ)*(major2) + (2290466293/6250000000000 : ℝ)*(sp1) + (40423108409/100000000000000 : ℝ)*(sp2) + (6119838110067677/100000000000000 : ℝ)*(sp4) + (6119799698318971/100000000000000 : ℝ)*(sp5) + (1223959148576359/20000000000000 : ℝ)*(sp6) + (2836163779707959/100000000000000 : ℝ)*(sp7) + (2836163779707959/100000000000000 : ℝ)*(f.failure) + (6119838110067677/100000000000000 : ℝ)*(f.sum) + (57639523764277/9525000000000000000000000000 : ℝ)*base66 + (42922080915671249/11906250000000000000000000000000 : ℝ)*base68 + (223284689054827499/11906250000000000000000000000000 : ℝ)*base70 + (166728189030671249/11906250000000000000000000000000 : ℝ)*base72 + (16308268325873/9525000000000000000000000000 : ℝ)*base73 + (123342045416733749/11906250000000000000000000000000 : ℝ)*base76 + (31486173820233749/11906250000000000000000000000000 : ℝ)*base78 + (43279324220264999/11906250000000000000000000000000 : ℝ)*base80 + (52580571988627/9525000000000000000000000000 : ℝ)*base82 + (3049583/1000000000000000000000 : ℝ)*base89 + (3049583/1000000000000000000000 : ℝ)*base91 + (3049583/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1422_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (299/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (462/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1422_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1422_s5_0 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-79072037/400000000 : ℝ)*x 0 + (676096901/1250000000 : ℝ)*x 1 + (262328399/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79072037/400000000 : ℝ)^2191 ≤ (6028947063971/50000000000000 : ℝ)^1679 := by
    have hnat : (79072037 : ℕ)^2191*50000000000000^1679 ≤ 6028947063971^1679*400000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79072037 400000000 6028947063971 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676096901/1250000000 : ℝ)^2191 ≤ (22422251139689/50000000000000 : ℝ)^1679 := by
    have hnat : (676096901 : ℕ)^2191*50000000000000^1679 ≤ 22422251139689^1679*1250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676096901 1250000000 22422251139689 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262328399/500000000 : ℝ)^2191 ≤ (21548801787923/50000000000000 : ℝ)^1679 := by
    have hnat : (262328399 : ℕ)^2191*50000000000000^1679 ≤ 21548801787923^1679*500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262328399 500000000 21548801787923 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79072037/400000000 : ℝ), (676096901/1250000000 : ℝ), (262328399/500000000 : ℝ)] ![(6028947063971/50000000000000 : ℝ), (22422251139689/50000000000000 : ℝ), (21548801787923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79072037/400000000 : ℝ)|^2191 ≤ (6028947063971/50000000000000 : ℝ)^1679
        have hw : |(-79072037/400000000 : ℝ)|=(79072037/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676096901/1250000000 : ℝ)|^2191 ≤ (22422251139689/50000000000000 : ℝ)^1679
        have hw : |(676096901/1250000000 : ℝ)|=(676096901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262328399/500000000 : ℝ)|^2191 ≤ (21548801787923/50000000000000 : ℝ)^1679
        have hw : |(262328399/500000000 : ℝ)|=(262328399/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s5_1 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069504677/2000000000 : ℝ)*x 0 + (-51484731/250000000 : ℝ)*x 1 + (104931411/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069504677/2000000000 : ℝ)^2191 ≤ (8836588691719/20000000000000 : ℝ)^1679 := by
    have hnat : (1069504677 : ℕ)^2191*20000000000000^1679 ≤ 8836588691719^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069504677 2000000000 8836588691719 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51484731/250000000 : ℝ)^2191 ≤ (6359712704941/50000000000000 : ℝ)^1679 := by
    have hnat : (51484731 : ℕ)^2191*50000000000000^1679 ≤ 6359712704941^1679*250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51484731 250000000 6359712704941 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104931411/200000000 : ℝ)^2191 ≤ (10774407781161/25000000000000 : ℝ)^1679 := by
    have hnat : (104931411 : ℕ)^2191*25000000000000^1679 ≤ 10774407781161^1679*200000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104931411 200000000 10774407781161 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069504677/2000000000 : ℝ), (-51484731/250000000 : ℝ), (104931411/200000000 : ℝ)] ![(8836588691719/20000000000000 : ℝ), (6359712704941/50000000000000 : ℝ), (10774407781161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069504677/2000000000 : ℝ)|^2191 ≤ (8836588691719/20000000000000 : ℝ)^1679
        have hw : |(1069504677/2000000000 : ℝ)|=(1069504677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51484731/250000000 : ℝ)|^2191 ≤ (6359712704941/50000000000000 : ℝ)^1679
        have hw : |(-51484731/250000000 : ℝ)|=(51484731/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104931411/200000000 : ℝ)|^2191 ≤ (10774407781161/25000000000000 : ℝ)^1679
        have hw : |(104931411/200000000 : ℝ)|=(104931411/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s5_2 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5347523771/10000000000 : ℝ)*x 0 + (5246568947/10000000000 : ℝ)*x 1 + (-411878171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347523771/10000000000 : ℝ)^2191 ≤ (5522868452549/12500000000000 : ℝ)^1679 := by
    have hnat : (5347523771 : ℕ)^2191*12500000000000^1679 ≤ 5522868452549^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347523771 10000000000 5522868452549 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246568947/10000000000 : ℝ)^2191 ≤ (43097613941483/100000000000000 : ℝ)^1679 := by
    have hnat : (5246568947 : ℕ)^2191*100000000000000^1679 ≤ 43097613941483^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246568947 10000000000 43097613941483 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (411878171/2000000000 : ℝ)^2191 ≤ (2543887685271/20000000000000 : ℝ)^1679 := by
    have hnat : (411878171 : ℕ)^2191*20000000000000^1679 ≤ 2543887685271^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411878171 2000000000 2543887685271 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347523771/10000000000 : ℝ), (5246568947/10000000000 : ℝ), (-411878171/2000000000 : ℝ)] ![(5522868452549/12500000000000 : ℝ), (43097613941483/100000000000000 : ℝ), (2543887685271/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347523771/10000000000 : ℝ)|^2191 ≤ (5522868452549/12500000000000 : ℝ)^1679
        have hw : |(5347523771/10000000000 : ℝ)|=(5347523771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246568947/10000000000 : ℝ)|^2191 ≤ (43097613941483/100000000000000 : ℝ)^1679
        have hw : |(5246568947/10000000000 : ℝ)|=(5246568947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-411878171/2000000000 : ℝ)|^2191 ≤ (2543887685271/20000000000000 : ℝ)^1679
        have hw : |(-411878171/2000000000 : ℝ)|=(411878171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s5_3 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4306113741/10000000000 : ℝ)*x 0 + (4134320929/10000000000 : ℝ)*x 1 + (896864589/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306113741/10000000000 : ℝ)^2191 ≤ (6660890177229/20000000000000 : ℝ)^1679 := by
    have hnat : (4306113741 : ℕ)^2191*20000000000000^1679 ≤ 6660890177229^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306113741 10000000000 6660890177229 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134320929/10000000000 : ℝ)^2191 ≤ (6316247839353/20000000000000 : ℝ)^1679 := by
    have hnat : (4134320929 : ℕ)^2191*20000000000000^1679 ≤ 6316247839353^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134320929 10000000000 6316247839353 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896864589/2000000000 : ℝ)^2191 ≤ (35114309899711/100000000000000 : ℝ)^1679 := by
    have hnat : (896864589 : ℕ)^2191*100000000000000^1679 ≤ 35114309899711^1679*2000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896864589 2000000000 35114309899711 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306113741/10000000000 : ℝ), (4134320929/10000000000 : ℝ), (896864589/2000000000 : ℝ)] ![(6660890177229/20000000000000 : ℝ), (6316247839353/20000000000000 : ℝ), (35114309899711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306113741/10000000000 : ℝ)|^2191 ≤ (6660890177229/20000000000000 : ℝ)^1679
        have hw : |(4306113741/10000000000 : ℝ)|=(4306113741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4134320929/10000000000 : ℝ)|^2191 ≤ (6316247839353/20000000000000 : ℝ)^1679
        have hw : |(4134320929/10000000000 : ℝ)|=(4134320929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896864589/2000000000 : ℝ)|^2191 ≤ (35114309899711/100000000000000 : ℝ)^1679
        have hw : |(896864589/2000000000 : ℝ)|=(896864589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s5_4 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-61775381/312500000 : ℝ)*x 0 + (5247155319/10000000000 : ℝ)*x 1 + (5408184989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61775381/312500000 : ℝ)^2191 ≤ (6028991905343/50000000000000 : ℝ)^1679 := by
    have hnat : (61775381 : ℕ)^2191*50000000000000^1679 ≤ 6028991905343^1679*312500000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61775381 312500000 6028991905343 50000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247155319/10000000000 : ℝ)^2191 ≤ (8620779918161/20000000000000 : ℝ)^1679 := by
    have hnat : (5247155319 : ℕ)^2191*20000000000000^1679 ≤ 8620779918161^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247155319 10000000000 8620779918161 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408184989/10000000000 : ℝ)^2191 ≤ (11209529147029/25000000000000 : ℝ)^1679 := by
    have hnat : (5408184989 : ℕ)^2191*25000000000000^1679 ≤ 11209529147029^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408184989 10000000000 11209529147029 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61775381/312500000 : ℝ), (5247155319/10000000000 : ℝ), (5408184989/10000000000 : ℝ)] ![(6028991905343/50000000000000 : ℝ), (8620779918161/20000000000000 : ℝ), (11209529147029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61775381/312500000 : ℝ)|^2191 ≤ (6028991905343/50000000000000 : ℝ)^1679
        have hw : |(-61775381/312500000 : ℝ)|=(61775381/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247155319/10000000000 : ℝ)|^2191 ≤ (8620779918161/20000000000000 : ℝ)^1679
        have hw : |(5247155319/10000000000 : ℝ)|=(5247155319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408184989/10000000000 : ℝ)|^2191 ≤ (11209529147029/25000000000000 : ℝ)^1679
        have hw : |(5408184989/10000000000 : ℝ)|=(5408184989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s5_5 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (132634607/250000000 : ℝ)*x 0 + (-75910971/400000000 : ℝ)*x 1 + (5408184989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132634607/250000000 : ℝ)^2191 ≤ (43729152469233/100000000000000 : ℝ)^1679 := by
    have hnat : (132634607 : ℕ)^2191*100000000000000^1679 ≤ 43729152469233^1679*250000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132634607 250000000 43729152469233 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75910971/400000000 : ℝ)^2191 ≤ (285818273311/2500000000000 : ℝ)^1679 := by
    have hnat : (75910971 : ℕ)^2191*2500000000000^1679 ≤ 285818273311^1679*400000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75910971 400000000 285818273311 2500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408184989/10000000000 : ℝ)^2191 ≤ (11209529147029/25000000000000 : ℝ)^1679 := by
    have hnat : (5408184989 : ℕ)^2191*25000000000000^1679 ≤ 11209529147029^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408184989 10000000000 11209529147029 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132634607/250000000 : ℝ), (-75910971/400000000 : ℝ), (5408184989/10000000000 : ℝ)] ![(43729152469233/100000000000000 : ℝ), (285818273311/2500000000000 : ℝ), (11209529147029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132634607/250000000 : ℝ)|^2191 ≤ (43729152469233/100000000000000 : ℝ)^1679
        have hw : |(132634607/250000000 : ℝ)|=(132634607/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75910971/400000000 : ℝ)|^2191 ≤ (285818273311/2500000000000 : ℝ)^1679
        have hw : |(-75910971/400000000 : ℝ)|=(75910971/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408184989/10000000000 : ℝ)|^2191 ≤ (11209529147029/25000000000000 : ℝ)^1679
        have hw : |(5408184989/10000000000 : ℝ)|=(5408184989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s5_6 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305384279/10000000000 : ℝ)*x 0 + (540818499/1000000000 : ℝ)*x 1 + (-948887137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305384279/10000000000 : ℝ)^2191 ≤ (43729152458477/100000000000000 : ℝ)^1679 := by
    have hnat : (5305384279 : ℕ)^2191*100000000000000^1679 ≤ 43729152458477^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305384279 10000000000 43729152458477 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540818499/1000000000 : ℝ)^2191 ≤ (8967623319787/20000000000000 : ℝ)^1679 := by
    have hnat : (540818499 : ℕ)^2191*20000000000000^1679 ≤ 8967623319787^1679*1000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540818499 1000000000 8967623319787 20000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948887137/5000000000 : ℝ)^2191 ≤ (11432730924579/100000000000000 : ℝ)^1679 := by
    have hnat : (948887137 : ℕ)^2191*100000000000000^1679 ≤ 11432730924579^1679*5000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948887137 5000000000 11432730924579 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305384279/10000000000 : ℝ), (540818499/1000000000 : ℝ), (-948887137/5000000000 : ℝ)] ![(43729152458477/100000000000000 : ℝ), (8967623319787/20000000000000 : ℝ), (11432730924579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305384279/10000000000 : ℝ)|^2191 ≤ (43729152458477/100000000000000 : ℝ)^1679
        have hw : |(5305384279/10000000000 : ℝ)|=(5305384279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540818499/1000000000 : ℝ)|^2191 ≤ (8967623319787/20000000000000 : ℝ)^1679
        have hw : |(540818499/1000000000 : ℝ)|=(540818499/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948887137/5000000000 : ℝ)|^2191 ≤ (11432730924579/100000000000000 : ℝ)^1679
        have hw : |(-948887137/5000000000 : ℝ)|=(948887137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1422_s5_7 (p : ℝ) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4306138383/10000000000 : ℝ)*x 0 + (1120764789/2500000000 : ℝ)*x 1 + (4135591363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4306138383/10000000000 : ℝ)^2191 ≤ (4163087448913/12500000000000 : ℝ)^1679 := by
    have hnat : (4306138383 : ℕ)^2191*12500000000000^1679 ≤ 4163087448913^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4306138383 10000000000 4163087448913 12500000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120764789/2500000000 : ℝ)^2191 ≤ (8775349167733/25000000000000 : ℝ)^1679 := by
    have hnat : (1120764789 : ℕ)^2191*25000000000000^1679 ≤ 8775349167733^1679*2500000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120764789 2500000000 8775349167733 25000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4135591363/10000000000 : ℝ)^2191 ≤ (31593903727917/100000000000000 : ℝ)^1679 := by
    have hnat : (4135591363 : ℕ)^2191*100000000000000^1679 ≤ 31593903727917^1679*10000000000^2191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135591363 10000000000 31593903727917 100000000000000 2191 1679 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2191/512 : ℝ)) 2191 1679 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4306138383/10000000000 : ℝ), (1120764789/2500000000 : ℝ), (4135591363/10000000000 : ℝ)] ![(4163087448913/12500000000000 : ℝ), (8775349167733/25000000000000 : ℝ), (31593903727917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4306138383/10000000000 : ℝ)|^2191 ≤ (4163087448913/12500000000000 : ℝ)^1679
        have hw : |(4306138383/10000000000 : ℝ)|=(4306138383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120764789/2500000000 : ℝ)|^2191 ≤ (8775349167733/25000000000000 : ℝ)^1679
        have hw : |(1120764789/2500000000 : ℝ)|=(1120764789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4135591363/10000000000 : ℝ)|^2191 ≤ (31593903727917/100000000000000 : ℝ)^1679
        have hw : |(4135591363/10000000000 : ℝ)|=(4135591363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1422_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (462/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (462/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (462/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11297/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (462/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (462/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11297/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (462/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (462/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11297/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11297/100000 : ℝ) ^ (4381/1024 : ℝ) ≤ (2219284222974329/25000000000000000000 : ℝ) := by
    have hpowers : (11297/100000 : ℝ)^4381 ≤ (2219284222974329/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11297 : ℕ)^4381*25000000000000000000^1024 ≤ 2219284222974329^1024*100000^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11297 100000 2219284222974329 25000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11297/100000 : ℝ)) (X := (2219284222974329/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (462/3125 : ℝ) ^ (4381/1024 : ℝ) ≤ (28061058726599211/100000000000000000000 : ℝ) := by
    have hpowers : (462/3125 : ℝ)^4381 ≤ (28061058726599211/100000000000000000000 : ℝ)^1024 := by
      have hnat : (462 : ℕ)^4381*100000000000000000000^1024 ≤ 28061058726599211^1024*3125^4381 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        462 3125 28061058726599211 100000000000000000000 4381 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (462/3125 : ℝ)) (X := (28061058726599211/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502219284222974329/12500000000000000000 : ℝ) ≤ (2500103738528953/2500000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (12502219284222974329/12500000000000000000 : ℝ)^1024 ≤ (2500103738528953/2500000000000000 : ℝ)^4381 := by
      have hnat : (12502219284222974329 : ℕ)^1024*2500000000000000^4381 ≤ 2500103738528953^4381*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502219284222974329 12500000000000000000 2500103738528953 2500000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500103738528953/2500000000000000 : ℝ)) (X := (12502219284222974329/12500000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036938195618496527/100000000000000000000 : ℝ) ≤ (10000863258627039/10000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (100036938195618496527/100000000000000000000 : ℝ)^1024 ≤ (10000863258627039/10000000000000000 : ℝ)^4381 := by
      have hnat : (100036938195618496527 : ℕ)^1024*10000000000000000^4381 ≤ 10000863258627039^4381*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036938195618496527 100000000000000000000 10000863258627039 10000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000863258627039/10000000000000000 : ℝ)) (X := (100036938195618496527/100000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028061058726599211/50000000000000000000 : ℝ) ≤ (5000655781569133/5000000000000000 : ℝ) ^ (4381/1024 : ℝ) := by
    have hpowers : (50028061058726599211/50000000000000000000 : ℝ)^1024 ≤ (5000655781569133/5000000000000000 : ℝ)^4381 := by
      have hnat : (50028061058726599211 : ℕ)^1024*5000000000000000^4381 ≤ 5000655781569133^4381*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028061058726599211 50000000000000000000 5000655781569133 5000000000000000 1024 4381 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000655781569133/5000000000000000 : ℝ)) (X := (50028061058726599211/50000000000000000000 : ℝ)) (by norm_num) 4381 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2219284222974329/25000000000000000000 : ℝ) ≤ ((1584605361494326073/1585000000000000000 : ℝ)+2*(448304511227/348700000000000 : ℝ)*(11297/100000 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (1584605361494326073/1585000000000000000 : ℝ)+2*(448304511227/348700000000000 : ℝ)*(11297/100000 : ℝ)=(2500103738528953/2500000000000000 : ℝ) by norm_num, show 1+2*(2219284222974329/25000000000000000000 : ℝ)=(12502219284222974329/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28061058726599211/100000000000000000000 : ℝ)+(2219284222974329/25000000000000000000 : ℝ) ≤ ((1584605361494326073/1585000000000000000 : ℝ)+(448304511227/348700000000000 : ℝ)*((462/3125 : ℝ)+(11297/100000 : ℝ)))^(4381/1024 : ℝ) := by
    rw [show (1584605361494326073/1585000000000000000 : ℝ)+(448304511227/348700000000000 : ℝ)*((462/3125 : ℝ)+(11297/100000 : ℝ))=(10000863258627039/10000000000000000 : ℝ) by norm_num, show 1+(28061058726599211/100000000000000000000 : ℝ)+(2219284222974329/25000000000000000000 : ℝ)=(100036938195618496527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28061058726599211/100000000000000000000 : ℝ) ≤ ((1584605361494326073/1585000000000000000 : ℝ)+2*(448304511227/348700000000000 : ℝ)*(462/3125 : ℝ))^(4381/1024 : ℝ) := by
    rw [show (1584605361494326073/1585000000000000000 : ℝ)+2*(448304511227/348700000000000 : ℝ)*(462/3125 : ℝ)=(5000655781569133/5000000000000000 : ℝ) by norm_num, show 1+2*(28061058726599211/100000000000000000000 : ℝ)=(50028061058726599211/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1584605361494326073/1585000000000000000 : ℝ)*(X 1 0+X 2 0)+(448304511227/348700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (1584605361494326073/1585000000000000000 : ℝ)) (alpha := (448304511227/348700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1584605361494326073/1585000000000000000 : ℝ)*(X 0 1+X 2 1)+(448304511227/348700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (1584605361494326073/1585000000000000000 : ℝ)) (alpha := (448304511227/348700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1584605361494326073/1585000000000000000 : ℝ)*(X 0 2+X 1 2)+(448304511227/348700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4381/1024 : ℝ)) (lo := (11297/100000 : ℝ)) (hi := (462/3125 : ℝ)) (c := (1584605361494326073/1585000000000000000 : ℝ)) (alpha := (448304511227/348700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-79072037/400000000 : ℝ)*X 0 0+(676096901/1250000000 : ℝ)*X 0 1+(262328399/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069504677/2000000000 : ℝ)*X 1 0+(-51484731/250000000 : ℝ)*X 1 1+(104931411/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347523771/10000000000 : ℝ)*X 2 0+(5246568947/10000000000 : ℝ)*X 2 1+(-411878171/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4306113741/10000000000 : ℝ)*X 0 0+(4134320929/10000000000 : ℝ)*X 0 1+(896864589/2000000000 : ℝ)*X 0 2+(4306113741/10000000000 : ℝ)*X 1 0+(4134320929/10000000000 : ℝ)*X 1 1+(896864589/2000000000 : ℝ)*X 1 2+(4306113741/10000000000 : ℝ)*X 2 0+(4134320929/10000000000 : ℝ)*X 2 1+(896864589/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61775381/312500000 : ℝ)*X 0 0+(5247155319/10000000000 : ℝ)*X 0 1+(5408184989/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132634607/250000000 : ℝ)*X 1 0+(-75910971/400000000 : ℝ)*X 1 1+(5408184989/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305384279/10000000000 : ℝ)*X 2 0+(540818499/1000000000 : ℝ)*X 2 1+(-948887137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4306138383/10000000000 : ℝ)*X 0 0+(1120764789/2500000000 : ℝ)*X 0 1+(4135591363/10000000000 : ℝ)*X 0 2+(4306138383/10000000000 : ℝ)*X 1 0+(1120764789/2500000000 : ℝ)*X 1 1+(4135591363/10000000000 : ℝ)*X 1 2+(4306138383/10000000000 : ℝ)*X 2 0+(1120764789/2500000000 : ℝ)*X 2 1+(4135591363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1422_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83142443037305033403306963/13621093750000000000000000000000 : ℝ) := by norm_num
    linear_combination (33823863/25000000000000 : ℝ)*(base19) + (155658979/50000000000000 : ℝ)*(base23) + (6840131/12500000000000 : ℝ)*(upper2) + (204770597/50000000000000 : ℝ)*(upper3) + (563892066859747/12500000000000 : ℝ)*(major0) + (563892066859747/12500000000000 : ℝ)*(major1) + (563892066859747/12500000000000 : ℝ)*(major2) + (6165045937463243/100000000000000 : ℝ)*(sp0) + (6165122477702407/100000000000000 : ℝ)*(sp1) + (616507518048487/10000000000000 : ℝ)*(sp2) + (714283812095607/25000000000000 : ℝ)*(sp3) + (15335106923/20000000000000 : ℝ)*(sp4) + (47121195031/100000000000000 : ℝ)*(sp6) + (3751227683/25000000000000 : ℝ)*(sp7) + (71428756332329/2500000000000 : ℝ)*(f.failure) + (6165122612997859/100000000000000 : ℝ)*(f.sum) + (44958410016237/17435000000000000000000000000 : ℝ)*base65 + (106718832993118659/217937500000000000000000000000000 : ℝ)*base68 + (976468241271506341/217937500000000000000000000000000 : ℝ)*base69 + (1654954394110506341/217937500000000000000000000000000 : ℝ)*base71 + (16418000294903/4358750000000000000000000000 : ℝ)*base73 + (1262694174001193841/217937500000000000000000000000000 : ℝ)*base75 + (1592215696448756341/217937500000000000000000000000000 : ℝ)*base77 + (449769350104568841/217937500000000000000000000000000 : ℝ)*base79 + (1904608569023/1089687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (355727/25000000000000000000 : ℝ)*base90 + (355727/25000000000000000000 : ℝ)*base92 + (355727/25000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (965244373424268866278064601/435875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379155141/100000000000000 : ℝ)*(base19) + (409066039/100000000000000 : ℝ)*(base23) + (22842963/50000000000000 : ℝ)*(upper3) + (1755169/12500000000000 : ℝ)*(lower4) + (46020307/100000000000000 : ℝ)*(upper5) + (2271999992065037/50000000000000 : ℝ)*(major0) + (2271999992065037/50000000000000 : ℝ)*(major1) + (2271999992065037/50000000000000 : ℝ)*(major2) + (7945769087/100000000000000 : ℝ)*(sp1) + (8526749859/100000000000000 : ℝ)*(sp2) + (1242007083163039/20000000000000 : ℝ)*(sp4) + (6210027090890967/100000000000000 : ℝ)*(sp5) + (6210026479999297/100000000000000 : ℝ)*(sp6) + (1438982239314171/50000000000000 : ℝ)*(sp7) + (1438982239314171/50000000000000 : ℝ)*(f.failure) + (1242007083163039/20000000000000 : ℝ)*(f.sum) + (6271991804143/1089687500000000000000000000 : ℝ)*base65 + (8727158280614106711/871750000000000000000000000000000 : ℝ)*base67 + (4844517643057106711/871750000000000000000000000000000 : ℝ)*base69 + (318974634587106711/871750000000000000000000000000000 : ℝ)*base71 + (99544488868853/17435000000000000000000000000 : ℝ)*base73 + (9619463446470606711/871750000000000000000000000000000 : ℝ)*base75 + (12044141243377356711/871750000000000000000000000000000 : ℝ)*base77 + (4240515321832606711/871750000000000000000000000000000 : ℝ)*base79 + (725656765707/17435000000000000000000000000 : ℝ)*base82 + (873773/500000000000000000000 : ℝ)*base90 + (873773/500000000000000000000 : ℝ)*base92 + (873773/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1422_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (462/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11297/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1422_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1422_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1033/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1422_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1422_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1422_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4381/1024 : ℝ) ≤ p) (hpb : p ≤ (2191/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15788937/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15821/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1033/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1422_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
