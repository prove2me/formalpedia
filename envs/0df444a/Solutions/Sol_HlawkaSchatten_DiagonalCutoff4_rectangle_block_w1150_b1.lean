-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:35:22.371248+00:00
-- url     : https://prove2.me/submissions/d8ba54b3-1d43-459b-8d6c-60f1d8494eff

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
theorem support_rectangle_w1150_s3_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-215935059/1000000000 : ℝ)*x 0 + (5428363983/10000000000 : ℝ)*x 1 + (1308206487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215935059/1000000000 : ℝ)^8343 ≤ (1311455245059/10000000000000 : ℝ)^6295 := by
    have hnat : (215935059 : ℕ)^8343*10000000000000^6295 ≤ 1311455245059^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215935059 1000000000 1311455245059 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428363983/10000000000 : ℝ)^8343 ≤ (44498646842349/100000000000000 : ℝ)^6295 := by
    have hnat : (5428363983 : ℕ)^8343*100000000000000^6295 ≤ 44498646842349^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428363983 10000000000 44498646842349 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308206487/2500000000 : ℝ)^8343 ≤ (2649175043301/6250000000000 : ℝ)^6295 := by
    have hnat : (1308206487 : ℕ)^8343*6250000000000^6295 ≤ 2649175043301^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308206487 2500000000 2649175043301 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215935059/1000000000 : ℝ), (5428363983/10000000000 : ℝ), (1308206487/2500000000 : ℝ)] ![(1311455245059/10000000000000 : ℝ), (44498646842349/100000000000000 : ℝ), (2649175043301/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215935059/1000000000 : ℝ)|^8343 ≤ (1311455245059/10000000000000 : ℝ)^6295
        have hw : |(-215935059/1000000000 : ℝ)|=(215935059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428363983/10000000000 : ℝ)|^8343 ≤ (44498646842349/100000000000000 : ℝ)^6295
        have hw : |(5428363983/10000000000 : ℝ)|=(5428363983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308206487/2500000000 : ℝ)|^8343 ≤ (2649175043301/6250000000000 : ℝ)^6295
        have hw : |(1308206487/2500000000 : ℝ)|=(1308206487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s3_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167300117/312500000 : ℝ)*x 0 + (-564821421/2500000000 : ℝ)*x 1 + (523282577/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167300117/312500000 : ℝ)^8343 ≤ (43688249597109/100000000000000 : ℝ)^6295 := by
    have hnat : (167300117 : ℕ)^8343*100000000000000^6295 ≤ 43688249597109^6295*312500000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167300117 312500000 43688249597109 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564821421/2500000000 : ℝ)^8343 ≤ (3481237902621/25000000000000 : ℝ)^6295 := by
    have hnat : (564821421 : ℕ)^8343*25000000000000^6295 ≤ 3481237902621^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564821421 2500000000 3481237902621 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (523282577/1000000000 : ℝ)^8343 ≤ (42386798781903/100000000000000 : ℝ)^6295 := by
    have hnat : (523282577 : ℕ)^8343*100000000000000^6295 ≤ 42386798781903^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523282577 1000000000 42386798781903 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167300117/312500000 : ℝ), (-564821421/2500000000 : ℝ), (523282577/1000000000 : ℝ)] ![(43688249597109/100000000000000 : ℝ), (3481237902621/25000000000000 : ℝ), (42386798781903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167300117/312500000 : ℝ)|^8343 ≤ (43688249597109/100000000000000 : ℝ)^6295
        have hw : |(167300117/312500000 : ℝ)|=(167300117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-564821421/2500000000 : ℝ)|^8343 ≤ (3481237902621/25000000000000 : ℝ)^6295
        have hw : |(-564821421/2500000000 : ℝ)|=(564821421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(523282577/1000000000 : ℝ)|^8343 ≤ (42386798781903/100000000000000 : ℝ)^6295
        have hw : |(523282577/1000000000 : ℝ)|=(523282577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s3_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334600239/625000000 : ℝ)*x 0 + (5232825829/10000000000 : ℝ)*x 1 + (-4518571/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334600239/625000000 : ℝ)^8343 ≤ (21844125231173/50000000000000 : ℝ)^6295 := by
    have hnat : (334600239 : ℕ)^8343*50000000000000^6295 ≤ 21844125231173^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334600239 625000000 21844125231173 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5232825829/10000000000 : ℝ)^8343 ≤ (10348339701/24414062500 : ℝ)^6295 := by
    have hnat : (5232825829 : ℕ)^8343*24414062500^6295 ≤ 10348339701^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5232825829 10000000000 10348339701 24414062500 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518571/20000000 : ℝ)^8343 ≤ (13924950107457/100000000000000 : ℝ)^6295 := by
    have hnat : (4518571 : ℕ)^8343*100000000000000^6295 ≤ 13924950107457^6295*20000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518571 20000000 13924950107457 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334600239/625000000 : ℝ), (5232825829/10000000000 : ℝ), (-4518571/20000000 : ℝ)] ![(21844125231173/50000000000000 : ℝ), (10348339701/24414062500 : ℝ), (13924950107457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334600239/625000000 : ℝ)|^8343 ≤ (21844125231173/50000000000000 : ℝ)^6295
        have hw : |(334600239/625000000 : ℝ)|=(334600239/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5232825829/10000000000 : ℝ)|^8343 ≤ (10348339701/24414062500 : ℝ)^6295
        have hw : |(5232825829/10000000000 : ℝ)|=(5232825829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4518571/20000000 : ℝ)|^8343 ≤ (13924950107457/100000000000000 : ℝ)^6295
        have hw : |(-4518571/20000000 : ℝ)|=(4518571/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s3_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180670031/5000000000 : ℝ)*x 0 + (208542083/500000000 : ℝ)*x 1 + (570058737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180670031/5000000000 : ℝ)^8343 ≤ (33294675113909/100000000000000 : ℝ)^6295 := by
    have hnat : (2180670031 : ℕ)^8343*100000000000000^6295 ≤ 33294675113909^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180670031 5000000000 33294675113909 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208542083/500000000 : ℝ)^8343 ≤ (31381103070129/100000000000000 : ℝ)^6295 := by
    have hnat : (208542083 : ℕ)^8343*100000000000000^6295 ≤ 31381103070129^6295*500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208542083 500000000 31381103070129 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570058737/1250000000 : ℝ)^8343 ≤ (35324221806821/100000000000000 : ℝ)^6295 := by
    have hnat : (570058737 : ℕ)^8343*100000000000000^6295 ≤ 35324221806821^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570058737 1250000000 35324221806821 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180670031/5000000000 : ℝ), (208542083/500000000 : ℝ), (570058737/1250000000 : ℝ)] ![(33294675113909/100000000000000 : ℝ), (31381103070129/100000000000000 : ℝ), (35324221806821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180670031/5000000000 : ℝ)|^8343 ≤ (33294675113909/100000000000000 : ℝ)^6295
        have hw : |(2180670031/5000000000 : ℝ)|=(2180670031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208542083/500000000 : ℝ)|^8343 ≤ (31381103070129/100000000000000 : ℝ)^6295
        have hw : |(208542083/500000000 : ℝ)|=(208542083/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570058737/1250000000 : ℝ)|^8343 ≤ (35324221806821/100000000000000 : ℝ)^6295
        have hw : |(570058737/1250000000 : ℝ)|=(570058737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s3_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2159368291/10000000000 : ℝ)*x 0 + (5233580617/10000000000 : ℝ)*x 1 + (2713802559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159368291/10000000000 : ℝ)^8343 ≤ (1639336866377/12500000000000 : ℝ)^6295 := by
    have hnat : (2159368291 : ℕ)^8343*12500000000000^6295 ≤ 1639336866377^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159368291 10000000000 1639336866377 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5233580617/10000000000 : ℝ)^8343 ≤ (10598725651363/25000000000000 : ℝ)^6295 := by
    have hnat : (5233580617 : ℕ)^8343*25000000000000^6295 ≤ 10598725651363^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233580617 10000000000 10598725651363 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713802559/5000000000 : ℝ)^8343 ≤ (8898080488677/20000000000000 : ℝ)^6295 := by
    have hnat : (2713802559 : ℕ)^8343*20000000000000^6295 ≤ 8898080488677^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713802559 5000000000 8898080488677 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2159368291/10000000000 : ℝ), (5233580617/10000000000 : ℝ), (2713802559/5000000000 : ℝ)] ![(1639336866377/12500000000000 : ℝ), (10598725651363/25000000000000 : ℝ), (8898080488677/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2159368291/10000000000 : ℝ)|^8343 ≤ (1639336866377/12500000000000 : ℝ)^6295
        have hw : |(-2159368291/10000000000 : ℝ)|=(2159368291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5233580617/10000000000 : ℝ)|^8343 ≤ (10598725651363/25000000000000 : ℝ)^6295
        have hw : |(5233580617/10000000000 : ℝ)|=(5233580617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713802559/5000000000 : ℝ)|^8343 ≤ (8898080488677/20000000000000 : ℝ)^6295
        have hw : |(2713802559/5000000000 : ℝ)|=(2713802559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s3_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (663004523/1250000000 : ℝ)*x 0 + (-2064506277/10000000000 : ℝ)*x 1 + (2713802599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663004523/1250000000 : ℝ)^8343 ≤ (4315296281933/10000000000000 : ℝ)^6295 := by
    have hnat : (663004523 : ℕ)^8343*10000000000000^6295 ≤ 4315296281933^6295*1250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663004523 1250000000 4315296281933 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2064506277/10000000000 : ℝ)^8343 ≤ (12356633852311/100000000000000 : ℝ)^6295 := by
    have hnat : (2064506277 : ℕ)^8343*100000000000000^6295 ≤ 12356633852311^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064506277 10000000000 12356633852311 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713802599/5000000000 : ℝ)^8343 ≤ (22245201656247/50000000000000 : ℝ)^6295 := by
    have hnat : (2713802599 : ℕ)^8343*50000000000000^6295 ≤ 22245201656247^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713802599 5000000000 22245201656247 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663004523/1250000000 : ℝ), (-2064506277/10000000000 : ℝ), (2713802599/5000000000 : ℝ)] ![(4315296281933/10000000000000 : ℝ), (12356633852311/100000000000000 : ℝ), (22245201656247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663004523/1250000000 : ℝ)|^8343 ≤ (4315296281933/10000000000000 : ℝ)^6295
        have hw : |(663004523/1250000000 : ℝ)|=(663004523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2064506277/10000000000 : ℝ)|^8343 ≤ (12356633852311/100000000000000 : ℝ)^6295
        have hw : |(-2064506277/10000000000 : ℝ)|=(2064506277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713802599/5000000000 : ℝ)|^8343 ≤ (22245201656247/50000000000000 : ℝ)^6295
        have hw : |(2713802599/5000000000 : ℝ)|=(2713802599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s3_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2652018031/5000000000 : ℝ)*x 0 + (2713802701/5000000000 : ℝ)*x 1 + (-412901233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652018031/5000000000 : ℝ)^8343 ≤ (43152961503831/100000000000000 : ℝ)^6295 := by
    have hnat : (2652018031 : ℕ)^8343*100000000000000^6295 ≤ 43152961503831^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652018031 5000000000 43152961503831 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713802701/5000000000 : ℝ)^8343 ≤ (11122601382181/25000000000000 : ℝ)^6295 := by
    have hnat : (2713802701 : ℕ)^8343*25000000000000^6295 ≤ 11122601382181^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713802701 5000000000 11122601382181 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412901233/2000000000 : ℝ)^8343 ≤ (12356632963871/100000000000000 : ℝ)^6295 := by
    have hnat : (412901233 : ℕ)^8343*100000000000000^6295 ≤ 12356632963871^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412901233 2000000000 12356632963871 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652018031/5000000000 : ℝ), (2713802701/5000000000 : ℝ), (-412901233/2000000000 : ℝ)] ![(43152961503831/100000000000000 : ℝ), (11122601382181/25000000000000 : ℝ), (12356632963871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652018031/5000000000 : ℝ)|^8343 ≤ (43152961503831/100000000000000 : ℝ)^6295
        have hw : |(2652018031/5000000000 : ℝ)|=(2652018031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713802701/5000000000 : ℝ)|^8343 ≤ (11122601382181/25000000000000 : ℝ)^6295
        have hw : |(2713802701/5000000000 : ℝ)|=(2713802701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-412901233/2000000000 : ℝ)|^8343 ≤ (12356632963871/100000000000000 : ℝ)^6295
        have hw : |(-412901233/2000000000 : ℝ)|=(412901233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s3_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4361375347/10000000000 : ℝ)*x 0 + (4558966303/10000000000 : ℝ)*x 1 + (4172353607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4361375347/10000000000 : ℝ)^8343 ≤ (33295032117047/100000000000000 : ℝ)^6295 := by
    have hnat : (4361375347 : ℕ)^8343*100000000000000^6295 ≤ 33295032117047^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361375347 10000000000 33295032117047 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4558966303/10000000000 : ℝ)^8343 ≤ (35308787166277/100000000000000 : ℝ)^6295 := by
    have hnat : (4558966303 : ℕ)^8343*100000000000000^6295 ≤ 35308787166277^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558966303 10000000000 35308787166277 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172353607/10000000000 : ℝ)^8343 ≤ (31396180703749/100000000000000 : ℝ)^6295 := by
    have hnat : (4172353607 : ℕ)^8343*100000000000000^6295 ≤ 31396180703749^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172353607 10000000000 31396180703749 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4361375347/10000000000 : ℝ), (4558966303/10000000000 : ℝ), (4172353607/10000000000 : ℝ)] ![(33295032117047/100000000000000 : ℝ), (35308787166277/100000000000000 : ℝ), (31396180703749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4361375347/10000000000 : ℝ)|^8343 ≤ (33295032117047/100000000000000 : ℝ)^6295
        have hw : |(4361375347/10000000000 : ℝ)|=(4361375347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4558966303/10000000000 : ℝ)|^8343 ≤ (35308787166277/100000000000000 : ℝ)^6295
        have hw : |(4558966303/10000000000 : ℝ)|=(4558966303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172353607/10000000000 : ℝ)|^8343 ≤ (31396180703749/100000000000000 : ℝ)^6295
        have hw : |(4172353607/10000000000 : ℝ)|=(4172353607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5329/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3699/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16479/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16479/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16479/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4553/50000 : ℝ) ^ (4171/1024 : ℝ) ≤ (5768852889188411/100000000000000000000 : ℝ) := by
    have hpowers : (4553/50000 : ℝ)^4171 ≤ (5768852889188411/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4553 : ℕ)^4171*100000000000000000000^1024 ≤ 5768852889188411^1024*50000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4553 50000 5768852889188411 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4553/50000 : ℝ)) (X := (5768852889188411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16479/100000 : ℝ) ^ (4171/1024 : ℝ) ≤ (64620411272243303/100000000000000000000 : ℝ) := by
    have hpowers : (16479/100000 : ℝ)^4171 ≤ (64620411272243303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16479 : ℕ)^4171*100000000000000000000^1024 ≤ 64620411272243303^1024*100000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16479 100000 64620411272243303 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16479/100000 : ℝ)) (X := (64620411272243303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005768852889188411/50000000000000000000 : ℝ) ≤ (5000141621871401/5000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50005768852889188411/50000000000000000000 : ℝ)^1024 ≤ (5000141621871401/5000000000000000 : ℝ)^4171 := by
      have hnat : (50005768852889188411 : ℕ)^1024*5000000000000000^4171 ≤ 5000141621871401^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005768852889188411 50000000000000000000 5000141621871401 5000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141621871401/5000000000000000 : ℝ)) (X := (50005768852889188411/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50035194632080715857/50000000000000000000 : ℝ) ≤ (5000863815325939/5000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50035194632080715857/50000000000000000000 : ℝ)^1024 ≤ (5000863815325939/5000000000000000 : ℝ)^4171 := by
      have hnat : (50035194632080715857 : ℕ)^1024*5000000000000000^4171 ≤ 5000863815325939^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035194632080715857 50000000000000000000 5000863815325939 5000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000863815325939/5000000000000000 : ℝ)) (X := (50035194632080715857/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50064620411272243303/50000000000000000000 : ℝ) ≤ (5001586008780477/5000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50064620411272243303/50000000000000000000 : ℝ)^1024 ≤ (5001586008780477/5000000000000000 : ℝ)^4171 := by
      have hnat : (50064620411272243303 : ℕ)^1024*5000000000000000^4171 ≤ 5001586008780477^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064620411272243303 50000000000000000000 5001586008780477 5000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001586008780477/5000000000000000 : ℝ)) (X := (50064620411272243303/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5768852889188411/100000000000000000000 : ℝ) ≤ ((36852891590863793517/36865000000000000000 : ℝ)+2*(361096727269/184325000000000 : ℝ)*(4553/50000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (36852891590863793517/36865000000000000000 : ℝ)+2*(361096727269/184325000000000 : ℝ)*(4553/50000 : ℝ)=(5000141621871401/5000000000000000 : ℝ) by norm_num, show 1+2*(5768852889188411/100000000000000000000 : ℝ)=(50005768852889188411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64620411272243303/100000000000000000000 : ℝ)+(5768852889188411/100000000000000000000 : ℝ) ≤ ((36852891590863793517/36865000000000000000 : ℝ)+(361096727269/184325000000000 : ℝ)*((16479/100000 : ℝ)+(4553/50000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (36852891590863793517/36865000000000000000 : ℝ)+(361096727269/184325000000000 : ℝ)*((16479/100000 : ℝ)+(4553/50000 : ℝ))=(5000863815325939/5000000000000000 : ℝ) by norm_num, show 1+(64620411272243303/100000000000000000000 : ℝ)+(5768852889188411/100000000000000000000 : ℝ)=(50035194632080715857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64620411272243303/100000000000000000000 : ℝ) ≤ ((36852891590863793517/36865000000000000000 : ℝ)+2*(361096727269/184325000000000 : ℝ)*(16479/100000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (36852891590863793517/36865000000000000000 : ℝ)+2*(361096727269/184325000000000 : ℝ)*(16479/100000 : ℝ)=(5001586008780477/5000000000000000 : ℝ) by norm_num, show 1+2*(64620411272243303/100000000000000000000 : ℝ)=(50064620411272243303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36852891590863793517/36865000000000000000 : ℝ)*(X 1 0+X 2 0)+(361096727269/184325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (4553/50000 : ℝ)) (hi := (16479/100000 : ℝ)) (c := (36852891590863793517/36865000000000000000 : ℝ)) (alpha := (361096727269/184325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36852891590863793517/36865000000000000000 : ℝ)*(X 0 1+X 2 1)+(361096727269/184325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (4553/50000 : ℝ)) (hi := (16479/100000 : ℝ)) (c := (36852891590863793517/36865000000000000000 : ℝ)) (alpha := (361096727269/184325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36852891590863793517/36865000000000000000 : ℝ)*(X 0 2+X 1 2)+(361096727269/184325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (4553/50000 : ℝ)) (hi := (16479/100000 : ℝ)) (c := (36852891590863793517/36865000000000000000 : ℝ)) (alpha := (361096727269/184325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-215935059/1000000000 : ℝ)*X 0 0+(5428363983/10000000000 : ℝ)*X 0 1+(1308206487/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167300117/312500000 : ℝ)*X 1 0+(-564821421/2500000000 : ℝ)*X 1 1+(523282577/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334600239/625000000 : ℝ)*X 2 0+(5232825829/10000000000 : ℝ)*X 2 1+(-4518571/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180670031/5000000000 : ℝ)*X 0 0+(208542083/500000000 : ℝ)*X 0 1+(570058737/1250000000 : ℝ)*X 0 2+(2180670031/5000000000 : ℝ)*X 1 0+(208542083/500000000 : ℝ)*X 1 1+(570058737/1250000000 : ℝ)*X 1 2+(2180670031/5000000000 : ℝ)*X 2 0+(208542083/500000000 : ℝ)*X 2 1+(570058737/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2159368291/10000000000 : ℝ)*X 0 0+(5233580617/10000000000 : ℝ)*X 0 1+(2713802559/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663004523/1250000000 : ℝ)*X 1 0+(-2064506277/10000000000 : ℝ)*X 1 1+(2713802599/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652018031/5000000000 : ℝ)*X 2 0+(2713802701/5000000000 : ℝ)*X 2 1+(-412901233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4361375347/10000000000 : ℝ)*X 0 0+(4558966303/10000000000 : ℝ)*X 0 1+(4172353607/10000000000 : ℝ)*X 0 2+(4361375347/10000000000 : ℝ)*X 1 0+(4558966303/10000000000 : ℝ)*X 1 1+(4172353607/10000000000 : ℝ)*X 1 2+(4361375347/10000000000 : ℝ)*X 2 0+(4558966303/10000000000 : ℝ)*X 2 1+(4172353607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90431136218561805180708489/9216250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1154573193/50000000000000 : ℝ)*(base19) + (1092911211/50000000000000 : ℝ)*(base23) + (5346807/5000000000000 : ℝ)*(lower2) + (189840097/100000000000000 : ℝ)*(upper3) + (7704471/3125000000000 : ℝ)*(upper5) + (38403812602961/1000000000000 : ℝ)*(major0) + (38403812602961/1000000000000 : ℝ)*(major1) + (38403812602961/1000000000000 : ℝ)*(major2) + (5114131961131657/100000000000000 : ℝ)*(sp0) + (5114171747755487/100000000000000 : ℝ)*(sp1) + (5114171871079451/100000000000000 : ℝ)*(sp2) + (1283284210826743/50000000000000 : ℝ)*(sp3) + (5261971277/12500000000000 : ℝ)*(sp4) + (2464370687/12500000000000 : ℝ)*(sp7) + (1283294068309491/50000000000000 : ℝ)*(f.failure) + (5114174056901873/100000000000000 : ℝ)*(f.sum) + (17406202354993/3686500000000000000000000000 : ℝ)*base65 + (48404882576988837/36865000000000000000000000000000 : ℝ)*base67 + (483582136169623837/36865000000000000000000000000000 : ℝ)*base69 + (267467572231823837/36865000000000000000000000000000 : ℝ)*base71 + (236748407569/73730000000000000000000000 : ℝ)*base74 + (139812373847533837/36865000000000000000000000000000 : ℝ)*base75 + (817431538714783837/36865000000000000000000000000000 : ℝ)*base77 + (186813237020251163/36865000000000000000000000000000 : ℝ)*base80 + (2079554229681/1843250000000000000000000000 : ℝ)*base82 + (10379699/2500000000000000000000 : ℝ)*base90 + (10379699/2500000000000000000000 : ℝ)*base92 + (10379699/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (342435615971539499647695723/92162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (765934877/100000000000000 : ℝ)*(base19) + (413941403/50000000000000 : ℝ)*(base23) + (108709049/100000000000000 : ℝ)*(upper3) + (33488041/50000000000000 : ℝ)*(lower4) + (58603/78125000000 : ℝ)*(upper5) + (193513832290573/5000000000000 : ℝ)*(major0) + (193513832290573/5000000000000 : ℝ)*(major1) + (193513832290573/5000000000000 : ℝ)*(major2) + (14515829589/100000000000000 : ℝ)*(sp1) + (10158957957/50000000000000 : ℝ)*(sp2) + (5153985467508837/100000000000000 : ℝ)*(sp4) + (1288492546436093/25000000000000 : ℝ)*(sp5) + (2576982160855059/50000000000000 : ℝ)*(sp6) + (1293283850130979/50000000000000 : ℝ)*(sp7) + (1293283850130979/50000000000000 : ℝ)*(f.failure) + (5153985467508837/100000000000000 : ℝ)*(f.sum) + (10480992664843/1474600000000000000000000000 : ℝ)*base66 + (751580094060459759/184325000000000000000000000000000 : ℝ)*base68 + (623233964141384759/184325000000000000000000000000000 : ℝ)*base70 + (628134301380765241/184325000000000000000000000000000 : ℝ)*base71 + (1252923048997/147460000000000000000000000 : ℝ)*base74 + (4089046511507884759/184325000000000000000000000000000 : ℝ)*base76 + (22738600732665241/184325000000000000000000000000000 : ℝ)*base77 + (3694289589259184759/184325000000000000000000000000000 : ℝ)*base80 + (105952634309/1843250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (32227869/2500000000000000000000 : ℝ)*base89 + (32227869/2500000000000000000000 : ℝ)*base91 + (32227869/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1150_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1150_s4_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-432458319/2000000000 : ℝ)*x 0 + (1080302561/2000000000 : ℝ)*x 1 + (5257752737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432458319/2000000000 : ℝ)^8343 ≤ (3284557663753/25000000000000 : ℝ)^6295 := by
    have hnat : (432458319 : ℕ)^8343*25000000000000^6295 ≤ 3284557663753^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432458319 2000000000 3284557663753 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080302561/2000000000 : ℝ)^8343 ≤ (5525895103799/12500000000000 : ℝ)^6295 := by
    have hnat : (1080302561 : ℕ)^8343*12500000000000^6295 ≤ 5525895103799^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080302561 2000000000 5525895103799 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257752737/10000000000 : ℝ)^8343 ≤ (42654608498377/100000000000000 : ℝ)^6295 := by
    have hnat : (5257752737 : ℕ)^8343*100000000000000^6295 ≤ 42654608498377^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257752737 10000000000 42654608498377 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-432458319/2000000000 : ℝ), (1080302561/2000000000 : ℝ), (5257752737/10000000000 : ℝ)] ![(3284557663753/25000000000000 : ℝ), (5525895103799/12500000000000 : ℝ), (42654608498377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-432458319/2000000000 : ℝ)|^8343 ≤ (3284557663753/25000000000000 : ℝ)^6295
        have hw : |(-432458319/2000000000 : ℝ)|=(432458319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080302561/2000000000 : ℝ)|^8343 ≤ (5525895103799/12500000000000 : ℝ)^6295
        have hw : |(1080302561/2000000000 : ℝ)|=(1080302561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257752737/10000000000 : ℝ)|^8343 ≤ (42654608498377/100000000000000 : ℝ)^6295
        have hw : |(5257752737/10000000000 : ℝ)|=(5257752737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s4_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673446291/5000000000 : ℝ)*x 0 + (-447068643/2000000000 : ℝ)*x 1 + (1051550527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673446291/5000000000 : ℝ)^8343 ≤ (8723136021833/20000000000000 : ℝ)^6295 := by
    have hnat : (2673446291 : ℕ)^8343*20000000000000^6295 ≤ 8723136021833^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673446291 5000000000 8723136021833 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447068643/2000000000 : ℝ)^8343 ≤ (13729712471853/100000000000000 : ℝ)^6295 := by
    have hnat : (447068643 : ℕ)^8343*100000000000000^6295 ≤ 13729712471853^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447068643 2000000000 13729712471853 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051550527/2000000000 : ℝ)^8343 ≤ (8530921480333/20000000000000 : ℝ)^6295 := by
    have hnat : (1051550527 : ℕ)^8343*20000000000000^6295 ≤ 8530921480333^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051550527 2000000000 8530921480333 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673446291/5000000000 : ℝ), (-447068643/2000000000 : ℝ), (1051550527/2000000000 : ℝ)] ![(8723136021833/20000000000000 : ℝ), (13729712471853/100000000000000 : ℝ), (8530921480333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673446291/5000000000 : ℝ)|^8343 ≤ (8723136021833/20000000000000 : ℝ)^6295
        have hw : |(2673446291/5000000000 : ℝ)|=(2673446291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-447068643/2000000000 : ℝ)|^8343 ≤ (13729712471853/100000000000000 : ℝ)^6295
        have hw : |(-447068643/2000000000 : ℝ)|=(447068643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1051550527/2000000000 : ℝ)|^8343 ≤ (8530921480333/20000000000000 : ℝ)^6295
        have hw : |(1051550527/2000000000 : ℝ)|=(1051550527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s4_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346892667/10000000000 : ℝ)*x 0 + (5257752709/10000000000 : ℝ)*x 1 + (-558835751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346892667/10000000000 : ℝ)^8343 ≤ (5451960128513/12500000000000 : ℝ)^6295 := by
    have hnat : (5346892667 : ℕ)^8343*12500000000000^6295 ≤ 5451960128513^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346892667 10000000000 5451960128513 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257752709/10000000000 : ℝ)^8343 ≤ (42654608197319/100000000000000 : ℝ)^6295 := by
    have hnat : (5257752709 : ℕ)^8343*100000000000000^6295 ≤ 42654608197319^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257752709 10000000000 42654608197319 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (558835751/2500000000 : ℝ)^8343 ≤ (3432427688559/25000000000000 : ℝ)^6295 := by
    have hnat : (558835751 : ℕ)^8343*25000000000000^6295 ≤ 3432427688559^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558835751 2500000000 3432427688559 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346892667/10000000000 : ℝ), (5257752709/10000000000 : ℝ), (-558835751/2500000000 : ℝ)] ![(5451960128513/12500000000000 : ℝ), (42654608197319/100000000000000 : ℝ), (3432427688559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346892667/10000000000 : ℝ)|^8343 ≤ (5451960128513/12500000000000 : ℝ)^6295
        have hw : |(5346892667/10000000000 : ℝ)|=(5346892667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257752709/10000000000 : ℝ)|^8343 ≤ (42654608197319/100000000000000 : ℝ)^6295
        have hw : |(5257752709/10000000000 : ℝ)|=(5257752709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-558835751/2500000000 : ℝ)|^8343 ≤ (3432427688559/25000000000000 : ℝ)^6295
        have hw : |(-558835751/2500000000 : ℝ)|=(558835751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s4_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272693407/625000000 : ℝ)*x 0 + (4222200997/10000000000 : ℝ)*x 1 + (4508656419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272693407/625000000 : ℝ)^8343 ≤ (16656213627709/50000000000000 : ℝ)^6295 := by
    have hnat : (272693407 : ℕ)^8343*50000000000000^6295 ≤ 16656213627709^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272693407 625000000 16656213627709 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4222200997/10000000000 : ℝ)^8343 ≤ (31894268141307/100000000000000 : ℝ)^6295 := by
    have hnat : (4222200997 : ℕ)^8343*100000000000000^6295 ≤ 31894268141307^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222200997 10000000000 31894268141307 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508656419/10000000000 : ℝ)^8343 ≤ (17396652296017/50000000000000 : ℝ)^6295 := by
    have hnat : (4508656419 : ℕ)^8343*50000000000000^6295 ≤ 17396652296017^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508656419 10000000000 17396652296017 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272693407/625000000 : ℝ), (4222200997/10000000000 : ℝ), (4508656419/10000000000 : ℝ)] ![(16656213627709/50000000000000 : ℝ), (31894268141307/100000000000000 : ℝ), (17396652296017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272693407/625000000 : ℝ)|^8343 ≤ (16656213627709/50000000000000 : ℝ)^6295
        have hw : |(272693407/625000000 : ℝ)|=(272693407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4222200997/10000000000 : ℝ)|^8343 ≤ (31894268141307/100000000000000 : ℝ)^6295
        have hw : |(4222200997/10000000000 : ℝ)|=(4222200997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508656419/10000000000 : ℝ)|^8343 ≤ (17396652296017/50000000000000 : ℝ)^6295
        have hw : |(4508656419/10000000000 : ℝ)|=(4508656419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s4_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2162298913/10000000000 : ℝ)*x 0 + (2629080619/5000000000 : ℝ)*x 1 + (540110243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162298913/10000000000 : ℝ)^8343 ≤ (1642286198217/12500000000000 : ℝ)^6295 := by
    have hnat : (2162298913 : ℕ)^8343*12500000000000^6295 ≤ 1642286198217^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162298913 10000000000 1642286198217 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2629080619/5000000000 : ℝ)^8343 ≤ (42659000787541/100000000000000 : ℝ)^6295 := by
    have hnat : (2629080619 : ℕ)^8343*100000000000000^6295 ≤ 42659000787541^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2629080619 5000000000 42659000787541 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540110243/1000000000 : ℝ)^8343 ≤ (4420270960843/10000000000000 : ℝ)^6295 := by
    have hnat : (540110243 : ℕ)^8343*10000000000000^6295 ≤ 4420270960843^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540110243 1000000000 4420270960843 10000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2162298913/10000000000 : ℝ), (2629080619/5000000000 : ℝ), (540110243/1000000000 : ℝ)] ![(1642286198217/12500000000000 : ℝ), (42659000787541/100000000000000 : ℝ), (4420270960843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2162298913/10000000000 : ℝ)|^8343 ≤ (1642286198217/12500000000000 : ℝ)^6295
        have hw : |(-2162298913/10000000000 : ℝ)|=(2162298913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2629080619/5000000000 : ℝ)|^8343 ≤ (42659000787541/100000000000000 : ℝ)^6295
        have hw : |(2629080619/5000000000 : ℝ)|=(2629080619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540110243/1000000000 : ℝ)|^8343 ≤ (4420270960843/10000000000000 : ℝ)^6295
        have hw : |(540110243/1000000000 : ℝ)|=(540110243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s4_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310450967/10000000000 : ℝ)*x 0 + (-2091993281/10000000000 : ℝ)*x 1 + (135027559/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310450967/10000000000 : ℝ)^8343 ≤ (43222145602379/100000000000000 : ℝ)^6295 := by
    have hnat : (5310450967 : ℕ)^8343*100000000000000^6295 ≤ 43222145602379^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310450967 10000000000 43222145602379 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091993281/10000000000 : ℝ)^8343 ≤ (12575145535313/100000000000000 : ℝ)^6295 := by
    have hnat : (2091993281 : ℕ)^8343*100000000000000^6295 ≤ 12575145535313^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091993281 10000000000 12575145535313 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135027559/250000000 : ℝ)^8343 ≤ (44202708849169/100000000000000 : ℝ)^6295 := by
    have hnat : (135027559 : ℕ)^8343*100000000000000^6295 ≤ 44202708849169^6295*250000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135027559 250000000 44202708849169 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310450967/10000000000 : ℝ), (-2091993281/10000000000 : ℝ), (135027559/250000000 : ℝ)] ![(43222145602379/100000000000000 : ℝ), (12575145535313/100000000000000 : ℝ), (44202708849169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310450967/10000000000 : ℝ)|^8343 ≤ (43222145602379/100000000000000 : ℝ)^6295
        have hw : |(5310450967/10000000000 : ℝ)|=(5310450967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091993281/10000000000 : ℝ)|^8343 ≤ (12575145535313/100000000000000 : ℝ)^6295
        have hw : |(-2091993281/10000000000 : ℝ)|=(2091993281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135027559/250000000 : ℝ)|^8343 ≤ (44202708849169/100000000000000 : ℝ)^6295
        have hw : |(135027559/250000000 : ℝ)|=(135027559/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s4_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531045087/1000000000 : ℝ)*x 0 + (5401102361/10000000000 : ℝ)*x 1 + (-209199341/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531045087/1000000000 : ℝ)^8343 ≤ (43222144556039/100000000000000 : ℝ)^6295 := by
    have hnat : (531045087 : ℕ)^8343*100000000000000^6295 ≤ 43222144556039^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531045087 1000000000 43222144556039 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401102361/10000000000 : ℝ)^8343 ≤ (2762669303751/6250000000000 : ℝ)^6295 := by
    have hnat : (5401102361 : ℕ)^8343*6250000000000^6295 ≤ 2762669303751^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401102361 10000000000 2762669303751 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209199341/1000000000 : ℝ)^8343 ≤ (12575146563019/100000000000000 : ℝ)^6295 := by
    have hnat : (209199341 : ℕ)^8343*100000000000000^6295 ≤ 12575146563019^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209199341 1000000000 12575146563019 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531045087/1000000000 : ℝ), (5401102361/10000000000 : ℝ), (-209199341/1000000000 : ℝ)] ![(43222144556039/100000000000000 : ℝ), (2762669303751/6250000000000 : ℝ), (12575146563019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531045087/1000000000 : ℝ)|^8343 ≤ (43222144556039/100000000000000 : ℝ)^6295
        have hw : |(531045087/1000000000 : ℝ)|=(531045087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401102361/10000000000 : ℝ)|^8343 ≤ (2762669303751/6250000000000 : ℝ)^6295
        have hw : |(5401102361/10000000000 : ℝ)|=(5401102361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209199341/1000000000 : ℝ)|^8343 ≤ (12575146563019/100000000000000 : ℝ)^6295
        have hw : |(-209199341/1000000000 : ℝ)|=(209199341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s4_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090777129/2500000000 : ℝ)*x 0 + (1126960547/2500000000 : ℝ)*x 1 + (4223018599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090777129/2500000000 : ℝ)^8343 ≤ (16656284481077/50000000000000 : ℝ)^6295 := by
    have hnat : (1090777129 : ℕ)^8343*50000000000000^6295 ≤ 16656284481077^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090777129 2500000000 16656284481077 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126960547/2500000000 : ℝ)^8343 ≤ (17392488591271/50000000000000 : ℝ)^6295 := by
    have hnat : (1126960547 : ℕ)^8343*50000000000000^6295 ≤ 17392488591271^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126960547 2500000000 17392488591271 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4223018599/10000000000 : ℝ)^8343 ≤ (31902453842189/100000000000000 : ℝ)^6295 := by
    have hnat : (4223018599 : ℕ)^8343*100000000000000^6295 ≤ 31902453842189^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4223018599 10000000000 31902453842189 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090777129/2500000000 : ℝ), (1126960547/2500000000 : ℝ), (4223018599/10000000000 : ℝ)] ![(16656284481077/50000000000000 : ℝ), (17392488591271/50000000000000 : ℝ), (31902453842189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090777129/2500000000 : ℝ)|^8343 ≤ (16656284481077/50000000000000 : ℝ)^6295
        have hw : |(1090777129/2500000000 : ℝ)|=(1090777129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126960547/2500000000 : ℝ)|^8343 ≤ (17392488591271/50000000000000 : ℝ)^6295
        have hw : |(1126960547/2500000000 : ℝ)|=(1126960547/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4223018599/10000000000 : ℝ)|^8343 ≤ (31902453842189/100000000000000 : ℝ)^6295
        have hw : |(4223018599/10000000000 : ℝ)|=(4223018599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1119/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3699/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3699/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5329/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3699/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3699/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5329/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3699/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3699/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5329/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5329/50000 : ℝ) ^ (4171/1024 : ℝ) ≤ (2737963881676699/25000000000000000000 : ℝ) := by
    have hpowers : (5329/50000 : ℝ)^4171 ≤ (2737963881676699/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5329 : ℕ)^4171*25000000000000000000^1024 ≤ 2737963881676699^1024*50000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5329 50000 2737963881676699 25000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5329/50000 : ℝ)) (X := (2737963881676699/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3699/25000 : ℝ) ^ (4171/1024 : ℝ) ≤ (2083372128253273/5000000000000000000 : ℝ) := by
    have hpowers : (3699/25000 : ℝ)^4171 ≤ (2083372128253273/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3699 : ℕ)^4171*5000000000000000000^1024 ≤ 2083372128253273^1024*25000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3699 25000 2083372128253273 5000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3699/25000 : ℝ)) (X := (2083372128253273/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502737963881676699/12500000000000000000 : ℝ) ≤ (5000268850958847/5000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (12502737963881676699/12500000000000000000 : ℝ)^1024 ≤ (5000268850958847/5000000000000000 : ℝ)^4171 := by
      have hnat : (12502737963881676699 : ℕ)^1024*5000000000000000^4171 ≤ 5000268850958847^4171*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502737963881676699 12500000000000000000 5000268850958847 5000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268850958847/5000000000000000 : ℝ)) (X := (12502737963881676699/12500000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126644353065367883/3125000000000000000 : ℝ) ≤ (10001291572012803/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (3126644353065367883/3125000000000000000 : ℝ)^1024 ≤ (10001291572012803/10000000000000000 : ℝ)^4171 := by
      have hnat : (3126644353065367883 : ℕ)^1024*10000000000000000^4171 ≤ 10001291572012803^4171*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126644353065367883 3125000000000000000 10001291572012803 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001291572012803/10000000000000000 : ℝ)) (X := (3126644353065367883/3125000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502083372128253273/2500000000000000000 : ℝ) ≤ (1250255680263489/1250000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (2502083372128253273/2500000000000000000 : ℝ)^1024 ≤ (1250255680263489/1250000000000000 : ℝ)^4171 := by
      have hnat : (2502083372128253273 : ℕ)^1024*1250000000000000^4171 ≤ 1250255680263489^4171*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502083372128253273 2500000000000000000 1250255680263489 1250000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250255680263489/1250000000000000 : ℝ)) (X := (2502083372128253273/2500000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2737963881676699/25000000000000000000 : ℝ) ≤ ((5170769439448509291/5172500000000000000 : ℝ)+2*(753870095109/413800000000000 : ℝ)*(5329/50000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (5170769439448509291/5172500000000000000 : ℝ)+2*(753870095109/413800000000000 : ℝ)*(5329/50000 : ℝ)=(5000268850958847/5000000000000000 : ℝ) by norm_num, show 1+2*(2737963881676699/25000000000000000000 : ℝ)=(12502737963881676699/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2083372128253273/5000000000000000000 : ℝ)+(2737963881676699/25000000000000000000 : ℝ) ≤ ((5170769439448509291/5172500000000000000 : ℝ)+(753870095109/413800000000000 : ℝ)*((3699/25000 : ℝ)+(5329/50000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (5170769439448509291/5172500000000000000 : ℝ)+(753870095109/413800000000000 : ℝ)*((3699/25000 : ℝ)+(5329/50000 : ℝ))=(10001291572012803/10000000000000000 : ℝ) by norm_num, show 1+(2083372128253273/5000000000000000000 : ℝ)+(2737963881676699/25000000000000000000 : ℝ)=(3126644353065367883/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2083372128253273/5000000000000000000 : ℝ) ≤ ((5170769439448509291/5172500000000000000 : ℝ)+2*(753870095109/413800000000000 : ℝ)*(3699/25000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (5170769439448509291/5172500000000000000 : ℝ)+2*(753870095109/413800000000000 : ℝ)*(3699/25000 : ℝ)=(1250255680263489/1250000000000000 : ℝ) by norm_num, show 1+2*(2083372128253273/5000000000000000000 : ℝ)=(2502083372128253273/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5170769439448509291/5172500000000000000 : ℝ)*(X 1 0+X 2 0)+(753870095109/413800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (5170769439448509291/5172500000000000000 : ℝ)) (alpha := (753870095109/413800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5170769439448509291/5172500000000000000 : ℝ)*(X 0 1+X 2 1)+(753870095109/413800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (5170769439448509291/5172500000000000000 : ℝ)) (alpha := (753870095109/413800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5170769439448509291/5172500000000000000 : ℝ)*(X 0 2+X 1 2)+(753870095109/413800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (5329/50000 : ℝ)) (hi := (3699/25000 : ℝ)) (c := (5170769439448509291/5172500000000000000 : ℝ)) (alpha := (753870095109/413800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-432458319/2000000000 : ℝ)*X 0 0+(1080302561/2000000000 : ℝ)*X 0 1+(5257752737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673446291/5000000000 : ℝ)*X 1 0+(-447068643/2000000000 : ℝ)*X 1 1+(1051550527/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346892667/10000000000 : ℝ)*X 2 0+(5257752709/10000000000 : ℝ)*X 2 1+(-558835751/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272693407/625000000 : ℝ)*X 0 0+(4222200997/10000000000 : ℝ)*X 0 1+(4508656419/10000000000 : ℝ)*X 0 2+(272693407/625000000 : ℝ)*X 1 0+(4222200997/10000000000 : ℝ)*X 1 1+(4508656419/10000000000 : ℝ)*X 1 2+(272693407/625000000 : ℝ)*X 2 0+(4222200997/10000000000 : ℝ)*X 2 1+(4508656419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2162298913/10000000000 : ℝ)*X 0 0+(2629080619/5000000000 : ℝ)*X 0 1+(540110243/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310450967/10000000000 : ℝ)*X 1 0+(-2091993281/10000000000 : ℝ)*X 1 1+(135027559/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531045087/1000000000 : ℝ)*X 2 0+(5401102361/10000000000 : ℝ)*X 2 1+(-209199341/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090777129/2500000000 : ℝ)*X 0 0+(1126960547/2500000000 : ℝ)*X 0 1+(4223018599/10000000000 : ℝ)*X 0 2+(1090777129/2500000000 : ℝ)*X 1 0+(1126960547/2500000000 : ℝ)*X 1 1+(4223018599/10000000000 : ℝ)*X 1 2+(1090777129/2500000000 : ℝ)*X 2 0+(1126960547/2500000000 : ℝ)*X 2 1+(4223018599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2634636431094112370602287273/258625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84952103/4000000000000 : ℝ)*(base19) + (1975450517/100000000000000 : ℝ)*(base23) + (13844941/10000000000000 : ℝ)*(lower2) + (58419463/50000000000000 : ℝ)*(upper3) + (61336109/25000000000000 : ℝ)*(upper5) + (5223565415042199/100000000000000 : ℝ)*(major0) + (5223565415042199/100000000000000 : ℝ)*(major1) + (5223565415042199/100000000000000 : ℝ)*(major2) + (1739020282929437/25000000000000 : ℝ)*(sp0) + (6956136166612991/100000000000000 : ℝ)*(sp1) + (6956136314965049/100000000000000 : ℝ)*(sp2) + (3490968577753911/100000000000000 : ℝ)*(sp3) + (57158697819/100000000000000 : ℝ)*(sp4) + (23622345211/100000000000000 : ℝ)*(sp7) + (1745496100049561/50000000000000 : ℝ)*(f.failure) + (3478069145207783/50000000000000 : ℝ)*(f.sum) + (57530523120999/20690000000000000000000000000 : ℝ)*base66 + (38785325231041591/517250000000000000000000000000000 : ℝ)*base68 + (982242098333208409/517250000000000000000000000000000 : ℝ)*base69 + (3493115570009708409/517250000000000000000000000000000 : ℝ)*base71 + (104766835255609/20690000000000000000000000000 : ℝ)*base74 + (3962877304639541591/517250000000000000000000000000000 : ℝ)*base76 + (794796674122458409/517250000000000000000000000000000 : ℝ)*base77 + (10445166294556208409/517250000000000000000000000000000 : ℝ)*base79 + (123449822802311/20690000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (26804071/2500000000000000000000 : ℝ)*base89 + (26804071/2500000000000000000000 : ℝ)*base91 + (26804071/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (223891488727888172903779653/32328125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (263742421/12500000000000 : ℝ)*(base19) + (2084113389/100000000000000 : ℝ)*(base23) + (43773587/50000000000000 : ℝ)*(upper2) + (120109117/100000000000000 : ℝ)*(upper3) + (287956403/100000000000000 : ℝ)*(upper5) + (328338377943257/6250000000000 : ℝ)*(major0) + (328338377943257/6250000000000 : ℝ)*(major1) + (328338377943257/6250000000000 : ℝ)*(major2) + (55895411649/100000000000000 : ℝ)*(sp1) + (23364662983/50000000000000 : ℝ)*(sp2) + (1399177469135339/20000000000000 : ℝ)*(sp4) + (6995829340325679/100000000000000 : ℝ)*(sp5) + (349791926611867/5000000000000 : ℝ)*(sp6) + (351094051765437/10000000000000 : ℝ)*(sp7) + (351094051765437/10000000000000 : ℝ)*(f.failure) + (1399177469135339/20000000000000 : ℝ)*(f.sum) + (1053267567279/10345000000000000000000000000 : ℝ)*base65 + (151425000361557037/32328125000000000000000000000000 : ℝ)*base67 + (100030183342963287/32328125000000000000000000000000 : ℝ)*base69 + (6718816316916603/8082031250000000000000000000000 : ℝ)*base71 + (7762936243567/5172500000000000000000000000 : ℝ)*base73 + (153588711771057419/16164062500000000000000000000000 : ℝ)*base76 + (69140803377682037/32328125000000000000000000000000 : ℝ)*base77 + (321792581208067963/32328125000000000000000000000000 : ℝ)*base80 + (13197324366917/5172500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2031107/500000000000000000000 : ℝ)*base89 + (2031107/500000000000000000000 : ℝ)*base91 + (2031107/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1150_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3699/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5329/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1150_s5_0 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-540727367/2500000000 : ℝ)*x 0 + (5394708073/10000000000 : ℝ)*x 1 + (1316037999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540727367/2500000000 : ℝ)^8343 ≤ (6571603259691/50000000000000 : ℝ)^6295 := by
    have hnat : (540727367 : ℕ)^8343*50000000000000^6295 ≤ 6571603259691^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540727367 2500000000 6571603259691 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394708073/10000000000 : ℝ)^8343 ≤ (44133366038037/100000000000000 : ℝ)^6295 := by
    have hnat : (5394708073 : ℕ)^8343*100000000000000^6295 ≤ 44133366038037^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394708073 10000000000 44133366038037 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316037999/2500000000 : ℝ)^8343 ≤ (21361713716981/50000000000000 : ℝ)^6295 := by
    have hnat : (1316037999 : ℕ)^8343*50000000000000^6295 ≤ 21361713716981^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316037999 2500000000 21361713716981 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-540727367/2500000000 : ℝ), (5394708073/10000000000 : ℝ), (1316037999/2500000000 : ℝ)] ![(6571603259691/50000000000000 : ℝ), (44133366038037/100000000000000 : ℝ), (21361713716981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-540727367/2500000000 : ℝ)|^8343 ≤ (6571603259691/50000000000000 : ℝ)^6295
        have hw : |(-540727367/2500000000 : ℝ)|=(540727367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394708073/10000000000 : ℝ)|^8343 ≤ (44133366038037/100000000000000 : ℝ)^6295
        have hw : |(5394708073/10000000000 : ℝ)|=(5394708073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316037999/2500000000 : ℝ)|^8343 ≤ (21361713716981/50000000000000 : ℝ)^6295
        have hw : |(1316037999/2500000000 : ℝ)|=(1316037999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s5_1 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (20879629/39062500 : ℝ)*x 0 + (-2229153943/10000000000 : ℝ)*x 1 + (5264151969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20879629/39062500 : ℝ)^8343 ≤ (8719444116171/20000000000000 : ℝ)^6295 := by
    have hnat : (20879629 : ℕ)^8343*20000000000000^6295 ≤ 8719444116171^6295*39062500^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20879629 39062500 8719444116171 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2229153943/10000000000 : ℝ)^8343 ≤ (2735870452347/20000000000000 : ℝ)^6295 := by
    have hnat : (2229153943 : ℕ)^8343*20000000000000^6295 ≤ 2735870452347^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229153943 10000000000 2735870452347 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264151969/10000000000 : ℝ)^8343 ≤ (42723427143541/100000000000000 : ℝ)^6295 := by
    have hnat : (5264151969 : ℕ)^8343*100000000000000^6295 ≤ 42723427143541^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264151969 10000000000 42723427143541 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20879629/39062500 : ℝ), (-2229153943/10000000000 : ℝ), (5264151969/10000000000 : ℝ)] ![(8719444116171/20000000000000 : ℝ), (2735870452347/20000000000000 : ℝ), (42723427143541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20879629/39062500 : ℝ)|^8343 ≤ (8719444116171/20000000000000 : ℝ)^6295
        have hw : |(20879629/39062500 : ℝ)|=(20879629/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2229153943/10000000000 : ℝ)|^8343 ≤ (2735870452347/20000000000000 : ℝ)^6295
        have hw : |(-2229153943/10000000000 : ℝ)|=(2229153943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264151969/10000000000 : ℝ)|^8343 ≤ (42723427143541/100000000000000 : ℝ)^6295
        have hw : |(5264151969/10000000000 : ℝ)|=(5264151969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s5_2 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345185061/10000000000 : ℝ)*x 0 + (2632075973/5000000000 : ℝ)*x 1 + (-89166157/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345185061/10000000000 : ℝ)^8343 ≤ (21798610490411/50000000000000 : ℝ)^6295 := by
    have hnat : (5345185061 : ℕ)^8343*50000000000000^6295 ≤ 21798610490411^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345185061 10000000000 21798610490411 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632075973/5000000000 : ℝ)^8343 ≤ (8544685379229/20000000000000 : ℝ)^6295 := by
    have hnat : (2632075973 : ℕ)^8343*20000000000000^6295 ≤ 8544685379229^6295*5000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632075973 5000000000 8544685379229 20000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89166157/400000000 : ℝ)^8343 ≤ (13679352115341/100000000000000 : ℝ)^6295 := by
    have hnat : (89166157 : ℕ)^8343*100000000000000^6295 ≤ 13679352115341^6295*400000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89166157 400000000 13679352115341 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345185061/10000000000 : ℝ), (2632075973/5000000000 : ℝ), (-89166157/400000000 : ℝ)] ![(21798610490411/50000000000000 : ℝ), (8544685379229/20000000000000 : ℝ), (13679352115341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345185061/10000000000 : ℝ)|^8343 ≤ (21798610490411/50000000000000 : ℝ)^6295
        have hw : |(5345185061/10000000000 : ℝ)|=(5345185061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632075973/5000000000 : ℝ)|^8343 ≤ (8544685379229/20000000000000 : ℝ)^6295
        have hw : |(2632075973/5000000000 : ℝ)|=(2632075973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89166157/400000000 : ℝ)|^8343 ≤ (13679352115341/100000000000000 : ℝ)^6295
        have hw : |(-89166157/400000000 : ℝ)|=(89166157/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s5_3 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436345631/1000000000 : ℝ)*x 0 + (4235308969/10000000000 : ℝ)*x 1 + (899090937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436345631/1000000000 : ℝ)^8343 ≤ (8329022085893/25000000000000 : ℝ)^6295 := by
    have hnat : (436345631 : ℕ)^8343*25000000000000^6295 ≤ 8329022085893^6295*1000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436345631 1000000000 8329022085893 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235308969/10000000000 : ℝ)^8343 ≤ (16012782580259/50000000000000 : ℝ)^6295 := by
    have hnat : (4235308969 : ℕ)^8343*50000000000000^6295 ≤ 16012782580259^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235308969 10000000000 16012782580259 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899090937/2000000000 : ℝ)^8343 ≤ (2166146655253/6250000000000 : ℝ)^6295 := by
    have hnat : (899090937 : ℕ)^8343*6250000000000^6295 ≤ 2166146655253^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899090937 2000000000 2166146655253 6250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436345631/1000000000 : ℝ), (4235308969/10000000000 : ℝ), (899090937/2000000000 : ℝ)] ![(8329022085893/25000000000000 : ℝ), (16012782580259/50000000000000 : ℝ), (2166146655253/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436345631/1000000000 : ℝ)|^8343 ≤ (8329022085893/25000000000000 : ℝ)^6295
        have hw : |(436345631/1000000000 : ℝ)|=(436345631/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235308969/10000000000 : ℝ)|^8343 ≤ (16012782580259/50000000000000 : ℝ)^6295
        have hw : |(4235308969/10000000000 : ℝ)|=(4235308969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899090937/2000000000 : ℝ)|^8343 ≤ (2166146655253/6250000000000 : ℝ)^6295
        have hw : |(899090937/2000000000 : ℝ)|=(899090937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s5_4 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-135182163/625000000 : ℝ)*x 0 + (329030589/625000000 : ℝ)*x 1 + (5394369499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135182163/625000000 : ℝ)^8343 ≤ (13143247914849/100000000000000 : ℝ)^6295 := by
    have hnat : (135182163 : ℕ)^8343*100000000000000^6295 ≤ 13143247914849^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135182163 625000000 13143247914849 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329030589/625000000 : ℝ)^8343 ≤ (21363528479601/50000000000000 : ℝ)^6295 := by
    have hnat : (329030589 : ℕ)^8343*50000000000000^6295 ≤ 21363528479601^6295*625000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329030589 625000000 21363528479601 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394369499/10000000000 : ℝ)^8343 ≤ (44129695119191/100000000000000 : ℝ)^6295 := by
    have hnat : (5394369499 : ℕ)^8343*100000000000000^6295 ≤ 44129695119191^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394369499 10000000000 44129695119191 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135182163/625000000 : ℝ), (329030589/625000000 : ℝ), (5394369499/10000000000 : ℝ)] ![(13143247914849/100000000000000 : ℝ), (21363528479601/50000000000000 : ℝ), (44129695119191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135182163/625000000 : ℝ)|^8343 ≤ (13143247914849/100000000000000 : ℝ)^6295
        have hw : |(-135182163/625000000 : ℝ)|=(135182163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329030589/625000000 : ℝ)|^8343 ≤ (21363528479601/50000000000000 : ℝ)^6295
        have hw : |(329030589/625000000 : ℝ)|=(329030589/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394369499/10000000000 : ℝ)|^8343 ≤ (44129695119191/100000000000000 : ℝ)^6295
        have hw : |(5394369499/10000000000 : ℝ)|=(5394369499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s5_5 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (212483571/400000000 : ℝ)*x 0 + (-16791487/80000000 : ℝ)*x 1 + (269718479/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212483571/400000000 : ℝ)^8343 ≤ (21619909474041/50000000000000 : ℝ)^6295 := by
    have hnat : (212483571 : ℕ)^8343*50000000000000^6295 ≤ 21619909474041^6295*400000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212483571 400000000 21619909474041 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16791487/80000000 : ℝ)^8343 ≤ (157881062931/1250000000000 : ℝ)^6295 := by
    have hnat : (16791487 : ℕ)^8343*1250000000000^6295 ≤ 157881062931^6295*80000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16791487 80000000 157881062931 1250000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269718479/500000000 : ℝ)^8343 ≤ (1379052999919/3125000000000 : ℝ)^6295 := by
    have hnat : (269718479 : ℕ)^8343*3125000000000^6295 ≤ 1379052999919^6295*500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269718479 500000000 1379052999919 3125000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212483571/400000000 : ℝ), (-16791487/80000000 : ℝ), (269718479/500000000 : ℝ)] ![(21619909474041/50000000000000 : ℝ), (157881062931/1250000000000 : ℝ), (1379052999919/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212483571/400000000 : ℝ)|^8343 ≤ (21619909474041/50000000000000 : ℝ)^6295
        have hw : |(212483571/400000000 : ℝ)|=(212483571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-16791487/80000000 : ℝ)|^8343 ≤ (157881062931/1250000000000 : ℝ)^6295
        have hw : |(-16791487/80000000 : ℝ)|=(16791487/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269718479/500000000 : ℝ)|^8343 ≤ (1379052999919/3125000000000 : ℝ)^6295
        have hw : |(269718479/500000000 : ℝ)|=(269718479/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s5_6 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328022237/2500000000 : ℝ)*x 0 + (1078873963/2000000000 : ℝ)*x 1 + (-2098935999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328022237/2500000000 : ℝ)^8343 ≤ (10809953855093/25000000000000 : ℝ)^6295 := by
    have hnat : (1328022237 : ℕ)^8343*25000000000000^6295 ≤ 10809953855093^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328022237 2500000000 10809953855093 25000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078873963/2000000000 : ℝ)^8343 ≤ (44129698545321/100000000000000 : ℝ)^6295 := by
    have hnat : (1078873963 : ℕ)^8343*100000000000000^6295 ≤ 44129698545321^6295*2000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078873963 2000000000 44129698545321 100000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098935999/10000000000 : ℝ)^8343 ≤ (6315243011709/50000000000000 : ℝ)^6295 := by
    have hnat : (2098935999 : ℕ)^8343*50000000000000^6295 ≤ 6315243011709^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098935999 10000000000 6315243011709 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328022237/2500000000 : ℝ), (1078873963/2000000000 : ℝ), (-2098935999/10000000000 : ℝ)] ![(10809953855093/25000000000000 : ℝ), (44129698545321/100000000000000 : ℝ), (6315243011709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328022237/2500000000 : ℝ)|^8343 ≤ (10809953855093/25000000000000 : ℝ)^6295
        have hw : |(1328022237/2500000000 : ℝ)|=(1328022237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078873963/2000000000 : ℝ)|^8343 ≤ (44129698545321/100000000000000 : ℝ)^6295
        have hw : |(1078873963/2000000000 : ℝ)|=(1078873963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098935999/10000000000 : ℝ)|^8343 ≤ (6315243011709/50000000000000 : ℝ)^6295
        have hw : |(-2098935999/10000000000 : ℝ)|=(2098935999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1150_s5_7 (p : ℝ) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1090866757/2500000000 : ℝ)*x 0 + (35115489/78125000 : ℝ)*x 1 + (4235983367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090866757/2500000000 : ℝ)^8343 ≤ (16658098401063/50000000000000 : ℝ)^6295 := by
    have hnat : (1090866757 : ℕ)^8343*50000000000000^6295 ≤ 16658098401063^6295*2500000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090866757 2500000000 16658098401063 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35115489/78125000 : ℝ)^8343 ≤ (17325739643307/50000000000000 : ℝ)^6295 := by
    have hnat : (35115489 : ℕ)^8343*50000000000000^6295 ≤ 17325739643307^6295*78125000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35115489 78125000 17325739643307 50000000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235983367/10000000000 : ℝ)^8343 ≤ (4004040487557/12500000000000 : ℝ)^6295 := by
    have hnat : (4235983367 : ℕ)^8343*12500000000000^6295 ≤ 4004040487557^6295*10000000000^8343 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235983367 10000000000 4004040487557 12500000000000 8343 6295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8343/2048 : ℝ)) 8343 6295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1090866757/2500000000 : ℝ), (35115489/78125000 : ℝ), (4235983367/10000000000 : ℝ)] ![(16658098401063/50000000000000 : ℝ), (17325739643307/50000000000000 : ℝ), (4004040487557/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1090866757/2500000000 : ℝ)|^8343 ≤ (16658098401063/50000000000000 : ℝ)^6295
        have hw : |(1090866757/2500000000 : ℝ)|=(1090866757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(35115489/78125000 : ℝ)|^8343 ≤ (17325739643307/50000000000000 : ℝ)^6295
        have hw : |(35115489/78125000 : ℝ)|=(35115489/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235983367/10000000000 : ℝ)|^8343 ≤ (4004040487557/12500000000000 : ℝ)^6295
        have hw : |(4235983367/10000000000 : ℝ)|=(4235983367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1150_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11327/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1119/10000 : ℝ) ^ (4171/1024 : ℝ) ≤ (13355328689720639/100000000000000000000 : ℝ) := by
    have hpowers : (1119/10000 : ℝ)^4171 ≤ (13355328689720639/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1119 : ℕ)^4171*100000000000000000000^1024 ≤ 13355328689720639^1024*10000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1119 10000 13355328689720639 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1119/10000 : ℝ)) (X := (13355328689720639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4171/1024 : ℝ) ≤ (35597535771641669/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4171 ≤ (35597535771641669/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4171*100000000000000000000^1024 ≤ 35597535771641669^1024*20000^4171 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 35597535771641669 100000000000000000000 4171 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (35597535771641669/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013355328689720639/50000000000000000000 : ℝ) ≤ (10000655693058801/10000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50013355328689720639/50000000000000000000 : ℝ)^1024 ≤ (10000655693058801/10000000000000000 : ℝ)^4171 := by
      have hnat : (50013355328689720639 : ℕ)^1024*10000000000000000^4171 ≤ 10000655693058801^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013355328689720639 50000000000000000000 10000655693058801 10000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000655693058801/10000000000000000 : ℝ)) (X := (50013355328689720639/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012238216115340577/25000000000000000000 : ℝ) ≤ (2500300398457157/2500000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (25012238216115340577/25000000000000000000 : ℝ)^1024 ≤ (2500300398457157/2500000000000000 : ℝ)^4171 := by
      have hnat : (25012238216115340577 : ℕ)^1024*2500000000000000^4171 ≤ 2500300398457157^4171*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012238216115340577 25000000000000000000 2500300398457157 2500000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500300398457157/2500000000000000 : ℝ)) (X := (25012238216115340577/25000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035597535771641669/50000000000000000000 : ℝ) ≤ (2000349498919691/2000000000000000 : ℝ) ^ (4171/1024 : ℝ) := by
    have hpowers : (50035597535771641669/50000000000000000000 : ℝ)^1024 ≤ (2000349498919691/2000000000000000 : ℝ)^4171 := by
      have hnat : (50035597535771641669 : ℕ)^1024*2000000000000000^4171 ≤ 2000349498919691^4171*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035597535771641669 50000000000000000000 2000349498919691 2000000000000000 1024 4171 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000349498919691/2000000000000000 : ℝ)) (X := (50035597535771641669/50000000000000000000 : ℝ)) (by norm_num) 4171 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13355328689720639/100000000000000000000 : ℝ) ≤ ((289902660248907817/290000000000000000 : ℝ)+2*(77985824261/43500000000000 : ℝ)*(1119/10000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (289902660248907817/290000000000000000 : ℝ)+2*(77985824261/43500000000000 : ℝ)*(1119/10000 : ℝ)=(10000655693058801/10000000000000000 : ℝ) by norm_num, show 1+2*(13355328689720639/100000000000000000000 : ℝ)=(50013355328689720639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35597535771641669/100000000000000000000 : ℝ)+(13355328689720639/100000000000000000000 : ℝ) ≤ ((289902660248907817/290000000000000000 : ℝ)+(77985824261/43500000000000 : ℝ)*((2847/20000 : ℝ)+(1119/10000 : ℝ)))^(4171/1024 : ℝ) := by
    rw [show (289902660248907817/290000000000000000 : ℝ)+(77985824261/43500000000000 : ℝ)*((2847/20000 : ℝ)+(1119/10000 : ℝ))=(2500300398457157/2500000000000000 : ℝ) by norm_num, show 1+(35597535771641669/100000000000000000000 : ℝ)+(13355328689720639/100000000000000000000 : ℝ)=(25012238216115340577/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35597535771641669/100000000000000000000 : ℝ) ≤ ((289902660248907817/290000000000000000 : ℝ)+2*(77985824261/43500000000000 : ℝ)*(2847/20000 : ℝ))^(4171/1024 : ℝ) := by
    rw [show (289902660248907817/290000000000000000 : ℝ)+2*(77985824261/43500000000000 : ℝ)*(2847/20000 : ℝ)=(2000349498919691/2000000000000000 : ℝ) by norm_num, show 1+2*(35597535771641669/100000000000000000000 : ℝ)=(50035597535771641669/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (289902660248907817/290000000000000000 : ℝ)*(X 1 0+X 2 0)+(77985824261/43500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (289902660248907817/290000000000000000 : ℝ)) (alpha := (77985824261/43500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (289902660248907817/290000000000000000 : ℝ)*(X 0 1+X 2 1)+(77985824261/43500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (289902660248907817/290000000000000000 : ℝ)) (alpha := (77985824261/43500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (289902660248907817/290000000000000000 : ℝ)*(X 0 2+X 1 2)+(77985824261/43500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4171/1024 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (289902660248907817/290000000000000000 : ℝ)) (alpha := (77985824261/43500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-540727367/2500000000 : ℝ)*X 0 0+(5394708073/10000000000 : ℝ)*X 0 1+(1316037999/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((20879629/39062500 : ℝ)*X 1 0+(-2229153943/10000000000 : ℝ)*X 1 1+(5264151969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345185061/10000000000 : ℝ)*X 2 0+(2632075973/5000000000 : ℝ)*X 2 1+(-89166157/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436345631/1000000000 : ℝ)*X 0 0+(4235308969/10000000000 : ℝ)*X 0 1+(899090937/2000000000 : ℝ)*X 0 2+(436345631/1000000000 : ℝ)*X 1 0+(4235308969/10000000000 : ℝ)*X 1 1+(899090937/2000000000 : ℝ)*X 1 2+(436345631/1000000000 : ℝ)*X 2 0+(4235308969/10000000000 : ℝ)*X 2 1+(899090937/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-135182163/625000000 : ℝ)*X 0 0+(329030589/625000000 : ℝ)*X 0 1+(5394369499/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212483571/400000000 : ℝ)*X 1 0+(-16791487/80000000 : ℝ)*X 1 1+(269718479/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328022237/2500000000 : ℝ)*X 2 0+(1078873963/2000000000 : ℝ)*X 2 1+(-2098935999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1090866757/2500000000 : ℝ)*X 0 0+(35115489/78125000 : ℝ)*X 0 1+(4235983367/10000000000 : ℝ)*X 0 2+(1090866757/2500000000 : ℝ)*X 1 0+(35115489/78125000 : ℝ)*X 1 1+(4235983367/10000000000 : ℝ)*X 1 2+(1090866757/2500000000 : ℝ)*X 2 0+(35115489/78125000 : ℝ)*X 2 1+(4235983367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1150_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (77110918244961653881859187/14500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (755828401/100000000000000 : ℝ)*(base19) + (732579083/100000000000000 : ℝ)*(base23) + (40767633/100000000000000 : ℝ)*(lower2) + (10232399/10000000000000 : ℝ)*(upper3) + (1317137/1562500000000 : ℝ)*(upper5) + (5751799281166537/100000000000000 : ℝ)*(major0) + (5751799281166537/100000000000000 : ℝ)*(major1) + (5751799281166537/100000000000000 : ℝ)*(major2) + (1914890253152629/25000000000000 : ℝ)*(sp0) + (957447287401269/12500000000000 : ℝ)*(sp1) + (765957832245947/10000000000000 : ℝ)*(sp2) + (1922004435898283/50000000000000 : ℝ)*(sp3) + (18042428037/100000000000000 : ℝ)*(sp4) + (5229115733/50000000000000 : ℝ)*(sp7) + (3844019330028033/100000000000000 : ℝ)*(f.failure) + (7659579055038553/100000000000000 : ℝ)*(f.sum) + (8856368614457/2175000000000000000000000000 : ℝ)*base65 + (519243776436500813/87000000000000000000000000000000 : ℝ)*base68 + (270998586500499187/87000000000000000000000000000000 : ℝ)*base69 + (2331034564674500813/87000000000000000000000000000000 : ℝ)*base72 + (6209652949093/2175000000000000000000000000 : ℝ)*base74 + (1738831624157499187/87000000000000000000000000000000 : ℝ)*base75 + (97119384588500813/87000000000000000000000000000000 : ℝ)*base78 + (81560023404500813/87000000000000000000000000000000 : ℝ)*base80 + (10082169343307/2175000000000000000000000000 : ℝ)*base81 + (66400063/5000000000000000000000 : ℝ)*base89 + (66400063/5000000000000000000000 : ℝ)*base91 + (66400063/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11940149619824150430427989/2900000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37640107/3125000000000 : ℝ)*(base19) + (1167356181/100000000000000 : ℝ)*(base23) + (104182009/100000000000000 : ℝ)*(upper3) + (216066841/100000000000000 : ℝ)*(lower4) + (1156339579283439/20000000000000 : ℝ)*(major0) + (1156339579283439/20000000000000 : ℝ)*(major1) + (1156339579283439/20000000000000 : ℝ)*(major2) + (19694864301/50000000000000 : ℝ)*(sp1) + (8843591999/20000000000000 : ℝ)*(sp2) + (2114378237/100000000000000 : ℝ)*(sp3) + (3849697301718293/50000000000000 : ℝ)*(sp4) + (7699354009224561/100000000000000 : ℝ)*(sp5) + (7699349218120409/100000000000000 : ℝ)*(sp6) + (482999867222057/12500000000000 : ℝ)*(sp7) + (1932000526077347/50000000000000 : ℝ)*(f.failure) + (3849697301718293/50000000000000 : ℝ)*(f.sum) + (354905071557/145000000000000000000000000 : ℝ)*base66 + (38937092150597337/5800000000000000000000000000000 : ℝ)*base68 + (52348759605802663/5800000000000000000000000000000 : ℝ)*base69 + (14946145524197337/5800000000000000000000000000000 : ℝ)*base72 + (38829654813/145000000000000000000000000 : ℝ)*base73 + (62155311957397337/5800000000000000000000000000000 : ℝ)*base76 + (42567106807397337/5800000000000000000000000000000 : ℝ)*base78 + (134350736631602663/5800000000000000000000000000000 : ℝ)*base79 + (652237915099/72500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (19921117/2500000000000000000000 : ℝ)*base89 + (19921117/2500000000000000000000 : ℝ)*base91 + (19921117/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1150_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1150_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1150_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1150_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1150_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1150_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4171/1024 : ℝ) ≤ p) (hpb : p ≤ (8343/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74814911/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16479/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11327/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3523/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1150_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
