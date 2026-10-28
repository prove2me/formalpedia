-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:51:24.582715+00:00
-- url     : https://prove2.me/submissions/d56b6f66-cfdf-4781-920d-a4a5eaae41e8

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
theorem support_rectangle_w1046_s0_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-961280863/5000000000 : ℝ)*x 0 + (1215357521/2000000000 : ℝ)*x 1 + (1192054029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961280863/5000000000 : ℝ)^8239 ≤ (5571291827657/50000000000000 : ℝ)^6191 := by
    have hnat : (961280863 : ℕ)^8239*50000000000000^6191 ≤ 5571291827657^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961280863 5000000000 5571291827657 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1215357521/2000000000 : ℝ)^8239 ≤ (25768126193519/50000000000000 : ℝ)^6191 := by
    have hnat : (1215357521 : ℕ)^8239*50000000000000^6191 ≤ 25768126193519^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215357521 2000000000 25768126193519 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192054029/2500000000 : ℝ)^8239 ≤ (37321163943871/100000000000000 : ℝ)^6191 := by
    have hnat : (1192054029 : ℕ)^8239*100000000000000^6191 ≤ 37321163943871^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192054029 2500000000 37321163943871 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-961280863/5000000000 : ℝ), (1215357521/2000000000 : ℝ), (1192054029/2500000000 : ℝ)] ![(5571291827657/50000000000000 : ℝ), (25768126193519/50000000000000 : ℝ), (37321163943871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-961280863/5000000000 : ℝ)|^8239 ≤ (5571291827657/50000000000000 : ℝ)^6191
        have hw : |(-961280863/5000000000 : ℝ)|=(961280863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1215357521/2000000000 : ℝ)|^8239 ≤ (25768126193519/50000000000000 : ℝ)^6191
        have hw : |(1215357521/2000000000 : ℝ)|=(1215357521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192054029/2500000000 : ℝ)|^8239 ≤ (37321163943871/100000000000000 : ℝ)^6191
        have hw : |(1192054029/2500000000 : ℝ)|=(1192054029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s0_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5522205839/10000000000 : ℝ)*x 0 + (-1338194271/5000000000 : ℝ)*x 1 + (4768208669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5522205839/10000000000 : ℝ)^8239 ≤ (4537354580767/10000000000000 : ℝ)^6191 := by
    have hnat : (5522205839 : ℕ)^8239*10000000000000^6191 ≤ 4537354580767^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522205839 10000000000 4537354580767 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1338194271/5000000000 : ℝ)^8239 ≤ (17305367811547/100000000000000 : ℝ)^6191 := by
    have hnat : (1338194271 : ℕ)^8239*100000000000000^6191 ≤ 17305367811547^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338194271 5000000000 17305367811547 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4768208669/10000000000 : ℝ)^8239 ≤ (186605431869/500000000000 : ℝ)^6191 := by
    have hnat : (4768208669 : ℕ)^8239*500000000000^6191 ≤ 186605431869^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4768208669 10000000000 186605431869 500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5522205839/10000000000 : ℝ), (-1338194271/5000000000 : ℝ), (4768208669/10000000000 : ℝ)] ![(4537354580767/10000000000000 : ℝ), (17305367811547/100000000000000 : ℝ), (186605431869/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5522205839/10000000000 : ℝ)|^8239 ≤ (4537354580767/10000000000000 : ℝ)^6191
        have hw : |(5522205839/10000000000 : ℝ)|=(5522205839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1338194271/5000000000 : ℝ)|^8239 ≤ (17305367811547/100000000000000 : ℝ)^6191
        have hw : |(-1338194271/5000000000 : ℝ)|=(1338194271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4768208669/10000000000 : ℝ)|^8239 ≤ (186605431869/500000000000 : ℝ)^6191
        have hw : |(4768208669/10000000000 : ℝ)|=(4768208669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s0_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (690275461/1250000000 : ℝ)*x 0 + (2384105419/5000000000 : ℝ)*x 1 + (-2676388649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690275461/1250000000 : ℝ)^8239 ≤ (708961285739/1562500000000 : ℝ)^6191 := by
    have hnat : (690275461 : ℕ)^8239*1562500000000^6191 ≤ 708961285739^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690275461 1250000000 708961285739 1562500000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2384105419/5000000000 : ℝ)^8239 ≤ (37321108966717/100000000000000 : ℝ)^6191 := by
    have hnat : (2384105419 : ℕ)^8239*100000000000000^6191 ≤ 37321108966717^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2384105419 5000000000 37321108966717 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2676388649/10000000000 : ℝ)^8239 ≤ (1730536873227/10000000000000 : ℝ)^6191 := by
    have hnat : (2676388649 : ℕ)^8239*10000000000000^6191 ≤ 1730536873227^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676388649 10000000000 1730536873227 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690275461/1250000000 : ℝ), (2384105419/5000000000 : ℝ), (-2676388649/10000000000 : ℝ)] ![(708961285739/1562500000000 : ℝ), (37321108966717/100000000000000 : ℝ), (1730536873227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690275461/1250000000 : ℝ)|^8239 ≤ (708961285739/1562500000000 : ℝ)^6191
        have hw : |(690275461/1250000000 : ℝ)|=(690275461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2384105419/5000000000 : ℝ)|^8239 ≤ (37321108966717/100000000000000 : ℝ)^6191
        have hw : |(2384105419/5000000000 : ℝ)|=(2384105419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2676388649/10000000000 : ℝ)|^8239 ≤ (1730536873227/10000000000000 : ℝ)^6191
        have hw : |(-2676388649/10000000000 : ℝ)|=(2676388649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s0_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (420886507/1000000000 : ℝ)*x 0 + (625190911/2000000000 : ℝ)*x 1 + (2840200313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420886507/1000000000 : ℝ)^8239 ≤ (1975685258351/6250000000000 : ℝ)^6191 := by
    have hnat : (420886507 : ℕ)^8239*6250000000000^6191 ≤ 1975685258351^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420886507 1000000000 1975685258351 6250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (625190911/2000000000 : ℝ)^8239 ≤ (83115410761/390625000000 : ℝ)^6191 := by
    have hnat : (625190911 : ℕ)^8239*390625000000^6191 ≤ 83115410761^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625190911 2000000000 83115410761 390625000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840200313/5000000000 : ℝ)^8239 ≤ (47111490699249/100000000000000 : ℝ)^6191 := by
    have hnat : (2840200313 : ℕ)^8239*100000000000000^6191 ≤ 47111490699249^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840200313 5000000000 47111490699249 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420886507/1000000000 : ℝ), (625190911/2000000000 : ℝ), (2840200313/5000000000 : ℝ)] ![(1975685258351/6250000000000 : ℝ), (83115410761/390625000000 : ℝ), (47111490699249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420886507/1000000000 : ℝ)|^8239 ≤ (1975685258351/6250000000000 : ℝ)^6191
        have hw : |(420886507/1000000000 : ℝ)|=(420886507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(625190911/2000000000 : ℝ)|^8239 ≤ (83115410761/390625000000 : ℝ)^6191
        have hw : |(625190911/2000000000 : ℝ)|=(625190911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840200313/5000000000 : ℝ)|^8239 ≤ (47111490699249/100000000000000 : ℝ)^6191
        have hw : |(2840200313/5000000000 : ℝ)|=(2840200313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s0_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-482001199/2500000000 : ℝ)*x 0 + (4802009157/10000000000 : ℝ)*x 1 + (1510452069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482001199/2500000000 : ℝ)^8239 ≤ (2796146328073/25000000000000 : ℝ)^6191 := by
    have hnat : (482001199 : ℕ)^8239*25000000000000^6191 ≤ 2796146328073^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482001199 2500000000 2796146328073 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4802009157/10000000000 : ℝ)^8239 ≤ (18836786967753/50000000000000 : ℝ)^6191 := by
    have hnat : (4802009157 : ℕ)^8239*50000000000000^6191 ≤ 18836786967753^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4802009157 10000000000 18836786967753 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1510452069/2500000000 : ℝ)^8239 ≤ (10228368147411/20000000000000 : ℝ)^6191 := by
    have hnat : (1510452069 : ℕ)^8239*20000000000000^6191 ≤ 10228368147411^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510452069 2500000000 10228368147411 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-482001199/2500000000 : ℝ), (4802009157/10000000000 : ℝ), (1510452069/2500000000 : ℝ)] ![(2796146328073/25000000000000 : ℝ), (18836786967753/50000000000000 : ℝ), (10228368147411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-482001199/2500000000 : ℝ)|^8239 ≤ (2796146328073/25000000000000 : ℝ)^6191
        have hw : |(-482001199/2500000000 : ℝ)|=(482001199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4802009157/10000000000 : ℝ)|^8239 ≤ (18836786967753/50000000000000 : ℝ)^6191
        have hw : |(4802009157/10000000000 : ℝ)|=(4802009157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1510452069/2500000000 : ℝ)|^8239 ≤ (10228368147411/20000000000000 : ℝ)^6191
        have hw : |(1510452069/2500000000 : ℝ)|=(1510452069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s0_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (645893033/1250000000 : ℝ)*x 0 + (-1402796433/10000000000 : ℝ)*x 1 + (6041808561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (645893033/1250000000 : ℝ)^8239 ≤ (2595811199597/6250000000000 : ℝ)^6191 := by
    have hnat : (645893033 : ℕ)^8239*6250000000000^6191 ≤ 2595811199597^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645893033 1250000000 2595811199597 6250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402796433/10000000000 : ℝ)^8239 ≤ (1465035370039/20000000000000 : ℝ)^6191 := by
    have hnat : (1402796433 : ℕ)^8239*20000000000000^6191 ≤ 1465035370039^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402796433 10000000000 1465035370039 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6041808561/10000000000 : ℝ)^8239 ≤ (2497160349/4882812500 : ℝ)^6191 := by
    have hnat : (6041808561 : ℕ)^8239*4882812500^6191 ≤ 2497160349^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6041808561 10000000000 2497160349 4882812500 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(645893033/1250000000 : ℝ), (-1402796433/10000000000 : ℝ), (6041808561/10000000000 : ℝ)] ![(2595811199597/6250000000000 : ℝ), (1465035370039/20000000000000 : ℝ), (2497160349/4882812500 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(645893033/1250000000 : ℝ)|^8239 ≤ (2595811199597/6250000000000 : ℝ)^6191
        have hw : |(645893033/1250000000 : ℝ)|=(645893033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1402796433/10000000000 : ℝ)|^8239 ≤ (1465035370039/20000000000000 : ℝ)^6191
        have hw : |(-1402796433/10000000000 : ℝ)|=(1402796433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6041808561/10000000000 : ℝ)|^8239 ≤ (2497160349/4882812500 : ℝ)^6191
        have hw : |(6041808561/10000000000 : ℝ)|=(6041808561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s0_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5167142393/10000000000 : ℝ)*x 0 + (6041810271/10000000000 : ℝ)*x 1 + (-1402796541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5167142393/10000000000 : ℝ)^8239 ≤ (41532959179733/100000000000000 : ℝ)^6191 := by
    have hnat : (5167142393 : ℕ)^8239*100000000000000^6191 ≤ 41532959179733^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167142393 10000000000 41532959179733 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6041810271/10000000000 : ℝ)^8239 ≤ (51141863210313/100000000000000 : ℝ)^6191 := by
    have hnat : (6041810271 : ℕ)^8239*100000000000000^6191 ≤ 51141863210313^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6041810271 10000000000 51141863210313 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1402796541/10000000000 : ℝ)^8239 ≤ (7325177600713/100000000000000 : ℝ)^6191 := by
    have hnat : (1402796541 : ℕ)^8239*100000000000000^6191 ≤ 7325177600713^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402796541 10000000000 7325177600713 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5167142393/10000000000 : ℝ), (6041810271/10000000000 : ℝ), (-1402796541/10000000000 : ℝ)] ![(41532959179733/100000000000000 : ℝ), (51141863210313/100000000000000 : ℝ), (7325177600713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5167142393/10000000000 : ℝ)|^8239 ≤ (41532959179733/100000000000000 : ℝ)^6191
        have hw : |(5167142393/10000000000 : ℝ)|=(5167142393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6041810271/10000000000 : ℝ)|^8239 ≤ (51141863210313/100000000000000 : ℝ)^6191
        have hw : |(6041810271/10000000000 : ℝ)|=(6041810271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1402796541/10000000000 : ℝ)|^8239 ≤ (7325177600713/100000000000000 : ℝ)^6191
        have hw : |(-1402796541/10000000000 : ℝ)|=(1402796541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s0_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1054869091/2500000000 : ℝ)*x 0 + (701802957/1250000000 : ℝ)*x 1 + (798557681/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054869091/2500000000 : ℝ)^8239 ≤ (15858534554527/50000000000000 : ℝ)^6191 := by
    have hnat : (1054869091 : ℕ)^8239*50000000000000^6191 ≤ 15858534554527^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054869091 2500000000 15858534554527 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701802957/1250000000 : ℝ)^8239 ≤ (11596171955317/25000000000000 : ℝ)^6191 := by
    have hnat : (701802957 : ℕ)^8239*25000000000000^6191 ≤ 11596171955317^6191*1250000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701802957 1250000000 11596171955317 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (798557681/2500000000 : ℝ)^8239 ≤ (5474560765891/25000000000000 : ℝ)^6191 := by
    have hnat : (798557681 : ℕ)^8239*25000000000000^6191 ≤ 5474560765891^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798557681 2500000000 5474560765891 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054869091/2500000000 : ℝ), (701802957/1250000000 : ℝ), (798557681/2500000000 : ℝ)] ![(15858534554527/50000000000000 : ℝ), (11596171955317/25000000000000 : ℝ), (5474560765891/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054869091/2500000000 : ℝ)|^8239 ≤ (15858534554527/50000000000000 : ℝ)^6191
        have hw : |(1054869091/2500000000 : ℝ)|=(1054869091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(701802957/1250000000 : ℝ)|^8239 ≤ (11596171955317/25000000000000 : ℝ)^6191
        have hw : |(701802957/1250000000 : ℝ)|=(701802957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(798557681/2500000000 : ℝ)|^8239 ≤ (5474560765891/25000000000000 : ℝ)^6191
        have hw : |(798557681/2500000000 : ℝ)|=(798557681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28187/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
  have base51 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [sign2]
  have base53 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign3]
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
  have base61 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [sign5]
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
  have hpowlo : (0 : ℝ) ^ (4119/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4119 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4119*1^1024 ≤ 0^1024*1^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4119/1024 : ℝ) ≤ (100314069945103337/4000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4119 ≤ (100314069945103337/4000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4119*4000000000000000000^1024 ≤ 100314069945103337^1024*5^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 100314069945103337 4000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (100314069945103337/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4119 := by
      have hnat : (1 : ℕ)^1024*1^4119 ≤ 1^4119*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4100314069945103337/4000000000000000000 : ℝ) ≤ (5030883618574451/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (4100314069945103337/4000000000000000000 : ℝ)^1024 ≤ (5030883618574451/5000000000000000 : ℝ)^4119 := by
      have hnat : (4100314069945103337 : ℕ)^1024*5000000000000000^4119 ≤ 5030883618574451^4119*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4100314069945103337 4000000000000000000 5030883618574451 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5030883618574451/5000000000000000 : ℝ)) (X := (4100314069945103337/4000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2100314069945103337/2000000000000000000 : ℝ) ≤ (2530883618574451/2500000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (2100314069945103337/2000000000000000000 : ℝ)^1024 ≤ (2530883618574451/2500000000000000 : ℝ)^4119 := by
      have hnat : (2100314069945103337 : ℕ)^1024*2500000000000000^4119 ≤ 2530883618574451^4119*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2100314069945103337 2000000000000000000 2530883618574451 2500000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2530883618574451/2500000000000000 : ℝ)) (X := (2100314069945103337/2000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(30883618574451/2000000000000000 : ℝ)*(0 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30883618574451/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100314069945103337/4000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(30883618574451/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (1 : ℝ)+(30883618574451/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5030883618574451/5000000000000000 : ℝ) by norm_num, show 1+(100314069945103337/4000000000000000000 : ℝ)+(0 : ℝ)=(4100314069945103337/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100314069945103337/4000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(30883618574451/2000000000000000 : ℝ)*(2/5 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(30883618574451/2000000000000000 : ℝ)*(2/5 : ℝ)=(2530883618574451/2500000000000000 : ℝ) by norm_num, show 1+2*(100314069945103337/4000000000000000000 : ℝ)=(2100314069945103337/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(30883618574451/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30883618574451/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(30883618574451/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30883618574451/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(30883618574451/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (30883618574451/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-961280863/5000000000 : ℝ)*X 0 0+(1215357521/2000000000 : ℝ)*X 0 1+(1192054029/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5522205839/10000000000 : ℝ)*X 1 0+(-1338194271/5000000000 : ℝ)*X 1 1+(4768208669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((690275461/1250000000 : ℝ)*X 2 0+(2384105419/5000000000 : ℝ)*X 2 1+(-2676388649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((420886507/1000000000 : ℝ)*X 0 0+(625190911/2000000000 : ℝ)*X 0 1+(2840200313/5000000000 : ℝ)*X 0 2+(420886507/1000000000 : ℝ)*X 1 0+(625190911/2000000000 : ℝ)*X 1 1+(2840200313/5000000000 : ℝ)*X 1 2+(420886507/1000000000 : ℝ)*X 2 0+(625190911/2000000000 : ℝ)*X 2 1+(2840200313/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-482001199/2500000000 : ℝ)*X 0 0+(4802009157/10000000000 : ℝ)*X 0 1+(1510452069/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((645893033/1250000000 : ℝ)*X 1 0+(-1402796433/10000000000 : ℝ)*X 1 1+(6041808561/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5167142393/10000000000 : ℝ)*X 2 0+(6041810271/10000000000 : ℝ)*X 2 1+(-1402796541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1054869091/2500000000 : ℝ)*X 0 0+(701802957/1250000000 : ℝ)*X 0 1+(798557681/2500000000 : ℝ)*X 0 2+(1054869091/2500000000 : ℝ)*X 1 0+(701802957/1250000000 : ℝ)*X 1 1+(798557681/2500000000 : ℝ)*X 1 2+(1054869091/2500000000 : ℝ)*X 2 0+(701802957/1250000000 : ℝ)*X 2 1+(798557681/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1751896830206616382917/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (288853277/50000000000000 : ℝ)*(base1) + (206794561/25000000000000 : ℝ)*(base19) + (672502181/100000000000000 : ℝ)*(base23) + (148229/100000000000000 : ℝ)*(base51) + (82358857/20000000000000 : ℝ)*(base53) + (79110457/100000000000000 : ℝ)*(base59) + (188269333/50000000000000 : ℝ)*(base61) + (288916780648411/50000000000000 : ℝ)*(major0) + (288916780648411/50000000000000 : ℝ)*(major1) + (288916780648411/50000000000000 : ℝ)*(major2) + (95524060411279/12500000000000 : ℝ)*(sp0) + (382095539202717/50000000000000 : ℝ)*(sp1) + (764191233081497/100000000000000 : ℝ)*(sp2) + (48934329620943/12500000000000 : ℝ)*(sp3) + (195737607337049/50000000000000 : ℝ)*(f.failure) + (382095952791839/50000000000000 : ℝ)*(f.sum) + (247569875947361/50000000000000000000000000000 : ℝ)*base65 + (152277530347361/100000000000000000000000000000 : ℝ)*base67 + (390485112747361/100000000000000000000000000000 : ℝ)*base69 + (740249537747361/100000000000000000000000000000 : ℝ)*base71 + (67100026252639/50000000000000000000000000000 : ℝ)*base74 + (973712269347361/100000000000000000000000000000 : ℝ)*base75 + (1150866356747361/100000000000000000000000000000 : ℝ)*base77 + (482528517747361/100000000000000000000000000000 : ℝ)*base79 + (39636491202639/50000000000000000000000000000 : ℝ)*base82 + (2402481/1250000000000000000000 : ℝ)*base90 + (2402481/1250000000000000000000 : ℝ)*base92 + (2402481/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97599466454753252956029/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (207025891/50000000000000 : ℝ)*(base19) + (502375871/100000000000000 : ℝ)*(base23) + (349146017/100000000000000 : ℝ)*(base39) + (16286051/12500000000000 : ℝ)*(base45) + (4663499/12500000000000 : ℝ)*(upper2) + (137083361/100000000000000 : ℝ)*(upper5) + (121976835897751/20000000000000 : ℝ)*(major0) + (121976835897751/20000000000000 : ℝ)*(major1) + (304941915171369/50000000000000 : ℝ)*(major2) + (88864189/20000000000000 : ℝ)*(sp1) + (100822353226957/12500000000000 : ℝ)*(sp4) + (806577967442929/100000000000000 : ℝ)*(sp5) + (403289336292901/50000000000000 : ℝ)*(sp6) + (413189118949519/100000000000000 : ℝ)*(sp7) + (413189118949519/100000000000000 : ℝ)*(f.failure) + (403289587480837/50000000000000 : ℝ)*(f.sum) + (282759163014657/200000000000000000000000000000 : ℝ)*base66 + (592093195506581/100000000000000000000000000000 : ℝ)*base68 + (21661784479701/40000000000000000000000000000 : ℝ)*base69 + (459992452606581/100000000000000000000000000000 : ℝ)*base72 + (1021310018414657/200000000000000000000000000000 : ℝ)*base74 + (157373051759701/40000000000000000000000000000 : ℝ)*base75 + (30649507120299/40000000000000000000000000000 : ℝ)*base78 + (15530335280299/40000000000000000000000000000 : ℝ)*base80 + (48168800520299/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13054089/2500000000000000000000 : ℝ)*base89 + (13054089/2500000000000000000000 : ℝ)*base91 + (13054089/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1046_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28187/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1046_s1_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134135409/10000000000 : ℝ)*x 0 + (5727951483/10000000000 : ℝ)*x 1 + (1245385521/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134135409/10000000000 : ℝ)^8239 ≤ (12803441933169/100000000000000 : ℝ)^6191 := by
    have hnat : (2134135409 : ℕ)^8239*100000000000000^6191 ≤ 12803441933169^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134135409 10000000000 12803441933169 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5727951483/10000000000 : ℝ)^8239 ≤ (47637047560177/100000000000000 : ℝ)^6191 := by
    have hnat : (5727951483 : ℕ)^8239*100000000000000^6191 ≤ 47637047560177^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5727951483 10000000000 47637047560177 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1245385521/2500000000 : ℝ)^8239 ≤ (2472469405769/6250000000000 : ℝ)^6191 := by
    have hnat : (1245385521 : ℕ)^8239*6250000000000^6191 ≤ 2472469405769^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245385521 2500000000 2472469405769 6250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134135409/10000000000 : ℝ), (5727951483/10000000000 : ℝ), (1245385521/2500000000 : ℝ)] ![(12803441933169/100000000000000 : ℝ), (47637047560177/100000000000000 : ℝ), (2472469405769/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134135409/10000000000 : ℝ)|^8239 ≤ (12803441933169/100000000000000 : ℝ)^6191
        have hw : |(-2134135409/10000000000 : ℝ)|=(2134135409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5727951483/10000000000 : ℝ)|^8239 ≤ (47637047560177/100000000000000 : ℝ)^6191
        have hw : |(5727951483/10000000000 : ℝ)|=(5727951483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1245385521/2500000000 : ℝ)|^8239 ≤ (2472469405769/6250000000000 : ℝ)^6191
        have hw : |(1245385521/2500000000 : ℝ)|=(1245385521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s1_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5424415493/10000000000 : ℝ)*x 0 + (-1269487393/5000000000 : ℝ)*x 1 + (4981542407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424415493/10000000000 : ℝ)^8239 ≤ (44307389677119/100000000000000 : ℝ)^6191 := by
    have hnat : (5424415493 : ℕ)^8239*100000000000000^6191 ≤ 44307389677119^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424415493 10000000000 44307389677119 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1269487393/5000000000 : ℝ)^8239 ≤ (16133096397107/100000000000000 : ℝ)^6191 := by
    have hnat : (1269487393 : ℕ)^8239*100000000000000^6191 ≤ 16133096397107^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269487393 5000000000 16133096397107 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981542407/10000000000 : ℝ)^8239 ≤ (39559513905831/100000000000000 : ℝ)^6191 := by
    have hnat : (4981542407 : ℕ)^8239*100000000000000^6191 ≤ 39559513905831^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981542407 10000000000 39559513905831 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424415493/10000000000 : ℝ), (-1269487393/5000000000 : ℝ), (4981542407/10000000000 : ℝ)] ![(44307389677119/100000000000000 : ℝ), (16133096397107/100000000000000 : ℝ), (39559513905831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424415493/10000000000 : ℝ)|^8239 ≤ (44307389677119/100000000000000 : ℝ)^6191
        have hw : |(5424415493/10000000000 : ℝ)|=(5424415493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1269487393/5000000000 : ℝ)|^8239 ≤ (16133096397107/100000000000000 : ℝ)^6191
        have hw : |(-1269487393/5000000000 : ℝ)|=(1269487393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981542407/10000000000 : ℝ)|^8239 ≤ (39559513905831/100000000000000 : ℝ)^6191
        have hw : |(4981542407/10000000000 : ℝ)|=(4981542407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s1_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084883181/2000000000 : ℝ)*x 0 + (49815419/100000000 : ℝ)*x 1 + (-253897489/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084883181/2000000000 : ℝ)^8239 ≤ (8861478831127/20000000000000 : ℝ)^6191 := by
    have hnat : (1084883181 : ℕ)^8239*20000000000000^6191 ≤ 8861478831127^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084883181 2000000000 8861478831127 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49815419/100000000 : ℝ)^8239 ≤ (9889877136939/25000000000000 : ℝ)^6191 := by
    have hnat : (49815419 : ℕ)^8239*25000000000000^6191 ≤ 9889877136939^6191*100000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49815419 100000000 9889877136939 25000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253897489/1000000000 : ℝ)^8239 ≤ (16133097276547/100000000000000 : ℝ)^6191 := by
    have hnat : (253897489 : ℕ)^8239*100000000000000^6191 ≤ 16133097276547^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253897489 1000000000 16133097276547 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084883181/2000000000 : ℝ), (49815419/100000000 : ℝ), (-253897489/1000000000 : ℝ)] ![(8861478831127/20000000000000 : ℝ), (9889877136939/25000000000000 : ℝ), (16133097276547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084883181/2000000000 : ℝ)|^8239 ≤ (8861478831127/20000000000000 : ℝ)^6191
        have hw : |(1084883181/2000000000 : ℝ)|=(1084883181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49815419/100000000 : ℝ)|^8239 ≤ (9889877136939/25000000000000 : ℝ)^6191
        have hw : |(49815419/100000000 : ℝ)|=(49815419/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253897489/1000000000 : ℝ)|^8239 ≤ (16133097276547/100000000000000 : ℝ)^6191
        have hw : |(-253897489/1000000000 : ℝ)|=(253897489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s1_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1081363989/2500000000 : ℝ)*x 0 + (1829341869/5000000000 : ℝ)*x 1 + (511573513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081363989/2500000000 : ℝ)^8239 ≤ (6556321310879/20000000000000 : ℝ)^6191 := by
    have hnat : (1081363989 : ℕ)^8239*20000000000000^6191 ≤ 6556321310879^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081363989 2500000000 6556321310879 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1829341869/5000000000 : ℝ)^8239 ≤ (2623442343027/10000000000000 : ℝ)^6191 := by
    have hnat : (1829341869 : ℕ)^8239*10000000000000^6191 ≤ 2623442343027^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829341869 5000000000 2623442343027 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511573513/1000000000 : ℝ)^8239 ≤ (512299624987/1250000000000 : ℝ)^6191 := by
    have hnat : (511573513 : ℕ)^8239*1250000000000^6191 ≤ 512299624987^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511573513 1000000000 512299624987 1250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081363989/2500000000 : ℝ), (1829341869/5000000000 : ℝ), (511573513/1000000000 : ℝ)] ![(6556321310879/20000000000000 : ℝ), (2623442343027/10000000000000 : ℝ), (512299624987/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081363989/2500000000 : ℝ)|^8239 ≤ (6556321310879/20000000000000 : ℝ)^6191
        have hw : |(1081363989/2500000000 : ℝ)|=(1081363989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1829341869/5000000000 : ℝ)|^8239 ≤ (2623442343027/10000000000000 : ℝ)^6191
        have hw : |(1829341869/5000000000 : ℝ)|=(1829341869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(511573513/1000000000 : ℝ)|^8239 ≤ (512299624987/1250000000000 : ℝ)^6191
        have hw : |(511573513/1000000000 : ℝ)|=(511573513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s1_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-427017851/2000000000 : ℝ)*x 0 + (2496055193/5000000000 : ℝ)*x 1 + (2858582581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427017851/2000000000 : ℝ)^8239 ≤ (12811057966349/100000000000000 : ℝ)^6191 := by
    have hnat : (427017851 : ℕ)^8239*100000000000000^6191 ≤ 12811057966349^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427017851 2000000000 12811057966349 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2496055193/5000000000 : ℝ)^8239 ≤ (7934247507519/20000000000000 : ℝ)^6191 := by
    have hnat : (2496055193 : ℕ)^8239*20000000000000^6191 ≤ 7934247507519^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2496055193 5000000000 7934247507519 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858582581/5000000000 : ℝ)^8239 ≤ (4751770449193/10000000000000 : ℝ)^6191 := by
    have hnat : (2858582581 : ℕ)^8239*10000000000000^6191 ≤ 4751770449193^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858582581 5000000000 4751770449193 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427017851/2000000000 : ℝ), (2496055193/5000000000 : ℝ), (2858582581/5000000000 : ℝ)] ![(12811057966349/100000000000000 : ℝ), (7934247507519/20000000000000 : ℝ), (4751770449193/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427017851/2000000000 : ℝ)|^8239 ≤ (12811057966349/100000000000000 : ℝ)^6191
        have hw : |(-427017851/2000000000 : ℝ)|=(427017851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2496055193/5000000000 : ℝ)|^8239 ≤ (7934247507519/20000000000000 : ℝ)^6191
        have hw : |(2496055193/5000000000 : ℝ)|=(2496055193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858582581/5000000000 : ℝ)|^8239 ≤ (4751770449193/10000000000000 : ℝ)^6191
        have hw : |(2858582581/5000000000 : ℝ)|=(2858582581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s1_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5233995467/10000000000 : ℝ)*x 0 + (-450837593/2500000000 : ℝ)*x 1 + (2858583201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233995467/10000000000 : ℝ)^8239 ≤ (8449920564623/20000000000000 : ℝ)^6191 := by
    have hnat : (5233995467 : ℕ)^8239*20000000000000^6191 ≤ 8449920564623^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233995467 10000000000 8449920564623 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450837593/2500000000 : ℝ)^8239 ≤ (5116339478067/50000000000000 : ℝ)^6191 := by
    have hnat : (450837593 : ℕ)^8239*50000000000000^6191 ≤ 5116339478067^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450837593 2500000000 5116339478067 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858583201/5000000000 : ℝ)^8239 ≤ (47517718207381/100000000000000 : ℝ)^6191 := by
    have hnat : (2858583201 : ℕ)^8239*100000000000000^6191 ≤ 47517718207381^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858583201 5000000000 47517718207381 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233995467/10000000000 : ℝ), (-450837593/2500000000 : ℝ), (2858583201/5000000000 : ℝ)] ![(8449920564623/20000000000000 : ℝ), (5116339478067/50000000000000 : ℝ), (47517718207381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233995467/10000000000 : ℝ)|^8239 ≤ (8449920564623/20000000000000 : ℝ)^6191
        have hw : |(5233995467/10000000000 : ℝ)|=(5233995467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450837593/2500000000 : ℝ)|^8239 ≤ (5116339478067/50000000000000 : ℝ)^6191
        have hw : |(-450837593/2500000000 : ℝ)|=(450837593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858583201/5000000000 : ℝ)|^8239 ≤ (47517718207381/100000000000000 : ℝ)^6191
        have hw : |(2858583201/5000000000 : ℝ)|=(2858583201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s1_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5233993561/10000000000 : ℝ)*x 0 + (2858584247/5000000000 : ℝ)*x 1 + (-1803350019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233993561/10000000000 : ℝ)^8239 ≤ (42249582348023/100000000000000 : ℝ)^6191 := by
    have hnat : (5233993561 : ℕ)^8239*100000000000000^6191 ≤ 42249582348023^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233993561 10000000000 42249582348023 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2858584247/5000000000 : ℝ)^8239 ≤ (23758870673339/50000000000000 : ℝ)^6191 := by
    have hnat : (2858584247 : ℕ)^8239*50000000000000^6191 ≤ 23758870673339^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858584247 5000000000 23758870673339 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1803350019/10000000000 : ℝ)^8239 ≤ (5116338145259/50000000000000 : ℝ)^6191 := by
    have hnat : (1803350019 : ℕ)^8239*50000000000000^6191 ≤ 5116338145259^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803350019 10000000000 5116338145259 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233993561/10000000000 : ℝ), (2858584247/5000000000 : ℝ), (-1803350019/10000000000 : ℝ)] ![(42249582348023/100000000000000 : ℝ), (23758870673339/50000000000000 : ℝ), (5116338145259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233993561/10000000000 : ℝ)|^8239 ≤ (42249582348023/100000000000000 : ℝ)^6191
        have hw : |(5233993561/10000000000 : ℝ)|=(5233993561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2858584247/5000000000 : ℝ)|^8239 ≤ (23758870673339/50000000000000 : ℝ)^6191
        have hw : |(2858584247/5000000000 : ℝ)|=(2858584247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1803350019/10000000000 : ℝ)|^8239 ≤ (5116338145259/50000000000000 : ℝ)^6191
        have hw : |(-1803350019/10000000000 : ℝ)|=(1803350019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s1_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2163657377/5000000000 : ℝ)*x 0 + (2547550789/5000000000 : ℝ)*x 1 + (3679736861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163657377/5000000000 : ℝ)^8239 ≤ (32800355424481/100000000000000 : ℝ)^6191 := by
    have hnat : (2163657377 : ℕ)^8239*100000000000000^6191 ≤ 32800355424481^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163657377 5000000000 32800355424481 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2547550789/5000000000 : ℝ)^8239 ≤ (40764131583653/100000000000000 : ℝ)^6191 := by
    have hnat : (2547550789 : ℕ)^8239*100000000000000^6191 ≤ 40764131583653^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547550789 5000000000 40764131583653 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679736861/10000000000 : ℝ)^8239 ≤ (13217756490169/50000000000000 : ℝ)^6191 := by
    have hnat : (3679736861 : ℕ)^8239*50000000000000^6191 ≤ 13217756490169^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679736861 10000000000 13217756490169 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163657377/5000000000 : ℝ), (2547550789/5000000000 : ℝ), (3679736861/10000000000 : ℝ)] ![(32800355424481/100000000000000 : ℝ), (40764131583653/100000000000000 : ℝ), (13217756490169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163657377/5000000000 : ℝ)|^8239 ≤ (32800355424481/100000000000000 : ℝ)^6191
        have hw : |(2163657377/5000000000 : ℝ)|=(2163657377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2547550789/5000000000 : ℝ)|^8239 ≤ (40764131583653/100000000000000 : ℝ)^6191
        have hw : |(2547550789/5000000000 : ℝ)|=(2547550789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679736861/10000000000 : ℝ)|^8239 ≤ (13217756490169/50000000000000 : ℝ)^6191
        have hw : |(3679736861/10000000000 : ℝ)|=(3679736861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28187/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1019/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20887/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28187/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28187/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28187/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28187/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28187/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28187/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3/25000 : ℝ) ^ (4119/1024 : ℝ) ≤ (16931/100000000000000000000 : ℝ) := by
    have hpowers : (3/25000 : ℝ)^4119 ≤ (16931/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3 : ℕ)^4119*100000000000000000000^1024 ≤ 16931^1024*25000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 25000 16931 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3/25000 : ℝ)) (X := (16931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (28187/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (613540171851444279/100000000000000000000 : ℝ) := by
    have hpowers : (28187/100000 : ℝ)^4119 ≤ (613540171851444279/100000000000000000000 : ℝ)^1024 := by
      have hnat : (28187 : ℕ)^4119*100000000000000000000^1024 ≤ 613540171851444279^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28187 100000 613540171851444279 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28187/100000 : ℝ)) (X := (613540171851444279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000000016931/50000000000000000000 : ℝ) ≤ (10000000000000001/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50000000000000016931/50000000000000000000 : ℝ)^1024 ≤ (10000000000000001/10000000000000000 : ℝ)^4119 := by
      have hnat : (50000000000000016931 : ℕ)^1024*10000000000000000^4119 ≤ 10000000000000001^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000000016931 50000000000000000000 10000000000000001 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000001/10000000000000000 : ℝ)) (X := (50000000000000016931/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10061354017185146121/10000000000000000000 : ℝ) ≤ (500760891131031/500000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (10061354017185146121/10000000000000000000 : ℝ)^1024 ≤ (500760891131031/500000000000000 : ℝ)^4119 := by
      have hnat : (10061354017185146121 : ℕ)^1024*500000000000000^4119 ≤ 500760891131031^4119*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10061354017185146121 10000000000000000000 500760891131031 500000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500760891131031/500000000000000 : ℝ)) (X := (10061354017185146121/10000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50613540171851444279/50000000000000000000 : ℝ) ≤ (10030435645241239/10000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50613540171851444279/50000000000000000000 : ℝ)^1024 ≤ (10030435645241239/10000000000000000 : ℝ)^4119 := by
      have hnat : (50613540171851444279 : ℕ)^1024*10000000000000000^4119 ≤ 10030435645241239^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50613540171851444279 50000000000000000000 10030435645241239 10000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030435645241239/10000000000000000 : ℝ)) (X := (50613540171851444279/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(16931/100000000000000000000 : ℝ) ≤ ((281749634772257133319/281750000000000000000 : ℝ)+2*(15217822620619/2817500000000000 : ℝ)*(3/25000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (281749634772257133319/281750000000000000000 : ℝ)+2*(15217822620619/2817500000000000 : ℝ)*(3/25000 : ℝ)=(10000000000000001/10000000000000000 : ℝ) by norm_num, show 1+2*(16931/100000000000000000000 : ℝ)=(50000000000000016931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(613540171851444279/100000000000000000000 : ℝ)+(16931/100000000000000000000 : ℝ) ≤ ((281749634772257133319/281750000000000000000 : ℝ)+(15217822620619/2817500000000000 : ℝ)*((28187/100000 : ℝ)+(3/25000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (281749634772257133319/281750000000000000000 : ℝ)+(15217822620619/2817500000000000 : ℝ)*((28187/100000 : ℝ)+(3/25000 : ℝ))=(500760891131031/500000000000000 : ℝ) by norm_num, show 1+(613540171851444279/100000000000000000000 : ℝ)+(16931/100000000000000000000 : ℝ)=(10061354017185146121/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(613540171851444279/100000000000000000000 : ℝ) ≤ ((281749634772257133319/281750000000000000000 : ℝ)+2*(15217822620619/2817500000000000 : ℝ)*(28187/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (281749634772257133319/281750000000000000000 : ℝ)+2*(15217822620619/2817500000000000 : ℝ)*(28187/100000 : ℝ)=(10030435645241239/10000000000000000 : ℝ) by norm_num, show 1+2*(613540171851444279/100000000000000000000 : ℝ)=(50613540171851444279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (281749634772257133319/281750000000000000000 : ℝ)*(X 1 0+X 2 0)+(15217822620619/2817500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (3/25000 : ℝ)) (hi := (28187/100000 : ℝ)) (c := (281749634772257133319/281750000000000000000 : ℝ)) (alpha := (15217822620619/2817500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (281749634772257133319/281750000000000000000 : ℝ)*(X 0 1+X 2 1)+(15217822620619/2817500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (3/25000 : ℝ)) (hi := (28187/100000 : ℝ)) (c := (281749634772257133319/281750000000000000000 : ℝ)) (alpha := (15217822620619/2817500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (281749634772257133319/281750000000000000000 : ℝ)*(X 0 2+X 1 2)+(15217822620619/2817500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (3/25000 : ℝ)) (hi := (28187/100000 : ℝ)) (c := (281749634772257133319/281750000000000000000 : ℝ)) (alpha := (15217822620619/2817500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2134135409/10000000000 : ℝ)*X 0 0+(5727951483/10000000000 : ℝ)*X 0 1+(1245385521/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5424415493/10000000000 : ℝ)*X 1 0+(-1269487393/5000000000 : ℝ)*X 1 1+(4981542407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1084883181/2000000000 : ℝ)*X 2 0+(49815419/100000000 : ℝ)*X 2 1+(-253897489/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081363989/2500000000 : ℝ)*X 0 0+(1829341869/5000000000 : ℝ)*X 0 1+(511573513/1000000000 : ℝ)*X 0 2+(1081363989/2500000000 : ℝ)*X 1 0+(1829341869/5000000000 : ℝ)*X 1 1+(511573513/1000000000 : ℝ)*X 1 2+(1081363989/2500000000 : ℝ)*X 2 0+(1829341869/5000000000 : ℝ)*X 2 1+(511573513/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-427017851/2000000000 : ℝ)*X 0 0+(2496055193/5000000000 : ℝ)*X 0 1+(2858582581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5233995467/10000000000 : ℝ)*X 1 0+(-450837593/2500000000 : ℝ)*X 1 1+(2858583201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5233993561/10000000000 : ℝ)*X 2 0+(2858584247/5000000000 : ℝ)*X 2 1+(-1803350019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163657377/5000000000 : ℝ)*X 0 0+(2547550789/5000000000 : ℝ)*X 0 1+(3679736861/10000000000 : ℝ)*X 0 2+(2163657377/5000000000 : ℝ)*X 1 0+(2547550789/5000000000 : ℝ)*X 1 1+(3679736861/10000000000 : ℝ)*X 1 2+(2163657377/5000000000 : ℝ)*X 2 0+(2547550789/5000000000 : ℝ)*X 2 1+(3679736861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7502842786735605204455988321/1760937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41845101/50000000000000 : ℝ)*(base1) + (479532691/50000000000000 : ℝ)*(base19) + (530411863/50000000000000 : ℝ)*(base23) + (53106153/50000000000000 : ℝ)*(upper3) + (99311159/100000000000000 : ℝ)*(upper5) + (253259931475853/25000000000000 : ℝ)*(major0) + (253259931475853/25000000000000 : ℝ)*(major1) + (253259931475853/25000000000000 : ℝ)*(major2) + (20933627677871/1562500000000 : ℝ)*(sp0) + (334939062276341/25000000000000 : ℝ)*(sp1) + (66987807367351/5000000000000 : ℝ)*(sp2) + (27452788256573/4000000000000 : ℝ)*(sp3) + (5120477203/100000000000000 : ℝ)*(sp4) + (2311507901/100000000000000 : ℝ)*(sp7) + (686322101612427/100000000000000 : ℝ)*(f.failure) + (669878604085373/50000000000000 : ℝ)*(f.sum) + (664129934361847/140875000000000000000000000000 : ℝ)*base66 + (23855040168586553893/7043750000000000000000000000000000 : ℝ)*base68 + (420377437757196107/7043750000000000000000000000000000 : ℝ)*base69 + (67253754576936553893/7043750000000000000000000000000000 : ℝ)*base72 + (58262153989559/17609375000000000000000000000 : ℝ)*base74 + (52554868720255303893/7043750000000000000000000000000000 : ℝ)*base76 + (31833191616286553893/7043750000000000000000000000000000 : ℝ)*base78 + (101270890992524053893/7043750000000000000000000000000000 : ℝ)*base80 + (154043003072597/140875000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (18712237/2500000000000000000000 : ℝ)*base89 + (18712237/2500000000000000000000 : ℝ)*base91 + (18712237/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4006843513190949732776738169/1006250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (630641623/25000000000000 : ℝ)*(base19) + (2373598443/100000000000000 : ℝ)*(base23) + (86198299/50000000000000 : ℝ)*(upper2) + (366765487/100000000000000 : ℝ)*(upper3) + (507856263/100000000000000 : ℝ)*(upper5) + (521434068774019/50000000000000 : ℝ)*(major0) + (521434068774019/50000000000000 : ℝ)*(major1) + (521434068774019/50000000000000 : ℝ)*(major2) + (12025562957/100000000000000 : ℝ)*(sp1) + (3170590889/25000000000000 : ℝ)*(sp2) + (275841130880601/20000000000000 : ℝ)*(sp4) + (1379191106273557/100000000000000 : ℝ)*(sp5) + (275838119688201/20000000000000 : ℝ)*(sp6) + (706530487961189/100000000000000 : ℝ)*(sp7) + (706530487961189/100000000000000 : ℝ)*(f.failure) + (275841130880601/20000000000000 : ℝ)*(f.sum) + (231935197871603/140875000000000000000000000000 : ℝ)*base66 + (19527603097492539061/14087500000000000000000000000000000 : ℝ)*base67 + (43858164460119960939/14087500000000000000000000000000000 : ℝ)*base70 + (95419004543232460939/14087500000000000000000000000000000 : ℝ)*base72 + (227452573262011/70437500000000000000000000000 : ℝ)*base73 + (153052315442382460939/14087500000000000000000000000000000 : ℝ)*base76 + (16098885908919960939/14087500000000000000000000000000000 : ℝ)*base78 + (66571640930242539061/14087500000000000000000000000000000 : ℝ)*base79 + (5316925733557/35218750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (12085859/2500000000000000000000 : ℝ)*base89 + (12085859/2500000000000000000000 : ℝ)*base91 + (12085859/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1046_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28187/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1019/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20887/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1046_s2_0 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2192688509/10000000000 : ℝ)*x 0 + (553008903/1000000000 : ℝ)*x 1 + (514227777/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2192688509/10000000000 : ℝ)^8239 ≤ (1327303628667/10000000000000 : ℝ)^6191 := by
    have hnat : (2192688509 : ℕ)^8239*10000000000000^6191 ≤ 1327303628667^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2192688509 10000000000 1327303628667 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553008903/1000000000 : ℝ)^8239 ≤ (22729882939363/50000000000000 : ℝ)^6191 := by
    have hnat : (553008903 : ℕ)^8239*50000000000000^6191 ≤ 22729882939363^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553008903 1000000000 22729882939363 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (514227777/1000000000 : ℝ)^8239 ≤ (1031679945321/2500000000000 : ℝ)^6191 := by
    have hnat : (514227777 : ℕ)^8239*2500000000000^6191 ≤ 1031679945321^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514227777 1000000000 1031679945321 2500000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2192688509/10000000000 : ℝ), (553008903/1000000000 : ℝ), (514227777/1000000000 : ℝ)] ![(1327303628667/10000000000000 : ℝ), (22729882939363/50000000000000 : ℝ), (1031679945321/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2192688509/10000000000 : ℝ)|^8239 ≤ (1327303628667/10000000000000 : ℝ)^6191
        have hw : |(-2192688509/10000000000 : ℝ)|=(2192688509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553008903/1000000000 : ℝ)|^8239 ≤ (22729882939363/50000000000000 : ℝ)^6191
        have hw : |(553008903/1000000000 : ℝ)|=(553008903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(514227777/1000000000 : ℝ)|^8239 ≤ (1031679945321/2500000000000 : ℝ)^6191
        have hw : |(514227777/1000000000 : ℝ)|=(514227777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s2_1 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5378104041/10000000000 : ℝ)*x 0 + (-1197555311/5000000000 : ℝ)*x 1 + (5142278407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378104041/10000000000 : ℝ)^8239 ≤ (21902343946739/50000000000000 : ℝ)^6191 := by
    have hnat : (5378104041 : ℕ)^8239*50000000000000^6191 ≤ 21902343946739^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378104041 10000000000 21902343946739 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1197555311/5000000000 : ℝ)^8239 ≤ (7464053739341/50000000000000 : ℝ)^6191 := by
    have hnat : (1197555311 : ℕ)^8239*50000000000000^6191 ≤ 7464053739341^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197555311 5000000000 7464053739341 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142278407/10000000000 : ℝ)^8239 ≤ (41267204615873/100000000000000 : ℝ)^6191 := by
    have hnat : (5142278407 : ℕ)^8239*100000000000000^6191 ≤ 41267204615873^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142278407 10000000000 41267204615873 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378104041/10000000000 : ℝ), (-1197555311/5000000000 : ℝ), (5142278407/10000000000 : ℝ)] ![(21902343946739/50000000000000 : ℝ), (7464053739341/50000000000000 : ℝ), (41267204615873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378104041/10000000000 : ℝ)|^8239 ≤ (21902343946739/50000000000000 : ℝ)^6191
        have hw : |(5378104041/10000000000 : ℝ)|=(5378104041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1197555311/5000000000 : ℝ)|^8239 ≤ (7464053739341/50000000000000 : ℝ)^6191
        have hw : |(-1197555311/5000000000 : ℝ)|=(1197555311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142278407/10000000000 : ℝ)|^8239 ≤ (41267204615873/100000000000000 : ℝ)^6191
        have hw : |(5142278407/10000000000 : ℝ)|=(5142278407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s2_2 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (537810417/1000000000 : ℝ)*x 0 + (257113921/500000000 : ℝ)*x 1 + (-598777609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537810417/1000000000 : ℝ)^8239 ≤ (547558616147/1250000000000 : ℝ)^6191 := by
    have hnat : (537810417 : ℕ)^8239*1250000000000^6191 ≤ 547558616147^6191*1000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537810417 1000000000 547558616147 1250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257113921/500000000 : ℝ)^8239 ≤ (41267204754711/100000000000000 : ℝ)^6191 := by
    have hnat : (257113921 : ℕ)^8239*100000000000000^6191 ≤ 41267204754711^6191*500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257113921 500000000 41267204754711 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598777609/2500000000 : ℝ)^8239 ≤ (2985621187179/20000000000000 : ℝ)^6191 := by
    have hnat : (598777609 : ℕ)^8239*20000000000000^6191 ≤ 2985621187179^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598777609 2500000000 2985621187179 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537810417/1000000000 : ℝ), (257113921/500000000 : ℝ), (-598777609/2500000000 : ℝ)] ![(547558616147/1250000000000 : ℝ), (41267204754711/100000000000000 : ℝ), (2985621187179/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537810417/1000000000 : ℝ)|^8239 ≤ (547558616147/1250000000000 : ℝ)^6191
        have hw : |(537810417/1000000000 : ℝ)|=(537810417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257113921/500000000 : ℝ)|^8239 ≤ (41267204754711/100000000000000 : ℝ)^6191
        have hw : |(257113921/500000000 : ℝ)|=(257113921/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-598777609/2500000000 : ℝ)|^8239 ≤ (2985621187179/20000000000000 : ℝ)^6191
        have hw : |(-598777609/2500000000 : ℝ)|=(598777609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s2_3 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182675043/5000000000 : ℝ)*x 0 + (4003457629/10000000000 : ℝ)*x 1 + (4760494859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182675043/5000000000 : ℝ)^8239 ≤ (1659229244491/5000000000000 : ℝ)^6191 := by
    have hnat : (2182675043 : ℕ)^8239*5000000000000^6191 ≤ 1659229244491^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182675043 5000000000 1659229244491 5000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4003457629/10000000000 : ℝ)^8239 ≤ (29574656433677/100000000000000 : ℝ)^6191 := by
    have hnat : (4003457629 : ℕ)^8239*100000000000000^6191 ≤ 29574656433677^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4003457629 10000000000 29574656433677 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4760494859/10000000000 : ℝ)^8239 ≤ (37240758662243/100000000000000 : ℝ)^6191 := by
    have hnat : (4760494859 : ℕ)^8239*100000000000000^6191 ≤ 37240758662243^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4760494859 10000000000 37240758662243 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182675043/5000000000 : ℝ), (4003457629/10000000000 : ℝ), (4760494859/10000000000 : ℝ)] ![(1659229244491/5000000000000 : ℝ), (29574656433677/100000000000000 : ℝ), (37240758662243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182675043/5000000000 : ℝ)|^8239 ≤ (1659229244491/5000000000000 : ℝ)^6191
        have hw : |(2182675043/5000000000 : ℝ)|=(2182675043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4003457629/10000000000 : ℝ)|^8239 ≤ (29574656433677/100000000000000 : ℝ)^6191
        have hw : |(4003457629/10000000000 : ℝ)|=(4003457629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4760494859/10000000000 : ℝ)|^8239 ≤ (37240758662243/100000000000000 : ℝ)^6191
        have hw : |(4760494859/10000000000 : ℝ)|=(4760494859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s2_4 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-438564259/2000000000 : ℝ)*x 0 + (1029027851/2000000000 : ℝ)*x 1 + (5527197261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438564259/2000000000 : ℝ)^8239 ≤ (2654821198163/20000000000000 : ℝ)^6191 := by
    have hnat : (438564259 : ℕ)^8239*20000000000000^6191 ≤ 2654821198163^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438564259 2000000000 2654821198163 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1029027851/2000000000 : ℝ)^8239 ≤ (41297760714611/100000000000000 : ℝ)^6191 := by
    have hnat : (1029027851 : ℕ)^8239*100000000000000^6191 ≤ 41297760714611^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029027851 2000000000 41297760714611 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527197261/10000000000 : ℝ)^8239 ≤ (45428133285283/100000000000000 : ℝ)^6191 := by
    have hnat : (5527197261 : ℕ)^8239*100000000000000^6191 ≤ 45428133285283^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527197261 10000000000 45428133285283 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438564259/2000000000 : ℝ), (1029027851/2000000000 : ℝ), (5527197261/10000000000 : ℝ)] ![(2654821198163/20000000000000 : ℝ), (41297760714611/100000000000000 : ℝ), (45428133285283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438564259/2000000000 : ℝ)|^8239 ≤ (2654821198163/20000000000000 : ℝ)^6191
        have hw : |(-438564259/2000000000 : ℝ)|=(438564259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1029027851/2000000000 : ℝ)|^8239 ≤ (41297760714611/100000000000000 : ℝ)^6191
        have hw : |(1029027851/2000000000 : ℝ)|=(1029027851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527197261/10000000000 : ℝ)|^8239 ≤ (45428133285283/100000000000000 : ℝ)^6191
        have hw : |(5527197261/10000000000 : ℝ)|=(5527197261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s2_5 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320088927/2500000000 : ℝ)*x 0 + (-1005095903/5000000000 : ℝ)*x 1 + (1381799331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320088927/2500000000 : ℝ)^8239 ≤ (42748353177949/100000000000000 : ℝ)^6191 := by
    have hnat : (1320088927 : ℕ)^8239*100000000000000^6191 ≤ 42748353177949^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320088927 2500000000 42748353177949 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005095903/5000000000 : ℝ)^8239 ≤ (11823512832697/100000000000000 : ℝ)^6191 := by
    have hnat : (1005095903 : ℕ)^8239*100000000000000^6191 ≤ 11823512832697^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005095903 5000000000 11823512832697 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1381799331/2500000000 : ℝ)^8239 ≤ (4542813397437/10000000000000 : ℝ)^6191 := by
    have hnat : (1381799331 : ℕ)^8239*10000000000000^6191 ≤ 4542813397437^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381799331 2500000000 4542813397437 10000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320088927/2500000000 : ℝ), (-1005095903/5000000000 : ℝ), (1381799331/2500000000 : ℝ)] ![(42748353177949/100000000000000 : ℝ), (11823512832697/100000000000000 : ℝ), (4542813397437/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320088927/2500000000 : ℝ)|^8239 ≤ (42748353177949/100000000000000 : ℝ)^6191
        have hw : |(1320088927/2500000000 : ℝ)|=(1320088927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005095903/5000000000 : ℝ)|^8239 ≤ (11823512832697/100000000000000 : ℝ)^6191
        have hw : |(-1005095903/5000000000 : ℝ)|=(1005095903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1381799331/2500000000 : ℝ)|^8239 ≤ (4542813397437/10000000000000 : ℝ)^6191
        have hw : |(1381799331/2500000000 : ℝ)|=(1381799331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s2_6 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320088983/2500000000 : ℝ)*x 0 + (1105439433/2000000000 : ℝ)*x 1 + (-2010191719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320088983/2500000000 : ℝ)^8239 ≤ (8549671118257/20000000000000 : ℝ)^6191 := by
    have hnat : (1320088983 : ℕ)^8239*20000000000000^6191 ≤ 8549671118257^6191*2500000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320088983 2500000000 8549671118257 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105439433/2000000000 : ℝ)^8239 ≤ (9085626447049/20000000000000 : ℝ)^6191 := by
    have hnat : (1105439433 : ℕ)^8239*20000000000000^6191 ≤ 9085626447049^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105439433 2000000000 9085626447049 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2010191719/10000000000 : ℝ)^8239 ≤ (2364702430341/20000000000000 : ℝ)^6191 := by
    have hnat : (2010191719 : ℕ)^8239*20000000000000^6191 ≤ 2364702430341^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010191719 10000000000 2364702430341 20000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320088983/2500000000 : ℝ), (1105439433/2000000000 : ℝ), (-2010191719/10000000000 : ℝ)] ![(8549671118257/20000000000000 : ℝ), (9085626447049/20000000000000 : ℝ), (2364702430341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320088983/2500000000 : ℝ)|^8239 ≤ (8549671118257/20000000000000 : ℝ)^6191
        have hw : |(1320088983/2500000000 : ℝ)|=(1320088983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105439433/2000000000 : ℝ)|^8239 ≤ (9085626447049/20000000000000 : ℝ)^6191
        have hw : |(1105439433/2000000000 : ℝ)|=(1105439433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2010191719/10000000000 : ℝ)|^8239 ≤ (2364702430341/20000000000000 : ℝ)^6191
        have hw : |(-2010191719/10000000000 : ℝ)|=(2010191719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1046_s2_7 (p : ℝ) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873121947/2000000000 : ℝ)*x 0 + (2377455249/5000000000 : ℝ)*x 1 + (4009101621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873121947/2000000000 : ℝ)^8239 ≤ (33187211659149/100000000000000 : ℝ)^6191 := by
    have hnat : (873121947 : ℕ)^8239*100000000000000^6191 ≤ 33187211659149^6191*2000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873121947 2000000000 33187211659149 100000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2377455249/5000000000 : ℝ)^8239 ≤ (18591316406661/50000000000000 : ℝ)^6191 := by
    have hnat : (2377455249 : ℕ)^8239*50000000000000^6191 ≤ 18591316406661^6191*5000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2377455249 5000000000 18591316406661 50000000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4009101621/10000000000 : ℝ)^8239 ≤ (1851884719613/6250000000000 : ℝ)^6191 := by
    have hnat : (4009101621 : ℕ)^8239*6250000000000^6191 ≤ 1851884719613^6191*10000000000^8239 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009101621 10000000000 1851884719613 6250000000000 8239 6191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8239/2048 : ℝ)) 8239 6191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873121947/2000000000 : ℝ), (2377455249/5000000000 : ℝ), (4009101621/10000000000 : ℝ)] ![(33187211659149/100000000000000 : ℝ), (18591316406661/50000000000000 : ℝ), (1851884719613/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873121947/2000000000 : ℝ)|^8239 ≤ (33187211659149/100000000000000 : ℝ)^6191
        have hw : |(873121947/2000000000 : ℝ)|=(873121947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2377455249/5000000000 : ℝ)|^8239 ≤ (18591316406661/50000000000000 : ℝ)^6191
        have hw : |(2377455249/5000000000 : ℝ)|=(2377455249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4009101621/10000000000 : ℝ)|^8239 ≤ (1851884719613/6250000000000 : ℝ)^6191
        have hw : |(4009101621/10000000000 : ℝ)|=(4009101621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1046_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20887/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1019/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8613/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2101/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20887/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1019/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20887/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1019/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20887/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1019/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20887/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1019/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20887/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1019/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20887/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1019/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1019/20000 : ℝ) ^ (4119/1024 : ℝ) ≤ (630286492224709/100000000000000000000 : ℝ) := by
    have hpowers : (1019/20000 : ℝ)^4119 ≤ (630286492224709/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1019 : ℕ)^4119*100000000000000000000^1024 ≤ 630286492224709^1024*20000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1019 20000 630286492224709 100000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1019/20000 : ℝ)) (X := (630286492224709/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (20887/100000 : ℝ) ^ (4119/1024 : ℝ) ≤ (36750059068459471/20000000000000000000 : ℝ) := by
    have hpowers : (20887/100000 : ℝ)^4119 ≤ (36750059068459471/20000000000000000000 : ℝ)^1024 := by
      have hnat : (20887 : ℕ)^4119*20000000000000000000^1024 ≤ 36750059068459471^1024*100000^4119 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20887 100000 36750059068459471 20000000000000000000 4119 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20887/100000 : ℝ)) (X := (36750059068459471/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000630286492224709/50000000000000000000 : ℝ) ≤ (5000015669102001/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (50000630286492224709/50000000000000000000 : ℝ)^1024 ≤ (5000015669102001/5000000000000000 : ℝ)^4119 := by
      have hnat : (50000630286492224709 : ℕ)^1024*5000000000000000^4119 ≤ 5000015669102001^4119*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000630286492224709 50000000000000000000 5000015669102001 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015669102001/5000000000000000 : ℝ)) (X := (50000630286492224709/50000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6261523786364657629/6250000000000000000 : ℝ) ≤ (5002290301869569/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (6261523786364657629/6250000000000000000 : ℝ)^1024 ≤ (5002290301869569/5000000000000000 : ℝ)^4119 := by
      have hnat : (6261523786364657629 : ℕ)^1024*5000000000000000^4119 ≤ 5002290301869569^4119*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6261523786364657629 6250000000000000000 5002290301869569 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002290301869569/5000000000000000 : ℝ)) (X := (6261523786364657629/6250000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10036750059068459471/10000000000000000000 : ℝ) ≤ (5004564934637137/5000000000000000 : ℝ) ^ (4119/1024 : ℝ) := by
    have hpowers : (10036750059068459471/10000000000000000000 : ℝ)^1024 ≤ (5004564934637137/5000000000000000 : ℝ)^4119 := by
      have hnat : (10036750059068459471 : ℕ)^1024*5000000000000000^4119 ≤ 5004564934637137^4119*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10036750059068459471 10000000000000000000 5004564934637137 5000000000000000 1024 4119 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004564934637137/5000000000000000 : ℝ)) (X := (10036750059068459471/10000000000000000000 : ℝ)) (by norm_num) 4119 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(630286492224709/100000000000000000000 : ℝ) ≤ ((704795258379975731/705000000000000000 : ℝ)+2*(20309221139/7050000000000 : ℝ)*(1019/20000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (704795258379975731/705000000000000000 : ℝ)+2*(20309221139/7050000000000 : ℝ)*(1019/20000 : ℝ)=(5000015669102001/5000000000000000 : ℝ) by norm_num, show 1+2*(630286492224709/100000000000000000000 : ℝ)=(50000630286492224709/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36750059068459471/20000000000000000000 : ℝ)+(630286492224709/100000000000000000000 : ℝ) ≤ ((704795258379975731/705000000000000000 : ℝ)+(20309221139/7050000000000 : ℝ)*((20887/100000 : ℝ)+(1019/20000 : ℝ)))^(4119/1024 : ℝ) := by
    rw [show (704795258379975731/705000000000000000 : ℝ)+(20309221139/7050000000000 : ℝ)*((20887/100000 : ℝ)+(1019/20000 : ℝ))=(5002290301869569/5000000000000000 : ℝ) by norm_num, show 1+(36750059068459471/20000000000000000000 : ℝ)+(630286492224709/100000000000000000000 : ℝ)=(6261523786364657629/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36750059068459471/20000000000000000000 : ℝ) ≤ ((704795258379975731/705000000000000000 : ℝ)+2*(20309221139/7050000000000 : ℝ)*(20887/100000 : ℝ))^(4119/1024 : ℝ) := by
    rw [show (704795258379975731/705000000000000000 : ℝ)+2*(20309221139/7050000000000 : ℝ)*(20887/100000 : ℝ)=(5004564934637137/5000000000000000 : ℝ) by norm_num, show 1+2*(36750059068459471/20000000000000000000 : ℝ)=(10036750059068459471/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (704795258379975731/705000000000000000 : ℝ)*(X 1 0+X 2 0)+(20309221139/7050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1019/20000 : ℝ)) (hi := (20887/100000 : ℝ)) (c := (704795258379975731/705000000000000000 : ℝ)) (alpha := (20309221139/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (704795258379975731/705000000000000000 : ℝ)*(X 0 1+X 2 1)+(20309221139/7050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1019/20000 : ℝ)) (hi := (20887/100000 : ℝ)) (c := (704795258379975731/705000000000000000 : ℝ)) (alpha := (20309221139/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (704795258379975731/705000000000000000 : ℝ)*(X 0 2+X 1 2)+(20309221139/7050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4119/1024 : ℝ)) (lo := (1019/20000 : ℝ)) (hi := (20887/100000 : ℝ)) (c := (704795258379975731/705000000000000000 : ℝ)) (alpha := (20309221139/7050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2192688509/10000000000 : ℝ)*X 0 0+(553008903/1000000000 : ℝ)*X 0 1+(514227777/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378104041/10000000000 : ℝ)*X 1 0+(-1197555311/5000000000 : ℝ)*X 1 1+(5142278407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537810417/1000000000 : ℝ)*X 2 0+(257113921/500000000 : ℝ)*X 2 1+(-598777609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2182675043/5000000000 : ℝ)*X 0 0+(4003457629/10000000000 : ℝ)*X 0 1+(4760494859/10000000000 : ℝ)*X 0 2+(2182675043/5000000000 : ℝ)*X 1 0+(4003457629/10000000000 : ℝ)*X 1 1+(4760494859/10000000000 : ℝ)*X 1 2+(2182675043/5000000000 : ℝ)*X 2 0+(4003457629/10000000000 : ℝ)*X 2 1+(4760494859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-438564259/2000000000 : ℝ)*X 0 0+(1029027851/2000000000 : ℝ)*X 0 1+(5527197261/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320088927/2500000000 : ℝ)*X 1 0+(-1005095903/5000000000 : ℝ)*X 1 1+(1381799331/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1320088983/2500000000 : ℝ)*X 2 0+(1105439433/2000000000 : ℝ)*X 2 1+(-2010191719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873121947/2000000000 : ℝ)*X 0 0+(2377455249/5000000000 : ℝ)*X 0 1+(4009101621/10000000000 : ℝ)*X 0 2+(873121947/2000000000 : ℝ)*X 1 0+(2377455249/5000000000 : ℝ)*X 1 1+(4009101621/10000000000 : ℝ)*X 1 2+(873121947/2000000000 : ℝ)*X 2 0+(2377455249/5000000000 : ℝ)*X 2 1+(4009101621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1046_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22094950590553069475713427/11750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (367845599/50000000000000 : ℝ)*(base19) + (34091591/5000000000000 : ℝ)*(base23) + (44379983/50000000000000 : ℝ)*(upper3) + (62229999/100000000000000 : ℝ)*(upper4) + (24134939/20000000000000 : ℝ)*(upper5) + (1949770280634661/100000000000000 : ℝ)*(major0) + (1949770280634661/100000000000000 : ℝ)*(major1) + (1949770280634661/100000000000000 : ℝ)*(major2) + (322322948187793/12500000000000 : ℝ)*(sp0) + (257859409566479/10000000000000 : ℝ)*(sp1) + (322324268690521/12500000000000 : ℝ)*(sp2) + (660471143365289/50000000000000 : ℝ)*(sp3) + (2249170729/20000000000000 : ℝ)*(sp4) + (84512551/2500000000000 : ℝ)*(sp7) + (660472833616309/50000000000000 : ℝ)*(f.failure) + (644648707838997/25000000000000 : ℝ)*(f.sum) + (119451786827/705000000000000000000000000 : ℝ)*base66 + (681245400816812191/70500000000000000000000000000000 : ℝ)*base67 + (214524946371812191/70500000000000000000000000000000 : ℝ)*base69 + (112240660736312191/70500000000000000000000000000000 : ℝ)*base71 + (396088605731/88125000000000000000000000 : ℝ)*base73 + (225647709869312191/70500000000000000000000000000000 : ℝ)*base75 + (552431086751312191/70500000000000000000000000000000 : ℝ)*base77 + (123813620384312191/70500000000000000000000000000000 : ℝ)*base79 + (29776765891/22031250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1985421/1250000000000000000000 : ℝ)*base90 + (1985421/1250000000000000000000 : ℝ)*base92 + (1985421/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12119543495584716269771031/1175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2009958661/100000000000000 : ℝ)*(base19) + (226919661/10000000000000 : ℝ)*(base23) + (126676673/50000000000000 : ℝ)*(upper3) + (5730431/10000000000000 : ℝ)*(lower4) + (229690979/100000000000000 : ℝ)*(upper5) + (395822984203699/20000000000000 : ℝ)*(major0) + (395822984203699/20000000000000 : ℝ)*(major1) + (395822984203699/20000000000000 : ℝ)*(major2) + (215029423/1250000000000 : ℝ)*(sp1) + (9672957407/50000000000000 : ℝ)*(sp2) + (26174031937881/1000000000000 : ℝ)*(sp4) + (1308691990737799/50000000000000 : ℝ)*(sp5) + (104695263147067/4000000000000 : ℝ)*(sp6) + (670413152216023/50000000000000 : ℝ)*(sp7) + (670413152216023/50000000000000 : ℝ)*(f.failure) + (26174031937881/1000000000000 : ℝ)*(f.sum) + (44969338847/35250000000000000000000000 : ℝ)*base66 + (50148026856271031/14100000000000000000000000000000 : ℝ)*base68 + (82104949905928969/14100000000000000000000000000000 : ℝ)*base69 + (29985597557128969/14100000000000000000000000000000 : ℝ)*base71 + (422134827859/70500000000000000000000000 : ℝ)*base74 + (35461606604728969/14100000000000000000000000000000 : ℝ)*base75 + (66552824407528969/14100000000000000000000000000000 : ℝ)*base77 + (87464099098228969/14100000000000000000000000000000 : ℝ)*base79 + (110802285161/28200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4080287/1250000000000000000000 : ℝ)*base90 + (4080287/1250000000000000000000 : ℝ)*base92 + (4080287/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1046_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20887/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1019/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2101/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1046_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1046_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2101/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1046_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1046_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1046_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4119/1024 : ℝ) ≤ p) (hpb : p ≤ (8239/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36901031/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8613/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2101/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1046_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
