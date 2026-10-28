-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1295_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:27:36.367409+00:00
-- url     : https://prove2.me/submissions/ab1ab64d-867b-40b0-82d1-9397df4947d2

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
theorem support_rectangle_w1295_s0_0 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1837260513/10000000000 : ℝ)*x 0 + (752183059/1250000000 : ℝ)*x 1 + (1199893077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1837260513/10000000000 : ℝ)^4255 ≤ (2147803564581/20000000000000 : ℝ)^3231 := by
    have hnat : (1837260513 : ℕ)^4255*20000000000000^3231 ≤ 2147803564581^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837260513 10000000000 2147803564581 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (752183059/1250000000 : ℝ)^4255 ≤ (51227495409011/100000000000000 : ℝ)^3231 := by
    have hnat : (752183059 : ℕ)^4255*100000000000000^3231 ≤ 51227495409011^3231*1250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752183059 1250000000 51227495409011 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199893077/2500000000 : ℝ)^4255 ≤ (38033486746267/100000000000000 : ℝ)^3231 := by
    have hnat : (1199893077 : ℕ)^4255*100000000000000^3231 ≤ 38033486746267^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199893077 2500000000 38033486746267 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1837260513/10000000000 : ℝ), (752183059/1250000000 : ℝ), (1199893077/2500000000 : ℝ)] ![(2147803564581/20000000000000 : ℝ), (51227495409011/100000000000000 : ℝ), (38033486746267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1837260513/10000000000 : ℝ)|^4255 ≤ (2147803564581/20000000000000 : ℝ)^3231
        have hw : |(-1837260513/10000000000 : ℝ)|=(1837260513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(752183059/1250000000 : ℝ)|^4255 ≤ (51227495409011/100000000000000 : ℝ)^3231
        have hw : |(752183059/1250000000 : ℝ)|=(752183059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199893077/2500000000 : ℝ)|^4255 ≤ (38033486746267/100000000000000 : ℝ)^3231
        have hw : |(1199893077/2500000000 : ℝ)|=(1199893077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s0_1 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2753540911/5000000000 : ℝ)*x 0 + (-2531904971/10000000000 : ℝ)*x 1 + (191982891/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753540911/5000000000 : ℝ)^4255 ≤ (142449811063/312500000000 : ℝ)^3231 := by
    have hnat : (2753540911 : ℕ)^4255*312500000000^3231 ≤ 142449811063^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753540911 5000000000 142449811063 312500000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2531904971/10000000000 : ℝ)^4255 ≤ (819128702441/5000000000000 : ℝ)^3231 := by
    have hnat : (2531904971 : ℕ)^4255*5000000000000^3231 ≤ 819128702441^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531904971 10000000000 819128702441 5000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191982891/400000000 : ℝ)^4255 ≤ (19016743200943/50000000000000 : ℝ)^3231 := by
    have hnat : (191982891 : ℕ)^4255*50000000000000^3231 ≤ 19016743200943^3231*400000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191982891 400000000 19016743200943 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753540911/5000000000 : ℝ), (-2531904971/10000000000 : ℝ), (191982891/400000000 : ℝ)] ![(142449811063/312500000000 : ℝ), (819128702441/5000000000000 : ℝ), (19016743200943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753540911/5000000000 : ℝ)|^4255 ≤ (142449811063/312500000000 : ℝ)^3231
        have hw : |(2753540911/5000000000 : ℝ)|=(2753540911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2531904971/10000000000 : ℝ)|^4255 ≤ (819128702441/5000000000000 : ℝ)^3231
        have hw : |(-2531904971/10000000000 : ℝ)|=(2531904971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(191982891/400000000 : ℝ)|^4255 ≤ (19016743200943/50000000000000 : ℝ)^3231
        have hw : |(191982891/400000000 : ℝ)|=(191982891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s0_2 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2753540903/5000000000 : ℝ)*x 0 + (2399786157/5000000000 : ℝ)*x 1 + (-2531904943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753540903/5000000000 : ℝ)^4255 ≤ (45583939365749/100000000000000 : ℝ)^3231 := by
    have hnat : (2753540903 : ℕ)^4255*100000000000000^3231 ≤ 45583939365749^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753540903 5000000000 45583939365749 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2399786157/5000000000 : ℝ)^4255 ≤ (19016743404441/50000000000000 : ℝ)^3231 := by
    have hnat : (2399786157 : ℕ)^4255*50000000000000^3231 ≤ 19016743404441^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399786157 5000000000 19016743404441 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2531904943/10000000000 : ℝ)^4255 ≤ (16382573810229/100000000000000 : ℝ)^3231 := by
    have hnat : (2531904943 : ℕ)^4255*100000000000000^3231 ≤ 16382573810229^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2531904943 10000000000 16382573810229 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753540903/5000000000 : ℝ), (2399786157/5000000000 : ℝ), (-2531904943/10000000000 : ℝ)] ![(45583939365749/100000000000000 : ℝ), (19016743404441/50000000000000 : ℝ), (16382573810229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753540903/5000000000 : ℝ)|^4255 ≤ (45583939365749/100000000000000 : ℝ)^3231
        have hw : |(2753540903/5000000000 : ℝ)|=(2753540903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2399786157/5000000000 : ℝ)|^4255 ≤ (19016743404441/50000000000000 : ℝ)^3231
        have hw : |(2399786157/5000000000 : ℝ)|=(2399786157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2531904943/10000000000 : ℝ)|^4255 ≤ (16382573810229/100000000000000 : ℝ)^3231
        have hw : |(-2531904943/10000000000 : ℝ)|=(2531904943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s0_3 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4185870703/10000000000 : ℝ)*x 0 + (77730991/250000000 : ℝ)*x 1 + (350947889/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185870703/10000000000 : ℝ)^4255 ≤ (1588138914063/5000000000000 : ℝ)^3231 := by
    have hnat : (4185870703 : ℕ)^4255*5000000000000^3231 ≤ 1588138914063^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185870703 10000000000 1588138914063 5000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77730991/250000000 : ℝ)^4255 ≤ (21471442414857/100000000000000 : ℝ)^3231 := by
    have hnat : (77730991 : ℕ)^4255*100000000000000^3231 ≤ 21471442414857^3231*250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77730991 250000000 21471442414857 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (350947889/625000000 : ℝ)^4255 ≤ (233828896449/500000000000 : ℝ)^3231 := by
    have hnat : (350947889 : ℕ)^4255*500000000000^3231 ≤ 233828896449^3231*625000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350947889 625000000 233828896449 500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185870703/10000000000 : ℝ), (77730991/250000000 : ℝ), (350947889/625000000 : ℝ)] ![(1588138914063/5000000000000 : ℝ), (21471442414857/100000000000000 : ℝ), (233828896449/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185870703/10000000000 : ℝ)|^4255 ≤ (1588138914063/5000000000000 : ℝ)^3231
        have hw : |(4185870703/10000000000 : ℝ)|=(4185870703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77730991/250000000 : ℝ)|^4255 ≤ (21471442414857/100000000000000 : ℝ)^3231
        have hw : |(77730991/250000000 : ℝ)|=(77730991/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(350947889/625000000 : ℝ)|^4255 ≤ (233828896449/500000000000 : ℝ)^3231
        have hw : |(350947889/625000000 : ℝ)|=(350947889/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s0_4 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73678697/400000000 : ℝ)*x 0 + (4831001189/10000000000 : ℝ)*x 1 + (149622949/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73678697/400000000 : ℝ)^4255 ≤ (5387632270123/50000000000000 : ℝ)^3231 := by
    have hnat : (73678697 : ℕ)^4255*50000000000000^3231 ≤ 5387632270123^3231*400000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73678697 400000000 5387632270123 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4831001189/10000000000 : ℝ)^4255 ≤ (38361812446369/100000000000000 : ℝ)^3231 := by
    have hnat : (4831001189 : ℕ)^4255*100000000000000^3231 ≤ 38361812446369^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4831001189 10000000000 38361812446369 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149622949/250000000 : ℝ)^4255 ≤ (25431461499113/50000000000000 : ℝ)^3231 := by
    have hnat : (149622949 : ℕ)^4255*50000000000000^3231 ≤ 25431461499113^3231*250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149622949 250000000 25431461499113 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73678697/400000000 : ℝ), (4831001189/10000000000 : ℝ), (149622949/250000000 : ℝ)] ![(5387632270123/50000000000000 : ℝ), (38361812446369/100000000000000 : ℝ), (25431461499113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73678697/400000000 : ℝ)|^4255 ≤ (5387632270123/50000000000000 : ℝ)^3231
        have hw : |(-73678697/400000000 : ℝ)|=(73678697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4831001189/10000000000 : ℝ)|^4255 ≤ (38361812446369/100000000000000 : ℝ)^3231
        have hw : |(4831001189/10000000000 : ℝ)|=(4831001189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149622949/250000000 : ℝ)|^4255 ≤ (25431461499113/50000000000000 : ℝ)^3231
        have hw : |(149622949/250000000 : ℝ)|=(149622949/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s0_5 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5175496557/10000000000 : ℝ)*x 0 + (-336639157/2500000000 : ℝ)*x 1 + (187028769/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175496557/10000000000 : ℝ)^4255 ≤ (21002206138037/50000000000000 : ℝ)^3231 := by
    have hnat : (5175496557 : ℕ)^4255*50000000000000^3231 ≤ 21002206138037^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175496557 10000000000 21002206138037 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336639157/2500000000 : ℝ)^4255 ≤ (7132635077221/100000000000000 : ℝ)^3231 := by
    have hnat : (336639157 : ℕ)^4255*100000000000000^3231 ≤ 7132635077221^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336639157 2500000000 7132635077221 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187028769/312500000 : ℝ)^4255 ≤ (50862952634509/100000000000000 : ℝ)^3231 := by
    have hnat : (187028769 : ℕ)^4255*100000000000000^3231 ≤ 50862952634509^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187028769 312500000 50862952634509 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175496557/10000000000 : ℝ), (-336639157/2500000000 : ℝ), (187028769/312500000 : ℝ)] ![(21002206138037/50000000000000 : ℝ), (7132635077221/100000000000000 : ℝ), (50862952634509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175496557/10000000000 : ℝ)|^4255 ≤ (21002206138037/50000000000000 : ℝ)^3231
        have hw : |(5175496557/10000000000 : ℝ)|=(5175496557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336639157/2500000000 : ℝ)|^4255 ≤ (7132635077221/100000000000000 : ℝ)^3231
        have hw : |(-336639157/2500000000 : ℝ)|=(336639157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(187028769/312500000 : ℝ)|^4255 ≤ (50862952634509/100000000000000 : ℝ)^3231
        have hw : |(187028769/312500000 : ℝ)|=(187028769/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s0_6 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646937233/1250000000 : ℝ)*x 0 + (93514349/156250000 : ℝ)*x 1 + (-1346558271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646937233/1250000000 : ℝ)^4255 ≤ (42004426245581/100000000000000 : ℝ)^3231 := by
    have hnat : (646937233 : ℕ)^4255*100000000000000^3231 ≤ 42004426245581^3231*1250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646937233 1250000000 42004426245581 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93514349/156250000 : ℝ)^4255 ≤ (50862927206399/100000000000000 : ℝ)^3231 := by
    have hnat : (93514349 : ℕ)^4255*100000000000000^3231 ≤ 50862927206399^3231*156250000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93514349 156250000 50862927206399 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346558271/10000000000 : ℝ)^4255 ≤ (7132646538303/100000000000000 : ℝ)^3231 := by
    have hnat : (1346558271 : ℕ)^4255*100000000000000^3231 ≤ 7132646538303^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346558271 10000000000 7132646538303 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646937233/1250000000 : ℝ), (93514349/156250000 : ℝ), (-1346558271/10000000000 : ℝ)] ![(42004426245581/100000000000000 : ℝ), (50862927206399/100000000000000 : ℝ), (7132646538303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646937233/1250000000 : ℝ)|^4255 ≤ (42004426245581/100000000000000 : ℝ)^3231
        have hw : |(646937233/1250000000 : ℝ)|=(646937233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(93514349/156250000 : ℝ)|^4255 ≤ (50862927206399/100000000000000 : ℝ)^3231
        have hw : |(93514349/156250000 : ℝ)|=(93514349/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1346558271/10000000000 : ℝ)|^4255 ≤ (7132646538303/100000000000000 : ℝ)^3231
        have hw : |(-1346558271/10000000000 : ℝ)|=(1346558271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s0_7 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131111289/312500000 : ℝ)*x 0 + (2775253077/5000000000 : ℝ)*x 1 + (1588099789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131111289/312500000 : ℝ)^4255 ≤ (7964912817179/25000000000000 : ℝ)^3231 := by
    have hnat : (131111289 : ℕ)^4255*25000000000000^3231 ≤ 7964912817179^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131111289 312500000 7964912817179 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2775253077/5000000000 : ℝ)^4255 ≤ (2878617748731/6250000000000 : ℝ)^3231 := by
    have hnat : (2775253077 : ℕ)^4255*6250000000000^3231 ≤ 2878617748731^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2775253077 5000000000 2878617748731 6250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588099789/5000000000 : ℝ)^4255 ≤ (1380154045941/6250000000000 : ℝ)^3231 := by
    have hnat : (1588099789 : ℕ)^4255*6250000000000^3231 ≤ 1380154045941^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588099789 5000000000 1380154045941 6250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131111289/312500000 : ℝ), (2775253077/5000000000 : ℝ), (1588099789/5000000000 : ℝ)] ![(7964912817179/25000000000000 : ℝ), (2878617748731/6250000000000 : ℝ), (1380154045941/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131111289/312500000 : ℝ)|^4255 ≤ (7964912817179/25000000000000 : ℝ)^3231
        have hw : |(131111289/312500000 : ℝ)|=(131111289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2775253077/5000000000 : ℝ)|^4255 ≤ (2878617748731/6250000000000 : ℝ)^3231
        have hw : |(2775253077/5000000000 : ℝ)|=(2775253077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1588099789/5000000000 : ℝ)|^4255 ≤ (1380154045941/6250000000000 : ℝ)^3231
        have hw : |(1588099789/5000000000 : ℝ)|=(1588099789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1295_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (33/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27213/100000 : ℝ)*pair X 0 0 := by
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
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (2127/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2127 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2127*1^512 ≤ 0^512*1^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2127/512 : ℝ) ≤ (2222486161793301907/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2127 ≤ (2222486161793301907/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2127*100000000000000000000^512 ≤ 2222486161793301907^512*5^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2222486161793301907 100000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2222486161793301907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2127 := by
      have hnat : (1 : ℕ)^512*1^2127 ≤ 1^2127*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102222486161793301907/100000000000000000000 : ℝ) ≤ (2513263223026787/2500000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (102222486161793301907/100000000000000000000 : ℝ)^512 ≤ (2513263223026787/2500000000000000 : ℝ)^2127 := by
      have hnat : (102222486161793301907 : ℕ)^512*2500000000000000^2127 ≤ 2513263223026787^2127*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102222486161793301907 100000000000000000000 2513263223026787 2500000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513263223026787/2500000000000000 : ℝ)) (X := (102222486161793301907/100000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52222486161793301907/50000000000000000000 : ℝ) ≤ (1263263223026787/1250000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (52222486161793301907/50000000000000000000 : ℝ)^512 ≤ (1263263223026787/1250000000000000 : ℝ)^2127 := by
      have hnat : (52222486161793301907 : ℕ)^512*1250000000000000^2127 ≤ 1263263223026787^2127*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52222486161793301907 50000000000000000000 1263263223026787 1250000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263263223026787/1250000000000000 : ℝ)) (X := (52222486161793301907/50000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13263223026787/1000000000000000 : ℝ)*(0 : ℝ))^(2127/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(13263223026787/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2222486161793301907/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13263223026787/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2127/512 : ℝ) := by
    rw [show (1 : ℝ)+(13263223026787/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2513263223026787/2500000000000000 : ℝ) by norm_num, show 1+(2222486161793301907/100000000000000000000 : ℝ)+(0 : ℝ)=(102222486161793301907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2222486161793301907/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13263223026787/1000000000000000 : ℝ)*(2/5 : ℝ))^(2127/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(13263223026787/1000000000000000 : ℝ)*(2/5 : ℝ)=(1263263223026787/1250000000000000 : ℝ) by norm_num, show 1+2*(2222486161793301907/100000000000000000000 : ℝ)=(52222486161793301907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13263223026787/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13263223026787/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13263223026787/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13263223026787/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13263223026787/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13263223026787/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1837260513/10000000000 : ℝ)*X 0 0+(752183059/1250000000 : ℝ)*X 0 1+(1199893077/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2753540911/5000000000 : ℝ)*X 1 0+(-2531904971/10000000000 : ℝ)*X 1 1+(191982891/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2753540903/5000000000 : ℝ)*X 2 0+(2399786157/5000000000 : ℝ)*X 2 1+(-2531904943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4185870703/10000000000 : ℝ)*X 0 0+(77730991/250000000 : ℝ)*X 0 1+(350947889/625000000 : ℝ)*X 0 2+(4185870703/10000000000 : ℝ)*X 1 0+(77730991/250000000 : ℝ)*X 1 1+(350947889/625000000 : ℝ)*X 1 2+(4185870703/10000000000 : ℝ)*X 2 0+(77730991/250000000 : ℝ)*X 2 1+(350947889/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-73678697/400000000 : ℝ)*X 0 0+(4831001189/10000000000 : ℝ)*X 0 1+(149622949/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175496557/10000000000 : ℝ)*X 1 0+(-336639157/2500000000 : ℝ)*X 1 1+(187028769/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((646937233/1250000000 : ℝ)*X 2 0+(93514349/156250000 : ℝ)*X 2 1+(-1346558271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((131111289/312500000 : ℝ)*X 0 0+(2775253077/5000000000 : ℝ)*X 0 1+(1588099789/5000000000 : ℝ)*X 0 2+(131111289/312500000 : ℝ)*X 1 0+(2775253077/5000000000 : ℝ)*X 1 1+(1588099789/5000000000 : ℝ)*X 1 2+(131111289/312500000 : ℝ)*X 2 0+(2775253077/5000000000 : ℝ)*X 2 1+(1588099789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54034660922167005488199/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128369/390625000000 : ℝ)*(base1) + (535937589/100000000000000 : ℝ)*(base19) + (21342081/4000000000000 : ℝ)*(base23) + (58895701/100000000000000 : ℝ)*(upper3) + (259961/400000000000 : ℝ)*(upper5) + (305037405857347/50000000000000 : ℝ)*(major0) + (305037405857347/50000000000000 : ℝ)*(major1) + (305037405857347/50000000000000 : ℝ)*(major2) + (410546166636899/50000000000000 : ℝ)*(sp0) + (82109346298743/10000000000000 : ℝ)*(sp1) + (821093465372993/100000000000000 : ℝ)*(sp2) + (99763685694477/25000000000000 : ℝ)*(sp3) + (339702737/20000000000000 : ℝ)*(sp4) + (48551111/6250000000000 : ℝ)*(sp7) + (99763888114537/25000000000000 : ℝ)*(f.failure) + (821093998925019/100000000000000 : ℝ)*(f.sum) + (38781974929089/25000000000000000000000000000 : ℝ)*base65 + (72347055495911/50000000000000000000000000000 : ℝ)*base68 + (247732766554089/50000000000000000000000000000 : ℝ)*base69 + (74266520154089/50000000000000000000000000000 : ℝ)*base71 + (37733720595911/25000000000000000000000000000 : ℝ)*base74 + (188911023254089/50000000000000000000000000000 : ℝ)*base75 + (314938125254089/50000000000000000000000000000 : ℝ)*base77 + (417410960454089/50000000000000000000000000000 : ℝ)*base79 + (63098243729089/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1123721/250000000000000000000 : ℝ)*base90 + (1123721/250000000000000000000 : ℝ)*base92 + (1123721/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41237376936244019670687/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212756029/50000000000000 : ℝ)*(base1) + (3516687/800000000000 : ℝ)*(base19) + (76374193/12500000000000 : ℝ)*(base23) + (673421/10000000000000 : ℝ)*(base59) + (4932637/12500000000000 : ℝ)*(upper3) + (160973891303433/25000000000000 : ℝ)*(major0) + (160973891303433/25000000000000 : ℝ)*(major1) + (160973891303433/25000000000000 : ℝ)*(major2) + (943602537/100000000000000 : ℝ)*(sp1) + (451747911/50000000000000 : ℝ)*(sp3) + (173322685439901/20000000000000 : ℝ)*(sp4) + (173322323699807/20000000000000 : ℝ)*(sp5) + (866612390693903/100000000000000 : ℝ)*(sp6) + (210588344882897/50000000000000 : ℝ)*(sp7) + (16847120750947/4000000000000 : ℝ)*(f.failure) + (866613001687447/100000000000000 : ℝ)*(f.sum) + (23690710352729/12500000000000000000000000000 : ℝ)*base66 + (141478609034771/25000000000000000000000000000 : ℝ)*base67 + (74701882559771/25000000000000000000000000000 : ℝ)*base69 + (26391936884771/25000000000000000000000000000 : ℝ)*base71 + (4131967197271/12500000000000000000000000000 : ℝ)*base73 + (20969746315229/25000000000000000000000000000 : ℝ)*base76 + (111436479809771/25000000000000000000000000000 : ℝ)*base77 + (85656259959771/25000000000000000000000000000 : ℝ)*base79 + (6419462777729/12500000000000000000000000000 : ℝ)*base82 + (154749/40000000000000000000 : ℝ)*base89 + (154749/40000000000000000000 : ℝ)*base91 + (154749/40000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1295_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (33/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27213/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1295_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1295_s1_0 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2028872309/10000000000 : ℝ)*x 0 + (5663871557/10000000000 : ℝ)*x 1 + (5030491667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028872309/10000000000 : ℝ)^4255 ≤ (6118896873581/50000000000000 : ℝ)^3231 := by
    have hnat : (2028872309 : ℕ)^4255*50000000000000^3231 ≤ 6118896873581^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028872309 10000000000 6118896873581 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5663871557/10000000000 : ℝ)^4255 ≤ (23650356544891/50000000000000 : ℝ)^3231 := by
    have hnat : (5663871557 : ℕ)^4255*50000000000000^3231 ≤ 23650356544891^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5663871557 10000000000 23650356544891 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5030491667/10000000000 : ℝ)^4255 ≤ (5057686642717/12500000000000 : ℝ)^3231 := by
    have hnat : (5030491667 : ℕ)^4255*12500000000000^3231 ≤ 5057686642717^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030491667 10000000000 5057686642717 12500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2028872309/10000000000 : ℝ), (5663871557/10000000000 : ℝ), (5030491667/10000000000 : ℝ)] ![(6118896873581/50000000000000 : ℝ), (23650356544891/50000000000000 : ℝ), (5057686642717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2028872309/10000000000 : ℝ)|^4255 ≤ (6118896873581/50000000000000 : ℝ)^3231
        have hw : |(-2028872309/10000000000 : ℝ)|=(2028872309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5663871557/10000000000 : ℝ)|^4255 ≤ (23650356544891/50000000000000 : ℝ)^3231
        have hw : |(5663871557/10000000000 : ℝ)|=(5663871557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5030491667/10000000000 : ℝ)|^4255 ≤ (5057686642717/12500000000000 : ℝ)^3231
        have hw : |(5030491667/10000000000 : ℝ)|=(5030491667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s1_1 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1352666377/2500000000 : ℝ)*x 0 + (-2368261123/10000000000 : ℝ)*x 1 + (1257622931/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352666377/2500000000 : ℝ)^4255 ≤ (44535865307527/100000000000000 : ℝ)^3231 := by
    have hnat : (1352666377 : ℕ)^4255*100000000000000^3231 ≤ 44535865307527^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352666377 2500000000 44535865307527 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2368261123/10000000000 : ℝ)^4255 ≤ (3000528185699/20000000000000 : ℝ)^3231 := by
    have hnat : (2368261123 : ℕ)^4255*20000000000000^3231 ≤ 3000528185699^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368261123 10000000000 3000528185699 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1257622931/2500000000 : ℝ)^4255 ≤ (20230746872751/50000000000000 : ℝ)^3231 := by
    have hnat : (1257622931 : ℕ)^4255*50000000000000^3231 ≤ 20230746872751^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257622931 2500000000 20230746872751 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352666377/2500000000 : ℝ), (-2368261123/10000000000 : ℝ), (1257622931/2500000000 : ℝ)] ![(44535865307527/100000000000000 : ℝ), (3000528185699/20000000000000 : ℝ), (20230746872751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352666377/2500000000 : ℝ)|^4255 ≤ (44535865307527/100000000000000 : ℝ)^3231
        have hw : |(1352666377/2500000000 : ℝ)|=(1352666377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2368261123/10000000000 : ℝ)|^4255 ≤ (3000528185699/20000000000000 : ℝ)^3231
        have hw : |(-2368261123/10000000000 : ℝ)|=(2368261123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1257622931/2500000000 : ℝ)|^4255 ≤ (20230746872751/50000000000000 : ℝ)^3231
        have hw : |(1257622931/2500000000 : ℝ)|=(1257622931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s1_2 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5410665471/10000000000 : ℝ)*x 0 + (125762291/250000000 : ℝ)*x 1 + (-1184130639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410665471/10000000000 : ℝ)^4255 ≤ (22267932453227/50000000000000 : ℝ)^3231 := by
    have hnat : (5410665471 : ℕ)^4255*50000000000000^3231 ≤ 22267932453227^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410665471 10000000000 22267932453227 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125762291/250000000 : ℝ)^4255 ≤ (40461492855741/100000000000000 : ℝ)^3231 := by
    have hnat : (125762291 : ℕ)^4255*100000000000000^3231 ≤ 40461492855741^3231*250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125762291 250000000 40461492855741 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1184130639/5000000000 : ℝ)^4255 ≤ (3750660555399/25000000000000 : ℝ)^3231 := by
    have hnat : (1184130639 : ℕ)^4255*25000000000000^3231 ≤ 3750660555399^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184130639 5000000000 3750660555399 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410665471/10000000000 : ℝ), (125762291/250000000 : ℝ), (-1184130639/5000000000 : ℝ)] ![(22267932453227/50000000000000 : ℝ), (40461492855741/100000000000000 : ℝ), (3750660555399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410665471/10000000000 : ℝ)|^4255 ≤ (22267932453227/50000000000000 : ℝ)^3231
        have hw : |(5410665471/10000000000 : ℝ)|=(5410665471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125762291/250000000 : ℝ)|^4255 ≤ (40461492855741/100000000000000 : ℝ)^3231
        have hw : |(125762291/250000000 : ℝ)|=(125762291/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1184130639/5000000000 : ℝ)|^4255 ≤ (3750660555399/25000000000000 : ℝ)^3231
        have hw : |(-1184130639/5000000000 : ℝ)|=(1184130639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s1_3 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300616899/10000000000 : ℝ)*x 0 + (3695703201/10000000000 : ℝ)*x 1 + (4998941011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300616899/10000000000 : ℝ)^4255 ≤ (32914385707191/100000000000000 : ℝ)^3231 := by
    have hnat : (4300616899 : ℕ)^4255*100000000000000^3231 ≤ 32914385707191^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300616899 10000000000 32914385707191 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3695703201/10000000000 : ℝ)^4255 ≤ (6739496363709/25000000000000 : ℝ)^3231 := by
    have hnat : (3695703201 : ℕ)^4255*25000000000000^3231 ≤ 6739496363709^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3695703201 10000000000 6739496363709 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998941011/10000000000 : ℝ)^4255 ≤ (40127628824891/100000000000000 : ℝ)^3231 := by
    have hnat : (4998941011 : ℕ)^4255*100000000000000^3231 ≤ 40127628824891^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998941011 10000000000 40127628824891 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300616899/10000000000 : ℝ), (3695703201/10000000000 : ℝ), (4998941011/10000000000 : ℝ)] ![(32914385707191/100000000000000 : ℝ), (6739496363709/25000000000000 : ℝ), (40127628824891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300616899/10000000000 : ℝ)|^4255 ≤ (32914385707191/100000000000000 : ℝ)^3231
        have hw : |(4300616899/10000000000 : ℝ)|=(4300616899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3695703201/10000000000 : ℝ)|^4255 ≤ (6739496363709/25000000000000 : ℝ)^3231
        have hw : |(3695703201/10000000000 : ℝ)|=(3695703201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998941011/10000000000 : ℝ)|^4255 ≤ (40127628824891/100000000000000 : ℝ)^3231
        have hw : |(4998941011/10000000000 : ℝ)|=(4998941011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s1_4 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2029502833/10000000000 : ℝ)*x 0 + (5038730531/10000000000 : ℝ)*x 1 + (2827738573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029502833/10000000000 : ℝ)^4255 ≤ (12242802551061/100000000000000 : ℝ)^3231 := by
    have hnat : (2029502833 : ℕ)^4255*100000000000000^3231 ≤ 12242802551061^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029502833 10000000000 12242802551061 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5038730531/10000000000 : ℝ)^4255 ≤ (40548785066219/100000000000000 : ℝ)^3231 := by
    have hnat : (5038730531 : ℕ)^4255*100000000000000^3231 ≤ 40548785066219^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038730531 10000000000 40548785066219 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2827738573/5000000000 : ℝ)^4255 ≤ (47208412371147/100000000000000 : ℝ)^3231 := by
    have hnat : (2827738573 : ℕ)^4255*100000000000000^3231 ≤ 47208412371147^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827738573 5000000000 47208412371147 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2029502833/10000000000 : ℝ), (5038730531/10000000000 : ℝ), (2827738573/5000000000 : ℝ)] ![(12242802551061/100000000000000 : ℝ), (40548785066219/100000000000000 : ℝ), (47208412371147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2029502833/10000000000 : ℝ)|^4255 ≤ (12242802551061/100000000000000 : ℝ)^3231
        have hw : |(-2029502833/10000000000 : ℝ)|=(2029502833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5038730531/10000000000 : ℝ)|^4255 ≤ (40548785066219/100000000000000 : ℝ)^3231
        have hw : |(5038730531/10000000000 : ℝ)|=(5038730531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2827738573/5000000000 : ℝ)|^4255 ≤ (47208412371147/100000000000000 : ℝ)^3231
        have hw : |(2827738573/5000000000 : ℝ)|=(2827738573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s1_5 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5246978161/10000000000 : ℝ)*x 0 + (-435818813/2500000000 : ℝ)*x 1 + (70693473/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246978161/10000000000 : ℝ)^4255 ≤ (10692522625221/25000000000000 : ℝ)^3231 := by
    have hnat : (5246978161 : ℕ)^4255*25000000000000^3231 ≤ 10692522625221^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246978161 10000000000 10692522625221 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (435818813/2500000000 : ℝ)^4255 ≤ (10021489481169/100000000000000 : ℝ)^3231 := by
    have hnat : (435818813 : ℕ)^4255*100000000000000^3231 ≤ 10021489481169^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435818813 2500000000 10021489481169 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70693473/125000000 : ℝ)^4255 ≤ (11802105000057/25000000000000 : ℝ)^3231 := by
    have hnat : (70693473 : ℕ)^4255*25000000000000^3231 ≤ 11802105000057^3231*125000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70693473 125000000 11802105000057 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246978161/10000000000 : ℝ), (-435818813/2500000000 : ℝ), (70693473/125000000 : ℝ)] ![(10692522625221/25000000000000 : ℝ), (10021489481169/100000000000000 : ℝ), (11802105000057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246978161/10000000000 : ℝ)|^4255 ≤ (10692522625221/25000000000000 : ℝ)^3231
        have hw : |(5246978161/10000000000 : ℝ)|=(5246978161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-435818813/2500000000 : ℝ)|^4255 ≤ (10021489481169/100000000000000 : ℝ)^3231
        have hw : |(-435818813/2500000000 : ℝ)|=(435818813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70693473/125000000 : ℝ)|^4255 ≤ (11802105000057/25000000000000 : ℝ)^3231
        have hw : |(70693473/125000000 : ℝ)|=(70693473/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s1_6 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (655872259/1250000000 : ℝ)*x 0 + (5655477437/10000000000 : ℝ)*x 1 + (-435818991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655872259/1250000000 : ℝ)^4255 ≤ (42770089545487/100000000000000 : ℝ)^3231 := by
    have hnat : (655872259 : ℕ)^4255*100000000000000^3231 ≤ 42770089545487^3231*1250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655872259 1250000000 42770089545487 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5655477437/10000000000 : ℝ)^4255 ≤ (11802103892521/25000000000000 : ℝ)^3231 := by
    have hnat : (5655477437 : ℕ)^4255*25000000000000^3231 ≤ 11802103892521^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5655477437 10000000000 11802103892521 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (435818991/2500000000 : ℝ)^4255 ≤ (10021494871419/100000000000000 : ℝ)^3231 := by
    have hnat : (435818991 : ℕ)^4255*100000000000000^3231 ≤ 10021494871419^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435818991 2500000000 10021494871419 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655872259/1250000000 : ℝ), (5655477437/10000000000 : ℝ), (-435818991/2500000000 : ℝ)] ![(42770089545487/100000000000000 : ℝ), (11802103892521/25000000000000 : ℝ), (10021494871419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655872259/1250000000 : ℝ)|^4255 ≤ (42770089545487/100000000000000 : ℝ)^3231
        have hw : |(655872259/1250000000 : ℝ)|=(655872259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5655477437/10000000000 : ℝ)|^4255 ≤ (11802103892521/25000000000000 : ℝ)^3231
        have hw : |(5655477437/10000000000 : ℝ)|=(5655477437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-435818991/2500000000 : ℝ)|^4255 ≤ (10021494871419/100000000000000 : ℝ)^3231
        have hw : |(-435818991/2500000000 : ℝ)|=(435818991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s1_7 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075478373/2500000000 : ℝ)*x 0 + (77843583/156250000 : ℝ)*x 1 + (29703797/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075478373/2500000000 : ℝ)^4255 ≤ (2057965918569/6250000000000 : ℝ)^3231 := by
    have hnat : (1075478373 : ℕ)^4255*6250000000000^3231 ≤ 2057965918569^3231*2500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075478373 2500000000 2057965918569 6250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77843583/156250000 : ℝ)^4255 ≤ (3994852382611/10000000000000 : ℝ)^3231 := by
    have hnat : (77843583 : ℕ)^4255*10000000000000^3231 ≤ 3994852382611^3231*156250000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77843583 156250000 3994852382611 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29703797/80000000 : ℝ)^4255 ≤ (27124021455707/100000000000000 : ℝ)^3231 := by
    have hnat : (29703797 : ℕ)^4255*100000000000000^3231 ≤ 27124021455707^3231*80000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29703797 80000000 27124021455707 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075478373/2500000000 : ℝ), (77843583/156250000 : ℝ), (29703797/80000000 : ℝ)] ![(2057965918569/6250000000000 : ℝ), (3994852382611/10000000000000 : ℝ), (27124021455707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075478373/2500000000 : ℝ)|^4255 ≤ (2057965918569/6250000000000 : ℝ)^3231
        have hw : |(1075478373/2500000000 : ℝ)|=(1075478373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77843583/156250000 : ℝ)|^4255 ≤ (3994852382611/10000000000000 : ℝ)^3231
        have hw : |(77843583/156250000 : ℝ)|=(77843583/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(29703797/80000000 : ℝ)|^4255 ≤ (27124021455707/100000000000000 : ℝ)^3231
        have hw : |(29703797/80000000 : ℝ)|=(29703797/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1295_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (6439/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9913/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27213/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (33/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27213/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (33/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27213/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (33/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27213/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (33/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27213/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (33/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27213/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (33/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (33/3125 : ℝ) ^ (2127/512 : ℝ) ≤ (308093968117/50000000000000000000 : ℝ) := by
    have hpowers : (33/3125 : ℝ)^2127 ≤ (308093968117/50000000000000000000 : ℝ)^512 := by
      have hnat : (33 : ℕ)^2127*50000000000000000000^512 ≤ 308093968117^512*3125^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33 3125 308093968117 50000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33/3125 : ℝ)) (X := (308093968117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hpowhi : (27213/100000 : ℝ) ^ (2127/512 : ℝ) ≤ (112158828261000721/25000000000000000000 : ℝ) := by
    have hpowers : (27213/100000 : ℝ)^2127 ≤ (112158828261000721/25000000000000000000 : ℝ)^512 := by
      have hnat : (27213 : ℕ)^2127*25000000000000000000^512 ≤ 112158828261000721^512*100000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27213 100000 112158828261000721 25000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27213/100000 : ℝ)) (X := (112158828261000721/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000308093968117/25000000000000000000 : ℝ) ≤ (1000000002966509/1000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (25000000308093968117/25000000000000000000 : ℝ)^512 ≤ (1000000002966509/1000000000000000 : ℝ)^2127 := by
      have hnat : (25000000308093968117 : ℕ)^512*1000000000000000^2127 ≤ 1000000002966509^2127*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000308093968117 25000000000000000000 1000000002966509 1000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000002966509/1000000000000000 : ℝ)) (X := (25000000308093968117/25000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50224317964615969559/50000000000000000000 : ℝ) ≤ (10010780977481529/10000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (50224317964615969559/50000000000000000000 : ℝ)^512 ≤ (10010780977481529/10000000000000000 : ℝ)^2127 := by
      have hnat : (50224317964615969559 : ℕ)^512*10000000000000000^2127 ≤ 10010780977481529^2127*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50224317964615969559 50000000000000000000 10010780977481529 10000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010780977481529/10000000000000000 : ℝ)) (X := (50224317964615969559/50000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12612158828261000721/12500000000000000000 : ℝ) ≤ (626347620331123/625000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (12612158828261000721/12500000000000000000 : ℝ)^512 ≤ (626347620331123/625000000000000 : ℝ)^2127 := by
      have hnat : (12612158828261000721 : ℕ)^512*625000000000000^2127 ≤ 626347620331123^2127*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12612158828261000721 12500000000000000000 626347620331123 625000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626347620331123/625000000000000 : ℝ)) (X := (12612158828261000721/12500000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(308093968117/50000000000000000000 : ℝ) ≤ ((43591205235693573327/43595000000000000000 : ℝ)+2*(10780947816439/2615700000000000 : ℝ)*(33/3125 : ℝ))^(2127/512 : ℝ) := by
    rw [show (43591205235693573327/43595000000000000000 : ℝ)+2*(10780947816439/2615700000000000 : ℝ)*(33/3125 : ℝ)=(1000000002966509/1000000000000000 : ℝ) by norm_num, show 1+2*(308093968117/50000000000000000000 : ℝ)=(25000000308093968117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(112158828261000721/25000000000000000000 : ℝ)+(308093968117/50000000000000000000 : ℝ) ≤ ((43591205235693573327/43595000000000000000 : ℝ)+(10780947816439/2615700000000000 : ℝ)*((27213/100000 : ℝ)+(33/3125 : ℝ)))^(2127/512 : ℝ) := by
    rw [show (43591205235693573327/43595000000000000000 : ℝ)+(10780947816439/2615700000000000 : ℝ)*((27213/100000 : ℝ)+(33/3125 : ℝ))=(10010780977481529/10000000000000000 : ℝ) by norm_num, show 1+(112158828261000721/25000000000000000000 : ℝ)+(308093968117/50000000000000000000 : ℝ)=(50224317964615969559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(112158828261000721/25000000000000000000 : ℝ) ≤ ((43591205235693573327/43595000000000000000 : ℝ)+2*(10780947816439/2615700000000000 : ℝ)*(27213/100000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (43591205235693573327/43595000000000000000 : ℝ)+2*(10780947816439/2615700000000000 : ℝ)*(27213/100000 : ℝ)=(626347620331123/625000000000000 : ℝ) by norm_num, show 1+2*(112158828261000721/25000000000000000000 : ℝ)=(12612158828261000721/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43591205235693573327/43595000000000000000 : ℝ)*(X 1 0+X 2 0)+(10780947816439/2615700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (33/3125 : ℝ)) (hi := (27213/100000 : ℝ)) (c := (43591205235693573327/43595000000000000000 : ℝ)) (alpha := (10780947816439/2615700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43591205235693573327/43595000000000000000 : ℝ)*(X 0 1+X 2 1)+(10780947816439/2615700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (33/3125 : ℝ)) (hi := (27213/100000 : ℝ)) (c := (43591205235693573327/43595000000000000000 : ℝ)) (alpha := (10780947816439/2615700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43591205235693573327/43595000000000000000 : ℝ)*(X 0 2+X 1 2)+(10780947816439/2615700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (33/3125 : ℝ)) (hi := (27213/100000 : ℝ)) (c := (43591205235693573327/43595000000000000000 : ℝ)) (alpha := (10780947816439/2615700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2028872309/10000000000 : ℝ)*X 0 0+(5663871557/10000000000 : ℝ)*X 0 1+(5030491667/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1352666377/2500000000 : ℝ)*X 1 0+(-2368261123/10000000000 : ℝ)*X 1 1+(1257622931/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5410665471/10000000000 : ℝ)*X 2 0+(125762291/250000000 : ℝ)*X 2 1+(-1184130639/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300616899/10000000000 : ℝ)*X 0 0+(3695703201/10000000000 : ℝ)*X 0 1+(4998941011/10000000000 : ℝ)*X 0 2+(4300616899/10000000000 : ℝ)*X 1 0+(3695703201/10000000000 : ℝ)*X 1 1+(4998941011/10000000000 : ℝ)*X 1 2+(4300616899/10000000000 : ℝ)*X 2 0+(3695703201/10000000000 : ℝ)*X 2 1+(4998941011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2029502833/10000000000 : ℝ)*X 0 0+(5038730531/10000000000 : ℝ)*X 0 1+(2827738573/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246978161/10000000000 : ℝ)*X 1 0+(-435818813/2500000000 : ℝ)*X 1 1+(70693473/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((655872259/1250000000 : ℝ)*X 2 0+(5655477437/10000000000 : ℝ)*X 2 1+(-435818991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075478373/2500000000 : ℝ)*X 0 0+(77843583/156250000 : ℝ)*X 0 1+(29703797/80000000 : ℝ)*X 0 2+(1075478373/2500000000 : ℝ)*X 1 0+(77843583/156250000 : ℝ)*X 1 1+(29703797/80000000 : ℝ)*X 1 2+(1075478373/2500000000 : ℝ)*X 2 0+(77843583/156250000 : ℝ)*X 2 1+(29703797/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2773853671040803237368792417/1089875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19600949/100000000000000 : ℝ)*(base1) + (211826637/50000000000000 : ℝ)*(base19) + (412856651/100000000000000 : ℝ)*(base23) + (1590091/2000000000000 : ℝ)*(upper3) + (4194599/25000000000000 : ℝ)*(upper5) + (586539483900481/50000000000000 : ℝ)*(major0) + (586539483900481/50000000000000 : ℝ)*(major1) + (586539483900481/50000000000000 : ℝ)*(major2) + (789417016002877/50000000000000 : ℝ)*(sp0) + (789417835755311/50000000000000 : ℝ)*(sp1) + (315767136461449/20000000000000 : ℝ)*(sp2) + (383660274014221/50000000000000 : ℝ)*(sp3) + (520689773/25000000000000 : ℝ)*(sp4) + (593985787/50000000000000 : ℝ)*(sp7) + (153464351120193/20000000000000 : ℝ)*(f.failure) + (197354511895487/12500000000000 : ℝ)*(f.sum) + (19363488370639/65392500000000000000000000000 : ℝ)*base65 + (878909271160160861/6539250000000000000000000000000000 : ℝ)*base67 + (45286490413481660861/6539250000000000000000000000000000 : ℝ)*base69 + (11070284739116660861/6539250000000000000000000000000000 : ℝ)*base71 + (163817660513239/65392500000000000000000000000 : ℝ)*base73 + (16995543644095160861/6539250000000000000000000000000000 : ℝ)*base75 + (40996433767420910861/6539250000000000000000000000000000 : ℝ)*base77 + (10264335333587660861/6539250000000000000000000000000000 : ℝ)*base79 + (35541399233453/8174062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (382369/200000000000000000000 : ℝ)*base90 + (382369/200000000000000000000 : ℝ)*base92 + (382369/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2970015542771199176850263049/435950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249337221/20000000000000 : ℝ)*(base19) + (243391177/20000000000000 : ℝ)*(base23) + (19470457/100000000000000 : ℝ)*(upper2) + (208391641/100000000000000 : ℝ)*(upper3) + (144403061/100000000000000 : ℝ)*(upper5) + (240942371201457/20000000000000 : ℝ)*(major0) + (240942371201457/20000000000000 : ℝ)*(major1) + (240942371201457/20000000000000 : ℝ)*(major2) + (3566157453/50000000000000 : ℝ)*(sp1) + (1174283107/20000000000000 : ℝ)*(sp2) + (1621410365842407/100000000000000 : ℝ)*(sp4) + (324280397368279/20000000000000 : ℝ)*(sp5) + (810701638735493/50000000000000 : ℝ)*(sp6) + (394006559540351/50000000000000 : ℝ)*(sp7) + (394006559540351/50000000000000 : ℝ)*(f.failure) + (1621410365842407/100000000000000 : ℝ)*(f.sum) + (394682137633/4359500000000000000000000000 : ℝ)*base66 + (5102657986607887439/871900000000000000000000000000000 : ℝ)*base67 + (2702725308778987439/871900000000000000000000000000000 : ℝ)*base69 + (6351756673924487439/871900000000000000000000000000000 : ℝ)*base71 + (42186510930467/8719000000000000000000000000 : ℝ)*base73 + (5505104049427187439/871900000000000000000000000000000 : ℝ)*base75 + (3516796376489887439/871900000000000000000000000000000 : ℝ)*base77 + (5239247952944387439/871900000000000000000000000000000 : ℝ)*base79 + (38173578363537/8719000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3743583/500000000000000000000 : ℝ)*base90 + (3743583/500000000000000000000 : ℝ)*base92 + (3743583/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1295_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27213/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (33/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6439/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9913/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1295_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1295_s2_0 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073282293/10000000000 : ℝ)*x 0 + (686666321/1250000000 : ℝ)*x 1 + (5172661909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073282293/10000000000 : ℝ)^4255 ≤ (6295890664751/50000000000000 : ℝ)^3231 := by
    have hnat : (2073282293 : ℕ)^4255*50000000000000^3231 ≤ 6295890664751^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073282293 10000000000 6295890664751 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686666321/1250000000 : ℝ)^4255 ≤ (4543410109429/10000000000000 : ℝ)^3231 := by
    have hnat : (686666321 : ℕ)^4255*10000000000000^3231 ≤ 4543410109429^3231*1250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686666321 1250000000 4543410109429 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172661909/10000000000 : ℝ)^4255 ≤ (20987058778413/50000000000000 : ℝ)^3231 := by
    have hnat : (5172661909 : ℕ)^4255*50000000000000^3231 ≤ 20987058778413^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172661909 10000000000 20987058778413 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073282293/10000000000 : ℝ), (686666321/1250000000 : ℝ), (5172661909/10000000000 : ℝ)] ![(6295890664751/50000000000000 : ℝ), (4543410109429/10000000000000 : ℝ), (20987058778413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073282293/10000000000 : ℝ)|^4255 ≤ (6295890664751/50000000000000 : ℝ)^3231
        have hw : |(-2073282293/10000000000 : ℝ)|=(2073282293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686666321/1250000000 : ℝ)|^4255 ≤ (4543410109429/10000000000000 : ℝ)^3231
        have hw : |(686666321/1250000000 : ℝ)|=(686666321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172661909/10000000000 : ℝ)|^4255 ≤ (20987058778413/50000000000000 : ℝ)^3231
        have hw : |(5172661909/10000000000 : ℝ)|=(5172661909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s2_1 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684679691/5000000000 : ℝ)*x 0 + (-34991067/156250000 : ℝ)*x 1 + (5172661973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684679691/5000000000 : ℝ)^4255 ≤ (2204432860641/5000000000000 : ℝ)^3231 := by
    have hnat : (2684679691 : ℕ)^4255*5000000000000^3231 ≤ 2204432860641^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684679691 5000000000 2204432860641 5000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34991067/156250000 : ℝ)^4255 ≤ (13937224536671/100000000000000 : ℝ)^3231 := by
    have hnat : (34991067 : ℕ)^4255*100000000000000^3231 ≤ 13937224536671^3231*156250000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34991067 156250000 13937224536671 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172661973/10000000000 : ℝ)^4255 ≤ (41974118240753/100000000000000 : ℝ)^3231 := by
    have hnat : (5172661973 : ℕ)^4255*100000000000000^3231 ≤ 41974118240753^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172661973 10000000000 41974118240753 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684679691/5000000000 : ℝ), (-34991067/156250000 : ℝ), (5172661973/10000000000 : ℝ)] ![(2204432860641/5000000000000 : ℝ), (13937224536671/100000000000000 : ℝ), (41974118240753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684679691/5000000000 : ℝ)|^4255 ≤ (2204432860641/5000000000000 : ℝ)^3231
        have hw : |(2684679691/5000000000 : ℝ)|=(2684679691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34991067/156250000 : ℝ)|^4255 ≤ (13937224536671/100000000000000 : ℝ)^3231
        have hw : |(-34991067/156250000 : ℝ)|=(34991067/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172661973/10000000000 : ℝ)|^4255 ≤ (41974118240753/100000000000000 : ℝ)^3231
        have hw : |(5172661973/10000000000 : ℝ)|=(5172661973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s2_2 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167792479/312500000 : ℝ)*x 0 + (1034532383/2000000000 : ℝ)*x 1 + (-1119714217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167792479/312500000 : ℝ)^4255 ≤ (4408865662889/10000000000000 : ℝ)^3231 := by
    have hnat : (167792479 : ℕ)^4255*10000000000000^3231 ≤ 4408865662889^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167792479 312500000 4408865662889 10000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034532383/2000000000 : ℝ)^4255 ≤ (2623382351309/6250000000000 : ℝ)^3231 := by
    have hnat : (1034532383 : ℕ)^4255*6250000000000^3231 ≤ 2623382351309^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034532383 2000000000 2623382351309 6250000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119714217/5000000000 : ℝ)^4255 ≤ (13937225733287/100000000000000 : ℝ)^3231 := by
    have hnat : (1119714217 : ℕ)^4255*100000000000000^3231 ≤ 13937225733287^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119714217 5000000000 13937225733287 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167792479/312500000 : ℝ), (1034532383/2000000000 : ℝ), (-1119714217/5000000000 : ℝ)] ![(4408865662889/10000000000000 : ℝ), (2623382351309/6250000000000 : ℝ), (13937225733287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167792479/312500000 : ℝ)|^4255 ≤ (4408865662889/10000000000000 : ℝ)^3231
        have hw : |(167792479/312500000 : ℝ)|=(167792479/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034532383/2000000000 : ℝ)|^4255 ≤ (2623382351309/6250000000000 : ℝ)^3231
        have hw : |(1034532383/2000000000 : ℝ)|=(1034532383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1119714217/5000000000 : ℝ)|^4255 ≤ (13937225733287/100000000000000 : ℝ)^3231
        have hw : |(-1119714217/5000000000 : ℝ)|=(1119714217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s2_3 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216574981/500000000 : ℝ)*x 0 + (802709583/2000000000 : ℝ)*x 1 + (2336680617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216574981/500000000 : ℝ)^4255 ≤ (4153250798763/12500000000000 : ℝ)^3231 := by
    have hnat : (216574981 : ℕ)^4255*12500000000000^3231 ≤ 4153250798763^3231*500000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216574981 500000000 4153250798763 12500000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (802709583/2000000000 : ℝ)^4255 ≤ (15026050032797/50000000000000 : ℝ)^3231 := by
    have hnat : (802709583 : ℕ)^4255*50000000000000^3231 ≤ 15026050032797^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802709583 2000000000 15026050032797 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2336680617/5000000000 : ℝ)^4255 ≤ (36721893524633/100000000000000 : ℝ)^3231 := by
    have hnat : (2336680617 : ℕ)^4255*100000000000000^3231 ≤ 36721893524633^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2336680617 5000000000 36721893524633 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216574981/500000000 : ℝ), (802709583/2000000000 : ℝ), (2336680617/5000000000 : ℝ)] ![(4153250798763/12500000000000 : ℝ), (15026050032797/50000000000000 : ℝ), (36721893524633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216574981/500000000 : ℝ)|^4255 ≤ (4153250798763/12500000000000 : ℝ)^3231
        have hw : |(216574981/500000000 : ℝ)|=(216574981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(802709583/2000000000 : ℝ)|^4255 ≤ (15026050032797/50000000000000 : ℝ)^3231
        have hw : |(802709583/2000000000 : ℝ)|=(802709583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2336680617/5000000000 : ℝ)|^4255 ≤ (36721893524633/100000000000000 : ℝ)^3231
        have hw : |(2336680617/5000000000 : ℝ)|=(2336680617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s2_4 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073363391/10000000000 : ℝ)*x 0 + (5174783053/10000000000 : ℝ)*x 1 + (686398707/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073363391/10000000000 : ℝ)^4255 ≤ (12592429970173/100000000000000 : ℝ)^3231 := by
    have hnat : (2073363391 : ℕ)^4255*100000000000000^3231 ≤ 12592429970173^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073363391 10000000000 12592429970173 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174783053/10000000000 : ℝ)^4255 ≤ (2099839317651/5000000000000 : ℝ)^3231 := by
    have hnat : (5174783053 : ℕ)^4255*5000000000000^3231 ≤ 2099839317651^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174783053 10000000000 2099839317651 5000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686398707/1250000000 : ℝ)^4255 ≤ (22705391828853/50000000000000 : ℝ)^3231 := by
    have hnat : (686398707 : ℕ)^4255*50000000000000^3231 ≤ 22705391828853^3231*1250000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686398707 1250000000 22705391828853 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073363391/10000000000 : ℝ), (5174783053/10000000000 : ℝ), (686398707/1250000000 : ℝ)] ![(12592429970173/100000000000000 : ℝ), (2099839317651/5000000000000 : ℝ), (22705391828853/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073363391/10000000000 : ℝ)|^4255 ≤ (12592429970173/100000000000000 : ℝ)^3231
        have hw : |(-2073363391/10000000000 : ℝ)|=(2073363391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174783053/10000000000 : ℝ)|^4255 ≤ (2099839317651/5000000000000 : ℝ)^3231
        have hw : |(5174783053/10000000000 : ℝ)|=(5174783053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686398707/1250000000 : ℝ)|^4255 ≤ (22705391828853/50000000000000 : ℝ)^3231
        have hw : |(686398707/1250000000 : ℝ)|=(686398707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s2_5 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287143103/10000000000 : ℝ)*x 0 + (-192090001/1000000000 : ℝ)*x 1 + (5491189787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287143103/10000000000 : ℝ)^4255 ≤ (43201774788187/100000000000000 : ℝ)^3231 := by
    have hnat : (5287143103 : ℕ)^4255*100000000000000^3231 ≤ 43201774788187^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287143103 10000000000 43201774788187 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192090001/1000000000 : ℝ)^4255 ≤ (2277488022891/20000000000000 : ℝ)^3231 := by
    have hnat : (192090001 : ℕ)^4255*20000000000000^3231 ≤ 2277488022891^3231*1000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192090001 1000000000 2277488022891 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491189787/10000000000 : ℝ)^4255 ≤ (9082157016877/20000000000000 : ℝ)^3231 := by
    have hnat : (5491189787 : ℕ)^4255*20000000000000^3231 ≤ 9082157016877^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491189787 10000000000 9082157016877 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287143103/10000000000 : ℝ), (-192090001/1000000000 : ℝ), (5491189787/10000000000 : ℝ)] ![(43201774788187/100000000000000 : ℝ), (2277488022891/20000000000000 : ℝ), (9082157016877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287143103/10000000000 : ℝ)|^4255 ≤ (43201774788187/100000000000000 : ℝ)^3231
        have hw : |(5287143103/10000000000 : ℝ)|=(5287143103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192090001/1000000000 : ℝ)|^4255 ≤ (2277488022891/20000000000000 : ℝ)^3231
        have hw : |(-192090001/1000000000 : ℝ)|=(192090001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491189787/10000000000 : ℝ)|^4255 ≤ (9082157016877/20000000000000 : ℝ)^3231
        have hw : |(5491189787/10000000000 : ℝ)|=(5491189787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s2_6 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643571631/5000000000 : ℝ)*x 0 + (171599677/312500000 : ℝ)*x 1 + (-1920899963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643571631/5000000000 : ℝ)^4255 ≤ (10800444124787/25000000000000 : ℝ)^3231 := by
    have hnat : (2643571631 : ℕ)^4255*25000000000000^3231 ≤ 10800444124787^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643571631 5000000000 10800444124787 25000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171599677/312500000 : ℝ)^4255 ≤ (45410783744831/100000000000000 : ℝ)^3231 := by
    have hnat : (171599677 : ℕ)^4255*100000000000000^3231 ≤ 45410783744831^3231*312500000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171599677 312500000 45410783744831 100000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920899963/10000000000 : ℝ)^4255 ≤ (5693719873763/50000000000000 : ℝ)^3231 := by
    have hnat : (1920899963 : ℕ)^4255*50000000000000^3231 ≤ 5693719873763^3231*10000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920899963 10000000000 5693719873763 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643571631/5000000000 : ℝ), (171599677/312500000 : ℝ), (-1920899963/10000000000 : ℝ)] ![(10800444124787/25000000000000 : ℝ), (45410783744831/100000000000000 : ℝ), (5693719873763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643571631/5000000000 : ℝ)|^4255 ≤ (10800444124787/25000000000000 : ℝ)^3231
        have hw : |(2643571631/5000000000 : ℝ)|=(2643571631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171599677/312500000 : ℝ)|^4255 ≤ (45410783744831/100000000000000 : ℝ)^3231
        have hw : |(171599677/312500000 : ℝ)|=(171599677/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1920899963/10000000000 : ℝ)|^4255 ≤ (5693719873763/50000000000000 : ℝ)^3231
        have hw : |(-1920899963/10000000000 : ℝ)|=(1920899963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1295_s2_7 (p : ℝ) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165832983/5000000000 : ℝ)*x 0 + (933799011/2000000000 : ℝ)*x 1 + (401795801/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165832983/5000000000 : ℝ)^4255 ≤ (6645537361737/20000000000000 : ℝ)^3231 := by
    have hnat : (2165832983 : ℕ)^4255*20000000000000^3231 ≤ 6645537361737^3231*5000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165832983 5000000000 6645537361737 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (933799011/2000000000 : ℝ)^4255 ≤ (18338359398493/50000000000000 : ℝ)^3231 := by
    have hnat : (933799011 : ℕ)^4255*50000000000000^3231 ≤ 18338359398493^3231*2000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933799011 2000000000 18338359398493 50000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401795801/1000000000 : ℝ)^4255 ≤ (6019118876611/20000000000000 : ℝ)^3231 := by
    have hnat : (401795801 : ℕ)^4255*20000000000000^3231 ≤ 6019118876611^3231*1000000000^4255 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401795801 1000000000 6019118876611 20000000000000 4255 3231 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4255/1024 : ℝ)) 4255 3231 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165832983/5000000000 : ℝ), (933799011/2000000000 : ℝ), (401795801/1000000000 : ℝ)] ![(6645537361737/20000000000000 : ℝ), (18338359398493/50000000000000 : ℝ), (6019118876611/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165832983/5000000000 : ℝ)|^4255 ≤ (6645537361737/20000000000000 : ℝ)^3231
        have hw : |(2165832983/5000000000 : ℝ)|=(2165832983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(933799011/2000000000 : ℝ)|^4255 ≤ (18338359398493/50000000000000 : ℝ)^3231
        have hw : |(933799011/2000000000 : ℝ)|=(933799011/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401795801/1000000000 : ℝ)|^4255 ≤ (6019118876611/20000000000000 : ℝ)^3231
        have hw : |(401795801/1000000000 : ℝ)|=(401795801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1295_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9913/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9527/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1019/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9913/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9913/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6439/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9913/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9913/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6439/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9913/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9913/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6439/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6439/100000 : ℝ) ^ (2127/512 : ℝ) ≤ (1125843710021047/100000000000000000000 : ℝ) := by
    have hpowers : (6439/100000 : ℝ)^2127 ≤ (1125843710021047/100000000000000000000 : ℝ)^512 := by
      have hnat : (6439 : ℕ)^2127*100000000000000000000^512 ≤ 1125843710021047^512*100000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6439 100000 1125843710021047 100000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6439/100000 : ℝ)) (X := (1125843710021047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9913/50000 : ℝ) ^ (2127/512 : ℝ) ≤ (12036659627405611/10000000000000000000 : ℝ) := by
    have hpowers : (9913/50000 : ℝ)^2127 ≤ (12036659627405611/10000000000000000000 : ℝ)^512 := by
      have hnat : (9913 : ℕ)^2127*10000000000000000000^512 ≤ 12036659627405611^512*50000^2127 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9913 50000 12036659627405611 10000000000000000000 2127 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9913/50000 : ℝ)) (X := (12036659627405611/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001125843710021047/50000000000000000000 : ℝ) ≤ (5000027100472593/5000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (50001125843710021047/50000000000000000000 : ℝ)^512 ≤ (5000027100472593/5000000000000000 : ℝ)^2127 := by
      have hnat : (50001125843710021047 : ℕ)^512*5000000000000000^2127 ≤ 5000027100472593^2127*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001125843710021047 50000000000000000000 5000027100472593 5000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000027100472593/5000000000000000 : ℝ)) (X := (50001125843710021047/50000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100121492439984077157/100000000000000000000 : ℝ) ≤ (312591348523213/312500000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (100121492439984077157/100000000000000000000 : ℝ)^512 ≤ (312591348523213/312500000000000 : ℝ)^2127 := by
      have hnat : (100121492439984077157 : ℕ)^512*312500000000000^2127 ≤ 312591348523213^2127*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100121492439984077157 100000000000000000000 312591348523213 312500000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312591348523213/312500000000000 : ℝ)) (X := (100121492439984077157/100000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (5012036659627405611/5000000000000000000 : ℝ) ≤ (5002896052270223/5000000000000000 : ℝ) ^ (2127/512 : ℝ) := by
    have hpowers : (5012036659627405611/5000000000000000000 : ℝ)^512 ≤ (5002896052270223/5000000000000000 : ℝ)^2127 := by
      have hnat : (5012036659627405611 : ℕ)^512*5000000000000000^2127 ≤ 5002896052270223^2127*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5012036659627405611 5000000000000000000 5002896052270223 5000000000000000 512 2127 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002896052270223/5000000000000000 : ℝ)) (X := (5012036659627405611/5000000000000000000 : ℝ)) (by norm_num) 2127 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1125843710021047/100000000000000000000 : ℝ) ≤ ((66916889613401662921/66935000000000000000 : ℝ)+2*(286895179763/133870000000000 : ℝ)*(6439/100000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (66916889613401662921/66935000000000000000 : ℝ)+2*(286895179763/133870000000000 : ℝ)*(6439/100000 : ℝ)=(5000027100472593/5000000000000000 : ℝ) by norm_num, show 1+2*(1125843710021047/100000000000000000000 : ℝ)=(50001125843710021047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12036659627405611/10000000000000000000 : ℝ)+(1125843710021047/100000000000000000000 : ℝ) ≤ ((66916889613401662921/66935000000000000000 : ℝ)+(286895179763/133870000000000 : ℝ)*((9913/50000 : ℝ)+(6439/100000 : ℝ)))^(2127/512 : ℝ) := by
    rw [show (66916889613401662921/66935000000000000000 : ℝ)+(286895179763/133870000000000 : ℝ)*((9913/50000 : ℝ)+(6439/100000 : ℝ))=(312591348523213/312500000000000 : ℝ) by norm_num, show 1+(12036659627405611/10000000000000000000 : ℝ)+(1125843710021047/100000000000000000000 : ℝ)=(100121492439984077157/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12036659627405611/10000000000000000000 : ℝ) ≤ ((66916889613401662921/66935000000000000000 : ℝ)+2*(286895179763/133870000000000 : ℝ)*(9913/50000 : ℝ))^(2127/512 : ℝ) := by
    rw [show (66916889613401662921/66935000000000000000 : ℝ)+2*(286895179763/133870000000000 : ℝ)*(9913/50000 : ℝ)=(5002896052270223/5000000000000000 : ℝ) by norm_num, show 1+2*(12036659627405611/10000000000000000000 : ℝ)=(5012036659627405611/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66916889613401662921/66935000000000000000 : ℝ)*(X 1 0+X 2 0)+(286895179763/133870000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (6439/100000 : ℝ)) (hi := (9913/50000 : ℝ)) (c := (66916889613401662921/66935000000000000000 : ℝ)) (alpha := (286895179763/133870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66916889613401662921/66935000000000000000 : ℝ)*(X 0 1+X 2 1)+(286895179763/133870000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (6439/100000 : ℝ)) (hi := (9913/50000 : ℝ)) (c := (66916889613401662921/66935000000000000000 : ℝ)) (alpha := (286895179763/133870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66916889613401662921/66935000000000000000 : ℝ)*(X 0 2+X 1 2)+(286895179763/133870000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2127/512 : ℝ)) (lo := (6439/100000 : ℝ)) (hi := (9913/50000 : ℝ)) (c := (66916889613401662921/66935000000000000000 : ℝ)) (alpha := (286895179763/133870000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2073282293/10000000000 : ℝ)*X 0 0+(686666321/1250000000 : ℝ)*X 0 1+(5172661909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684679691/5000000000 : ℝ)*X 1 0+(-34991067/156250000 : ℝ)*X 1 1+(5172661973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167792479/312500000 : ℝ)*X 2 0+(1034532383/2000000000 : ℝ)*X 2 1+(-1119714217/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((216574981/500000000 : ℝ)*X 0 0+(802709583/2000000000 : ℝ)*X 0 1+(2336680617/5000000000 : ℝ)*X 0 2+(216574981/500000000 : ℝ)*X 1 0+(802709583/2000000000 : ℝ)*X 1 1+(2336680617/5000000000 : ℝ)*X 1 2+(216574981/500000000 : ℝ)*X 2 0+(802709583/2000000000 : ℝ)*X 2 1+(2336680617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2073363391/10000000000 : ℝ)*X 0 0+(5174783053/10000000000 : ℝ)*X 0 1+(686398707/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287143103/10000000000 : ℝ)*X 1 0+(-192090001/1000000000 : ℝ)*X 1 1+(5491189787/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643571631/5000000000 : ℝ)*X 2 0+(171599677/312500000 : ℝ)*X 2 1+(-1920899963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165832983/5000000000 : ℝ)*X 0 0+(933799011/2000000000 : ℝ)*X 0 1+(401795801/1000000000 : ℝ)*X 0 2+(2165832983/5000000000 : ℝ)*X 1 0+(933799011/2000000000 : ℝ)*X 1 1+(401795801/1000000000 : ℝ)*X 1 2+(2165832983/5000000000 : ℝ)*X 2 0+(933799011/2000000000 : ℝ)*X 2 1+(401795801/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1295_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2624858966800358882675860059/1673375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1242357281/100000000000000 : ℝ)*(base19) + (61298587/6250000000000 : ℝ)*(base23) + (24722353/20000000000000 : ℝ)*(lower2) + (24154631/5000000000000 : ℝ)*(upper3) + (22888393/12500000000000 : ℝ)*(upper5) + (1158525338257207/50000000000000 : ℝ)*(major0) + (1158525338257207/50000000000000 : ℝ)*(major1) + (1158525338257207/50000000000000 : ℝ)*(major2) + (779623206868757/25000000000000 : ℝ)*(sp0) + (12473983493591/400000000000 : ℝ)*(sp1) + (3118496134977639/100000000000000 : ℝ)*(sp2) + (757795308213643/50000000000000 : ℝ)*(sp3) + (1072070001/25000000000000 : ℝ)*(sp4) + (6784279889/50000000000000 : ℝ)*(sp7) + (303120836997413/20000000000000 : ℝ)*(f.failure) + (3118497115755031/100000000000000 : ℝ)*(f.sum) + (16140182476383/1673375000000000000000000000 : ℝ)*base65 + (2670091760620421647/3346750000000000000000000000000000 : ℝ)*base67 + (7874396943931578353/3346750000000000000000000000000000 : ℝ)*base70 + (539785441570578353/3346750000000000000000000000000000 : ℝ)*base72 + (17420726746001/3346750000000000000000000000 : ℝ)*base73 + (33129938292608921647/3346750000000000000000000000000000 : ℝ)*base75 + (33410061247528421647/3346750000000000000000000000000000 : ℝ)*base77 + (3189204248819671647/3346750000000000000000000000000000 : ℝ)*base79 + (21336574946239/6693500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1029371/200000000000000000000 : ℝ)*base89 + (1029371/200000000000000000000 : ℝ)*base91 + (1029371/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4407773129148428852466311769/418343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2005706711/100000000000000 : ℝ)*(base19) + (2377205259/100000000000000 : ℝ)*(base23) + (286104173/100000000000000 : ℝ)*(upper3) + (106932843/100000000000000 : ℝ)*(lower4) + (3326347/2000000000000 : ℝ)*(upper5) + (587062417320537/25000000000000 : ℝ)*(major0) + (587062417320537/25000000000000 : ℝ)*(major1) + (587062417320537/25000000000000 : ℝ)*(major2) + (20708813181/100000000000000 : ℝ)*(sp1) + (25480689267/100000000000000 : ℝ)*(sp2) + (3160487253891321/100000000000000 : ℝ)*(sp4) + (316046453937143/10000000000000 : ℝ)*(sp5) + (1580229697998397/50000000000000 : ℝ)*(sp6) + (768005866732361/50000000000000 : ℝ)*(sp7) + (768005866732361/50000000000000 : ℝ)*(f.failure) + (3160487253891321/100000000000000 : ℝ)*(f.sum) + (92315794817681/13387000000000000000000000000 : ℝ)*base65 + (6703655569900083577/1673375000000000000000000000000000 : ℝ)*base67 + (16620634604993708577/1673375000000000000000000000000000 : ℝ)*base69 + (17987758405486708577/1673375000000000000000000000000000 : ℝ)*base71 + (14221149605143/6693500000000000000000000000 : ℝ)*base74 + (9336885482817416423/1673375000000000000000000000000000 : ℝ)*base76 + (22607489661291208577/1673375000000000000000000000000000 : ℝ)*base77 + (21202578939825583577/1673375000000000000000000000000000 : ℝ)*base79 + (1271369615151/1673375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (7199913/500000000000000000000 : ℝ)*base90 + (7199913/500000000000000000000 : ℝ)*base92 + (7199913/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1295_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9913/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6439/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1295_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1295_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1295_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1295_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1295_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2127/512 : ℝ) ≤ p) (hpb : p ≤ (4255/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15287967/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9527/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1295_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
