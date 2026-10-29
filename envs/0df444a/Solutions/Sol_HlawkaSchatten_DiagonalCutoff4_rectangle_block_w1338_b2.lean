-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1338_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:30.049638+00:00
-- url     : https://prove2.me/submissions/a70f88e4-afb3-4d3e-9397-89486dadc2aa

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
theorem support_rectangle_w1338_s6_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-102371383/500000000 : ℝ)*x 0 + (541292997/1000000000 : ℝ)*x 1 + (327779401/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102371383/500000000 : ℝ)^2149 ≤ (623371815957/5000000000000 : ℝ)^1637 := by
    have hnat : (102371383 : ℕ)^2149*5000000000000^1637 ≤ 623371815957^1637*500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102371383 500000000 623371815957 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541292997/1000000000 : ℝ)^2149 ≤ (11168601685351/25000000000000 : ℝ)^1637 := by
    have hnat : (541292997 : ℕ)^2149*25000000000000^1637 ≤ 11168601685351^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541292997 1000000000 11168601685351 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327779401/625000000 : ℝ)^2149 ≤ (42858156919721/100000000000000 : ℝ)^1637 := by
    have hnat : (327779401 : ℕ)^2149*100000000000000^1637 ≤ 42858156919721^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327779401 625000000 42858156919721 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-102371383/500000000 : ℝ), (541292997/1000000000 : ℝ), (327779401/625000000 : ℝ)] ![(623371815957/5000000000000 : ℝ), (11168601685351/25000000000000 : ℝ), (42858156919721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-102371383/500000000 : ℝ)|^2149 ≤ (623371815957/5000000000000 : ℝ)^1637
        have hw : |(-102371383/500000000 : ℝ)|=(102371383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541292997/1000000000 : ℝ)|^2149 ≤ (11168601685351/25000000000000 : ℝ)^1637
        have hw : |(541292997/1000000000 : ℝ)|=(541292997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327779401/625000000 : ℝ)|^2149 ≤ (42858156919721/100000000000000 : ℝ)^1637
        have hw : |(327779401/625000000 : ℝ)|=(327779401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s6_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349071249/10000000000 : ℝ)*x 0 + (-213326267/1000000000 : ℝ)*x 1 + (5244470133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349071249/10000000000 : ℝ)^2149 ≤ (1759352040553/4000000000000 : ℝ)^1637 := by
    have hnat : (5349071249 : ℕ)^2149*4000000000000^1637 ≤ 1759352040553^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349071249 10000000000 1759352040553 4000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213326267/1000000000 : ℝ)^2149 ≤ (6579022544377/50000000000000 : ℝ)^1637 := by
    have hnat : (213326267 : ℕ)^2149*50000000000000^1637 ≤ 6579022544377^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213326267 1000000000 6579022544377 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244470133/10000000000 : ℝ)^2149 ≤ (42858153883691/100000000000000 : ℝ)^1637 := by
    have hnat : (5244470133 : ℕ)^2149*100000000000000^1637 ≤ 42858153883691^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244470133 10000000000 42858153883691 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349071249/10000000000 : ℝ), (-213326267/1000000000 : ℝ), (5244470133/10000000000 : ℝ)] ![(1759352040553/4000000000000 : ℝ), (6579022544377/50000000000000 : ℝ), (42858153883691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349071249/10000000000 : ℝ)|^2149 ≤ (1759352040553/4000000000000 : ℝ)^1637
        have hw : |(5349071249/10000000000 : ℝ)|=(5349071249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213326267/1000000000 : ℝ)|^2149 ≤ (6579022544377/50000000000000 : ℝ)^1637
        have hw : |(-213326267/1000000000 : ℝ)|=(213326267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244470133/10000000000 : ℝ)|^2149 ≤ (42858153883691/100000000000000 : ℝ)^1637
        have hw : |(5244470133/10000000000 : ℝ)|=(5244470133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s6_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (53490707/100000000 : ℝ)*x 0 + (5244470089/10000000000 : ℝ)*x 1 + (-106663173/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53490707/100000000 : ℝ)^2149 ≤ (43983795087651/100000000000000 : ℝ)^1637 := by
    have hnat : (53490707 : ℕ)^2149*100000000000000^1637 ≤ 43983795087651^1637*100000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53490707 100000000 43983795087651 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244470089/10000000000 : ℝ)^2149 ≤ (21429076705829/50000000000000 : ℝ)^1637 := by
    have hnat : (5244470089 : ℕ)^2149*50000000000000^1637 ≤ 21429076705829^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244470089 10000000000 21429076705829 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106663173/500000000 : ℝ)^2149 ≤ (13158051485541/100000000000000 : ℝ)^1637 := by
    have hnat : (106663173 : ℕ)^2149*100000000000000^1637 ≤ 13158051485541^1637*500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106663173 500000000 13158051485541 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53490707/100000000 : ℝ), (5244470089/10000000000 : ℝ), (-106663173/500000000 : ℝ)] ![(43983795087651/100000000000000 : ℝ), (21429076705829/50000000000000 : ℝ), (13158051485541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53490707/100000000 : ℝ)|^2149 ≤ (43983795087651/100000000000000 : ℝ)^1637
        have hw : |(53490707/100000000 : ℝ)|=(53490707/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244470089/10000000000 : ℝ)|^2149 ≤ (21429076705829/50000000000000 : ℝ)^1637
        have hw : |(5244470089/10000000000 : ℝ)|=(5244470089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106663173/500000000 : ℝ)|^2149 ≤ (13158051485541/100000000000000 : ℝ)^1637
        have hw : |(-106663173/500000000 : ℝ)|=(106663173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s6_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4327664613/10000000000 : ℝ)*x 0 + (259678807/625000000 : ℝ)*x 1 + (2253590823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327664613/10000000000 : ℝ)^2149 ≤ (33303174370817/100000000000000 : ℝ)^1637 := by
    have hnat : (4327664613 : ℕ)^2149*100000000000000^1637 ≤ 33303174370817^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327664613 10000000000 33303174370817 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259678807/625000000 : ℝ)^2149 ≤ (1578423193513/5000000000000 : ℝ)^1637 := by
    have hnat : (259678807 : ℕ)^2149*5000000000000^1637 ≤ 1578423193513^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259678807 625000000 1578423193513 5000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253590823/5000000000 : ℝ)^2149 ≤ (17564180871341/50000000000000 : ℝ)^1637 := by
    have hnat : (2253590823 : ℕ)^2149*50000000000000^1637 ≤ 17564180871341^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253590823 5000000000 17564180871341 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327664613/10000000000 : ℝ), (259678807/625000000 : ℝ), (2253590823/5000000000 : ℝ)] ![(33303174370817/100000000000000 : ℝ), (1578423193513/5000000000000 : ℝ), (17564180871341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327664613/10000000000 : ℝ)|^2149 ≤ (33303174370817/100000000000000 : ℝ)^1637
        have hw : |(4327664613/10000000000 : ℝ)|=(4327664613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259678807/625000000 : ℝ)|^2149 ≤ (1578423193513/5000000000000 : ℝ)^1637
        have hw : |(259678807/625000000 : ℝ)|=(259678807/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253590823/5000000000 : ℝ)|^2149 ≤ (17564180871341/50000000000000 : ℝ)^1637
        have hw : |(2253590823/5000000000 : ℝ)|=(2253590823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s6_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2047440289/10000000000 : ℝ)*x 0 + (5245073121/10000000000 : ℝ)*x 1 + (5412323857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2047440289/10000000000 : ℝ)^2149 ≤ (6233768636823/50000000000000 : ℝ)^1637 := by
    have hnat : (2047440289 : ℕ)^2149*50000000000000^1637 ≤ 6233768636823^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047440289 10000000000 6233768636823 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245073121/10000000000 : ℝ)^2149 ≤ (21432311433699/50000000000000 : ℝ)^1637 := by
    have hnat : (5245073121 : ℕ)^2149*50000000000000^1637 ≤ 21432311433699^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245073121 10000000000 21432311433699 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412323857/10000000000 : ℝ)^2149 ≤ (22333919922877/50000000000000 : ℝ)^1637 := by
    have hnat : (5412323857 : ℕ)^2149*50000000000000^1637 ≤ 22333919922877^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412323857 10000000000 22333919922877 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2047440289/10000000000 : ℝ), (5245073121/10000000000 : ℝ), (5412323857/10000000000 : ℝ)] ![(6233768636823/50000000000000 : ℝ), (21432311433699/50000000000000 : ℝ), (22333919922877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2047440289/10000000000 : ℝ)|^2149 ≤ (6233768636823/50000000000000 : ℝ)^1637
        have hw : |(-2047440289/10000000000 : ℝ)|=(2047440289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245073121/10000000000 : ℝ)|^2149 ≤ (21432311433699/50000000000000 : ℝ)^1637
        have hw : |(5245073121/10000000000 : ℝ)|=(5245073121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412323857/10000000000 : ℝ)|^2149 ≤ (22333919922877/50000000000000 : ℝ)^1637
        have hw : |(5412323857/10000000000 : ℝ)|=(5412323857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s6_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652849787/5000000000 : ℝ)*x 0 + (-1965409279/10000000000 : ℝ)*x 1 + (676540489/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652849787/5000000000 : ℝ)^2149 ≤ (21758110336281/50000000000000 : ℝ)^1637 := by
    have hnat : (2652849787 : ℕ)^2149*50000000000000^1637 ≤ 21758110336281^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652849787 5000000000 21758110336281 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965409279/10000000000 : ℝ)^2149 ≤ (11815938870293/100000000000000 : ℝ)^1637 := by
    have hnat : (1965409279 : ℕ)^2149*100000000000000^1637 ≤ 11815938870293^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965409279 10000000000 11815938870293 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676540489/1250000000 : ℝ)^2149 ≤ (22333920220819/50000000000000 : ℝ)^1637 := by
    have hnat : (676540489 : ℕ)^2149*50000000000000^1637 ≤ 22333920220819^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676540489 1250000000 22333920220819 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652849787/5000000000 : ℝ), (-1965409279/10000000000 : ℝ), (676540489/1250000000 : ℝ)] ![(21758110336281/50000000000000 : ℝ), (11815938870293/100000000000000 : ℝ), (22333920220819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652849787/5000000000 : ℝ)|^2149 ≤ (21758110336281/50000000000000 : ℝ)^1637
        have hw : |(2652849787/5000000000 : ℝ)|=(2652849787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1965409279/10000000000 : ℝ)|^2149 ≤ (11815938870293/100000000000000 : ℝ)^1637
        have hw : |(-1965409279/10000000000 : ℝ)|=(1965409279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676540489/1250000000 : ℝ)|^2149 ≤ (22333920220819/50000000000000 : ℝ)^1637
        have hw : |(676540489/1250000000 : ℝ)|=(676540489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s6_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (265284981/500000000 : ℝ)*x 0 + (5412323859/10000000000 : ℝ)*x 1 + (-1965409289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265284981/500000000 : ℝ)^2149 ≤ (21758110583923/50000000000000 : ℝ)^1637 := by
    have hnat : (265284981 : ℕ)^2149*50000000000000^1637 ≤ 21758110583923^1637*500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265284981 500000000 21758110583923 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412323859/10000000000 : ℝ)^2149 ≤ (22333919933711/50000000000000 : ℝ)^1637 := by
    have hnat : (5412323859 : ℕ)^2149*50000000000000^1637 ≤ 22333919933711^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412323859 10000000000 22333919933711 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965409289/10000000000 : ℝ)^2149 ≤ (369248092163/3125000000000 : ℝ)^1637 := by
    have hnat : (1965409289 : ℕ)^2149*3125000000000^1637 ≤ 369248092163^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965409289 10000000000 369248092163 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265284981/500000000 : ℝ), (5412323859/10000000000 : ℝ), (-1965409289/10000000000 : ℝ)] ![(21758110583923/50000000000000 : ℝ), (22333919933711/50000000000000 : ℝ), (369248092163/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265284981/500000000 : ℝ)|^2149 ≤ (21758110583923/50000000000000 : ℝ)^1637
        have hw : |(265284981/500000000 : ℝ)|=(265284981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412323859/10000000000 : ℝ)|^2149 ≤ (22333919933711/50000000000000 : ℝ)^1637
        have hw : |(5412323859/10000000000 : ℝ)|=(5412323859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965409289/10000000000 : ℝ)|^2149 ≤ (369248092163/3125000000000 : ℝ)^1637
        have hw : |(-1965409289/10000000000 : ℝ)|=(1965409289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s6_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081922523/2500000000 : ℝ)*x 0 + (4505920361/10000000000 : ℝ)*x 1 + (831225759/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081922523/2500000000 : ℝ)^2149 ≤ (6660686353453/20000000000000 : ℝ)^1637 := by
    have hnat : (1081922523 : ℕ)^2149*20000000000000^1637 ≤ 6660686353453^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081922523 2500000000 6660686353453 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505920361/10000000000 : ℝ)^2149 ≤ (7023091486493/20000000000000 : ℝ)^1637 := by
    have hnat : (4505920361 : ℕ)^2149*20000000000000^1637 ≤ 7023091486493^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505920361 10000000000 7023091486493 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831225759/2000000000 : ℝ)^2149 ≤ (15790555392601/50000000000000 : ℝ)^1637 := by
    have hnat : (831225759 : ℕ)^2149*50000000000000^1637 ≤ 15790555392601^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831225759 2000000000 15790555392601 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081922523/2500000000 : ℝ), (4505920361/10000000000 : ℝ), (831225759/2000000000 : ℝ)] ![(6660686353453/20000000000000 : ℝ), (7023091486493/20000000000000 : ℝ), (15790555392601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081922523/2500000000 : ℝ)|^2149 ≤ (6660686353453/20000000000000 : ℝ)^1637
        have hw : |(1081922523/2500000000 : ℝ)|=(1081922523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505920361/10000000000 : ℝ)|^2149 ≤ (7023091486493/20000000000000 : ℝ)^1637
        have hw : |(4505920361/10000000000 : ℝ)|=(4505920361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831225759/2000000000 : ℝ)|^2149 ≤ (15790555392601/50000000000000 : ℝ)^1637
        have hw : |(831225759/2000000000 : ℝ)|=(831225759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11139/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14713/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14713/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11131/100000 : ℝ) ^ (4297/1024 : ℝ) ≤ (9976582990820423/100000000000000000000 : ℝ) := by
    have hpowers : (11131/100000 : ℝ)^4297 ≤ (9976582990820423/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11131 : ℕ)^4297*100000000000000000000^1024 ≤ 9976582990820423^1024*100000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11131 100000 9976582990820423 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11131/100000 : ℝ)) (X := (9976582990820423/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14713/100000 : ℝ) ^ (4297/1024 : ℝ) ≤ (32168721111015901/100000000000000000000 : ℝ) := by
    have hpowers : (14713/100000 : ℝ)^4297 ≤ (32168721111015901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14713 : ℕ)^4297*100000000000000000000^1024 ≤ 32168721111015901^1024*100000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14713 100000 32168721111015901 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14713/100000 : ℝ)) (X := (32168721111015901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009976582990820423/50000000000000000000 : ℝ) ≤ (10000475459378513/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50009976582990820423/50000000000000000000 : ℝ)^1024 ≤ (10000475459378513/10000000000000000 : ℝ)^4297 := by
      have hnat : (50009976582990820423 : ℕ)^1024*10000000000000000^4297 ≤ 10000475459378513^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009976582990820423 50000000000000000000 10000475459378513 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000475459378513/10000000000000000 : ℝ)) (X := (50009976582990820423/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010536326025459081/25000000000000000000 : ℝ) ≤ (10001004185851837/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (25010536326025459081/25000000000000000000 : ℝ)^1024 ≤ (10001004185851837/10000000000000000 : ℝ)^4297 := by
      have hnat : (25010536326025459081 : ℕ)^1024*10000000000000000^4297 ≤ 10001004185851837^4297*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010536326025459081 25000000000000000000 10001004185851837 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001004185851837/10000000000000000 : ℝ)) (X := (25010536326025459081/25000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032168721111015901/50000000000000000000 : ℝ) ≤ (10001532912325161/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50032168721111015901/50000000000000000000 : ℝ)^1024 ≤ (10001532912325161/10000000000000000 : ℝ)^4297 := by
      have hnat : (50032168721111015901 : ℕ)^1024*10000000000000000^4297 ≤ 10001532912325161^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032168721111015901 50000000000000000000 10001532912325161 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001532912325161/10000000000000000 : ℝ)) (X := (50032168721111015901/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9976582990820423/100000000000000000000 : ℝ) ≤ ((17904966293372347339/17910000000000000000 : ℝ)+2*(132181618331/89550000000000 : ℝ)*(11131/100000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (17904966293372347339/17910000000000000000 : ℝ)+2*(132181618331/89550000000000 : ℝ)*(11131/100000 : ℝ)=(10000475459378513/10000000000000000 : ℝ) by norm_num, show 1+2*(9976582990820423/100000000000000000000 : ℝ)=(50009976582990820423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32168721111015901/100000000000000000000 : ℝ)+(9976582990820423/100000000000000000000 : ℝ) ≤ ((17904966293372347339/17910000000000000000 : ℝ)+(132181618331/89550000000000 : ℝ)*((14713/100000 : ℝ)+(11131/100000 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (17904966293372347339/17910000000000000000 : ℝ)+(132181618331/89550000000000 : ℝ)*((14713/100000 : ℝ)+(11131/100000 : ℝ))=(10001004185851837/10000000000000000 : ℝ) by norm_num, show 1+(32168721111015901/100000000000000000000 : ℝ)+(9976582990820423/100000000000000000000 : ℝ)=(25010536326025459081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32168721111015901/100000000000000000000 : ℝ) ≤ ((17904966293372347339/17910000000000000000 : ℝ)+2*(132181618331/89550000000000 : ℝ)*(14713/100000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (17904966293372347339/17910000000000000000 : ℝ)+2*(132181618331/89550000000000 : ℝ)*(14713/100000 : ℝ)=(10001532912325161/10000000000000000 : ℝ) by norm_num, show 1+2*(32168721111015901/100000000000000000000 : ℝ)=(50032168721111015901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17904966293372347339/17910000000000000000 : ℝ)*(X 1 0+X 2 0)+(132181618331/89550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (17904966293372347339/17910000000000000000 : ℝ)) (alpha := (132181618331/89550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17904966293372347339/17910000000000000000 : ℝ)*(X 0 1+X 2 1)+(132181618331/89550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (17904966293372347339/17910000000000000000 : ℝ)) (alpha := (132181618331/89550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17904966293372347339/17910000000000000000 : ℝ)*(X 0 2+X 1 2)+(132181618331/89550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (14713/100000 : ℝ)) (c := (17904966293372347339/17910000000000000000 : ℝ)) (alpha := (132181618331/89550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-102371383/500000000 : ℝ)*X 0 0+(541292997/1000000000 : ℝ)*X 0 1+(327779401/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349071249/10000000000 : ℝ)*X 1 0+(-213326267/1000000000 : ℝ)*X 1 1+(5244470133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53490707/100000000 : ℝ)*X 2 0+(5244470089/10000000000 : ℝ)*X 2 1+(-106663173/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327664613/10000000000 : ℝ)*X 0 0+(259678807/625000000 : ℝ)*X 0 1+(2253590823/5000000000 : ℝ)*X 0 2+(4327664613/10000000000 : ℝ)*X 1 0+(259678807/625000000 : ℝ)*X 1 1+(2253590823/5000000000 : ℝ)*X 1 2+(4327664613/10000000000 : ℝ)*X 2 0+(259678807/625000000 : ℝ)*X 2 1+(2253590823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2047440289/10000000000 : ℝ)*X 0 0+(5245073121/10000000000 : ℝ)*X 0 1+(5412323857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652849787/5000000000 : ℝ)*X 1 0+(-1965409279/10000000000 : ℝ)*X 1 1+(676540489/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265284981/500000000 : ℝ)*X 2 0+(5412323859/10000000000 : ℝ)*X 2 1+(-1965409289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081922523/2500000000 : ℝ)*X 0 0+(4505920361/10000000000 : ℝ)*X 0 1+(831225759/2000000000 : ℝ)*X 0 2+(1081922523/2500000000 : ℝ)*X 1 0+(4505920361/10000000000 : ℝ)*X 1 1+(831225759/2000000000 : ℝ)*X 1 2+(1081922523/2500000000 : ℝ)*X 2 0+(4505920361/10000000000 : ℝ)*X 2 1+(831225759/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1141995311409681749545230511/149250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233240709/25000000000000 : ℝ)*(base19) + (789175311/100000000000000 : ℝ)*(base23) + (118416447/100000000000000 : ℝ)*(upper3) + (158627547/50000000000000 : ℝ)*(lower4) + (2193631712856851/50000000000000 : ℝ)*(major0) + (2193631712856851/50000000000000 : ℝ)*(major1) + (2193631712856851/50000000000000 : ℝ)*(major2) + (5936169392998517/100000000000000 : ℝ)*(sp0) + (5936177829099331/100000000000000 : ℝ)*(sp1) + (1484040557886491/25000000000000 : ℝ)*(sp2) + (141916848894407/5000000000000 : ℝ)*(sp3) + (187381273/2000000000000 : ℝ)*(sp4) + (15741340893/100000000000000 : ℝ)*(sp6) + (5428212547/50000000000000 : ℝ)*(sp7) + (1419173917156617/50000000000000 : ℝ)*(f.failure) + (742022345257771/12500000000000 : ℝ)*(f.sum) + (29985265093183/4477500000000000000000000000 : ℝ)*base66 + (3737817361486969489/895500000000000000000000000000000 : ℝ)*base67 + (3503104538707969489/895500000000000000000000000000000 : ℝ)*base69 + (1612225719614530511/895500000000000000000000000000000 : ℝ)*base72 + (4961478913/1093139648437500000000000 : ℝ)*base74 + (4277792722362469489/895500000000000000000000000000000 : ℝ)*base75 + (715813241830030511/895500000000000000000000000000000 : ℝ)*base78 + (5640816881130469489/895500000000000000000000000000000 : ℝ)*base79 + (28509828600109/8955000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6673069/1250000000000000000000 : ℝ)*base89 + (6673069/1250000000000000000000 : ℝ)*base91 + (6673069/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (419827007686463030836495369/74625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (479850451/50000000000000 : ℝ)*(base19) + (1091370833/100000000000000 : ℝ)*(base23) + (57590209/50000000000000 : ℝ)*(upper3) + (38440627/100000000000000 : ℝ)*(lower4) + (131614199/100000000000000 : ℝ)*(upper5) + (2209473082626229/50000000000000 : ℝ)*(major0) + (2209473082626229/50000000000000 : ℝ)*(major1) + (2209473082626229/50000000000000 : ℝ)*(major2) + (4265427107/20000000000000 : ℝ)*(sp1) + (22230304249/100000000000000 : ℝ)*(sp2) + (1494761776068261/25000000000000 : ℝ)*(sp4) + (5979024817436607/100000000000000 : ℝ)*(sp5) + (2989511891298981/50000000000000 : ℝ)*(sp6) + (714711259676111/25000000000000 : ℝ)*(sp7) + (714711259676111/25000000000000 : ℝ)*(f.failure) + (1494761776068261/25000000000000 : ℝ)*(f.sum) + (7863802436017/1119375000000000000000000000 : ℝ)*base65 + (5135627369795554631/895500000000000000000000000000000 : ℝ)*base67 + (1315949617344445369/895500000000000000000000000000000 : ℝ)*base70 + (4656380062024054631/895500000000000000000000000000000 : ℝ)*base71 + (66762588712841/8955000000000000000000000000 : ℝ)*base73 + (2554838358895054631/895500000000000000000000000000000 : ℝ)*base75 + (2255598196205554631/895500000000000000000000000000000 : ℝ)*base77 + (9919179543673054631/895500000000000000000000000000000 : ℝ)*base79 + (10911296683093/4477500000000000000000000000 : ℝ)*base81 + (6421973/625000000000000000000 : ℝ)*base90 + (6421973/625000000000000000000 : ℝ)*base92 + (6421973/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1338_s7_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-81897417/400000000 : ℝ)*x 0 + (2706431131/5000000000 : ℝ)*x 1 + (5244533011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81897417/400000000 : ℝ)^2149 ≤ (12467498391469/100000000000000 : ℝ)^1637 := by
    have hnat : (81897417 : ℕ)^2149*100000000000000^1637 ≤ 12467498391469^1637*400000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81897417 400000000 12467498391469 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706431131/5000000000 : ℝ)^2149 ≤ (44673673151649/100000000000000 : ℝ)^1637 := by
    have hnat : (2706431131 : ℕ)^2149*100000000000000^1637 ≤ 44673673151649^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706431131 5000000000 44673673151649 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244533011/10000000000 : ℝ)^2149 ≤ (8571765688281/20000000000000 : ℝ)^1637 := by
    have hnat : (5244533011 : ℕ)^2149*20000000000000^1637 ≤ 8571765688281^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244533011 10000000000 8571765688281 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-81897417/400000000 : ℝ), (2706431131/5000000000 : ℝ), (5244533011/10000000000 : ℝ)] ![(12467498391469/100000000000000 : ℝ), (44673673151649/100000000000000 : ℝ), (8571765688281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-81897417/400000000 : ℝ)|^2149 ≤ (12467498391469/100000000000000 : ℝ)^1637
        have hw : |(-81897417/400000000 : ℝ)|=(81897417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706431131/5000000000 : ℝ)|^2149 ≤ (44673673151649/100000000000000 : ℝ)^1637
        have hw : |(2706431131/5000000000 : ℝ)|=(2706431131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244533011/10000000000 : ℝ)|^2149 ≤ (8571765688281/20000000000000 : ℝ)^1637
        have hw : |(5244533011/10000000000 : ℝ)|=(5244533011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s7_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167157891/312500000 : ℝ)*x 0 + (-426640757/2000000000 : ℝ)*x 1 + (5244533431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167157891/312500000 : ℝ)^2149 ≤ (8796719751517/20000000000000 : ℝ)^1637 := by
    have hnat : (167157891 : ℕ)^2149*20000000000000^1637 ≤ 8796719751517^1637*312500000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167157891 312500000 8796719751517 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426640757/2000000000 : ℝ)^2149 ≤ (13157568287293/100000000000000 : ℝ)^1637 := by
    have hnat : (426640757 : ℕ)^2149*100000000000000^1637 ≤ 13157568287293^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426640757 2000000000 13157568287293 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244533431/10000000000 : ℝ)^2149 ≤ (4285883294719/10000000000000 : ℝ)^1637 := by
    have hnat : (5244533431 : ℕ)^2149*10000000000000^1637 ≤ 4285883294719^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244533431 10000000000 4285883294719 10000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167157891/312500000 : ℝ), (-426640757/2000000000 : ℝ), (5244533431/10000000000 : ℝ)] ![(8796719751517/20000000000000 : ℝ), (13157568287293/100000000000000 : ℝ), (4285883294719/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167157891/312500000 : ℝ)|^2149 ≤ (8796719751517/20000000000000 : ℝ)^1637
        have hw : |(167157891/312500000 : ℝ)|=(167157891/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426640757/2000000000 : ℝ)|^2149 ≤ (13157568287293/100000000000000 : ℝ)^1637
        have hw : |(-426640757/2000000000 : ℝ)|=(426640757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244533431/10000000000 : ℝ)|^2149 ≤ (4285883294719/10000000000000 : ℝ)^1637
        have hw : |(5244533431/10000000000 : ℝ)|=(5244533431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s7_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349054843/10000000000 : ℝ)*x 0 + (5244531891/10000000000 : ℝ)*x 1 + (-1066601359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349054843/10000000000 : ℝ)^2149 ≤ (21991811959757/50000000000000 : ℝ)^1637 := by
    have hnat : (5349054843 : ℕ)^2149*50000000000000^1637 ≤ 21991811959757^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349054843 10000000000 21991811959757 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244531891/10000000000 : ℝ)^2149 ≤ (21429408212989/50000000000000 : ℝ)^1637 := by
    have hnat : (5244531891 : ℕ)^2149*50000000000000^1637 ≤ 21429408212989^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244531891 10000000000 21429408212989 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066601359/5000000000 : ℝ)^2149 ≤ (6578779823829/50000000000000 : ℝ)^1637 := by
    have hnat : (1066601359 : ℕ)^2149*50000000000000^1637 ≤ 6578779823829^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066601359 5000000000 6578779823829 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349054843/10000000000 : ℝ), (5244531891/10000000000 : ℝ), (-1066601359/5000000000 : ℝ)] ![(21991811959757/50000000000000 : ℝ), (21429408212989/50000000000000 : ℝ), (6578779823829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349054843/10000000000 : ℝ)|^2149 ≤ (21991811959757/50000000000000 : ℝ)^1637
        have hw : |(5349054843/10000000000 : ℝ)|=(5349054843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244531891/10000000000 : ℝ)|^2149 ≤ (21429408212989/50000000000000 : ℝ)^1637
        have hw : |(5244531891/10000000000 : ℝ)|=(5244531891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066601359/5000000000 : ℝ)|^2149 ≤ (6578779823829/50000000000000 : ℝ)^1637
        have hw : |(-1066601359/5000000000 : ℝ)|=(1066601359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s7_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (865534331/2000000000 : ℝ)*x 0 + (4154993967/10000000000 : ℝ)*x 1 + (2253522491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865534331/2000000000 : ℝ)^2149 ≤ (2081452844447/6250000000000 : ℝ)^1637 := by
    have hnat : (865534331 : ℕ)^2149*6250000000000^1637 ≤ 2081452844447^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865534331 2000000000 2081452844447 6250000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154993967/10000000000 : ℝ)^2149 ≤ (31569791014327/100000000000000 : ℝ)^1637 := by
    have hnat : (4154993967 : ℕ)^2149*100000000000000^1637 ≤ 31569791014327^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154993967 10000000000 31569791014327 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253522491/5000000000 : ℝ)^2149 ≤ (35126963467531/100000000000000 : ℝ)^1637 := by
    have hnat : (2253522491 : ℕ)^2149*100000000000000^1637 ≤ 35126963467531^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253522491 5000000000 35126963467531 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865534331/2000000000 : ℝ), (4154993967/10000000000 : ℝ), (2253522491/5000000000 : ℝ)] ![(2081452844447/6250000000000 : ℝ), (31569791014327/100000000000000 : ℝ), (35126963467531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865534331/2000000000 : ℝ)|^2149 ≤ (2081452844447/6250000000000 : ℝ)^1637
        have hw : |(865534331/2000000000 : ℝ)|=(865534331/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154993967/10000000000 : ℝ)|^2149 ≤ (31569791014327/100000000000000 : ℝ)^1637
        have hw : |(4154993967/10000000000 : ℝ)|=(4154993967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253522491/5000000000 : ℝ)|^2149 ≤ (35126963467531/100000000000000 : ℝ)^1637
        have hw : |(2253522491/5000000000 : ℝ)|=(2253522491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s7_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-511861733/2500000000 : ℝ)*x 0 + (104902689/200000000 : ℝ)*x 1 + (2706129113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511861733/2500000000 : ℝ)^2149 ≤ (6233795188481/50000000000000 : ℝ)^1637 := by
    have hnat : (511861733 : ℕ)^2149*50000000000000^1637 ≤ 6233795188481^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511861733 2500000000 6233795188481 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104902689/200000000 : ℝ)^2149 ≤ (42865280831007/100000000000000 : ℝ)^1637 := by
    have hnat : (104902689 : ℕ)^2149*100000000000000^1637 ≤ 42865280831007^1637*200000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104902689 200000000 42865280831007 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706129113/5000000000 : ℝ)^2149 ≤ (8933425756869/20000000000000 : ℝ)^1637 := by
    have hnat : (2706129113 : ℕ)^2149*20000000000000^1637 ≤ 8933425756869^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706129113 5000000000 8933425756869 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-511861733/2500000000 : ℝ), (104902689/200000000 : ℝ), (2706129113/5000000000 : ℝ)] ![(6233795188481/50000000000000 : ℝ), (42865280831007/100000000000000 : ℝ), (8933425756869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-511861733/2500000000 : ℝ)|^2149 ≤ (6233795188481/50000000000000 : ℝ)^1637
        have hw : |(-511861733/2500000000 : ℝ)|=(511861733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104902689/200000000 : ℝ)|^2149 ≤ (42865280831007/100000000000000 : ℝ)^1637
        have hw : |(104902689/200000000 : ℝ)|=(104902689/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706129113/5000000000 : ℝ)|^2149 ≤ (8933425756869/20000000000000 : ℝ)^1637
        have hw : |(2706129113/5000000000 : ℝ)|=(2706129113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s7_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652858197/5000000000 : ℝ)*x 0 + (-1965476677/10000000000 : ℝ)*x 1 + (54122581/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652858197/5000000000 : ℝ)^2149 ≤ (43516401774233/100000000000000 : ℝ)^1637 := by
    have hnat : (2652858197 : ℕ)^2149*100000000000000^1637 ≤ 43516401774233^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652858197 5000000000 43516401774233 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965476677/10000000000 : ℝ)^2149 ≤ (11816470797627/100000000000000 : ℝ)^1637 := by
    have hnat : (1965476677 : ℕ)^2149*100000000000000^1637 ≤ 11816470797627^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965476677 10000000000 11816470797627 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54122581/100000000 : ℝ)^2149 ≤ (8933425483847/20000000000000 : ℝ)^1637 := by
    have hnat : (54122581 : ℕ)^2149*20000000000000^1637 ≤ 8933425483847^1637*100000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54122581 100000000 8933425483847 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652858197/5000000000 : ℝ), (-1965476677/10000000000 : ℝ), (54122581/100000000 : ℝ)] ![(43516401774233/100000000000000 : ℝ), (11816470797627/100000000000000 : ℝ), (8933425483847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652858197/5000000000 : ℝ)|^2149 ≤ (43516401774233/100000000000000 : ℝ)^1637
        have hw : |(2652858197/5000000000 : ℝ)|=(2652858197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1965476677/10000000000 : ℝ)|^2149 ≤ (11816470797627/100000000000000 : ℝ)^1637
        have hw : |(-1965476677/10000000000 : ℝ)|=(1965476677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54122581/100000000 : ℝ)|^2149 ≤ (8933425483847/20000000000000 : ℝ)^1637
        have hw : |(54122581/100000000 : ℝ)|=(54122581/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s7_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326429103/2500000000 : ℝ)*x 0 + (541225801/1000000000 : ℝ)*x 1 + (-245684597/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326429103/2500000000 : ℝ)^2149 ≤ (1087910049201/2500000000000 : ℝ)^1637 := by
    have hnat : (1326429103 : ℕ)^2149*2500000000000^1637 ≤ 1087910049201^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326429103 2500000000 1087910049201 2500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541225801/1000000000 : ℝ)^2149 ≤ (11166781611039/25000000000000 : ℝ)^1637 := by
    have hnat : (541225801 : ℕ)^2149*25000000000000^1637 ≤ 11166781611039^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541225801 1000000000 11166781611039 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245684597/1250000000 : ℝ)^2149 ≤ (2954117894743/25000000000000 : ℝ)^1637 := by
    have hnat : (245684597 : ℕ)^2149*25000000000000^1637 ≤ 2954117894743^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245684597 1250000000 2954117894743 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326429103/2500000000 : ℝ), (541225801/1000000000 : ℝ), (-245684597/1250000000 : ℝ)] ![(1087910049201/2500000000000 : ℝ), (11166781611039/25000000000000 : ℝ), (2954117894743/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326429103/2500000000 : ℝ)|^2149 ≤ (1087910049201/2500000000000 : ℝ)^1637
        have hw : |(1326429103/2500000000 : ℝ)|=(1326429103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541225801/1000000000 : ℝ)|^2149 ≤ (11166781611039/25000000000000 : ℝ)^1637
        have hw : |(541225801/1000000000 : ℝ)|=(541225801/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245684597/1250000000 : ℝ)|^2149 ≤ (2954117894743/25000000000000 : ℝ)^1637
        have hw : |(-245684597/1250000000 : ℝ)|=(245684597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_s7_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1081923649/2500000000 : ℝ)*x 0 + (4505787003/10000000000 : ℝ)*x 1 + (1039065251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081923649/2500000000 : ℝ)^2149 ≤ (1040733664627/3125000000000 : ℝ)^1637 := by
    have hnat : (1081923649 : ℕ)^2149*3125000000000^1637 ≤ 1040733664627^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081923649 2500000000 1040733664627 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505787003/10000000000 : ℝ)^2149 ≤ (3511409310187/10000000000000 : ℝ)^1637 := by
    have hnat : (4505787003 : ℕ)^2149*10000000000000^1637 ≤ 3511409310187^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505787003 10000000000 3511409310187 10000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039065251/2500000000 : ℝ)^2149 ≤ (31582429616729/100000000000000 : ℝ)^1637 := by
    have hnat : (1039065251 : ℕ)^2149*100000000000000^1637 ≤ 31582429616729^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039065251 2500000000 31582429616729 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081923649/2500000000 : ℝ), (4505787003/10000000000 : ℝ), (1039065251/2500000000 : ℝ)] ![(1040733664627/3125000000000 : ℝ), (3511409310187/10000000000000 : ℝ), (31582429616729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081923649/2500000000 : ℝ)|^2149 ≤ (1040733664627/3125000000000 : ℝ)^1637
        have hw : |(1081923649/2500000000 : ℝ)|=(1081923649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505787003/10000000000 : ℝ)|^2149 ≤ (3511409310187/10000000000000 : ℝ)^1637
        have hw : |(4505787003/10000000000 : ℝ)|=(4505787003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039065251/2500000000 : ℝ)|^2149 ≤ (31582429616729/100000000000000 : ℝ)^1637
        have hw : |(1039065251/2500000000 : ℝ)|=(1039065251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (557/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (919/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11139/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11139/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11139/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11139/100000 : ℝ) ^ (4297/1024 : ℝ) ≤ (1000670624115837/10000000000000000000 : ℝ) := by
    have hpowers : (11139/100000 : ℝ)^4297 ≤ (1000670624115837/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11139 : ℕ)^4297*10000000000000000000^1024 ≤ 1000670624115837^1024*100000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11139 100000 1000670624115837 10000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11139/100000 : ℝ)) (X := (1000670624115837/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (4297/1024 : ℝ) ≤ (32095386238387611/100000000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^4297 ≤ (32095386238387611/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2941 : ℕ)^4297*100000000000000000000^1024 ≤ 32095386238387611^1024*20000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 32095386238387611 100000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (32095386238387611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001000670624115837/5000000000000000000 : ℝ) ≤ (5000238447434521/5000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (5001000670624115837/5000000000000000000 : ℝ)^1024 ≤ (5000238447434521/5000000000000000 : ℝ)^4297 := by
      have hnat : (5001000670624115837 : ℕ)^1024*5000000000000000^4297 ≤ 5000238447434521^4297*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001000670624115837 5000000000000000000 5000238447434521 5000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000238447434521/5000000000000000 : ℝ)) (X := (5001000670624115837/5000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042102092479545981/100000000000000000000 : ℝ) ≤ (10001003156424117/10000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (100042102092479545981/100000000000000000000 : ℝ)^1024 ≤ (10001003156424117/10000000000000000 : ℝ)^4297 := by
      have hnat : (100042102092479545981 : ℕ)^1024*10000000000000000^4297 ≤ 10001003156424117^4297*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042102092479545981 100000000000000000000 10001003156424117 10000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001003156424117/10000000000000000 : ℝ)) (X := (100042102092479545981/100000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032095386238387611/50000000000000000000 : ℝ) ≤ (1250191177247399/1250000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50032095386238387611/50000000000000000000 : ℝ)^1024 ≤ (1250191177247399/1250000000000000 : ℝ)^4297 := by
      have hnat : (50032095386238387611 : ℕ)^1024*1250000000000000^4297 ≤ 1250191177247399^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032095386238387611 50000000000000000000 1250191177247399 1250000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250191177247399/1250000000000000 : ℝ)) (X := (50032095386238387611/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1000670624115837/10000000000000000000 : ℝ) ≤ ((17824988276089521461/17830000000000000000 : ℝ)+2*(21050462203/14264000000000 : ℝ)*(11139/100000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (17824988276089521461/17830000000000000000 : ℝ)+2*(21050462203/14264000000000 : ℝ)*(11139/100000 : ℝ)=(5000238447434521/5000000000000000 : ℝ) by norm_num, show 1+2*(1000670624115837/10000000000000000000 : ℝ)=(5001000670624115837/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32095386238387611/100000000000000000000 : ℝ)+(1000670624115837/10000000000000000000 : ℝ) ≤ ((17824988276089521461/17830000000000000000 : ℝ)+(21050462203/14264000000000 : ℝ)*((2941/20000 : ℝ)+(11139/100000 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (17824988276089521461/17830000000000000000 : ℝ)+(21050462203/14264000000000 : ℝ)*((2941/20000 : ℝ)+(11139/100000 : ℝ))=(10001003156424117/10000000000000000 : ℝ) by norm_num, show 1+(32095386238387611/100000000000000000000 : ℝ)+(1000670624115837/10000000000000000000 : ℝ)=(100042102092479545981/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32095386238387611/100000000000000000000 : ℝ) ≤ ((17824988276089521461/17830000000000000000 : ℝ)+2*(21050462203/14264000000000 : ℝ)*(2941/20000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (17824988276089521461/17830000000000000000 : ℝ)+2*(21050462203/14264000000000 : ℝ)*(2941/20000 : ℝ)=(1250191177247399/1250000000000000 : ℝ) by norm_num, show 1+2*(32095386238387611/100000000000000000000 : ℝ)=(50032095386238387611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17824988276089521461/17830000000000000000 : ℝ)*(X 1 0+X 2 0)+(21050462203/14264000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (17824988276089521461/17830000000000000000 : ℝ)) (alpha := (21050462203/14264000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17824988276089521461/17830000000000000000 : ℝ)*(X 0 1+X 2 1)+(21050462203/14264000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (17824988276089521461/17830000000000000000 : ℝ)) (alpha := (21050462203/14264000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17824988276089521461/17830000000000000000 : ℝ)*(X 0 2+X 1 2)+(21050462203/14264000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (11139/100000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (17824988276089521461/17830000000000000000 : ℝ)) (alpha := (21050462203/14264000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-81897417/400000000 : ℝ)*X 0 0+(2706431131/5000000000 : ℝ)*X 0 1+(5244533011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167157891/312500000 : ℝ)*X 1 0+(-426640757/2000000000 : ℝ)*X 1 1+(5244533431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349054843/10000000000 : ℝ)*X 2 0+(5244531891/10000000000 : ℝ)*X 2 1+(-1066601359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865534331/2000000000 : ℝ)*X 0 0+(4154993967/10000000000 : ℝ)*X 0 1+(2253522491/5000000000 : ℝ)*X 0 2+(865534331/2000000000 : ℝ)*X 1 0+(4154993967/10000000000 : ℝ)*X 1 1+(2253522491/5000000000 : ℝ)*X 1 2+(865534331/2000000000 : ℝ)*X 2 0+(4154993967/10000000000 : ℝ)*X 2 1+(2253522491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-511861733/2500000000 : ℝ)*X 0 0+(104902689/200000000 : ℝ)*X 0 1+(2706129113/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652858197/5000000000 : ℝ)*X 1 0+(-1965476677/10000000000 : ℝ)*X 1 1+(54122581/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326429103/2500000000 : ℝ)*X 2 0+(541225801/1000000000 : ℝ)*X 2 1+(-245684597/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1081923649/2500000000 : ℝ)*X 0 0+(4505787003/10000000000 : ℝ)*X 0 1+(1039065251/2500000000 : ℝ)*X 0 2+(1081923649/2500000000 : ℝ)*X 1 0+(4505787003/10000000000 : ℝ)*X 1 1+(1039065251/2500000000 : ℝ)*X 1 2+(1081923649/2500000000 : ℝ)*X 2 0+(4505787003/10000000000 : ℝ)*X 2 1+(1039065251/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6609763837567887302427/891500000000000000000000000 : ℝ) := by norm_num
    linear_combination (61465653/5000000000000 : ℝ)*(base19) + (3360568721/100000000000000 : ℝ)*(base23) + (244767583/100000000000000 : ℝ)*(lower2) + (3751351/4000000000000 : ℝ)*(upper3) + (758785457/50000000000000 : ℝ)*(upper5) + (1097659987363247/25000000000000 : ℝ)*(major0) + (1097659987363247/25000000000000 : ℝ)*(major1) + (1097659987363247/25000000000000 : ℝ)*(major2) + (371293951899159/6250000000000 : ℝ)*(sp0) + (2970373070066661/50000000000000 : ℝ)*(sp1) + (297037200443883/5000000000000 : ℝ)*(sp2) + (2840519567484487/100000000000000 : ℝ)*(sp3) + (22069529919/50000000000000 : ℝ)*(sp4) + (3178708733/25000000000000 : ℝ)*(sp7) + (2840532282319419/100000000000000 : ℝ)*(f.failure) + (5940747369446381/100000000000000 : ℝ)*(f.sum) + (810611113293/1783000000000000000000000000 : ℝ)*base66 + (780245055485643867/445750000000000000000000000000000 : ℝ)*base67 + (1956221763795106133/445750000000000000000000000000000 : ℝ)*base70 + (137987073749643867/445750000000000000000000000000000 : ℝ)*base71 + (954766909329/356600000000000000000000000 : ℝ)*base73 + (3563665983552606133/445750000000000000000000000000000 : ℝ)*base76 + (824165422757356133/445750000000000000000000000000000 : ℝ)*base78 + (8628996153171643867/445750000000000000000000000000000 : ℝ)*base79 + (1200776553199/445750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4798183/2500000000000000000000 : ℝ)*base89 + (4798183/2500000000000000000000 : ℝ)*base91 + (4798183/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (201841094743292038319850399/27859375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (571888151/25000000000000 : ℝ)*(base19) + (488017347/20000000000000 : ℝ)*(base23) + (185714721/25000000000000 : ℝ)*(lower1) + (76821611/100000000000000 : ℝ)*(upper2) + (205435629/100000000000000 : ℝ)*(upper3) + (2965677/1250000000000 : ℝ)*(upper5) + (138195929671811/3125000000000 : ℝ)*(major0) + (138195929671811/3125000000000 : ℝ)*(major1) + (138195929671811/3125000000000 : ℝ)*(major2) + (768608553/50000000000000 : ℝ)*(sp1) + (2991772010042257/50000000000000 : ℝ)*(sp4) + (1495885048828701/25000000000000 : ℝ)*(sp5) + (299177078999889/5000000000000 : ℝ)*(sp6) + (2860995237411471/100000000000000 : ℝ)*(sp7) + (2860995237411471/100000000000000 : ℝ)*(f.failure) + (2991772010042257/50000000000000 : ℝ)*(f.sum) + (1159103015649/445750000000000000000000000 : ℝ)*base65 + (355418860397517121/55718750000000000000000000000000 : ℝ)*base67 + (1671302372669235871/55718750000000000000000000000000 : ℝ)*base69 + (321583145149610871/55718750000000000000000000000000 : ℝ)*base71 + (1259263024171/356600000000000000000000000 : ℝ)*base73 + (389254558484048371/55718750000000000000000000000000 : ℝ)*base75 + (190243001702860871/55718750000000000000000000000000 : ℝ)*base77 + (441042252774357879/55718750000000000000000000000000 : ℝ)*base80 + (894808954177/445750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (17134453/2500000000000000000000 : ℝ)*base90 + (17134453/2500000000000000000000 : ℝ)*base92 + (17134453/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11139/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (919/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1338_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1338_box_0 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1879853963/10000000000 : ℝ)*x 0 + (107802191/200000000 : ℝ)*x 1 + (539011019/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1879853963/10000000000 : ℝ)^2149 ≤ (11145354890053/100000000000000 : ℝ)^1637 := by
    have hnat : (1879853963 : ℕ)^2149*100000000000000^1637 ≤ 11145354890053^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1879853963 10000000000 11145354890053 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107802191/200000000 : ℝ)^2149 ≤ (11106829770827/25000000000000 : ℝ)^1637 := by
    have hnat : (107802191 : ℕ)^2149*25000000000000^1637 ≤ 11106829770827^1637*200000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107802191 200000000 11106829770827 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539011019/1000000000 : ℝ)^2149 ≤ (8885465201663/20000000000000 : ℝ)^1637 := by
    have hnat : (539011019 : ℕ)^2149*20000000000000^1637 ≤ 8885465201663^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539011019 1000000000 8885465201663 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1879853963/10000000000 : ℝ), (107802191/200000000 : ℝ), (539011019/1000000000 : ℝ)] ![(11145354890053/100000000000000 : ℝ), (11106829770827/25000000000000 : ℝ), (8885465201663/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1879853963/10000000000 : ℝ)|^2149 ≤ (11145354890053/100000000000000 : ℝ)^1637
        have hw : |(-1879853963/10000000000 : ℝ)|=(1879853963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107802191/200000000 : ℝ)|^2149 ≤ (11106829770827/25000000000000 : ℝ)^1637
        have hw : |(107802191/200000000 : ℝ)|=(107802191/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539011019/1000000000 : ℝ)|^2149 ≤ (8885465201663/20000000000000 : ℝ)^1637
        have hw : |(539011019/1000000000 : ℝ)|=(539011019/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_1 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285107161/10000000000 : ℝ)*x 0 + (-404738209/2000000000 : ℝ)*x 1 + (673763817/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285107161/10000000000 : ℝ)^2149 ≤ (43294636069751/100000000000000 : ℝ)^1637 := by
    have hnat : (5285107161 : ℕ)^2149*100000000000000^1637 ≤ 43294636069751^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285107161 10000000000 43294636069751 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404738209/2000000000 : ℝ)^2149 ≤ (1227803416599/10000000000000 : ℝ)^1637 := by
    have hnat : (404738209 : ℕ)^2149*10000000000000^1637 ≤ 1227803416599^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404738209 2000000000 1227803416599 10000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673763817/1250000000 : ℝ)^2149 ≤ (44427329752147/100000000000000 : ℝ)^1637 := by
    have hnat : (673763817 : ℕ)^2149*100000000000000^1637 ≤ 44427329752147^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673763817 1250000000 44427329752147 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285107161/10000000000 : ℝ), (-404738209/2000000000 : ℝ), (673763817/1250000000 : ℝ)] ![(43294636069751/100000000000000 : ℝ), (1227803416599/10000000000000 : ℝ), (44427329752147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285107161/10000000000 : ℝ)|^2149 ≤ (43294636069751/100000000000000 : ℝ)^1637
        have hw : |(5285107161/10000000000 : ℝ)|=(5285107161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404738209/2000000000 : ℝ)|^2149 ≤ (1227803416599/10000000000000 : ℝ)^1637
        have hw : |(-404738209/2000000000 : ℝ)|=(404738209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673763817/1250000000 : ℝ)|^2149 ≤ (44427329752147/100000000000000 : ℝ)^1637
        have hw : |(673763817/1250000000 : ℝ)|=(673763817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_2 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5285107017/10000000000 : ℝ)*x 0 + (2695054989/5000000000 : ℝ)*x 1 + (-2023691997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285107017/10000000000 : ℝ)^2149 ≤ (43294634521183/100000000000000 : ℝ)^1637 := by
    have hnat : (5285107017 : ℕ)^2149*100000000000000^1637 ≤ 43294634521183^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285107017 10000000000 43294634521183 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695054989/5000000000 : ℝ)^2149 ≤ (22213661857203/50000000000000 : ℝ)^1637 := by
    have hnat : (2695054989 : ℕ)^2149*50000000000000^1637 ≤ 22213661857203^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695054989 5000000000 22213661857203 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023691997/10000000000 : ℝ)^2149 ≤ (3069510437109/25000000000000 : ℝ)^1637 := by
    have hnat : (2023691997 : ℕ)^2149*25000000000000^1637 ≤ 3069510437109^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023691997 10000000000 3069510437109 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285107017/10000000000 : ℝ), (2695054989/5000000000 : ℝ), (-2023691997/10000000000 : ℝ)] ![(43294634521183/100000000000000 : ℝ), (22213661857203/50000000000000 : ℝ), (3069510437109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285107017/10000000000 : ℝ)|^2149 ≤ (43294634521183/100000000000000 : ℝ)^1637
        have hw : |(5285107017/10000000000 : ℝ)|=(5285107017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695054989/5000000000 : ℝ)|^2149 ≤ (22213661857203/50000000000000 : ℝ)^1637
        have hw : |(2695054989/5000000000 : ℝ)|=(2695054989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2023691997/10000000000 : ℝ)|^2149 ≤ (3069510437109/25000000000000 : ℝ)^1637
        have hw : |(-2023691997/10000000000 : ℝ)|=(2023691997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_3 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4475958709/10000000000 : ℝ)*x 0 + (4257421837/10000000000 : ℝ)*x 1 + (425742293/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475958709/10000000000 : ℝ)^2149 ≤ (17404624981487/50000000000000 : ℝ)^1637 := by
    have hnat : (4475958709 : ℕ)^2149*50000000000000^1637 ≤ 17404624981487^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475958709 10000000000 17404624981487 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4257421837/10000000000 : ℝ)^2149 ≤ (32595369514451/100000000000000 : ℝ)^1637 := by
    have hnat : (4257421837 : ℕ)^2149*100000000000000^1637 ≤ 32595369514451^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4257421837 10000000000 32595369514451 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425742293/1000000000 : ℝ)^2149 ≤ (32595380499883/100000000000000 : ℝ)^1637 := by
    have hnat : (425742293 : ℕ)^2149*100000000000000^1637 ≤ 32595380499883^1637*1000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425742293 1000000000 32595380499883 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4475958709/10000000000 : ℝ), (4257421837/10000000000 : ℝ), (425742293/1000000000 : ℝ)] ![(17404624981487/50000000000000 : ℝ), (32595369514451/100000000000000 : ℝ), (32595380499883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4475958709/10000000000 : ℝ)|^2149 ≤ (17404624981487/50000000000000 : ℝ)^1637
        have hw : |(4475958709/10000000000 : ℝ)|=(4475958709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4257421837/10000000000 : ℝ)|^2149 ≤ (32595369514451/100000000000000 : ℝ)^1637
        have hw : |(4257421837/10000000000 : ℝ)|=(4257421837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425742293/1000000000 : ℝ)|^2149 ≤ (32595380499883/100000000000000 : ℝ)^1637
        have hw : |(425742293/1000000000 : ℝ)|=(425742293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_4 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2217766451/10000000000 : ℝ)*x 0 + (5264834887/10000000000 : ℝ)*x 1 + (82263031/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2217766451/10000000000 : ℝ)^2149 ≤ (6923244917653/50000000000000 : ℝ)^1637 := by
    have hnat : (2217766451 : ℕ)^2149*50000000000000^1637 ≤ 6923244917653^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217766451 10000000000 6923244917653 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264834887/10000000000 : ℝ)^2149 ≤ (43076759925013/100000000000000 : ℝ)^1637 := by
    have hnat : (5264834887 : ℕ)^2149*100000000000000^1637 ≤ 43076759925013^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264834887 10000000000 43076759925013 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82263031/156250000 : ℝ)^2149 ≤ (21538375112931/50000000000000 : ℝ)^1637 := by
    have hnat : (82263031 : ℕ)^2149*50000000000000^1637 ≤ 21538375112931^1637*156250000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82263031 156250000 21538375112931 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2217766451/10000000000 : ℝ), (5264834887/10000000000 : ℝ), (82263031/156250000 : ℝ)] ![(6923244917653/50000000000000 : ℝ), (43076759925013/100000000000000 : ℝ), (21538375112931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2217766451/10000000000 : ℝ)|^2149 ≤ (6923244917653/50000000000000 : ℝ)^1637
        have hw : |(-2217766451/10000000000 : ℝ)|=(2217766451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264834887/10000000000 : ℝ)|^2149 ≤ (43076759925013/100000000000000 : ℝ)^1637
        have hw : |(5264834887/10000000000 : ℝ)|=(5264834887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82263031/156250000 : ℝ)|^2149 ≤ (21538375112931/50000000000000 : ℝ)^1637
        have hw : |(82263031/156250000 : ℝ)|=(82263031/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_5 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686557093/5000000000 : ℝ)*x 0 + (-1036966231/5000000000 : ℝ)*x 1 + (329052099/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686557093/5000000000 : ℝ)^2149 ≤ (44243514486463/100000000000000 : ℝ)^1637 := by
    have hnat : (2686557093 : ℕ)^2149*100000000000000^1637 ≤ 44243514486463^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686557093 5000000000 44243514486463 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036966231/5000000000 : ℝ)^2149 ≤ (12679739560103/100000000000000 : ℝ)^1637 := by
    have hnat : (1036966231 : ℕ)^2149*100000000000000^1637 ≤ 12679739560103^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036966231 5000000000 12679739560103 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329052099/625000000 : ℝ)^2149 ≤ (43076745929449/100000000000000 : ℝ)^1637 := by
    have hnat : (329052099 : ℕ)^2149*100000000000000^1637 ≤ 43076745929449^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329052099 625000000 43076745929449 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686557093/5000000000 : ℝ), (-1036966231/5000000000 : ℝ), (329052099/625000000 : ℝ)] ![(44243514486463/100000000000000 : ℝ), (12679739560103/100000000000000 : ℝ), (43076745929449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686557093/5000000000 : ℝ)|^2149 ≤ (44243514486463/100000000000000 : ℝ)^1637
        have hw : |(2686557093/5000000000 : ℝ)|=(2686557093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036966231/5000000000 : ℝ)|^2149 ≤ (12679739560103/100000000000000 : ℝ)^1637
        have hw : |(-1036966231/5000000000 : ℝ)|=(1036966231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329052099/625000000 : ℝ)|^2149 ≤ (43076745929449/100000000000000 : ℝ)^1637
        have hw : |(329052099/625000000 : ℝ)|=(329052099/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_6 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686556709/5000000000 : ℝ)*x 0 + (1316208503/2500000000 : ℝ)*x 1 + (-518483231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686556709/5000000000 : ℝ)^2149 ≤ (22121753092329/50000000000000 : ℝ)^1637 := by
    have hnat : (2686556709 : ℕ)^2149*50000000000000^1637 ≤ 22121753092329^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686556709 5000000000 22121753092329 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316208503/2500000000 : ℝ)^2149 ≤ (4307675052661/10000000000000 : ℝ)^1637 := by
    have hnat : (1316208503 : ℕ)^2149*10000000000000^1637 ≤ 4307675052661^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316208503 2500000000 4307675052661 10000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518483231/2500000000 : ℝ)^2149 ≤ (12679743268151/100000000000000 : ℝ)^1637 := by
    have hnat : (518483231 : ℕ)^2149*100000000000000^1637 ≤ 12679743268151^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518483231 2500000000 12679743268151 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686556709/5000000000 : ℝ), (1316208503/2500000000 : ℝ), (-518483231/2500000000 : ℝ)] ![(22121753092329/50000000000000 : ℝ), (4307675052661/10000000000000 : ℝ), (12679743268151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686556709/5000000000 : ℝ)|^2149 ≤ (22121753092329/50000000000000 : ℝ)^1637
        have hw : |(2686556709/5000000000 : ℝ)|=(2686556709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316208503/2500000000 : ℝ)|^2149 ≤ (4307675052661/10000000000000 : ℝ)^1637
        have hw : |(1316208503/2500000000 : ℝ)|=(1316208503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-518483231/2500000000 : ℝ)|^2149 ≤ (12679743268151/100000000000000 : ℝ)^1637
        have hw : |(-518483231/2500000000 : ℝ)|=(518483231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_7 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2089229253/5000000000 : ℝ)*x 0 + (4406118191/10000000000 : ℝ)*x 1 + (4406119297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089229253/5000000000 : ℝ)^2149 ≤ (15902021681429/50000000000000 : ℝ)^1637 := by
    have hnat : (2089229253 : ℕ)^2149*50000000000000^1637 ≤ 15902021681429^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089229253 5000000000 15902021681429 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4406118191/10000000000 : ℝ)^2149 ≤ (34097972693023/100000000000000 : ℝ)^1637 := by
    have hnat : (4406118191 : ℕ)^2149*100000000000000^1637 ≤ 34097972693023^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406118191 10000000000 34097972693023 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406119297/10000000000 : ℝ)^2149 ≤ (6819596785823/20000000000000 : ℝ)^1637 := by
    have hnat : (4406119297 : ℕ)^2149*20000000000000^1637 ≤ 6819596785823^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406119297 10000000000 6819596785823 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089229253/5000000000 : ℝ), (4406118191/10000000000 : ℝ), (4406119297/10000000000 : ℝ)] ![(15902021681429/50000000000000 : ℝ), (34097972693023/100000000000000 : ℝ), (6819596785823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089229253/5000000000 : ℝ)|^2149 ≤ (15902021681429/50000000000000 : ℝ)^1637
        have hw : |(2089229253/5000000000 : ℝ)|=(2089229253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4406118191/10000000000 : ℝ)|^2149 ≤ (34097972693023/100000000000000 : ℝ)^1637
        have hw : |(4406118191/10000000000 : ℝ)|=(4406118191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4406119297/10000000000 : ℝ)|^2149 ≤ (6819596785823/20000000000000 : ℝ)^1637
        have hw : |(4406119297/10000000000 : ℝ)|=(4406119297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_8 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073408197/5000000000 : ℝ)*x 0 + (5178609533/10000000000 : ℝ)*x 1 + (84439561/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073408197/5000000000 : ℝ)^2149 ≤ (2653580232809/20000000000000 : ℝ)^1637 := by
    have hnat : (1073408197 : ℕ)^2149*20000000000000^1637 ≤ 2653580232809^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073408197 5000000000 2653580232809 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178609533/10000000000 : ℝ)^2149 ≤ (42152991642903/100000000000000 : ℝ)^1637 := by
    have hnat : (5178609533 : ℕ)^2149*100000000000000^1637 ≤ 42152991642903^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178609533 10000000000 42152991642903 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84439561/156250000 : ℝ)^2149 ≤ (22289553591103/50000000000000 : ℝ)^1637 := by
    have hnat : (84439561 : ℕ)^2149*50000000000000^1637 ≤ 22289553591103^1637*156250000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84439561 156250000 22289553591103 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073408197/5000000000 : ℝ), (5178609533/10000000000 : ℝ), (84439561/156250000 : ℝ)] ![(2653580232809/20000000000000 : ℝ), (42152991642903/100000000000000 : ℝ), (22289553591103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073408197/5000000000 : ℝ)|^2149 ≤ (2653580232809/20000000000000 : ℝ)^1637
        have hw : |(-1073408197/5000000000 : ℝ)|=(1073408197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178609533/10000000000 : ℝ)|^2149 ≤ (42152991642903/100000000000000 : ℝ)^1637
        have hw : |(5178609533/10000000000 : ℝ)|=(5178609533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84439561/156250000 : ℝ)|^2149 ≤ (22289553591103/50000000000000 : ℝ)^1637
        have hw : |(84439561/156250000 : ℝ)|=(84439561/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_9 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5275251527/10000000000 : ℝ)*x 0 + (-2017935641/10000000000 : ℝ)*x 1 + (84439559/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275251527/10000000000 : ℝ)^2149 ≤ (8637735998267/20000000000000 : ℝ)^1637 := by
    have hnat : (5275251527 : ℕ)^2149*20000000000000^1637 ≤ 8637735998267^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275251527 10000000000 8637735998267 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017935641/10000000000 : ℝ)^2149 ≤ (12232214190403/100000000000000 : ℝ)^1637 := by
    have hnat : (2017935641 : ℕ)^2149*100000000000000^1637 ≤ 12232214190403^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017935641 10000000000 12232214190403 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84439559/156250000 : ℝ)^2149 ≤ (22289552898039/50000000000000 : ℝ)^1637 := by
    have hnat : (84439559 : ℕ)^2149*50000000000000^1637 ≤ 22289552898039^1637*156250000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84439559 156250000 22289552898039 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275251527/10000000000 : ℝ), (-2017935641/10000000000 : ℝ), (84439559/156250000 : ℝ)] ![(8637735998267/20000000000000 : ℝ), (12232214190403/100000000000000 : ℝ), (22289552898039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275251527/10000000000 : ℝ)|^2149 ≤ (8637735998267/20000000000000 : ℝ)^1637
        have hw : |(5275251527/10000000000 : ℝ)|=(5275251527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2017935641/10000000000 : ℝ)|^2149 ≤ (12232214190403/100000000000000 : ℝ)^1637
        have hw : |(-2017935641/10000000000 : ℝ)|=(2017935641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84439559/156250000 : ℝ)|^2149 ≤ (22289552898039/50000000000000 : ℝ)^1637
        have hw : |(84439559/156250000 : ℝ)|=(84439559/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_10 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637625599/5000000000 : ℝ)*x 0 + (2702066073/5000000000 : ℝ)*x 1 + (-1008967791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637625599/5000000000 : ℝ)^2149 ≤ (863773529107/2000000000000 : ℝ)^1637 := by
    have hnat : (2637625599 : ℕ)^2149*2000000000000^1637 ≤ 863773529107^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637625599 5000000000 863773529107 2000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702066073/5000000000 : ℝ)^2149 ≤ (44579109802853/100000000000000 : ℝ)^1637 := by
    have hnat : (2702066073 : ℕ)^2149*100000000000000^1637 ≤ 44579109802853^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702066073 5000000000 44579109802853 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1008967791/5000000000 : ℝ)^2149 ≤ (12232213720901/100000000000000 : ℝ)^1637 := by
    have hnat : (1008967791 : ℕ)^2149*100000000000000^1637 ≤ 12232213720901^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008967791 5000000000 12232213720901 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637625599/5000000000 : ℝ), (2702066073/5000000000 : ℝ), (-1008967791/5000000000 : ℝ)] ![(863773529107/2000000000000 : ℝ), (44579109802853/100000000000000 : ℝ), (12232213720901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637625599/5000000000 : ℝ)|^2149 ≤ (863773529107/2000000000000 : ℝ)^1637
        have hw : |(2637625599/5000000000 : ℝ)|=(2637625599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702066073/5000000000 : ℝ)|^2149 ≤ (44579109802853/100000000000000 : ℝ)^1637
        have hw : |(2702066073/5000000000 : ℝ)|=(2702066073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1008967791/5000000000 : ℝ)|^2149 ≤ (12232213720901/100000000000000 : ℝ)^1637
        have hw : |(-1008967791/5000000000 : ℝ)|=(1008967791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_11 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (901739759/2000000000 : ℝ)*x 0 + (1060191167/2500000000 : ℝ)*x 1 + (4240765017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (901739759/2000000000 : ℝ)^2149 ≤ (35143885314861/100000000000000 : ℝ)^1637 := by
    have hnat : (901739759 : ℕ)^2149*100000000000000^1637 ≤ 35143885314861^1637*2000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901739759 2000000000 35143885314861 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060191167/2500000000 : ℝ)^2149 ≤ (16214027790403/50000000000000 : ℝ)^1637 := by
    have hnat : (1060191167 : ℕ)^2149*50000000000000^1637 ≤ 16214027790403^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060191167 2500000000 16214027790403 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240765017/10000000000 : ℝ)^2149 ≤ (2026753692763/6250000000000 : ℝ)^1637 := by
    have hnat : (4240765017 : ℕ)^2149*6250000000000^1637 ≤ 2026753692763^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240765017 10000000000 2026753692763 6250000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(901739759/2000000000 : ℝ), (1060191167/2500000000 : ℝ), (4240765017/10000000000 : ℝ)] ![(35143885314861/100000000000000 : ℝ), (16214027790403/50000000000000 : ℝ), (2026753692763/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(901739759/2000000000 : ℝ)|^2149 ≤ (35143885314861/100000000000000 : ℝ)^1637
        have hw : |(901739759/2000000000 : ℝ)|=(901739759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060191167/2500000000 : ℝ)|^2149 ≤ (16214027790403/50000000000000 : ℝ)^1637
        have hw : |(1060191167/2500000000 : ℝ)|=(1060191167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240765017/10000000000 : ℝ)|^2149 ≤ (2026753692763/6250000000000 : ℝ)^1637
        have hw : |(4240765017/10000000000 : ℝ)|=(4240765017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_12 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951149831/10000000000 : ℝ)*x 0 + (2737060187/5000000000 : ℝ)*x 1 + (5253767299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951149831/10000000000 : ℝ)^2149 ≤ (11703527088259/100000000000000 : ℝ)^1637 := by
    have hnat : (1951149831 : ℕ)^2149*100000000000000^1637 ≤ 11703527088259^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951149831 10000000000 11703527088259 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737060187/5000000000 : ℝ)^2149 ≤ (9067710239229/20000000000000 : ℝ)^1637 := by
    have hnat : (2737060187 : ℕ)^2149*20000000000000^1637 ≤ 9067710239229^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737060187 5000000000 9067710239229 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253767299/10000000000 : ℝ)^2149 ≤ (42957921707379/100000000000000 : ℝ)^1637 := by
    have hnat : (5253767299 : ℕ)^2149*100000000000000^1637 ≤ 42957921707379^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253767299 10000000000 42957921707379 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951149831/10000000000 : ℝ), (2737060187/5000000000 : ℝ), (5253767299/10000000000 : ℝ)] ![(11703527088259/100000000000000 : ℝ), (9067710239229/20000000000000 : ℝ), (42957921707379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951149831/10000000000 : ℝ)|^2149 ≤ (11703527088259/100000000000000 : ℝ)^1637
        have hw : |(-1951149831/10000000000 : ℝ)|=(1951149831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737060187/5000000000 : ℝ)|^2149 ≤ (9067710239229/20000000000000 : ℝ)^1637
        have hw : |(2737060187/5000000000 : ℝ)|=(2737060187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253767299/10000000000 : ℝ)|^2149 ≤ (42957921707379/100000000000000 : ℝ)^1637
        have hw : |(5253767299/10000000000 : ℝ)|=(5253767299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_13 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2690442447/5000000000 : ℝ)*x 0 + (-1039133627/5000000000 : ℝ)*x 1 + (328360479/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690442447/5000000000 : ℝ)^2149 ≤ (1385235376377/3125000000000 : ℝ)^1637 := by
    have hnat : (2690442447 : ℕ)^2149*3125000000000^1637 ≤ 1385235376377^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690442447 5000000000 1385235376377 3125000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1039133627/5000000000 : ℝ)^2149 ≤ (1589317789011/12500000000000 : ℝ)^1637 := by
    have hnat : (1039133627 : ℕ)^2149*12500000000000^1637 ≤ 1589317789011^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039133627 5000000000 1589317789011 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328360479/625000000 : ℝ)^2149 ≤ (10739481406319/25000000000000 : ℝ)^1637 := by
    have hnat : (328360479 : ℕ)^2149*25000000000000^1637 ≤ 10739481406319^1637*625000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328360479 625000000 10739481406319 25000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690442447/5000000000 : ℝ), (-1039133627/5000000000 : ℝ), (328360479/625000000 : ℝ)] ![(1385235376377/3125000000000 : ℝ), (1589317789011/12500000000000 : ℝ), (10739481406319/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690442447/5000000000 : ℝ)|^2149 ≤ (1385235376377/3125000000000 : ℝ)^1637
        have hw : |(2690442447/5000000000 : ℝ)|=(2690442447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1039133627/5000000000 : ℝ)|^2149 ≤ (1589317789011/12500000000000 : ℝ)^1637
        have hw : |(-1039133627/5000000000 : ℝ)|=(1039133627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328360479/625000000 : ℝ)|^2149 ≤ (10739481406319/25000000000000 : ℝ)^1637
        have hw : |(328360479/625000000 : ℝ)|=(328360479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_14 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1345221429/2500000000 : ℝ)*x 0 + (656720883/1250000000 : ℝ)*x 1 + (-2078266949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345221429/2500000000 : ℝ)^2149 ≤ (22163770466803/50000000000000 : ℝ)^1637 := by
    have hnat : (1345221429 : ℕ)^2149*50000000000000^1637 ≤ 22163770466803^1637*2500000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345221429 2500000000 22163770466803 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656720883/1250000000 : ℝ)^2149 ≤ (42957919184897/100000000000000 : ℝ)^1637 := by
    have hnat : (656720883 : ℕ)^2149*100000000000000^1637 ≤ 42957919184897^1637*1250000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656720883 1250000000 42957919184897 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078266949/10000000000 : ℝ)^2149 ≤ (2542907972507/20000000000000 : ℝ)^1637 := by
    have hnat : (2078266949 : ℕ)^2149*20000000000000^1637 ≤ 2542907972507^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078266949 10000000000 2542907972507 20000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345221429/2500000000 : ℝ), (656720883/1250000000 : ℝ), (-2078266949/10000000000 : ℝ)] ![(22163770466803/50000000000000 : ℝ), (42957919184897/100000000000000 : ℝ), (2542907972507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345221429/2500000000 : ℝ)|^2149 ≤ (22163770466803/50000000000000 : ℝ)^1637
        have hw : |(1345221429/2500000000 : ℝ)|=(1345221429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656720883/1250000000 : ℝ)|^2149 ≤ (42957919184897/100000000000000 : ℝ)^1637
        have hw : |(656720883/1250000000 : ℝ)|=(656720883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2078266949/10000000000 : ℝ)|^2149 ≤ (2542907972507/20000000000000 : ℝ)^1637
        have hw : |(-2078266949/10000000000 : ℝ)|=(2078266949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1338_box_15 (p : ℝ) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4151731537/10000000000 : ℝ)*x 0 + (4419242881/10000000000 : ℝ)*x 1 + (2209621603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4151731537/10000000000 : ℝ)^2149 ≤ (31537254059243/100000000000000 : ℝ)^1637 := by
    have hnat : (4151731537 : ℕ)^2149*100000000000000^1637 ≤ 31537254059243^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4151731537 10000000000 31537254059243 100000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4419242881/10000000000 : ℝ)^2149 ≤ (17115685655059/50000000000000 : ℝ)^1637 := by
    have hnat : (4419242881 : ℕ)^2149*50000000000000^1637 ≤ 17115685655059^1637*10000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4419242881 10000000000 17115685655059 50000000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209621603/5000000000 : ℝ)^2149 ≤ (4278921826867/12500000000000 : ℝ)^1637 := by
    have hnat : (2209621603 : ℕ)^2149*12500000000000^1637 ≤ 4278921826867^1637*5000000000^2149 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209621603 5000000000 4278921826867 12500000000000 2149 1637 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2149/512 : ℝ)) 2149 1637 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4151731537/10000000000 : ℝ), (4419242881/10000000000 : ℝ), (2209621603/5000000000 : ℝ)] ![(31537254059243/100000000000000 : ℝ), (17115685655059/50000000000000 : ℝ), (4278921826867/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4151731537/10000000000 : ℝ)|^2149 ≤ (31537254059243/100000000000000 : ℝ)^1637
        have hw : |(4151731537/10000000000 : ℝ)|=(4151731537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4419242881/10000000000 : ℝ)|^2149 ≤ (17115685655059/50000000000000 : ℝ)^1637
        have hw : |(4419242881/10000000000 : ℝ)|=(4419242881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209621603/5000000000 : ℝ)|^2149 ≤ (4278921826867/12500000000000 : ℝ)^1637
        have hw : |(2209621603/5000000000 : ℝ)|=(2209621603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1338_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31427/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58933/100000 : ℝ) ∧ (79931/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84337/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (557/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (919/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (557/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (557/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (919/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (557/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (557/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (919/6250 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (557/5000 : ℝ) ^ (4297/1024 : ℝ) ≤ (2502619128224823/25000000000000000000 : ℝ) := by
    have hpowers : (557/5000 : ℝ)^4297 ≤ (2502619128224823/25000000000000000000 : ℝ)^1024 := by
      have hnat : (557 : ℕ)^4297*25000000000000000000^1024 ≤ 2502619128224823^1024*5000^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        557 5000 2502619128224823 25000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (557/5000 : ℝ)) (X := (2502619128224823/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (919/6250 : ℝ) ^ (4297/1024 : ℝ) ≤ (3208622834095659/10000000000000000000 : ℝ) := by
    have hpowers : (919/6250 : ℝ)^4297 ≤ (3208622834095659/10000000000000000000 : ℝ)^1024 := by
      have hnat : (919 : ℕ)^4297*10000000000000000000^1024 ≤ 3208622834095659^1024*6250^4297 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        919 6250 3208622834095659 10000000000000000000 4297 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (919/6250 : ℝ)) (X := (3208622834095659/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502502619128224823/12500000000000000000 : ℝ) ≤ (1000047707453717/1000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (12502502619128224823/12500000000000000000 : ℝ)^1024 ≤ (1000047707453717/1000000000000000 : ℝ)^4297 := by
      have hnat : (12502502619128224823 : ℕ)^1024*1000000000000000^4297 ≤ 1000047707453717^4297*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502502619128224823 12500000000000000000 1000047707453717 1000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000047707453717/1000000000000000 : ℝ)) (X := (12502502619128224823/12500000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021048352426927941/50000000000000000000 : ℝ) ≤ (1000100302807503/1000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (50021048352426927941/50000000000000000000 : ℝ)^1024 ≤ (1000100302807503/1000000000000000 : ℝ)^4297 := by
      have hnat : (50021048352426927941 : ℕ)^1024*1000000000000000^4297 ≤ 1000100302807503^4297*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021048352426927941 50000000000000000000 1000100302807503 1000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000100302807503/1000000000000000 : ℝ)) (X := (50021048352426927941/50000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003208622834095659/5000000000000000000 : ℝ) ≤ (1000152898161289/1000000000000000 : ℝ) ^ (4297/1024 : ℝ) := by
    have hpowers : (5003208622834095659/5000000000000000000 : ℝ)^1024 ≤ (1000152898161289/1000000000000000 : ℝ)^4297 := by
      have hnat : (5003208622834095659 : ℕ)^1024*1000000000000000^4297 ≤ 1000152898161289^4297*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003208622834095659 5000000000000000000 1000152898161289 1000000000000000 1024 4297 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000152898161289/1000000000000000 : ℝ)) (X := (5003208622834095659/5000000000000000000 : ℝ)) (by norm_num) 4297 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2502619128224823/25000000000000000000 : ℝ) ≤ ((890749551220673827/891000000000000000 : ℝ)+2*(26297676893/17820000000000 : ℝ)*(557/5000 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (890749551220673827/891000000000000000 : ℝ)+2*(26297676893/17820000000000 : ℝ)*(557/5000 : ℝ)=(1000047707453717/1000000000000000 : ℝ) by norm_num, show 1+2*(2502619128224823/25000000000000000000 : ℝ)=(12502502619128224823/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3208622834095659/10000000000000000000 : ℝ)+(2502619128224823/25000000000000000000 : ℝ) ≤ ((890749551220673827/891000000000000000 : ℝ)+(26297676893/17820000000000 : ℝ)*((919/6250 : ℝ)+(557/5000 : ℝ)))^(4297/1024 : ℝ) := by
    rw [show (890749551220673827/891000000000000000 : ℝ)+(26297676893/17820000000000 : ℝ)*((919/6250 : ℝ)+(557/5000 : ℝ))=(1000100302807503/1000000000000000 : ℝ) by norm_num, show 1+(3208622834095659/10000000000000000000 : ℝ)+(2502619128224823/25000000000000000000 : ℝ)=(50021048352426927941/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3208622834095659/10000000000000000000 : ℝ) ≤ ((890749551220673827/891000000000000000 : ℝ)+2*(26297676893/17820000000000 : ℝ)*(919/6250 : ℝ))^(4297/1024 : ℝ) := by
    rw [show (890749551220673827/891000000000000000 : ℝ)+2*(26297676893/17820000000000 : ℝ)*(919/6250 : ℝ)=(1000152898161289/1000000000000000 : ℝ) by norm_num, show 1+2*(3208622834095659/10000000000000000000 : ℝ)=(5003208622834095659/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (890749551220673827/891000000000000000 : ℝ)*(X 1 0+X 2 0)+(26297676893/17820000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (890749551220673827/891000000000000000 : ℝ)) (alpha := (26297676893/17820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (890749551220673827/891000000000000000 : ℝ)*(X 0 1+X 2 1)+(26297676893/17820000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (890749551220673827/891000000000000000 : ℝ)) (alpha := (26297676893/17820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (890749551220673827/891000000000000000 : ℝ)*(X 0 2+X 1 2)+(26297676893/17820000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4297/1024 : ℝ)) (lo := (557/5000 : ℝ)) (hi := (919/6250 : ℝ)) (c := (890749551220673827/891000000000000000 : ℝ)) (alpha := (26297676893/17820000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1879853963/10000000000 : ℝ)*X 0 0+(107802191/200000000 : ℝ)*X 0 1+(539011019/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5285107161/10000000000 : ℝ)*X 1 0+(-404738209/2000000000 : ℝ)*X 1 1+(673763817/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285107017/10000000000 : ℝ)*X 2 0+(2695054989/5000000000 : ℝ)*X 2 1+(-2023691997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4475958709/10000000000 : ℝ)*X 0 0+(4257421837/10000000000 : ℝ)*X 0 1+(425742293/1000000000 : ℝ)*X 0 2+(4475958709/10000000000 : ℝ)*X 1 0+(4257421837/10000000000 : ℝ)*X 1 1+(425742293/1000000000 : ℝ)*X 1 2+(4475958709/10000000000 : ℝ)*X 2 0+(4257421837/10000000000 : ℝ)*X 2 1+(425742293/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2217766451/10000000000 : ℝ)*X 0 0+(5264834887/10000000000 : ℝ)*X 0 1+(82263031/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2686557093/5000000000 : ℝ)*X 1 0+(-1036966231/5000000000 : ℝ)*X 1 1+(329052099/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686556709/5000000000 : ℝ)*X 2 0+(1316208503/2500000000 : ℝ)*X 2 1+(-518483231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089229253/5000000000 : ℝ)*X 0 0+(4406118191/10000000000 : ℝ)*X 0 1+(4406119297/10000000000 : ℝ)*X 0 2+(2089229253/5000000000 : ℝ)*X 1 0+(4406118191/10000000000 : ℝ)*X 1 1+(4406119297/10000000000 : ℝ)*X 1 2+(2089229253/5000000000 : ℝ)*X 2 0+(4406118191/10000000000 : ℝ)*X 2 1+(4406119297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1073408197/5000000000 : ℝ)*X 0 0+(5178609533/10000000000 : ℝ)*X 0 1+(84439561/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275251527/10000000000 : ℝ)*X 1 0+(-2017935641/10000000000 : ℝ)*X 1 1+(84439559/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637625599/5000000000 : ℝ)*X 2 0+(2702066073/5000000000 : ℝ)*X 2 1+(-1008967791/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((901739759/2000000000 : ℝ)*X 0 0+(1060191167/2500000000 : ℝ)*X 0 1+(4240765017/10000000000 : ℝ)*X 0 2+(901739759/2000000000 : ℝ)*X 1 0+(1060191167/2500000000 : ℝ)*X 1 1+(4240765017/10000000000 : ℝ)*X 1 2+(901739759/2000000000 : ℝ)*X 2 0+(1060191167/2500000000 : ℝ)*X 2 1+(4240765017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1951149831/10000000000 : ℝ)*X 0 0+(2737060187/5000000000 : ℝ)*X 0 1+(5253767299/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2690442447/5000000000 : ℝ)*X 1 0+(-1039133627/5000000000 : ℝ)*X 1 1+(328360479/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1345221429/2500000000 : ℝ)*X 2 0+(656720883/1250000000 : ℝ)*X 2 1+(-2078266949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4151731537/10000000000 : ℝ)*X 0 0+(4419242881/10000000000 : ℝ)*X 0 1+(2209621603/5000000000 : ℝ)*X 0 2+(4151731537/10000000000 : ℝ)*X 1 0+(4419242881/10000000000 : ℝ)*X 1 1+(2209621603/5000000000 : ℝ)*X 1 2+(4151731537/10000000000 : ℝ)*X 2 0+(4419242881/10000000000 : ℝ)*X 2 1+(2209621603/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1338_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31427/50000 : ℝ) ≤ (-212123241699926695515423058331/337500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61569429/100000000000000 : ℝ)*(lower3) + (14220093/4000000000000 : ℝ)*(lower4) + (1781521/25000000000000 : ℝ)*(lower5) + (729006276167917/25000000000000 : ℝ)*(major0) + (729006276167917/25000000000000 : ℝ)*(major1) + (729006276167917/25000000000000 : ℝ)*(major2) + (8076383383/50000000000000 : ℝ)*(sp1) + (10966980057/50000000000000 : ℝ)*(sp2) + (329877189/4000000000000 : ℝ)*(sp3) + (3966465496065801/100000000000000 : ℝ)*(sp4) + (198322845014981/5000000000000 : ℝ)*(sp5) + (123951597472071/3125000000000 : ℝ)*(sp6) + (1886519352971899/100000000000000 : ℝ)*(sp7) + (944625073/12500000000000 : ℝ)*(sp8) + (235815949987703/12500000000000 : ℝ)*(f.failure) + (1983236526533193/50000000000000 : ℝ)*(f.sum) + (13998000419/10125000000000000000000000 : ℝ)*base65 + (24350801823316669/2025000000000000000000000000000 : ℝ)*base67 + (12920854238683331/2025000000000000000000000000000 : ℝ)*base70 + (2603147722516669/2025000000000000000000000000000 : ℝ)*base71 + (70367557307/4050000000000000000000000 : ℝ)*base73 + (8991689099083331/2025000000000000000000000000000 : ℝ)*base76 + (6567787678183331/2025000000000000000000000000000 : ℝ)*base78 + (7749850520608331/2025000000000000000000000000000 : ℝ)*base80 + (121194457057/81000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2482829/312500000000000000000 : ℝ)*base90 + (2482829/312500000000000000000 : ℝ)*base92 + (2482829/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58933/100000 : ℝ) ≤ (8751966709598245127334271/14850000000000000000000000 : ℝ) := by norm_num
    linear_combination (15227529/100000000000000 : ℝ)*(lower1) + (31040143/50000000000000 : ℝ)*(upper2) + (80635879/25000000000000 : ℝ)*(lower4) + (746149016632447/25000000000000 : ℝ)*(major0) + (746149016632447/25000000000000 : ℝ)*(major1) + (746149016632447/25000000000000 : ℝ)*(major2) + (2009316933066667/50000000000000 : ℝ)*(sp0) + (4018621924957771/100000000000000 : ℝ)*(sp1) + (2009320129581109/50000000000000 : ℝ)*(sp2) + (965444829308141/50000000000000 : ℝ)*(sp3) + (35235538283/100000000000000 : ℝ)*(sp5) + (724393/1562500000000 : ℝ)*(sp7) + (4225333459/25000000000000 : ℝ)*(sp10) + (23294362721/100000000000000 : ℝ)*(sp12) + (965444852488717/50000000000000 : ℝ)*(f.failure) + (2009328580248027/50000000000000 : ℝ)*(f.sum) + (1449169908103/891000000000000000000000000 : ℝ)*base66 + (104718417590085331/22275000000000000000000000000000 : ℝ)*base68 + (17601940027410331/22275000000000000000000000000000 : ℝ)*base70 + (139737318077189669/22275000000000000000000000000000 : ℝ)*base71 + (1625798889809/891000000000000000000000000 : ℝ)*base73 + (47711892594885331/22275000000000000000000000000000 : ℝ)*base76 + (68859638769314669/22275000000000000000000000000000 : ℝ)*base77 + (6019831353764669/22275000000000000000000000000000 : ℝ)*base79 + (1441335848081/445500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (13727231/1250000000000000000000 : ℝ)*base90 + (13727231/1250000000000000000000 : ℝ)*base92 + (13727231/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79931/100000 : ℝ) ≤ (791340307337002523035149158987/990000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (821707/2500000000000 : ℝ)*(upper0) + (64895291/100000000000000 : ℝ)*(upper2) + (204323/1000000000000 : ℝ)*(lower3) + (659370219872919/20000000000000 : ℝ)*(major0) + (659370219872919/20000000000000 : ℝ)*(major1) + (659370219872919/20000000000000 : ℝ)*(major2) + (2609849467/100000000000000 : ℝ)*(sp0) + (3286926359/4000000000000 : ℝ)*(sp2) + (20257200703/50000000000000 : ℝ)*(sp3) + (554268663853223/12500000000000 : ℝ)*(sp8) + (2217077046544569/50000000000000 : ℝ)*(sp9) + (2217035959965081/50000000000000 : ℝ)*(sp10) + (533215784111537/25000000000000 : ℝ)*(sp11) + (1086206943/50000000000000 : ℝ)*(sp12) + (1066451825423777/50000000000000 : ℝ)*(f.failure) + (2217077046544569/50000000000000 : ℝ)*(f.sum) + (63038788481/148500000000000000000000000 : ℝ)*base66 + (63646774635233671/5940000000000000000000000000000 : ℝ)*base67 + (18067279353473671/5940000000000000000000000000000 : ℝ)*base69 + (6945159415313671/5940000000000000000000000000000 : ℝ)*base71 + (899540168729/297000000000000000000000000 : ℝ)*base73 + (17099334327953671/5940000000000000000000000000000 : ℝ)*base75 + (68636526740813671/5940000000000000000000000000000 : ℝ)*base77 + (27471473026193671/5940000000000000000000000000000 : ℝ)*base79 + (179744974111/74250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (866811/1250000000000000000000 : ℝ)*base90 + (866811/1250000000000000000000 : ℝ)*base92 + (866811/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84337/100000 : ℝ) ≤ (-5218168907568146500627241/6187500000000000000000000 : ℝ) := by norm_num
    linear_combination (43968593/50000000000000 : ℝ)*(lower1) + (7283507/3125000000000 : ℝ)*(lower2) + (3971623/2000000000000 : ℝ)*(upper5) + (1666634005533639/50000000000000 : ℝ)*(major0) + (1666634005533639/50000000000000 : ℝ)*(major1) + (1666634005533639/50000000000000 : ℝ)*(major2) + (20110318977/100000000000000 : ℝ)*(sp0) + (91000279307/50000000000000 : ℝ)*(sp5) + (362047105921/100000000000000 : ℝ)*(sp6) + (40875473/12500000000000 : ℝ)*(sp8) + (4538163296167043/100000000000000 : ℝ)*(sp12) + (453800173293119/10000000000000 : ℝ)*(sp13) + (4537821686383883/100000000000000 : ℝ)*(sp14) + (431292727258989/20000000000000 : ℝ)*(sp15) + (431292727258989/20000000000000 : ℝ)*(f.failure) + (1134545933372451/25000000000000 : ℝ)*(f.sum) + (2488174516873/297000000000000000000000000 : ℝ)*base65 + (30493267832077849/14850000000000000000000000000000 : ℝ)*base68 + (14666368564522151/14850000000000000000000000000000 : ℝ)*base69 + (35749405730077849/14850000000000000000000000000000 : ℝ)*base72 + (479683112831/297000000000000000000000000 : ℝ)*base74 + (3608123303527849/14850000000000000000000000000000 : ℝ)*base76 + (135035675311222151/14850000000000000000000000000000 : ℝ)*base77 + (118063499856922151/14850000000000000000000000000000 : ℝ)*base79 + (290412880837/59400000000000000000000000 : ℝ)*base82 + (2007327/500000000000000000000 : ℝ)*base90 + (2007327/500000000000000000000 : ℝ)*base92 + (2007327/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1338_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (919/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (557/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31427/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58933/100000 : ℝ) else (79931/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84337/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1338_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1338_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31427/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58933/100000 : ℝ) else (79931/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84337/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1338_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1338_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1338_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4297/1024 : ℝ) ≤ p) (hpb : p ≤ (2149/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38642757/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31427/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58933/100000 : ℝ) else (79931/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84337/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1338_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
