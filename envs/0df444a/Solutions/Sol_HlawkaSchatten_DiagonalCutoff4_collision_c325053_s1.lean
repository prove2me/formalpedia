-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c325053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:04:04.569843+00:00
-- url     : https://prove2.me/submissions/2017aba7-81bf-434e-9a4b-7b0d407909c8

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c325053_s1_s1_0 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-976644503/5000000000 : ℝ)*x 0 + (314017859/625000000 : ℝ)*x 1 + (5065529027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (976644503/5000000000 : ℝ)^87 ≤ (3379708531393/25000000000000 : ℝ)^71 := by
    have hnat : (976644503 : ℕ)^87*25000000000000^71 ≤ 3379708531393^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976644503 5000000000 3379708531393 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314017859/625000000 : ℝ)^87 ≤ (5378000184767/12500000000000 : ℝ)^71 := by
    have hnat : (314017859 : ℕ)^87*12500000000000^71 ≤ 5378000184767^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314017859 625000000 5378000184767 12500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5065529027/10000000000 : ℝ)^87 ≤ (84877274193/195312500000 : ℝ)^71 := by
    have hnat : (5065529027 : ℕ)^87*195312500000^71 ≤ 84877274193^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065529027 10000000000 84877274193 195312500000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-976644503/5000000000 : ℝ), (314017859/625000000 : ℝ), (5065529027/10000000000 : ℝ)] ![(3379708531393/25000000000000 : ℝ), (5378000184767/12500000000000 : ℝ), (84877274193/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-976644503/5000000000 : ℝ)|^87 ≤ (3379708531393/25000000000000 : ℝ)^71
        have hw : |(-976644503/5000000000 : ℝ)|=(976644503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314017859/625000000 : ℝ)|^87 ≤ (5378000184767/12500000000000 : ℝ)^71
        have hw : |(314017859/625000000 : ℝ)|=(314017859/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5065529027/10000000000 : ℝ)|^87 ≤ (84877274193/195312500000 : ℝ)^71
        have hw : |(5065529027/10000000000 : ℝ)|=(5065529027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1112399909/2500000000 : ℝ)*x 0 + (-172598733/1250000000 : ℝ)*x 1 + (1514000277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1112399909/2500000000 : ℝ)^87 ≤ (37073988931129/100000000000000 : ℝ)^71 := by
    have hnat : (1112399909 : ℕ)^87*100000000000000^71 ≤ 37073988931129^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112399909 2500000000 37073988931129 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172598733/1250000000 : ℝ)^87 ≤ (4418995207239/50000000000000 : ℝ)^71 := by
    have hnat : (172598733 : ℕ)^87*50000000000000^71 ≤ 4418995207239^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172598733 1250000000 4418995207239 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1514000277/2500000000 : ℝ)^87 ≤ (2704401032277/5000000000000 : ℝ)^71 := by
    have hnat : (1514000277 : ℕ)^87*5000000000000^71 ≤ 2704401032277^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514000277 2500000000 2704401032277 5000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1112399909/2500000000 : ℝ), (-172598733/1250000000 : ℝ), (1514000277/2500000000 : ℝ)] ![(37073988931129/100000000000000 : ℝ), (4418995207239/50000000000000 : ℝ), (2704401032277/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1112399909/2500000000 : ℝ)|^87 ≤ (37073988931129/100000000000000 : ℝ)^71
        have hw : |(1112399909/2500000000 : ℝ)|=(1112399909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172598733/1250000000 : ℝ)|^87 ≤ (4418995207239/50000000000000 : ℝ)^71
        have hw : |(-172598733/1250000000 : ℝ)|=(172598733/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1514000277/2500000000 : ℝ)|^87 ≤ (2704401032277/5000000000000 : ℝ)^71
        have hw : |(1514000277/2500000000 : ℝ)|=(1514000277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_2 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4469366243/10000000000 : ℝ)*x 0 + (3027210679/5000000000 : ℝ)*x 1 + (-848253/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4469366243/10000000000 : ℝ)^87 ≤ (37275899239559/100000000000000 : ℝ)^71 := by
    have hnat : (4469366243 : ℕ)^87*100000000000000^71 ≤ 37275899239559^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469366243 10000000000 37275899239559 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3027210679/5000000000 : ℝ)^87 ≤ (27035366185617/50000000000000 : ℝ)^71 := by
    have hnat : (3027210679 : ℕ)^87*50000000000000^71 ≤ 27035366185617^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3027210679 5000000000 27035366185617 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848253/6250000 : ℝ)^87 ≤ (8653368382239/100000000000000 : ℝ)^71 := by
    have hnat : (848253 : ℕ)^87*100000000000000^71 ≤ 8653368382239^71*6250000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848253 6250000 8653368382239 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4469366243/10000000000 : ℝ), (3027210679/5000000000 : ℝ), (-848253/6250000 : ℝ)] ![(37275899239559/100000000000000 : ℝ), (27035366185617/50000000000000 : ℝ), (8653368382239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4469366243/10000000000 : ℝ)|^87 ≤ (37275899239559/100000000000000 : ℝ)^71
        have hw : |(4469366243/10000000000 : ℝ)|=(4469366243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3027210679/5000000000 : ℝ)|^87 ≤ (27035366185617/50000000000000 : ℝ)^71
        have hw : |(3027210679/5000000000 : ℝ)|=(3027210679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-848253/6250000 : ℝ)|^87 ≤ (8653368382239/100000000000000 : ℝ)^71
        have hw : |(-848253/6250000 : ℝ)|=(848253/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_6 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (286908443/400000000 : ℝ)*x 0 + (147052207/625000000 : ℝ)*x 1 + (458883189/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (286908443/400000000 : ℝ)^87 ≤ (66552024700807/100000000000000 : ℝ)^71 := by
    have hnat : (286908443 : ℕ)^87*100000000000000^71 ≤ 66552024700807^71*400000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286908443 400000000 66552024700807 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147052207/625000000 : ℝ)^87 ≤ (8490795038447/50000000000000 : ℝ)^71 := by
    have hnat : (147052207 : ℕ)^87*50000000000000^71 ≤ 8490795038447^71*625000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147052207 625000000 8490795038447 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458883189/2000000000 : ℝ)^87 ≤ (658655408323/4000000000000 : ℝ)^71 := by
    have hnat : (458883189 : ℕ)^87*4000000000000^71 ≤ 658655408323^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458883189 2000000000 658655408323 4000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(286908443/400000000 : ℝ), (147052207/625000000 : ℝ), (458883189/2000000000 : ℝ)] ![(66552024700807/100000000000000 : ℝ), (8490795038447/50000000000000 : ℝ), (658655408323/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(286908443/400000000 : ℝ)|^87 ≤ (66552024700807/100000000000000 : ℝ)^71
        have hw : |(286908443/400000000 : ℝ)|=(286908443/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147052207/625000000 : ℝ)|^87 ≤ (8490795038447/50000000000000 : ℝ)^71
        have hw : |(147052207/625000000 : ℝ)|=(147052207/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(458883189/2000000000 : ℝ)|^87 ≤ (658655408323/4000000000000 : ℝ)^71
        have hw : |(458883189/2000000000 : ℝ)|=(458883189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_7 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1898248253/10000000000 : ℝ)*x 0 + (2075885469/5000000000 : ℝ)*x 1 + (2973146831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1898248253/10000000000 : ℝ)^87 ≤ (6526770458109/50000000000000 : ℝ)^71 := by
    have hnat : (1898248253 : ℕ)^87*50000000000000^71 ≤ 6526770458109^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1898248253 10000000000 6526770458109 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075885469/5000000000 : ℝ)^87 ≤ (3405661432663/10000000000000 : ℝ)^71 := by
    have hnat : (2075885469 : ℕ)^87*10000000000000^71 ≤ 3405661432663^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075885469 5000000000 3405661432663 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2973146831/5000000000 : ℝ)^87 ≤ (52889844739081/100000000000000 : ℝ)^71 := by
    have hnat : (2973146831 : ℕ)^87*100000000000000^71 ≤ 52889844739081^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2973146831 5000000000 52889844739081 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1898248253/10000000000 : ℝ), (2075885469/5000000000 : ℝ), (2973146831/5000000000 : ℝ)] ![(6526770458109/50000000000000 : ℝ), (3405661432663/10000000000000 : ℝ), (52889844739081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1898248253/10000000000 : ℝ)|^87 ≤ (6526770458109/50000000000000 : ℝ)^71
        have hw : |(-1898248253/10000000000 : ℝ)|=(1898248253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2075885469/5000000000 : ℝ)|^87 ≤ (3405661432663/10000000000000 : ℝ)^71
        have hw : |(2075885469/5000000000 : ℝ)|=(2075885469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2973146831/5000000000 : ℝ)|^87 ≤ (52889844739081/100000000000000 : ℝ)^71
        have hw : |(2973146831/5000000000 : ℝ)|=(2973146831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_8 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1045949319/2500000000 : ℝ)*x 0 + (-5580871/50000000 : ℝ)*x 1 + (6484241477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045949319/2500000000 : ℝ)^87 ≤ (34378804905543/100000000000000 : ℝ)^71 := by
    have hnat : (1045949319 : ℕ)^87*100000000000000^71 ≤ 34378804905543^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045949319 2500000000 34378804905543 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5580871/50000000 : ℝ)^87 ≤ (1361966310971/20000000000000 : ℝ)^71 := by
    have hnat : (5580871 : ℕ)^87*20000000000000^71 ≤ 1361966310971^71*50000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5580871 50000000 1361966310971 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6484241477/10000000000 : ℝ)^87 ≤ (29405681765773/50000000000000 : ℝ)^71 := by
    have hnat : (6484241477 : ℕ)^87*50000000000000^71 ≤ 29405681765773^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6484241477 10000000000 29405681765773 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045949319/2500000000 : ℝ), (-5580871/50000000 : ℝ), (6484241477/10000000000 : ℝ)] ![(34378804905543/100000000000000 : ℝ), (1361966310971/20000000000000 : ℝ), (29405681765773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045949319/2500000000 : ℝ)|^87 ≤ (34378804905543/100000000000000 : ℝ)^71
        have hw : |(1045949319/2500000000 : ℝ)|=(1045949319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5580871/50000000 : ℝ)|^87 ≤ (1361966310971/20000000000000 : ℝ)^71
        have hw : |(-5580871/50000000 : ℝ)|=(5580871/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6484241477/10000000000 : ℝ)|^87 ≤ (29405681765773/50000000000000 : ℝ)^71
        have hw : |(6484241477/10000000000 : ℝ)|=(6484241477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_9 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4203678407/10000000000 : ℝ)*x 0 + (1367924171/2000000000 : ℝ)*x 1 + (-64304147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203678407/10000000000 : ℝ)^87 ≤ (8644773156143/25000000000000 : ℝ)^71 := by
    have hnat : (4203678407 : ℕ)^87*25000000000000^71 ≤ 8644773156143^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203678407 10000000000 8644773156143 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367924171/2000000000 : ℝ)^87 ≤ (31392517943503/50000000000000 : ℝ)^71 := by
    have hnat : (1367924171 : ℕ)^87*50000000000000^71 ≤ 31392517943503^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367924171 2000000000 31392517943503 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64304147/1250000000 : ℝ)^87 ≤ (2635871468493/100000000000000 : ℝ)^71 := by
    have hnat : (64304147 : ℕ)^87*100000000000000^71 ≤ 2635871468493^71*1250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64304147 1250000000 2635871468493 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203678407/10000000000 : ℝ), (1367924171/2000000000 : ℝ), (-64304147/1250000000 : ℝ)] ![(8644773156143/25000000000000 : ℝ), (31392517943503/50000000000000 : ℝ), (2635871468493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203678407/10000000000 : ℝ)|^87 ≤ (8644773156143/25000000000000 : ℝ)^71
        have hw : |(4203678407/10000000000 : ℝ)|=(4203678407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367924171/2000000000 : ℝ)|^87 ≤ (31392517943503/50000000000000 : ℝ)^71
        have hw : |(1367924171/2000000000 : ℝ)|=(1367924171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-64304147/1250000000 : ℝ)|^87 ≤ (2635871468493/100000000000000 : ℝ)^71
        have hw : |(-64304147/1250000000 : ℝ)|=(64304147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_13 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6971676571/10000000000 : ℝ)*x 0 + (909430969/2500000000 : ℝ)*x 1 + (554895123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6971676571/10000000000 : ℝ)^87 ≤ (16068411824143/25000000000000 : ℝ)^71 := by
    have hnat : (6971676571 : ℕ)^87*25000000000000^71 ≤ 16068411824143^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6971676571 10000000000 16068411824143 25000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (909430969/2500000000 : ℝ)^87 ≤ (14482108164791/50000000000000 : ℝ)^71 := by
    have hnat : (909430969 : ℕ)^87*50000000000000^71 ≤ 14482108164791^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      909430969 2500000000 14482108164791 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (554895123/5000000000 : ℝ)^87 ≤ (676213635679/10000000000000 : ℝ)^71 := by
    have hnat : (554895123 : ℕ)^87*10000000000000^71 ≤ 676213635679^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554895123 5000000000 676213635679 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6971676571/10000000000 : ℝ), (909430969/2500000000 : ℝ), (554895123/5000000000 : ℝ)] ![(16068411824143/25000000000000 : ℝ), (14482108164791/50000000000000 : ℝ), (676213635679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6971676571/10000000000 : ℝ)|^87 ≤ (16068411824143/25000000000000 : ℝ)^71
        have hw : |(6971676571/10000000000 : ℝ)|=(6971676571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(909430969/2500000000 : ℝ)|^87 ≤ (14482108164791/50000000000000 : ℝ)^71
        have hw : |(909430969/2500000000 : ℝ)|=(909430969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(554895123/5000000000 : ℝ)|^87 ≤ (676213635679/10000000000000 : ℝ)^71
        have hw : |(554895123/5000000000 : ℝ)|=(554895123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_14 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-216494707/2000000000 : ℝ)*x 0 + (2428276713/5000000000 : ℝ)*x 1 + (73502707/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216494707/2000000000 : ℝ)^87 ≤ (655875159719/10000000000000 : ℝ)^71 := by
    have hnat : (216494707 : ℕ)^87*10000000000000^71 ≤ 655875159719^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216494707 2000000000 655875159719 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2428276713/5000000000 : ℝ)^87 ≤ (41270673978657/100000000000000 : ℝ)^71 := by
    have hnat : (2428276713 : ℕ)^87*100000000000000^71 ≤ 41270673978657^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2428276713 5000000000 41270673978657 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73502707/125000000 : ℝ)^87 ≤ (26085287207179/50000000000000 : ℝ)^71 := by
    have hnat : (73502707 : ℕ)^87*50000000000000^71 ≤ 26085287207179^71*125000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73502707 125000000 26085287207179 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216494707/2000000000 : ℝ), (2428276713/5000000000 : ℝ), (73502707/125000000 : ℝ)] ![(655875159719/10000000000000 : ℝ), (41270673978657/100000000000000 : ℝ), (26085287207179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216494707/2000000000 : ℝ)|^87 ≤ (655875159719/10000000000000 : ℝ)^71
        have hw : |(-216494707/2000000000 : ℝ)|=(216494707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2428276713/5000000000 : ℝ)|^87 ≤ (41270673978657/100000000000000 : ℝ)^71
        have hw : |(2428276713/5000000000 : ℝ)|=(2428276713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73502707/125000000 : ℝ)|^87 ≤ (26085287207179/50000000000000 : ℝ)^71
        have hw : |(73502707/125000000 : ℝ)|=(73502707/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_15 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (103639011/250000000 : ℝ)*x 0 + (-569965597/5000000000 : ℝ)*x 1 + (6502822747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103639011/250000000 : ℝ)^87 ≤ (33994200302761/100000000000000 : ℝ)^71 := by
    have hnat : (103639011 : ℕ)^87*100000000000000^71 ≤ 33994200302761^71*250000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103639011 250000000 33994200302761 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569965597/5000000000 : ℝ)^87 ≤ (1397572165401/20000000000000 : ℝ)^71 := by
    have hnat : (569965597 : ℕ)^87*20000000000000^71 ≤ 1397572165401^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569965597 5000000000 1397572165401 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6502822747/10000000000 : ℝ)^87 ≤ (11803587773483/20000000000000 : ℝ)^71 := by
    have hnat : (6502822747 : ℕ)^87*20000000000000^71 ≤ 11803587773483^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6502822747 10000000000 11803587773483 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(103639011/250000000 : ℝ), (-569965597/5000000000 : ℝ), (6502822747/10000000000 : ℝ)] ![(33994200302761/100000000000000 : ℝ), (1397572165401/20000000000000 : ℝ), (11803587773483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(103639011/250000000 : ℝ)|^87 ≤ (33994200302761/100000000000000 : ℝ)^71
        have hw : |(103639011/250000000 : ℝ)|=(103639011/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-569965597/5000000000 : ℝ)|^87 ≤ (1397572165401/20000000000000 : ℝ)^71
        have hw : |(-569965597/5000000000 : ℝ)|=(569965597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6502822747/10000000000 : ℝ)|^87 ≤ (11803587773483/20000000000000 : ℝ)^71
        have hw : |(6502822747/10000000000 : ℝ)|=(6502822747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_16 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2689086409/5000000000 : ℝ)*x 0 + (2848102361/5000000000 : ℝ)*x 1 + (-580509353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689086409/5000000000 : ℝ)^87 ≤ (46766269278789/100000000000000 : ℝ)^71 := by
    have hnat : (2689086409 : ℕ)^87*100000000000000^71 ≤ 46766269278789^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689086409 5000000000 46766269278789 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2848102361/5000000000 : ℝ)^87 ≤ (10035436826287/20000000000000 : ℝ)^71 := by
    have hnat : (2848102361 : ℕ)^87*20000000000000^71 ≤ 10035436826287^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848102361 5000000000 10035436826287 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (580509353/10000000000 : ℝ)^87 ≤ (305654657401/10000000000000 : ℝ)^71 := by
    have hnat : (580509353 : ℕ)^87*10000000000000^71 ≤ 305654657401^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580509353 10000000000 305654657401 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689086409/5000000000 : ℝ), (2848102361/5000000000 : ℝ), (-580509353/10000000000 : ℝ)] ![(46766269278789/100000000000000 : ℝ), (10035436826287/20000000000000 : ℝ), (305654657401/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689086409/5000000000 : ℝ)|^87 ≤ (46766269278789/100000000000000 : ℝ)^71
        have hw : |(2689086409/5000000000 : ℝ)|=(2689086409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2848102361/5000000000 : ℝ)|^87 ≤ (10035436826287/20000000000000 : ℝ)^71
        have hw : |(2848102361/5000000000 : ℝ)|=(2848102361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-580509353/10000000000 : ℝ)|^87 ≤ (305654657401/10000000000000 : ℝ)^71
        have hw : |(-580509353/10000000000 : ℝ)|=(580509353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_20 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1633997873/2000000000 : ℝ)*x 0 + (2194500617/10000000000 : ℝ)*x 1 + (526850591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1633997873/2000000000 : ℝ)^87 ≤ (7806213387397/10000000000000 : ℝ)^71 := by
    have hnat : (1633997873 : ℕ)^87*10000000000000^71 ≤ 7806213387397^71*2000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633997873 2000000000 7806213387397 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194500617/10000000000 : ℝ)^87 ≤ (15592089441571/100000000000000 : ℝ)^71 := by
    have hnat : (2194500617 : ℕ)^87*100000000000000^71 ≤ 15592089441571^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194500617 10000000000 15592089441571 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526850591/5000000000 : ℝ)^87 ≤ (6345776671267/100000000000000 : ℝ)^71 := by
    have hnat : (526850591 : ℕ)^87*100000000000000^71 ≤ 6345776671267^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526850591 5000000000 6345776671267 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1633997873/2000000000 : ℝ), (2194500617/10000000000 : ℝ), (526850591/5000000000 : ℝ)] ![(7806213387397/10000000000000 : ℝ), (15592089441571/100000000000000 : ℝ), (6345776671267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1633997873/2000000000 : ℝ)|^87 ≤ (7806213387397/10000000000000 : ℝ)^71
        have hw : |(1633997873/2000000000 : ℝ)|=(1633997873/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194500617/10000000000 : ℝ)|^87 ≤ (15592089441571/100000000000000 : ℝ)^71
        have hw : |(2194500617/10000000000 : ℝ)|=(2194500617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526850591/5000000000 : ℝ)|^87 ≤ (6345776671267/100000000000000 : ℝ)^71
        have hw : |(526850591/5000000000 : ℝ)|=(526850591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_21 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-239994303/2500000000 : ℝ)*x 0 + (5391515803/10000000000 : ℝ)*x 1 + (5440410627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239994303/2500000000 : ℝ)^87 ≤ (2830618085961/50000000000000 : ℝ)^71 := by
    have hnat : (239994303 : ℕ)^87*50000000000000^71 ≤ 2830618085961^71*2500000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239994303 2500000000 2830618085961 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391515803/10000000000 : ℝ)^87 ≤ (23454240138361/50000000000000 : ℝ)^71 := by
    have hnat : (5391515803 : ℕ)^87*50000000000000^71 ≤ 23454240138361^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391515803 10000000000 23454240138361 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440410627/10000000000 : ℝ)^87 ≤ (47430283540641/100000000000000 : ℝ)^71 := by
    have hnat : (5440410627 : ℕ)^87*100000000000000^71 ≤ 47430283540641^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440410627 10000000000 47430283540641 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239994303/2500000000 : ℝ), (5391515803/10000000000 : ℝ), (5440410627/10000000000 : ℝ)] ![(2830618085961/50000000000000 : ℝ), (23454240138361/50000000000000 : ℝ), (47430283540641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239994303/2500000000 : ℝ)|^87 ≤ (2830618085961/50000000000000 : ℝ)^71
        have hw : |(-239994303/2500000000 : ℝ)|=(239994303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391515803/10000000000 : ℝ)|^87 ≤ (23454240138361/50000000000000 : ℝ)^71
        have hw : |(5391515803/10000000000 : ℝ)|=(5391515803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440410627/10000000000 : ℝ)|^87 ≤ (47430283540641/100000000000000 : ℝ)^71
        have hw : |(5440410627/10000000000 : ℝ)|=(5440410627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_22 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5480785827/10000000000 : ℝ)*x 0 + (-708904741/10000000000 : ℝ)*x 1 + (2757742781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5480785827/10000000000 : ℝ)^87 ≤ (23930981779833/50000000000000 : ℝ)^71 := by
    have hnat : (5480785827 : ℕ)^87*50000000000000^71 ≤ 23930981779833^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480785827 10000000000 23930981779833 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708904741/10000000000 : ℝ)^87 ≤ (3904500038413/100000000000000 : ℝ)^71 := by
    have hnat : (708904741 : ℕ)^87*100000000000000^71 ≤ 3904500038413^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708904741 10000000000 3904500038413 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2757742781/5000000000 : ℝ)^87 ≤ (482335363809/1000000000000 : ℝ)^71 := by
    have hnat : (2757742781 : ℕ)^87*1000000000000^71 ≤ 482335363809^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757742781 5000000000 482335363809 1000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5480785827/10000000000 : ℝ), (-708904741/10000000000 : ℝ), (2757742781/5000000000 : ℝ)] ![(23930981779833/50000000000000 : ℝ), (3904500038413/100000000000000 : ℝ), (482335363809/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5480785827/10000000000 : ℝ)|^87 ≤ (23930981779833/50000000000000 : ℝ)^71
        have hw : |(5480785827/10000000000 : ℝ)|=(5480785827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-708904741/10000000000 : ℝ)|^87 ≤ (3904500038413/100000000000000 : ℝ)^71
        have hw : |(-708904741/10000000000 : ℝ)|=(708904741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2757742781/5000000000 : ℝ)|^87 ≤ (482335363809/1000000000000 : ℝ)^71
        have hw : |(2757742781/5000000000 : ℝ)|=(2757742781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_23 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2054502633/5000000000 : ℝ)*x 0 + (3354485843/5000000000 : ℝ)*x 1 + (-8750933/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054502633/5000000000 : ℝ)^87 ≤ (16813628639873/50000000000000 : ℝ)^71 := by
    have hnat : (2054502633 : ℕ)^87*50000000000000^71 ≤ 16813628639873^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054502633 5000000000 16813628639873 50000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3354485843/5000000000 : ℝ)^87 ≤ (61318639885641/100000000000000 : ℝ)^71 := by
    have hnat : (3354485843 : ℕ)^87*100000000000000^71 ≤ 61318639885641^71*5000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3354485843 5000000000 61318639885641 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8750933/100000000 : ℝ)^87 ≤ (505410282581/10000000000000 : ℝ)^71 := by
    have hnat : (8750933 : ℕ)^87*10000000000000^71 ≤ 505410282581^71*100000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8750933 100000000 505410282581 10000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2054502633/5000000000 : ℝ), (3354485843/5000000000 : ℝ), (-8750933/100000000 : ℝ)] ![(16813628639873/50000000000000 : ℝ), (61318639885641/100000000000000 : ℝ), (505410282581/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2054502633/5000000000 : ℝ)|^87 ≤ (16813628639873/50000000000000 : ℝ)^71
        have hw : |(2054502633/5000000000 : ℝ)|=(2054502633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3354485843/5000000000 : ℝ)|^87 ≤ (61318639885641/100000000000000 : ℝ)^71
        have hw : |(3354485843/5000000000 : ℝ)|=(3354485843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8750933/100000000 : ℝ)|^87 ≤ (505410282581/10000000000000 : ℝ)^71
        have hw : |(-8750933/100000000 : ℝ)|=(8750933/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c325053_s1_s1_27 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8340370493/10000000000 : ℝ)*x 0 + (1519062863/10000000000 : ℝ)*x 1 + (152773919/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8340370493/10000000000 : ℝ)^87 ≤ (16012321056231/20000000000000 : ℝ)^71 := by
    have hnat : (8340370493 : ℕ)^87*20000000000000^71 ≤ 16012321056231^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8340370493 10000000000 16012321056231 20000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1519062863/10000000000 : ℝ)^87 ≤ (9934410738569/100000000000000 : ℝ)^71 := by
    have hnat : (1519062863 : ℕ)^87*100000000000000^71 ≤ 9934410738569^71*10000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519062863 10000000000 9934410738569 100000000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (152773919/1000000000 : ℝ)^87 ≤ (50019919851/500000000000 : ℝ)^71 := by
    have hnat : (152773919 : ℕ)^87*500000000000^71 ≤ 50019919851^71*1000000000^87 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152773919 1000000000 50019919851 500000000000 87 71 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (87/16 : ℝ)) 87 71 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8340370493/10000000000 : ℝ), (1519062863/10000000000 : ℝ), (152773919/1000000000 : ℝ)] ![(16012321056231/20000000000000 : ℝ), (9934410738569/100000000000000 : ℝ), (50019919851/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8340370493/10000000000 : ℝ)|^87 ≤ (16012321056231/20000000000000 : ℝ)^71
        have hw : |(8340370493/10000000000 : ℝ)|=(8340370493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1519062863/10000000000 : ℝ)|^87 ≤ (9934410738569/100000000000000 : ℝ)^71
        have hw : |(1519062863/10000000000 : ℝ)|=(1519062863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(152773919/1000000000 : ℝ)|^87 ≤ (50019919851/500000000000 : ℝ)^71
        have hw : |(152773919/1000000000 : ℝ)|=(152773919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c325053_s1 (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((67047/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67047/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4201/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4201/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65643/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30529/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30529/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36817/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(701/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(701/2000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (81317/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (81317/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (81317/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (67047/100000 : ℝ) ^ (85/16 : ℝ) ≤ (2391499496506087057/20000000000000000000 : ℝ) := by
    have hpowers : (67047/100000 : ℝ)^85 ≤ (2391499496506087057/20000000000000000000 : ℝ)^16 := by
      have hnat : (67047 : ℕ)^85*20000000000000000000^16 ≤ 2391499496506087057^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67047 100000 2391499496506087057 20000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67047/100000 : ℝ)) (X := (2391499496506087057/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (22391499496506087057/20000000000000000000 : ℝ) ≤ (638430398555783/625000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (22391499496506087057/20000000000000000000 : ℝ)^16 ≤ (638430398555783/625000000000000 : ℝ)^85 := by
      have hnat : (22391499496506087057 : ℕ)^16*625000000000000^85 ≤ 638430398555783^85*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22391499496506087057 20000000000000000000 638430398555783 625000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (638430398555783/625000000000000 : ℝ)) (X := (22391499496506087057/20000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (12391499496506087057/10000000000000000000 : ℝ) ≤ (2602970262249757/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (12391499496506087057/10000000000000000000 : ℝ)^16 ≤ (2602970262249757/2500000000000000 : ℝ)^85 := by
      have hnat : (12391499496506087057 : ℕ)^16*2500000000000000^85 ≤ 2602970262249757^85*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12391499496506087057 10000000000000000000 2602970262249757 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2602970262249757/2500000000000000 : ℝ)) (X := (12391499496506087057/10000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13430398555783/419043750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(393989344213/13409400000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (67047/100000 : ℝ)) (alpha := (13430398555783/419043750000000 : ℝ)) (beta := (393989344213/13409400000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (67047/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13430398555783/419043750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(393989344213/13409400000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (4201/6250 : ℝ) ^ (85/16 : ℝ) ≤ (12118490550169430539/100000000000000000000 : ℝ) := by
    have hpowers : (4201/6250 : ℝ)^85 ≤ (12118490550169430539/100000000000000000000 : ℝ)^16 := by
      have hnat : (4201 : ℕ)^85*100000000000000000000^16 ≤ 12118490550169430539^16*6250^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4201 6250 12118490550169430539 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4201/6250 : ℝ)) (X := (12118490550169430539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (112118490550169430539/100000000000000000000 : ℝ) ≤ (255441243071201/250000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (112118490550169430539/100000000000000000000 : ℝ)^16 ≤ (255441243071201/250000000000000 : ℝ)^85 := by
      have hnat : (112118490550169430539 : ℕ)^16*250000000000000^85 ≤ 255441243071201^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112118490550169430539 100000000000000000000 255441243071201 250000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (255441243071201/250000000000000 : ℝ)) (X := (112118490550169430539/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (62118490550169430539/50000000000000000000 : ℝ) ≤ (10416968333257161/10000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (62118490550169430539/50000000000000000000 : ℝ)^16 ≤ (10416968333257161/10000000000000000 : ℝ)^85 := by
      have hnat : (62118490550169430539 : ℕ)^16*10000000000000000^85 ≤ 10416968333257161^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62118490550169430539 50000000000000000000 10416968333257161 10000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10416968333257161/10000000000000000 : ℝ)) (X := (62118490550169430539/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(5441243071201/168040000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(199318610409121/6721600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (4201/6250 : ℝ)) (alpha := (5441243071201/168040000000000 : ℝ)) (beta := (199318610409121/6721600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (4201/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(5441243071201/168040000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(199318610409121/6721600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (65643/100000 : ℝ) ^ (85/16 : ℝ) ≤ (10685958562888286031/100000000000000000000 : ℝ) := by
    have hpowers : (65643/100000 : ℝ)^85 ≤ (10685958562888286031/100000000000000000000 : ℝ)^16 := by
      have hnat : (65643 : ℕ)^85*100000000000000000000^16 ≤ 10685958562888286031^16*100000^85 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65643 100000 10685958562888286031 100000000000000000000 85 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65643/100000 : ℝ)) (X := (10685958562888286031/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110685958562888286031/100000000000000000000 : ℝ) ≤ (5096473551845229/5000000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (110685958562888286031/100000000000000000000 : ℝ)^16 ≤ (5096473551845229/5000000000000000 : ℝ)^85 := by
      have hnat : (110685958562888286031 : ℕ)^16*5000000000000000^85 ≤ 5096473551845229^85*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110685958562888286031 100000000000000000000 5096473551845229 5000000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5096473551845229/5000000000000000 : ℝ)) (X := (110685958562888286031/100000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60685958562888286031/50000000000000000000 : ℝ) ≤ (2592829892684549/2500000000000000 : ℝ) ^ (85/16 : ℝ) := by
    have hpowers : (60685958562888286031/50000000000000000000 : ℝ)^16 ≤ (2592829892684549/2500000000000000 : ℝ)^85 := by
      have hnat : (60685958562888286031 : ℕ)^16*2500000000000000^85 ≤ 2592829892684549^85*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60685958562888286031 50000000000000000000 2592829892684549 2500000000000000 16 85 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2592829892684549/2500000000000000 : ℝ)) (X := (60685958562888286031/50000000000000000000 : ℝ)) (by norm_num) 85 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(96473551845229/3282150000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(89186233523869/3282150000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (85/16 : ℝ)) (rho := (65643/100000 : ℝ)) (alpha := (96473551845229/3282150000000000 : ℝ)) (beta := (89186233523869/3282150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (65643/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(96473551845229/3282150000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(89186233523869/3282150000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-976644503/5000000000 : ℝ)*X 0 0+(314017859/625000000 : ℝ)*X 0 1+(5065529027/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1112399909/2500000000 : ℝ)*X 1 0+(-172598733/1250000000 : ℝ)*X 1 1+(1514000277/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4469366243/10000000000 : ℝ)*X 2 0+(3027210679/5000000000 : ℝ)*X 2 1+(-848253/6250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((286908443/400000000 : ℝ)*X 0 0+(147052207/625000000 : ℝ)*X 0 1+(458883189/2000000000 : ℝ)*X 0 2+(286908443/400000000 : ℝ)*X 1 0+(147052207/625000000 : ℝ)*X 1 1+(458883189/2000000000 : ℝ)*X 1 2+(286908443/400000000 : ℝ)*X 2 0+(147052207/625000000 : ℝ)*X 2 1+(458883189/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1898248253/10000000000 : ℝ)*X 0 0+(2075885469/5000000000 : ℝ)*X 0 1+(2973146831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1045949319/2500000000 : ℝ)*X 1 0+(-5580871/50000000 : ℝ)*X 1 1+(6484241477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4203678407/10000000000 : ℝ)*X 2 0+(1367924171/2000000000 : ℝ)*X 2 1+(-64304147/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6971676571/10000000000 : ℝ)*X 0 0+(909430969/2500000000 : ℝ)*X 0 1+(554895123/5000000000 : ℝ)*X 0 2+(6971676571/10000000000 : ℝ)*X 1 0+(909430969/2500000000 : ℝ)*X 1 1+(554895123/5000000000 : ℝ)*X 1 2+(6971676571/10000000000 : ℝ)*X 2 0+(909430969/2500000000 : ℝ)*X 2 1+(554895123/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-216494707/2000000000 : ℝ)*X 0 0+(2428276713/5000000000 : ℝ)*X 0 1+(73502707/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((103639011/250000000 : ℝ)*X 1 0+(-569965597/5000000000 : ℝ)*X 1 1+(6502822747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2689086409/5000000000 : ℝ)*X 2 0+(2848102361/5000000000 : ℝ)*X 2 1+(-580509353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1633997873/2000000000 : ℝ)*X 0 0+(2194500617/10000000000 : ℝ)*X 0 1+(526850591/5000000000 : ℝ)*X 0 2+(1633997873/2000000000 : ℝ)*X 1 0+(2194500617/10000000000 : ℝ)*X 1 1+(526850591/5000000000 : ℝ)*X 1 2+(1633997873/2000000000 : ℝ)*X 2 0+(2194500617/10000000000 : ℝ)*X 2 1+(526850591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-239994303/2500000000 : ℝ)*X 0 0+(5391515803/10000000000 : ℝ)*X 0 1+(5440410627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5480785827/10000000000 : ℝ)*X 1 0+(-708904741/10000000000 : ℝ)*X 1 1+(2757742781/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2054502633/5000000000 : ℝ)*X 2 0+(3354485843/5000000000 : ℝ)*X 2 1+(-8750933/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8340370493/10000000000 : ℝ)*X 0 0+(1519062863/10000000000 : ℝ)*X 0 1+(152773919/1000000000 : ℝ)*X 0 2+(8340370493/10000000000 : ℝ)*X 1 0+(1519062863/10000000000 : ℝ)*X 1 1+(152773919/1000000000 : ℝ)*X 1 2+(8340370493/10000000000 : ℝ)*X 2 0+(1519062863/10000000000 : ℝ)*X 2 1+(152773919/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c325053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((30529/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30529/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (732550368536980924621456410693/164349327061520000000000000000000000 : ℝ) := by norm_num
    linear_combination (78973/100000000000 : ℝ)*(base8) + (123398723359/1000000000000 : ℝ)*(base49) + (952007312787/1000000000000 : ℝ)*(base59) + (2832426721551/500000000000 : ℝ)*(major_s1_0) + (2832426721551/500000000000 : ℝ)*(major_s1_1) + (2832426721551/500000000000 : ℝ)*(major_s1_2) + (64249/12500000000 : ℝ)*(sp_s1_0) + (1481389/1000000000000 : ℝ)*(sp_s1_6) + (8510508849203/1000000000000 : ℝ)*(sp_s1_7) + (4254910603501/500000000000 : ℝ)*(sp_s1_8) + (1063811216747/125000000000 : ℝ)*(sp_s1_9) + (2819189140193/1000000000000 : ℝ)*(sp_s1_13) + (13871437/20000000000 : ℝ)*(sp_s1_15) + (6261219/250000000000 : ℝ)*(sp_s1_23) + (2819190621583/1000000000000 : ℝ)*(f.failure) + (8510514778853/1000000000000 : ℝ)*(f.sum) + (6830395801873224937/9192208100000000000000000000000 : ℝ)*base63 + (70340118975201/273512500000000000000000000 : ℝ)*base65 + (2443897581364609/3360800000000000000000000000 : ℝ)*base67 + (15366798188049/17094531250000000000000000 : ℝ)*base69 + (77669907682612309/12225461725000000000000000000000 : ℝ)*base70 + (166511680851637/223490000000000000000000000 : ℝ)*base73 + (75669277345099/84020000000000000000000000 : ℝ)*base75 + (229192583120059/279362500000000000000000000 : ℝ)*base77 + (34081552365289694381/75110519200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (66437/100000000000000000 : ℝ)*base87 + (66437/100000000000000000 : ℝ)*base89 + (66437/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36817/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (128441828115288452995652399/9192208100000000000000000000000 : ℝ) := by norm_num
    linear_combination (37873221841/200000000000 : ℝ)*(base49) + (18365750607/50000000000 : ℝ)*(base59) + (5488722741329/1000000000000 : ℝ)*(major_s1_0) + (5488722741329/1000000000000 : ℝ)*(major_s1_1) + (5488722741329/1000000000000 : ℝ)*(major_s1_2) + (28653293/1000000000000 : ℝ)*(sp_s1_1) + (29833961/1000000000000 : ℝ)*(sp_s1_2) + (76610749/1000000000000 : ℝ)*(sp_s1_7) + (80776943/500000000000 : ℝ)*(sp_s1_8) + (8245827408903/1000000000000 : ℝ)*(sp_s1_14) + (1030714226559/125000000000 : ℝ)*(sp_s1_15) + (8245874185691/1000000000000 : ℝ)*(sp_s1_16) + (682862667031/250000000000 : ℝ)*(sp_s1_20) + (2153431/25000000000 : ℝ)*(sp_s1_27) + (2731536805363/1000000000000 : ℝ)*(f.failure) + (8245904019651/1000000000000 : ℝ)*(f.sum) + (23256182579931837181/55153248600000000000000000000000 : ℝ)*base62 + (531662699682521/3282150000000000000000000000 : ℝ)*base64 + (1206394696603569/6721600000000000000000000000 : ℝ)*base66 + (1680557263053619/3282150000000000000000000000 : ℝ)*base68 + (17526401268561822907/73352770350000000000000000000000 : ℝ)*base71 + (3311682197999/167617500000000000000000000 : ℝ)*base72 + (33353982101607/33608000000000000000000000 : ℝ)*base74 + (68495950051207/104760937500000000000000000 : ℝ)*base76 + (191637622364587641577/450663115200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (64143/100000000000000000 : ℝ)*base86 + (64143/100000000000000000 : ℝ)*base88 + (64143/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(701/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(701/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12568397685350591411245885878189/821746635307600000000000000000000000 : ℝ) := by norm_num
    linear_combination (246144621783/1000000000000 : ℝ)*(base40) + (17727426503/1000000000000 : ℝ)*(base49) + (208633668109/500000000000 : ℝ)*(base59) + (2391502901563/500000000000 : ℝ)*(major_s1_0) + (2391502901563/500000000000 : ℝ)*(major_s1_1) + (2391502901563/500000000000 : ℝ)*(major_s1_2) + (32990881/1000000000000 : ℝ)*(sp_s1_0) + (18807971/500000000000 : ℝ)*(sp_s1_2) + (32654601/1000000000000 : ℝ)*(sp_s1_16) + (100126787/500000000000 : ℝ)*(sp_s1_20) + (7185646252063/1000000000000 : ℝ)*(sp_s1_21) + (7185679242943/1000000000000 : ℝ)*(sp_s1_22) + (7185608972401/1000000000000 : ℝ)*(sp_s1_23) + (2380127011479/1000000000000 : ℝ)*(sp_s1_27) + (2380327265053/1000000000000 : ℝ)*(f.failure) + (7185679242943/1000000000000 : ℝ)*(f.sum) + (12557711550707302903/27576624300000000000000000000000 : ℝ)*base63 + (49720416415043/1641075000000000000000000000 : ℝ)*base65 + (90386541246597/3360800000000000000000000000 : ℝ)*base67 + (727068213325121/820537500000000000000000000 : ℝ)*base69 + (4343048543721664921/36676385175000000000000000000000 : ℝ)*base70 + (30611151418627/41904375000000000000000000 : ℝ)*base73 + (31474636322669/84020000000000000000000000 : ℝ)*base75 + (365937897746801/3352350000000000000000000000 : ℝ)*base76 + (53811758751805895219/225331557600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (115233/100000000000000000 : ℝ)*base86 + (115233/100000000000000000 : ℝ)*base88 + (115233/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (85/16 : ℝ) ≤ p) (hpb : p ≤ (87/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (200939/100000 : ℝ) (33069/20000 : ℝ) (81317/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((67047/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(67047/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4201/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4201/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65643/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65643/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30529/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30529/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36817/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36817/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(701/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(701/2000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c325053_s1 p hpa hpb X hX hprev0

#print axioms solution
