-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302053_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:30.889711+00:00
-- url     : https://prove2.me/submissions/82b4a74f-25c1-4a13-91d3-89fb8e02008c

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
theorem collision_support_c302053_s7_s7_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-13994203/50000000 : ℝ)*x 0 + (1263571493/2500000000 : ℝ)*x 1 + (5065743721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13994203/50000000 : ℝ)^33 ≤ (4655337660757/25000000000000 : ℝ)^25 := by
    have hnat : (13994203 : ℕ)^33*25000000000000^25 ≤ 4655337660757^25*50000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13994203 50000000 4655337660757 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1263571493/2500000000 : ℝ)^33 ≤ (40628515119067/100000000000000 : ℝ)^25 := by
    have hnat : (1263571493 : ℕ)^33*100000000000000^25 ≤ 40628515119067^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263571493 2500000000 40628515119067 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5065743721/10000000000 : ℝ)^33 ≤ (20375067109959/50000000000000 : ℝ)^25 := by
    have hnat : (5065743721 : ℕ)^33*50000000000000^25 ≤ 20375067109959^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5065743721 10000000000 20375067109959 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13994203/50000000 : ℝ), (1263571493/2500000000 : ℝ), (5065743721/10000000000 : ℝ)] ![(4655337660757/25000000000000 : ℝ), (40628515119067/100000000000000 : ℝ), (20375067109959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13994203/50000000 : ℝ)|^33 ≤ (4655337660757/25000000000000 : ℝ)^25
        have hw : |(-13994203/50000000 : ℝ)|=(13994203/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1263571493/2500000000 : ℝ)|^33 ≤ (40628515119067/100000000000000 : ℝ)^25
        have hw : |(1263571493/2500000000 : ℝ)|=(1263571493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5065743721/10000000000 : ℝ)|^33 ≤ (20375067109959/50000000000000 : ℝ)^25
        have hw : |(5065743721/10000000000 : ℝ)|=(5065743721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1131603523/2500000000 : ℝ)*x 0 + (-581732197/2500000000 : ℝ)*x 1 + (5940271909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1131603523/2500000000 : ℝ)^33 ≤ (1756166372151/5000000000000 : ℝ)^25 := by
    have hnat : (1131603523 : ℕ)^33*5000000000000^25 ≤ 1756166372151^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131603523 2500000000 1756166372151 5000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (581732197/2500000000 : ℝ)^33 ≤ (14593305769527/100000000000000 : ℝ)^25 := by
    have hnat : (581732197 : ℕ)^33*100000000000000^25 ≤ 14593305769527^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      581732197 2500000000 14593305769527 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5940271909/10000000000 : ℝ)^33 ≤ (1005667335629/2000000000000 : ℝ)^25 := by
    have hnat : (5940271909 : ℕ)^33*2000000000000^25 ≤ 1005667335629^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5940271909 10000000000 1005667335629 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1131603523/2500000000 : ℝ), (-581732197/2500000000 : ℝ), (5940271909/10000000000 : ℝ)] ![(1756166372151/5000000000000 : ℝ), (14593305769527/100000000000000 : ℝ), (1005667335629/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1131603523/2500000000 : ℝ)|^33 ≤ (1756166372151/5000000000000 : ℝ)^25
        have hw : |(1131603523/2500000000 : ℝ)|=(1131603523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-581732197/2500000000 : ℝ)|^33 ≤ (14593305769527/100000000000000 : ℝ)^25
        have hw : |(-581732197/2500000000 : ℝ)|=(581732197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5940271909/10000000000 : ℝ)|^33 ≤ (1005667335629/2000000000000 : ℝ)^25
        have hw : |(5940271909/10000000000 : ℝ)|=(5940271909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (22706449/50000000 : ℝ)*x 0 + (2966806397/5000000000 : ℝ)*x 1 + (-2317493861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22706449/50000000 : ℝ)^33 ≤ (35275775214659/100000000000000 : ℝ)^25 := by
    have hnat : (22706449 : ℕ)^33*100000000000000^25 ≤ 35275775214659^25*50000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22706449 50000000 35275775214659 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2966806397/5000000000 : ℝ)^33 ≤ (50208974042693/100000000000000 : ℝ)^25 := by
    have hnat : (2966806397 : ℕ)^33*100000000000000^25 ≤ 50208974042693^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2966806397 5000000000 50208974042693 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2317493861/10000000000 : ℝ)^33 ≤ (1451525072661/10000000000000 : ℝ)^25 := by
    have hnat : (2317493861 : ℕ)^33*10000000000000^25 ≤ 1451525072661^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317493861 10000000000 1451525072661 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(22706449/50000000 : ℝ), (2966806397/5000000000 : ℝ), (-2317493861/10000000000 : ℝ)] ![(35275775214659/100000000000000 : ℝ), (50208974042693/100000000000000 : ℝ), (1451525072661/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(22706449/50000000 : ℝ)|^33 ≤ (35275775214659/100000000000000 : ℝ)^25
        have hw : |(22706449/50000000 : ℝ)|=(22706449/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2966806397/5000000000 : ℝ)|^33 ≤ (50208974042693/100000000000000 : ℝ)^25
        have hw : |(2966806397/5000000000 : ℝ)|=(2966806397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2317493861/10000000000 : ℝ)|^33 ≤ (1451525072661/10000000000000 : ℝ)^25
        have hw : |(-2317493861/10000000000 : ℝ)|=(2317493861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1242357959/2000000000 : ℝ)*x 0 + (1664377969/5000000000 : ℝ)*x 1 + (3311472647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1242357959/2000000000 : ℝ)^33 ≤ (53339152531951/100000000000000 : ℝ)^25 := by
    have hnat : (1242357959 : ℕ)^33*100000000000000^25 ≤ 53339152531951^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242357959 2000000000 53339152531951 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1664377969/5000000000 : ℝ)^33 ≤ (468211606433/2000000000000 : ℝ)^25 := by
    have hnat : (1664377969 : ℕ)^33*2000000000000^25 ≤ 468211606433^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664377969 5000000000 468211606433 2000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3311472647/10000000000 : ℝ)^33 ≤ (23250267138413/100000000000000 : ℝ)^25 := by
    have hnat : (3311472647 : ℕ)^33*100000000000000^25 ≤ 23250267138413^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3311472647 10000000000 23250267138413 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1242357959/2000000000 : ℝ), (1664377969/5000000000 : ℝ), (3311472647/10000000000 : ℝ)] ![(53339152531951/100000000000000 : ℝ), (468211606433/2000000000000 : ℝ), (23250267138413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1242357959/2000000000 : ℝ)|^33 ≤ (53339152531951/100000000000000 : ℝ)^25
        have hw : |(1242357959/2000000000 : ℝ)|=(1242357959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1664377969/5000000000 : ℝ)|^33 ≤ (468211606433/2000000000000 : ℝ)^25
        have hw : |(1664377969/5000000000 : ℝ)|=(1664377969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3311472647/10000000000 : ℝ)|^33 ≤ (23250267138413/100000000000000 : ℝ)^25
        have hw : |(3311472647/10000000000 : ℝ)|=(3311472647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-273573789/1000000000 : ℝ)*x 0 + (2170601083/5000000000 : ℝ)*x 1 + (1449324741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273573789/1000000000 : ℝ)^33 ≤ (4517293716139/25000000000000 : ℝ)^25 := by
    have hnat : (273573789 : ℕ)^33*25000000000000^25 ≤ 4517293716139^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273573789 1000000000 4517293716139 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2170601083/5000000000 : ℝ)^33 ≤ (33238790679941/100000000000000 : ℝ)^25 := by
    have hnat : (2170601083 : ℕ)^33*100000000000000^25 ≤ 33238790679941^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170601083 5000000000 33238790679941 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1449324741/2500000000 : ℝ)^33 ≤ (9738406886409/20000000000000 : ℝ)^25 := by
    have hnat : (1449324741 : ℕ)^33*20000000000000^25 ≤ 9738406886409^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449324741 2500000000 9738406886409 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273573789/1000000000 : ℝ), (2170601083/5000000000 : ℝ), (1449324741/2500000000 : ℝ)] ![(4517293716139/25000000000000 : ℝ), (33238790679941/100000000000000 : ℝ), (9738406886409/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273573789/1000000000 : ℝ)|^33 ≤ (4517293716139/25000000000000 : ℝ)^25
        have hw : |(-273573789/1000000000 : ℝ)|=(273573789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2170601083/5000000000 : ℝ)|^33 ≤ (33238790679941/100000000000000 : ℝ)^25
        have hw : |(2170601083/5000000000 : ℝ)|=(2170601083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1449324741/2500000000 : ℝ)|^33 ≤ (9738406886409/20000000000000 : ℝ)^25
        have hw : |(1449324741/2500000000 : ℝ)|=(1449324741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2166765823/5000000000 : ℝ)*x 0 + (-1971866187/10000000000 : ℝ)*x 1 + (6367432909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166765823/5000000000 : ℝ)^33 ≤ (6632257800687/20000000000000 : ℝ)^25 := by
    have hnat : (2166765823 : ℕ)^33*20000000000000^25 ≤ 6632257800687^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166765823 5000000000 6632257800687 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1971866187/10000000000 : ℝ)^33 ≤ (293209629621/2500000000000 : ℝ)^25 := by
    have hnat : (1971866187 : ℕ)^33*2500000000000^25 ≤ 293209629621^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1971866187 10000000000 293209629621 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6367432909/10000000000 : ℝ)^33 ≤ (6888790725803/12500000000000 : ℝ)^25 := by
    have hnat : (6367432909 : ℕ)^33*12500000000000^25 ≤ 6888790725803^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6367432909 10000000000 6888790725803 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166765823/5000000000 : ℝ), (-1971866187/10000000000 : ℝ), (6367432909/10000000000 : ℝ)] ![(6632257800687/20000000000000 : ℝ), (293209629621/2500000000000 : ℝ), (6888790725803/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166765823/5000000000 : ℝ)|^33 ≤ (6632257800687/20000000000000 : ℝ)^25
        have hw : |(2166765823/5000000000 : ℝ)|=(2166765823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1971866187/10000000000 : ℝ)|^33 ≤ (293209629621/2500000000000 : ℝ)^25
        have hw : |(-1971866187/10000000000 : ℝ)|=(1971866187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6367432909/10000000000 : ℝ)|^33 ≤ (6888790725803/12500000000000 : ℝ)^25
        have hw : |(6367432909/10000000000 : ℝ)|=(6367432909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2174230873/5000000000 : ℝ)*x 0 + (1648028559/2500000000 : ℝ)*x 1 + (-322590057/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174230873/5000000000 : ℝ)^33 ≤ (4164022582519/12500000000000 : ℝ)^25 := by
    have hnat : (2174230873 : ℕ)^33*12500000000000^25 ≤ 4164022582519^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174230873 5000000000 4164022582519 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1648028559/2500000000 : ℝ)^33 ≤ (57691607031423/100000000000000 : ℝ)^25 := by
    have hnat : (1648028559 : ℕ)^33*100000000000000^25 ≤ 57691607031423^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648028559 2500000000 57691607031423 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (322590057/2000000000 : ℝ)^33 ≤ (4498106149851/50000000000000 : ℝ)^25 := by
    have hnat : (322590057 : ℕ)^33*50000000000000^25 ≤ 4498106149851^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322590057 2000000000 4498106149851 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174230873/5000000000 : ℝ), (1648028559/2500000000 : ℝ), (-322590057/2000000000 : ℝ)] ![(4164022582519/12500000000000 : ℝ), (57691607031423/100000000000000 : ℝ), (4498106149851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174230873/5000000000 : ℝ)|^33 ≤ (4164022582519/12500000000000 : ℝ)^25
        have hw : |(2174230873/5000000000 : ℝ)|=(2174230873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1648028559/2500000000 : ℝ)|^33 ≤ (57691607031423/100000000000000 : ℝ)^25
        have hw : |(1648028559/2500000000 : ℝ)|=(1648028559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-322590057/2000000000 : ℝ)|^33 ≤ (4498106149851/50000000000000 : ℝ)^25
        have hw : |(-322590057/2000000000 : ℝ)|=(322590057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6066323707/10000000000 : ℝ)*x 0 + (1059465203/2500000000 : ℝ)*x 1 + (2507345589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6066323707/10000000000 : ℝ)^33 ≤ (51696574511097/100000000000000 : ℝ)^25 := by
    have hnat : (6066323707 : ℕ)^33*100000000000000^25 ≤ 51696574511097^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6066323707 10000000000 51696574511097 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1059465203/2500000000 : ℝ)^33 ≤ (4024793862521/12500000000000 : ℝ)^25 := by
    have hnat : (1059465203 : ℕ)^33*12500000000000^25 ≤ 4024793862521^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059465203 2500000000 4024793862521 12500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2507345589/10000000000 : ℝ)^33 ≤ (16105074577993/100000000000000 : ℝ)^25 := by
    have hnat : (2507345589 : ℕ)^33*100000000000000^25 ≤ 16105074577993^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2507345589 10000000000 16105074577993 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6066323707/10000000000 : ℝ), (1059465203/2500000000 : ℝ), (2507345589/10000000000 : ℝ)] ![(51696574511097/100000000000000 : ℝ), (4024793862521/12500000000000 : ℝ), (16105074577993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6066323707/10000000000 : ℝ)|^33 ≤ (51696574511097/100000000000000 : ℝ)^25
        have hw : |(6066323707/10000000000 : ℝ)|=(6066323707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1059465203/2500000000 : ℝ)|^33 ≤ (4024793862521/12500000000000 : ℝ)^25
        have hw : |(1059465203/2500000000 : ℝ)|=(1059465203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2507345589/10000000000 : ℝ)|^33 ≤ (16105074577993/100000000000000 : ℝ)^25
        have hw : |(2507345589/10000000000 : ℝ)|=(2507345589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-208798079/1000000000 : ℝ)*x 0 + (4935243679/10000000000 : ℝ)*x 1 + (2866540399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208798079/1000000000 : ℝ)^33 ≤ (12648498637587/100000000000000 : ℝ)^25 := by
    have hnat : (208798079 : ℕ)^33*100000000000000^25 ≤ 12648498637587^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208798079 1000000000 12648498637587 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4935243679/10000000000 : ℝ)^33 ≤ (39370175726713/100000000000000 : ℝ)^25 := by
    have hnat : (4935243679 : ℕ)^33*100000000000000^25 ≤ 39370175726713^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4935243679 10000000000 39370175726713 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2866540399/5000000000 : ℝ)^33 ≤ (1199533140589/2500000000000 : ℝ)^25 := by
    have hnat : (2866540399 : ℕ)^33*2500000000000^25 ≤ 1199533140589^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2866540399 5000000000 1199533140589 2500000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208798079/1000000000 : ℝ), (4935243679/10000000000 : ℝ), (2866540399/5000000000 : ℝ)] ![(12648498637587/100000000000000 : ℝ), (39370175726713/100000000000000 : ℝ), (1199533140589/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208798079/1000000000 : ℝ)|^33 ≤ (12648498637587/100000000000000 : ℝ)^25
        have hw : |(-208798079/1000000000 : ℝ)|=(208798079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4935243679/10000000000 : ℝ)|^33 ≤ (39370175726713/100000000000000 : ℝ)^25
        have hw : |(4935243679/10000000000 : ℝ)|=(4935243679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2866540399/5000000000 : ℝ)|^33 ≤ (1199533140589/2500000000000 : ℝ)^25
        have hw : |(2866540399/5000000000 : ℝ)|=(2866540399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2076133969/5000000000 : ℝ)*x 0 + (-535997657/2500000000 : ℝ)*x 1 + (6406666921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076133969/5000000000 : ℝ)^33 ≤ (979460012167/3125000000000 : ℝ)^25 := by
    have hnat : (2076133969 : ℕ)^33*3125000000000^25 ≤ 979460012167^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076133969 5000000000 979460012167 3125000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535997657/2500000000 : ℝ)^33 ≤ (13098278039281/100000000000000 : ℝ)^25 := by
    have hnat : (535997657 : ℕ)^33*100000000000000^25 ≤ 13098278039281^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535997657 2500000000 13098278039281 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6406666921/10000000000 : ℝ)^33 ≤ (27779500780807/50000000000000 : ℝ)^25 := by
    have hnat : (6406666921 : ℕ)^33*50000000000000^25 ≤ 27779500780807^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6406666921 10000000000 27779500780807 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2076133969/5000000000 : ℝ), (-535997657/2500000000 : ℝ), (6406666921/10000000000 : ℝ)] ![(979460012167/3125000000000 : ℝ), (13098278039281/100000000000000 : ℝ), (27779500780807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2076133969/5000000000 : ℝ)|^33 ≤ (979460012167/3125000000000 : ℝ)^25
        have hw : |(2076133969/5000000000 : ℝ)|=(2076133969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535997657/2500000000 : ℝ)|^33 ≤ (13098278039281/100000000000000 : ℝ)^25
        have hw : |(-535997657/2500000000 : ℝ)|=(535997657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6406666921/10000000000 : ℝ)|^33 ≤ (27779500780807/50000000000000 : ℝ)^25
        have hw : |(6406666921/10000000000 : ℝ)|=(6406666921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5279003143/10000000000 : ℝ)*x 0 + (1422325753/2500000000 : ℝ)*x 1 + (-1677168403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279003143/10000000000 : ℝ)^33 ≤ (21514860746653/50000000000000 : ℝ)^25 := by
    have hnat : (5279003143 : ℕ)^33*50000000000000^25 ≤ 21514860746653^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279003143 10000000000 21514860746653 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1422325753/2500000000 : ℝ)^33 ≤ (9499657801129/20000000000000 : ℝ)^25 := by
    have hnat : (1422325753 : ℕ)^33*20000000000000^25 ≤ 9499657801129^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422325753 2500000000 9499657801129 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677168403/10000000000 : ℝ)^33 ≤ (9471989477891/100000000000000 : ℝ)^25 := by
    have hnat : (1677168403 : ℕ)^33*100000000000000^25 ≤ 9471989477891^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677168403 10000000000 9471989477891 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279003143/10000000000 : ℝ), (1422325753/2500000000 : ℝ), (-1677168403/10000000000 : ℝ)] ![(21514860746653/50000000000000 : ℝ), (9499657801129/20000000000000 : ℝ), (9471989477891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279003143/10000000000 : ℝ)|^33 ≤ (21514860746653/50000000000000 : ℝ)^25
        have hw : |(5279003143/10000000000 : ℝ)|=(5279003143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1422325753/2500000000 : ℝ)|^33 ≤ (9499657801129/20000000000000 : ℝ)^25
        have hw : |(1422325753/2500000000 : ℝ)|=(1422325753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1677168403/10000000000 : ℝ)|^33 ≤ (9471989477891/100000000000000 : ℝ)^25
        have hw : |(-1677168403/10000000000 : ℝ)|=(1677168403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3493358203/5000000000 : ℝ)*x 0 + (400483479/1250000000 : ℝ)*x 1 + (485905703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3493358203/5000000000 : ℝ)^33 ≤ (62293181523631/100000000000000 : ℝ)^25 := by
    have hnat : (3493358203 : ℕ)^33*100000000000000^25 ≤ 62293181523631^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3493358203 5000000000 62293181523631 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400483479/1250000000 : ℝ)^33 ≤ (5564555394193/25000000000000 : ℝ)^25 := by
    have hnat : (400483479 : ℕ)^33*25000000000000^25 ≤ 5564555394193^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400483479 1250000000 5564555394193 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485905703/2000000000 : ℝ)^33 ≤ (15448596886049/100000000000000 : ℝ)^25 := by
    have hnat : (485905703 : ℕ)^33*100000000000000^25 ≤ 15448596886049^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485905703 2000000000 15448596886049 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3493358203/5000000000 : ℝ), (400483479/1250000000 : ℝ), (485905703/2000000000 : ℝ)] ![(62293181523631/100000000000000 : ℝ), (5564555394193/25000000000000 : ℝ), (15448596886049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3493358203/5000000000 : ℝ)|^33 ≤ (62293181523631/100000000000000 : ℝ)^25
        have hw : |(3493358203/5000000000 : ℝ)|=(3493358203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400483479/1250000000 : ℝ)|^33 ≤ (5564555394193/25000000000000 : ℝ)^25
        have hw : |(400483479/1250000000 : ℝ)|=(400483479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(485905703/2000000000 : ℝ)|^33 ≤ (15448596886049/100000000000000 : ℝ)^25
        have hw : |(485905703/2000000000 : ℝ)|=(485905703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-63107453/312500000 : ℝ)*x 0 + (672475133/1250000000 : ℝ)*x 1 + (1069701661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63107453/312500000 : ℝ)^33 ≤ (12103317685313/100000000000000 : ℝ)^25 := by
    have hnat : (63107453 : ℕ)^33*100000000000000^25 ≤ 12103317685313^25*312500000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63107453 312500000 12103317685313 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672475133/1250000000 : ℝ)^33 ≤ (4411755194977/10000000000000 : ℝ)^25 := by
    have hnat : (672475133 : ℕ)^33*10000000000000^25 ≤ 4411755194977^25*1250000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672475133 1250000000 4411755194977 10000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1069701661/2000000000 : ℝ)^33 ≤ (21889565178009/50000000000000 : ℝ)^25 := by
    have hnat : (1069701661 : ℕ)^33*50000000000000^25 ≤ 21889565178009^25*2000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069701661 2000000000 21889565178009 50000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63107453/312500000 : ℝ), (672475133/1250000000 : ℝ), (1069701661/2000000000 : ℝ)] ![(12103317685313/100000000000000 : ℝ), (4411755194977/10000000000000 : ℝ), (21889565178009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63107453/312500000 : ℝ)|^33 ≤ (12103317685313/100000000000000 : ℝ)^25
        have hw : |(-63107453/312500000 : ℝ)|=(63107453/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(672475133/1250000000 : ℝ)|^33 ≤ (4411755194977/10000000000000 : ℝ)^25
        have hw : |(672475133/1250000000 : ℝ)|=(672475133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1069701661/2000000000 : ℝ)|^33 ≤ (21889565178009/50000000000000 : ℝ)^25
        have hw : |(1069701661/2000000000 : ℝ)|=(1069701661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1333153961/2500000000 : ℝ)*x 0 + (-86913107/500000000 : ℝ)*x 1 + (2797528439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1333153961/2500000000 : ℝ)^33 ≤ (43607500483371/100000000000000 : ℝ)^25 := by
    have hnat : (1333153961 : ℕ)^33*100000000000000^25 ≤ 43607500483371^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333153961 2500000000 43607500483371 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86913107/500000000 : ℝ)^33 ≤ (2482516630993/25000000000000 : ℝ)^25 := by
    have hnat : (86913107 : ℕ)^33*25000000000000^25 ≤ 2482516630993^25*500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86913107 500000000 2482516630993 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2797528439/5000000000 : ℝ)^33 ≤ (11615608245763/25000000000000 : ℝ)^25 := by
    have hnat : (2797528439 : ℕ)^33*25000000000000^25 ≤ 11615608245763^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2797528439 5000000000 11615608245763 25000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1333153961/2500000000 : ℝ), (-86913107/500000000 : ℝ), (2797528439/5000000000 : ℝ)] ![(43607500483371/100000000000000 : ℝ), (2482516630993/25000000000000 : ℝ), (11615608245763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1333153961/2500000000 : ℝ)|^33 ≤ (43607500483371/100000000000000 : ℝ)^25
        have hw : |(1333153961/2500000000 : ℝ)|=(1333153961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86913107/500000000 : ℝ)|^33 ≤ (2482516630993/25000000000000 : ℝ)^25
        have hw : |(-86913107/500000000 : ℝ)|=(86913107/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2797528439/5000000000 : ℝ)|^33 ≤ (11615608245763/25000000000000 : ℝ)^25
        have hw : |(2797528439/5000000000 : ℝ)|=(2797528439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1033655451/2500000000 : ℝ)*x 0 + (651839001/1000000000 : ℝ)*x 1 + (-1002645551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033655451/2500000000 : ℝ)^33 ≤ (31167017406923/100000000000000 : ℝ)^25 := by
    have hnat : (1033655451 : ℕ)^33*100000000000000^25 ≤ 31167017406923^25*2500000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033655451 2500000000 31167017406923 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651839001/1000000000 : ℝ)^33 ≤ (11368292696803/20000000000000 : ℝ)^25 := by
    have hnat : (651839001 : ℕ)^33*20000000000000^25 ≤ 11368292696803^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651839001 1000000000 11368292696803 20000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1002645551/5000000000 : ℝ)^33 ≤ (11991519093571/100000000000000 : ℝ)^25 := by
    have hnat : (1002645551 : ℕ)^33*100000000000000^25 ≤ 11991519093571^25*5000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002645551 5000000000 11991519093571 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033655451/2500000000 : ℝ), (651839001/1000000000 : ℝ), (-1002645551/5000000000 : ℝ)] ![(31167017406923/100000000000000 : ℝ), (11368292696803/20000000000000 : ℝ), (11991519093571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033655451/2500000000 : ℝ)|^33 ≤ (31167017406923/100000000000000 : ℝ)^25
        have hw : |(1033655451/2500000000 : ℝ)|=(1033655451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651839001/1000000000 : ℝ)|^33 ≤ (11368292696803/20000000000000 : ℝ)^25
        have hw : |(651839001/1000000000 : ℝ)|=(651839001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1002645551/5000000000 : ℝ)|^33 ≤ (11991519093571/100000000000000 : ℝ)^25
        have hw : |(-1002645551/5000000000 : ℝ)|=(1002645551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302053_s7_s7_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7051326699/10000000000 : ℝ)*x 0 + (2787463379/10000000000 : ℝ)*x 1 + (277631687/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7051326699/10000000000 : ℝ)^33 ≤ (63054705904801/100000000000000 : ℝ)^25 := by
    have hnat : (7051326699 : ℕ)^33*100000000000000^25 ≤ 63054705904801^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7051326699 10000000000 63054705904801 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787463379/10000000000 : ℝ)^33 ≤ (18521497825901/100000000000000 : ℝ)^25 := by
    have hnat : (2787463379 : ℕ)^33*100000000000000^25 ≤ 18521497825901^25*10000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787463379 10000000000 18521497825901 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (277631687/1000000000 : ℝ)^33 ≤ (18423796258667/100000000000000 : ℝ)^25 := by
    have hnat : (277631687 : ℕ)^33*100000000000000^25 ≤ 18423796258667^25*1000000000^33 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277631687 1000000000 18423796258667 100000000000000 33 25 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (33/8 : ℝ)) 33 25 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7051326699/10000000000 : ℝ), (2787463379/10000000000 : ℝ), (277631687/1000000000 : ℝ)] ![(63054705904801/100000000000000 : ℝ), (18521497825901/100000000000000 : ℝ), (18423796258667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7051326699/10000000000 : ℝ)|^33 ≤ (63054705904801/100000000000000 : ℝ)^25
        have hw : |(7051326699/10000000000 : ℝ)|=(7051326699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2787463379/10000000000 : ℝ)|^33 ≤ (18521497825901/100000000000000 : ℝ)^25
        have hw : |(2787463379/10000000000 : ℝ)|=(2787463379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(277631687/1000000000 : ℝ)|^33 ≤ (18423796258667/100000000000000 : ℝ)^25
        have hw : |(277631687/1000000000 : ℝ)|=(277631687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302053_s7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev6 : (0 : ℝ) ≤ ((5027/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45991/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8919/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8919/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12911/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12911/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29591/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29591/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28577/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28577/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (5027/12500 : ℝ) ^ (65/16 : ℝ) ≤ (494197352017017201/20000000000000000000 : ℝ) := by
    have hpowers : (5027/12500 : ℝ)^65 ≤ (494197352017017201/20000000000000000000 : ℝ)^16 := by
      have hnat : (5027 : ℕ)^65*20000000000000000000^16 ≤ 494197352017017201^16*12500^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5027 12500 494197352017017201 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5027/12500 : ℝ)) (X := (494197352017017201/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner0a : (20494197352017017201/20000000000000000000 : ℝ) ≤ (10060265835968313/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (20494197352017017201/20000000000000000000 : ℝ)^16 ≤ (10060265835968313/10000000000000000 : ℝ)^65 := by
      have hnat : (20494197352017017201 : ℕ)^16*10000000000000000^65 ≤ 10060265835968313^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20494197352017017201 20000000000000000000 10060265835968313 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060265835968313/10000000000000000 : ℝ)) (X := (20494197352017017201/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner0b : (10494197352017017201/10000000000000000000 : ℝ) ≤ (2023889179570417/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (10494197352017017201/10000000000000000000 : ℝ)^16 ≤ (2023889179570417/2000000000000000 : ℝ)^65 := by
      have hnat : (10494197352017017201 : ℕ)^16*2000000000000000^65 ≤ 2023889179570417^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10494197352017017201 10000000000000000000 2023889179570417 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2023889179570417/2000000000000000 : ℝ)) (X := (10494197352017017201/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(60265835968313/4021600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14795015470943/1005400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (5027/12500 : ℝ)) (alpha := (60265835968313/4021600000000000 : ℝ)) (beta := (14795015470943/1005400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5027/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(60265835968313/4021600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14795015470943/1005400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (45991/100000 : ℝ) ^ (65/16 : ℝ) ≤ (2130975558101938507/50000000000000000000 : ℝ) := by
    have hpowers : (45991/100000 : ℝ)^65 ≤ (2130975558101938507/50000000000000000000 : ℝ)^16 := by
      have hnat : (45991 : ℕ)^65*50000000000000000000^16 ≤ 2130975558101938507^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45991 100000 2130975558101938507 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45991/100000 : ℝ)) (X := (2130975558101938507/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner1a : (52130975558101938507/50000000000000000000 : ℝ) ≤ (2020653013301369/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (52130975558101938507/50000000000000000000 : ℝ)^16 ≤ (2020653013301369/2000000000000000 : ℝ)^65 := by
      have hnat : (52130975558101938507 : ℕ)^16*2000000000000000^65 ≤ 2020653013301369^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52130975558101938507 50000000000000000000 2020653013301369 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2020653013301369/2000000000000000 : ℝ)) (X := (52130975558101938507/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner1b : (27130975558101938507/25000000000000000000 : ℝ) ≤ (2040679068390423/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (27130975558101938507/25000000000000000000 : ℝ)^16 ≤ (2040679068390423/2000000000000000 : ℝ)^65 := by
      have hnat : (27130975558101938507 : ℕ)^16*2000000000000000^65 ≤ 2040679068390423^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27130975558101938507 25000000000000000000 2040679068390423 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2040679068390423/2000000000000000 : ℝ)) (X := (27130975558101938507/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(20653013301369/919820000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(10013027544527/459910000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (45991/100000 : ℝ)) (alpha := (20653013301369/919820000000000 : ℝ)) (beta := (10013027544527/459910000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (45991/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(20653013301369/919820000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(10013027544527/459910000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (8919/20000 : ℝ) ^ (65/16 : ℝ) ≤ (940080549750107533/25000000000000000000 : ℝ) := by
    have hpowers : (8919/20000 : ℝ)^65 ≤ (940080549750107533/25000000000000000000 : ℝ)^16 := by
      have hnat : (8919 : ℕ)^65*25000000000000000000^16 ≤ 940080549750107533^16*20000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8919 20000 940080549750107533 25000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8919/20000 : ℝ)) (X := (940080549750107533/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner2a : (25940080549750107533/25000000000000000000 : ℝ) ≤ (5045638982636117/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (25940080549750107533/25000000000000000000 : ℝ)^16 ≤ (5045638982636117/5000000000000000 : ℝ)^65 := by
      have hnat : (25940080549750107533 : ℕ)^16*5000000000000000^65 ≤ 5045638982636117^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25940080549750107533 25000000000000000000 5045638982636117 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5045638982636117/5000000000000000 : ℝ)) (X := (25940080549750107533/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner2b : (13440080549750107533/12500000000000000000 : ℝ) ≤ (5090047632170261/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (13440080549750107533/12500000000000000000 : ℝ)^16 ≤ (5090047632170261/5000000000000000 : ℝ)^65 := by
      have hnat : (13440080549750107533 : ℕ)^16*5000000000000000^65 ≤ 5090047632170261^65*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13440080549750107533 12500000000000000000 5090047632170261 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5090047632170261/5000000000000000 : ℝ)) (X := (13440080549750107533/12500000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(15212994212039/743250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(231295049657/11613281250000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (8919/20000 : ℝ)) (alpha := (15212994212039/743250000000000 : ℝ)) (beta := (231295049657/11613281250000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8919/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(15212994212039/743250000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(231295049657/11613281250000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-13994203/50000000 : ℝ)*X 0 0+(1263571493/2500000000 : ℝ)*X 0 1+(5065743721/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((1131603523/2500000000 : ℝ)*X 1 0+(-581732197/2500000000 : ℝ)*X 1 1+(5940271909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((22706449/50000000 : ℝ)*X 2 0+(2966806397/5000000000 : ℝ)*X 2 1+(-2317493861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((1242357959/2000000000 : ℝ)*X 0 0+(1664377969/5000000000 : ℝ)*X 0 1+(3311472647/10000000000 : ℝ)*X 0 2+(1242357959/2000000000 : ℝ)*X 1 0+(1664377969/5000000000 : ℝ)*X 1 1+(3311472647/10000000000 : ℝ)*X 1 2+(1242357959/2000000000 : ℝ)*X 2 0+(1664377969/5000000000 : ℝ)*X 2 1+(3311472647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-273573789/1000000000 : ℝ)*X 0 0+(2170601083/5000000000 : ℝ)*X 0 1+(1449324741/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((2166765823/5000000000 : ℝ)*X 1 0+(-1971866187/10000000000 : ℝ)*X 1 1+(6367432909/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((2174230873/5000000000 : ℝ)*X 2 0+(1648028559/2500000000 : ℝ)*X 2 1+(-322590057/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((6066323707/10000000000 : ℝ)*X 0 0+(1059465203/2500000000 : ℝ)*X 0 1+(2507345589/10000000000 : ℝ)*X 0 2+(6066323707/10000000000 : ℝ)*X 1 0+(1059465203/2500000000 : ℝ)*X 1 1+(2507345589/10000000000 : ℝ)*X 1 2+(6066323707/10000000000 : ℝ)*X 2 0+(1059465203/2500000000 : ℝ)*X 2 1+(2507345589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-208798079/1000000000 : ℝ)*X 0 0+(4935243679/10000000000 : ℝ)*X 0 1+(2866540399/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((2076133969/5000000000 : ℝ)*X 1 0+(-535997657/2500000000 : ℝ)*X 1 1+(6406666921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((5279003143/10000000000 : ℝ)*X 2 0+(1422325753/2500000000 : ℝ)*X 2 1+(-1677168403/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((3493358203/5000000000 : ℝ)*X 0 0+(400483479/1250000000 : ℝ)*X 0 1+(485905703/2000000000 : ℝ)*X 0 2+(3493358203/5000000000 : ℝ)*X 1 0+(400483479/1250000000 : ℝ)*X 1 1+(485905703/2000000000 : ℝ)*X 1 2+(3493358203/5000000000 : ℝ)*X 2 0+(400483479/1250000000 : ℝ)*X 2 1+(485905703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-63107453/312500000 : ℝ)*X 0 0+(672475133/1250000000 : ℝ)*X 0 1+(1069701661/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((1333153961/2500000000 : ℝ)*X 1 0+(-86913107/500000000 : ℝ)*X 1 1+(2797528439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((1033655451/2500000000 : ℝ)*X 2 0+(651839001/1000000000 : ℝ)*X 2 1+(-1002645551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((7051326699/10000000000 : ℝ)*X 0 0+(2787463379/10000000000 : ℝ)*X 0 1+(277631687/1000000000 : ℝ)*X 0 2+(7051326699/10000000000 : ℝ)*X 1 0+(2787463379/10000000000 : ℝ)*X 1 1+(277631687/1000000000 : ℝ)*X 1 2+(7051326699/10000000000 : ℝ)*X 2 0+(2787463379/10000000000 : ℝ)*X 2 1+(277631687/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302053_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((12911/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12911/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2023026615729418314177/247750000000000000000000000 : ℝ) := by norm_num
    linear_combination (270028829387/1000000000000 : ℝ)*(base49) + (203914983879/250000000000 : ℝ)*(base59) + (960001/1000000000000 : ℝ)*(base60) + (6867510813063/1000000000000 : ℝ)*(major_s7_0) + (6867510813063/1000000000000 : ℝ)*(major_s7_1) + (6867510813063/1000000000000 : ℝ)*(major_s7_2) + (56118699/1000000000000 : ℝ)*(sp_s7_0) + (15017853/1000000000000 : ℝ)*(sp_s7_6) + (9131147800593/1000000000000 : ℝ)*(sp_s7_7) + (9131086298311/1000000000000 : ℝ)*(sp_s7_8) + (9131050712747/1000000000000 : ℝ)*(sp_s7_9) + (2301899983553/500000000000 : ℝ)*(sp_s7_13) + (117620981/1000000000000 : ℝ)*(sp_s7_15) + (9575409/62500000000 : ℝ)*(sp_s7_23) + (2301907492479/500000000000 : ℝ)*(f.failure) + (2282800979823/250000000000 : ℝ)*(f.sum) + (3415847630615873667/22788540500000000000000000000000 : ℝ)*base62 + (3644037421327/61937500000000000000000000 : ℝ)*base64 + (10450504350403/459910000000000000000000000 : ℝ)*base67 + (9510317014511/61937500000000000000000000 : ℝ)*base69 + (7738612557797615611/19927028000000000000000000000000 : ℝ)*base70 + (185544708624909/1005400000000000000000000000 : ℝ)*base73 + (435556745970117/919820000000000000000000000 : ℝ)*base75 + (3080751312969839/4021600000000000000000000000 : ℝ)*base77 + (165871698289706381/382143400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (5757/5000000000000000 : ℝ)*base86 + (5757/5000000000000000 : ℝ)*base88 + (5757/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29591/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29591/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (78771465722598071838317167/5697135125000000000000000000000 : ℝ) := by norm_num
    linear_combination (852721/1000000000000 : ℝ)*(base39) + (179512813219/500000000000 : ℝ)*(base49) + (221069372013/500000000000 : ℝ)*(base59) + (6764629096681/1000000000000 : ℝ)*(major_s7_0) + (6764629096681/1000000000000 : ℝ)*(major_s7_1) + (6764629096681/1000000000000 : ℝ)*(major_s7_2) + (21805539/1000000000000 : ℝ)*(sp_s7_1) + (3796073/125000000000 : ℝ)*(sp_s7_2) + (17171351/200000000000 : ℝ)*(sp_s7_7) + (8994322184643/1000000000000 : ℝ)*(sp_s7_14) + (8994386235859/1000000000000 : ℝ)*(sp_s7_15) + (8994377672813/1000000000000 : ℝ)*(sp_s7_16) + (2267351963103/500000000000 : ℝ)*(sp_s7_20) + (3540423/25000000000 : ℝ)*(sp_s7_27) + (2267422771563/500000000000 : ℝ)*(f.failure) + (4497204020699/500000000000 : ℝ)*(f.sum) + (11945189274145020463/68365621500000000000000000000000 : ℝ)*base63 + (366901830359363/743250000000000000000000000 : ℝ)*base64 + (47253395896071/459910000000000000000000000 : ℝ)*base66 + (210715027551391/743250000000000000000000000 : ℝ)*base68 + (2071468399187693071/59781084000000000000000000000000 : ℝ)*base70 + (584604792193017/1005400000000000000000000000 : ℝ)*base72 + (169479006145439/919820000000000000000000000 : ℝ)*base75 + (679509578097313/4021600000000000000000000000 : ℝ)*base77 + (5212756947192633/382143400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (271/5000000000000000 : ℝ)*base87 + (271/5000000000000000 : ℝ)*base89 + (271/5000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28577/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28577/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34084286843865699219522081/2490878500000000000000000000000 : ℝ) := by norm_num
    linear_combination (59806312713/250000000000 : ℝ)*(base40) + (1729993253/8000000000 : ℝ)*(base49) + (15096072961/31250000000 : ℝ)*(base59) + (1550170188553/250000000000 : ℝ)*(major_s7_0) + (1550170188553/250000000000 : ℝ)*(major_s7_1) + (1550170188553/250000000000 : ℝ)*(major_s7_2) + (7793957/200000000000 : ℝ)*(sp_s7_0) + (61543283/1000000000000 : ℝ)*(sp_s7_2) + (46596927/1000000000000 : ℝ)*(sp_s7_9) + (42251681/200000000000 : ℝ)*(sp_s7_20) + (2061132478499/250000000000 : ℝ)*(sp_s7_21) + (8244568883781/1000000000000 : ℝ)*(sp_s7_22) + (824446074357/100000000000 : ℝ)*(sp_s7_23) + (4156576805021/1000000000000 : ℝ)*(sp_s7_27) + (2078394031713/500000000000 : ℝ)*(f.failure) + (8244568883781/1000000000000 : ℝ)*(f.sum) + (7751466392424738337/34182810750000000000000000000000 : ℝ)*base62 + (71113792027151/743250000000000000000000000 : ℝ)*base64 + (45628725845617/229955000000000000000000000 : ℝ)*base66 + (284254544982457/743250000000000000000000000 : ℝ)*base68 + (5607444585810245923/14945271000000000000000000000000 : ℝ)*base70 + (26460802567237/125675000000000000000000000 : ℝ)*base73 + (36950412679093/459910000000000000000000000 : ℝ)*base75 + (50068420729131/1005400000000000000000000000 : ℝ)*base76 + (9237590591067587/47767925000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (2821/5000000000000000 : ℝ)*base87 + (2821/5000000000000000 : ℝ)*base89 + (2821/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (33/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev6 : (0 : ℝ) ≤ ((5027/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5027/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45991/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(45991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8919/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8919/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12911/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12911/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29591/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29591/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28577/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28577/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302053_s7 p hpa hpb X hX hprev6

#print axioms solution
