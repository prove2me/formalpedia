-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304080_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:49:26.666629+00:00
-- url     : https://prove2.me/submissions/636dd209-0e92-4a1b-a198-85d08a1943a7

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
theorem collision_support_c304080_s2_s2_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3375633687/10000000000 : ℝ)*x 0 + (5675962157/10000000000 : ℝ)*x 1 + (3868700419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3375633687/10000000000 : ℝ)^133 ≤ (23928932905843/100000000000000 : ℝ)^101 := by
    have hnat : (3375633687 : ℕ)^133*100000000000000^101 ≤ 23928932905843^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3375633687 10000000000 23928932905843 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675962157/10000000000 : ℝ)^133 ≤ (23718182892063/50000000000000 : ℝ)^101 := by
    have hnat : (5675962157 : ℕ)^133*50000000000000^101 ≤ 23718182892063^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675962157 10000000000 23718182892063 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3868700419/10000000000 : ℝ)^133 ≤ (5726940259147/20000000000000 : ℝ)^101 := by
    have hnat : (3868700419 : ℕ)^133*20000000000000^101 ≤ 5726940259147^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3868700419 10000000000 5726940259147 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3375633687/10000000000 : ℝ), (5675962157/10000000000 : ℝ), (3868700419/10000000000 : ℝ)] ![(23928932905843/100000000000000 : ℝ), (23718182892063/50000000000000 : ℝ), (5726940259147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3375633687/10000000000 : ℝ)|^133 ≤ (23928932905843/100000000000000 : ℝ)^101
        have hw : |(-3375633687/10000000000 : ℝ)|=(3375633687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675962157/10000000000 : ℝ)|^133 ≤ (23718182892063/50000000000000 : ℝ)^101
        have hw : |(5675962157/10000000000 : ℝ)|=(5675962157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3868700419/10000000000 : ℝ)|^133 ≤ (5726940259147/20000000000000 : ℝ)^101
        have hw : |(3868700419/10000000000 : ℝ)|=(3868700419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (612019787/2000000000 : ℝ)*x 0 + (1249218653/2000000000 : ℝ)*x 1 + (-701415327/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612019787/2000000000 : ℝ)^133 ≤ (2628513327509/12500000000000 : ℝ)^101 := by
    have hnat : (612019787 : ℕ)^133*12500000000000^101 ≤ 2628513327509^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612019787 2000000000 2628513327509 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249218653/2000000000 : ℝ)^133 ≤ (26904241637811/50000000000000 : ℝ)^101 := by
    have hnat : (1249218653 : ℕ)^133*50000000000000^101 ≤ 26904241637811^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249218653 2000000000 26904241637811 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (701415327/2000000000 : ℝ)^133 ≤ (5032682019283/20000000000000 : ℝ)^101 := by
    have hnat : (701415327 : ℕ)^133*20000000000000^101 ≤ 5032682019283^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701415327 2000000000 5032682019283 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(612019787/2000000000 : ℝ), (1249218653/2000000000 : ℝ), (-701415327/2000000000 : ℝ)] ![(2628513327509/12500000000000 : ℝ), (26904241637811/50000000000000 : ℝ), (5032682019283/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(612019787/2000000000 : ℝ)|^133 ≤ (2628513327509/12500000000000 : ℝ)^101
        have hw : |(612019787/2000000000 : ℝ)|=(612019787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1249218653/2000000000 : ℝ)|^133 ≤ (26904241637811/50000000000000 : ℝ)^101
        have hw : |(1249218653/2000000000 : ℝ)|=(1249218653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-701415327/2000000000 : ℝ)|^133 ≤ (5032682019283/20000000000000 : ℝ)^101
        have hw : |(-701415327/2000000000 : ℝ)|=(701415327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4290342739/10000000000 : ℝ)*x 0 + (4910063971/10000000000 : ℝ)*x 1 + (1901338159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4290342739/10000000000 : ℝ)^133 ≤ (32813594398149/100000000000000 : ℝ)^101 := by
    have hnat : (4290342739 : ℕ)^133*100000000000000^101 ≤ 32813594398149^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290342739 10000000000 32813594398149 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4910063971/10000000000 : ℝ)^133 ≤ (9798368781051/25000000000000 : ℝ)^101 := by
    have hnat : (4910063971 : ℕ)^133*25000000000000^101 ≤ 9798368781051^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4910063971 10000000000 9798368781051 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1901338159/5000000000 : ℝ)^133 ≤ (5598586091129/20000000000000 : ℝ)^101 := by
    have hnat : (1901338159 : ℕ)^133*20000000000000^101 ≤ 5598586091129^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901338159 5000000000 5598586091129 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4290342739/10000000000 : ℝ), (4910063971/10000000000 : ℝ), (1901338159/5000000000 : ℝ)] ![(32813594398149/100000000000000 : ℝ), (9798368781051/25000000000000 : ℝ), (5598586091129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4290342739/10000000000 : ℝ)|^133 ≤ (32813594398149/100000000000000 : ℝ)^101
        have hw : |(4290342739/10000000000 : ℝ)|=(4290342739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4910063971/10000000000 : ℝ)|^133 ≤ (9798368781051/25000000000000 : ℝ)^101
        have hw : |(4910063971/10000000000 : ℝ)|=(4910063971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1901338159/5000000000 : ℝ)|^133 ≤ (5598586091129/20000000000000 : ℝ)^101
        have hw : |(1901338159/5000000000 : ℝ)|=(1901338159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-420384689/1250000000 : ℝ)*x 0 + (8667283/15625000 : ℝ)*x 1 + (80495007/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420384689/1250000000 : ℝ)^133 ≤ (5952948615813/25000000000000 : ℝ)^101 := by
    have hnat : (420384689 : ℕ)^133*25000000000000^101 ≤ 5952948615813^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420384689 1250000000 5952948615813 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8667283/15625000 : ℝ)^133 ≤ (23011450221453/50000000000000 : ℝ)^101 := by
    have hnat : (8667283 : ℕ)^133*50000000000000^101 ≤ 23011450221453^101*15625000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8667283 15625000 23011450221453 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80495007/200000000 : ℝ)^133 ≤ (1206612203459/4000000000000 : ℝ)^101 := by
    have hnat : (80495007 : ℕ)^133*4000000000000^101 ≤ 1206612203459^101*200000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80495007 200000000 1206612203459 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420384689/1250000000 : ℝ), (8667283/15625000 : ℝ), (80495007/200000000 : ℝ)] ![(5952948615813/25000000000000 : ℝ), (23011450221453/50000000000000 : ℝ), (1206612203459/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420384689/1250000000 : ℝ)|^133 ≤ (5952948615813/25000000000000 : ℝ)^101
        have hw : |(-420384689/1250000000 : ℝ)|=(420384689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8667283/15625000 : ℝ)|^133 ≤ (23011450221453/50000000000000 : ℝ)^101
        have hw : |(8667283/15625000 : ℝ)|=(8667283/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80495007/200000000 : ℝ)|^133 ≤ (1206612203459/4000000000000 : ℝ)^101
        have hw : |(80495007/200000000 : ℝ)|=(80495007/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5740551237/10000000000 : ℝ)*x 0 + (2028743/250000000 : ℝ)*x 1 + (151427759/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5740551237/10000000000 : ℝ)^133 ≤ (12037116639069/25000000000000 : ℝ)^101 := by
    have hnat : (5740551237 : ℕ)^133*25000000000000^101 ≤ 12037116639069^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5740551237 10000000000 12037116639069 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2028743/250000000 : ℝ)^133 ≤ (7062247057/4000000000000 : ℝ)^101 := by
    have hnat : (2028743 : ℕ)^133*4000000000000^101 ≤ 7062247057^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028743 250000000 7062247057 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151427759/250000000 : ℝ)^133 ≤ (25837488628449/50000000000000 : ℝ)^101 := by
    have hnat : (151427759 : ℕ)^133*50000000000000^101 ≤ 25837488628449^101*250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151427759 250000000 25837488628449 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5740551237/10000000000 : ℝ), (2028743/250000000 : ℝ), (151427759/250000000 : ℝ)] ![(12037116639069/25000000000000 : ℝ), (7062247057/4000000000000 : ℝ), (25837488628449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5740551237/10000000000 : ℝ)|^133 ≤ (12037116639069/25000000000000 : ℝ)^101
        have hw : |(5740551237/10000000000 : ℝ)|=(5740551237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2028743/250000000 : ℝ)|^133 ≤ (7062247057/4000000000000 : ℝ)^101
        have hw : |(2028743/250000000 : ℝ)|=(2028743/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151427759/250000000 : ℝ)|^133 ≤ (25837488628449/50000000000000 : ℝ)^101
        have hw : |(151427759/250000000 : ℝ)|=(151427759/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1272214717/5000000000 : ℝ)*x 0 + (7008187871/10000000000 : ℝ)*x 1 + (-609007269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1272214717/5000000000 : ℝ)^133 ≤ (659663738283/4000000000000 : ℝ)^101 := by
    have hnat : (1272214717 : ℕ)^133*4000000000000^101 ≤ 659663738283^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272214717 5000000000 659663738283 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7008187871/10000000000 : ℝ)^133 ≤ (31308246555981/50000000000000 : ℝ)^101 := by
    have hnat : (7008187871 : ℕ)^133*50000000000000^101 ≤ 31308246555981^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7008187871 10000000000 31308246555981 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609007269/2000000000 : ℝ)^133 ≤ (20891913407271/100000000000000 : ℝ)^101 := by
    have hnat : (609007269 : ℕ)^133*100000000000000^101 ≤ 20891913407271^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609007269 2000000000 20891913407271 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1272214717/5000000000 : ℝ), (7008187871/10000000000 : ℝ), (-609007269/2000000000 : ℝ)] ![(659663738283/4000000000000 : ℝ), (31308246555981/50000000000000 : ℝ), (20891913407271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1272214717/5000000000 : ℝ)|^133 ≤ (659663738283/4000000000000 : ℝ)^101
        have hw : |(1272214717/5000000000 : ℝ)|=(1272214717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7008187871/10000000000 : ℝ)|^133 ≤ (31308246555981/50000000000000 : ℝ)^101
        have hw : |(7008187871/10000000000 : ℝ)|=(7008187871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-609007269/2000000000 : ℝ)|^133 ≤ (20891913407271/100000000000000 : ℝ)^101
        have hw : |(-609007269/2000000000 : ℝ)|=(609007269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_12 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (947934237/2500000000 : ℝ)*x 0 + (2596000753/5000000000 : ℝ)*x 1 + (4000829921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947934237/2500000000 : ℝ)^133 ≤ (27886935916547/100000000000000 : ℝ)^101 := by
    have hnat : (947934237 : ℕ)^133*100000000000000^101 ≤ 27886935916547^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947934237 2500000000 27886935916547 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2596000753/5000000000 : ℝ)^133 ≤ (4218362119363/10000000000000 : ℝ)^101 := by
    have hnat : (2596000753 : ℕ)^133*10000000000000^101 ≤ 4218362119363^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596000753 5000000000 4218362119363 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4000829921/10000000000 : ℝ)^133 ≤ (3741180359619/12500000000000 : ℝ)^101 := by
    have hnat : (4000829921 : ℕ)^133*12500000000000^101 ≤ 3741180359619^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000829921 10000000000 3741180359619 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(947934237/2500000000 : ℝ), (2596000753/5000000000 : ℝ), (4000829921/10000000000 : ℝ)] ![(27886935916547/100000000000000 : ℝ), (4218362119363/10000000000000 : ℝ), (3741180359619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(947934237/2500000000 : ℝ)|^133 ≤ (27886935916547/100000000000000 : ℝ)^101
        have hw : |(947934237/2500000000 : ℝ)|=(947934237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2596000753/5000000000 : ℝ)|^133 ≤ (4218362119363/10000000000000 : ℝ)^101
        have hw : |(2596000753/5000000000 : ℝ)|=(2596000753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4000829921/10000000000 : ℝ)|^133 ≤ (3741180359619/12500000000000 : ℝ)^101
        have hw : |(4000829921/10000000000 : ℝ)|=(4000829921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-851102763/2000000000 : ℝ)*x 0 + (561076727/1000000000 : ℝ)*x 1 + (3036690827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851102763/2000000000 : ℝ)^133 ≤ (1623163425333/5000000000000 : ℝ)^101 := by
    have hnat : (851102763 : ℕ)^133*5000000000000^101 ≤ 1623163425333^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851102763 2000000000 1623163425333 5000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561076727/1000000000 : ℝ)^133 ≤ (5840023120687/12500000000000 : ℝ)^101 := by
    have hnat : (561076727 : ℕ)^133*12500000000000^101 ≤ 5840023120687^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561076727 1000000000 5840023120687 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3036690827/10000000000 : ℝ)^133 ≤ (20816546518839/100000000000000 : ℝ)^101 := by
    have hnat : (3036690827 : ℕ)^133*100000000000000^101 ≤ 20816546518839^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3036690827 10000000000 20816546518839 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-851102763/2000000000 : ℝ), (561076727/1000000000 : ℝ), (3036690827/10000000000 : ℝ)] ![(1623163425333/5000000000000 : ℝ), (5840023120687/12500000000000 : ℝ), (20816546518839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-851102763/2000000000 : ℝ)|^133 ≤ (1623163425333/5000000000000 : ℝ)^101
        have hw : |(-851102763/2000000000 : ℝ)|=(851102763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561076727/1000000000 : ℝ)|^133 ≤ (5840023120687/12500000000000 : ℝ)^101
        have hw : |(561076727/1000000000 : ℝ)|=(561076727/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3036690827/10000000000 : ℝ)|^133 ≤ (20816546518839/100000000000000 : ℝ)^101
        have hw : |(3036690827/10000000000 : ℝ)|=(3036690827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5735673639/10000000000 : ℝ)*x 0 + (-264216223/10000000000 : ℝ)*x 1 + (6003167221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5735673639/10000000000 : ℝ)^133 ≤ (48094601556593/100000000000000 : ℝ)^101 := by
    have hnat : (5735673639 : ℕ)^133*100000000000000^101 ≤ 48094601556593^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5735673639 10000000000 48094601556593 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264216223/10000000000 : ℝ)^133 ≤ (208894138787/25000000000000 : ℝ)^101 := by
    have hnat : (264216223 : ℕ)^133*25000000000000^101 ≤ 208894138787^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264216223 10000000000 208894138787 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6003167221/10000000000 : ℝ)^133 ≤ (10213964375043/20000000000000 : ℝ)^101 := by
    have hnat : (6003167221 : ℕ)^133*20000000000000^101 ≤ 10213964375043^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003167221 10000000000 10213964375043 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5735673639/10000000000 : ℝ), (-264216223/10000000000 : ℝ), (6003167221/10000000000 : ℝ)] ![(48094601556593/100000000000000 : ℝ), (208894138787/25000000000000 : ℝ), (10213964375043/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5735673639/10000000000 : ℝ)|^133 ≤ (48094601556593/100000000000000 : ℝ)^101
        have hw : |(5735673639/10000000000 : ℝ)|=(5735673639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264216223/10000000000 : ℝ)|^133 ≤ (208894138787/25000000000000 : ℝ)^101
        have hw : |(-264216223/10000000000 : ℝ)|=(264216223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6003167221/10000000000 : ℝ)|^133 ≤ (10213964375043/20000000000000 : ℝ)^101
        have hw : |(6003167221/10000000000 : ℝ)|=(6003167221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (142057069/625000000 : ℝ)*x 0 + (6106998503/10000000000 : ℝ)*x 1 + (-436321161/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (142057069/625000000 : ℝ)^133 ≤ (7107189457449/50000000000000 : ℝ)^101 := by
    have hnat : (142057069 : ℕ)^133*50000000000000^101 ≤ 7107189457449^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142057069 625000000 7107189457449 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6106998503/10000000000 : ℝ)^133 ≤ (52236164300771/100000000000000 : ℝ)^101 := by
    have hnat : (6106998503 : ℕ)^133*100000000000000^101 ≤ 52236164300771^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6106998503 10000000000 52236164300771 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436321161/1000000000 : ℝ)^133 ≤ (33549456764449/100000000000000 : ℝ)^101 := by
    have hnat : (436321161 : ℕ)^133*100000000000000^101 ≤ 33549456764449^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436321161 1000000000 33549456764449 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(142057069/625000000 : ℝ), (6106998503/10000000000 : ℝ), (-436321161/1000000000 : ℝ)] ![(7107189457449/50000000000000 : ℝ), (52236164300771/100000000000000 : ℝ), (33549456764449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(142057069/625000000 : ℝ)|^133 ≤ (7107189457449/50000000000000 : ℝ)^101
        have hw : |(142057069/625000000 : ℝ)|=(142057069/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6106998503/10000000000 : ℝ)|^133 ≤ (52236164300771/100000000000000 : ℝ)^101
        have hw : |(6106998503/10000000000 : ℝ)|=(6106998503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436321161/1000000000 : ℝ)|^133 ≤ (33549456764449/100000000000000 : ℝ)^101
        have hw : |(-436321161/1000000000 : ℝ)|=(436321161/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1079217313/2000000000 : ℝ)*x 0 + (4447986581/10000000000 : ℝ)*x 1 + (3080063841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079217313/2000000000 : ℝ)^133 ≤ (22190292245509/50000000000000 : ℝ)^101 := by
    have hnat : (1079217313 : ℕ)^133*50000000000000^101 ≤ 22190292245509^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079217313 2000000000 22190292245509 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4447986581/10000000000 : ℝ)^133 ≤ (17205231169769/50000000000000 : ℝ)^101 := by
    have hnat : (4447986581 : ℕ)^133*50000000000000^101 ≤ 17205231169769^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447986581 10000000000 17205231169769 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3080063841/10000000000 : ℝ)^133 ≤ (2120895316141/10000000000000 : ℝ)^101 := by
    have hnat : (3080063841 : ℕ)^133*10000000000000^101 ≤ 2120895316141^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080063841 10000000000 2120895316141 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079217313/2000000000 : ℝ), (4447986581/10000000000 : ℝ), (3080063841/10000000000 : ℝ)] ![(22190292245509/50000000000000 : ℝ), (17205231169769/50000000000000 : ℝ), (2120895316141/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079217313/2000000000 : ℝ)|^133 ≤ (22190292245509/50000000000000 : ℝ)^101
        have hw : |(1079217313/2000000000 : ℝ)|=(1079217313/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4447986581/10000000000 : ℝ)|^133 ≤ (17205231169769/50000000000000 : ℝ)^101
        have hw : |(4447986581/10000000000 : ℝ)|=(4447986581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3080063841/10000000000 : ℝ)|^133 ≤ (2120895316141/10000000000000 : ℝ)^101
        have hw : |(3080063841/10000000000 : ℝ)|=(3080063841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2910922759/10000000000 : ℝ)*x 0 + (6105039669/10000000000 : ℝ)*x 1 + (476677543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2910922759/10000000000 : ℝ)^133 ≤ (19688771573281/100000000000000 : ℝ)^101 := by
    have hnat : (2910922759 : ℕ)^133*100000000000000^101 ≤ 19688771573281^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2910922759 10000000000 19688771573281 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6105039669/10000000000 : ℝ)^133 ≤ (52214102076411/100000000000000 : ℝ)^101 := by
    have hnat : (6105039669 : ℕ)^133*100000000000000^101 ≤ 52214102076411^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6105039669 10000000000 52214102076411 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (476677543/1250000000 : ℝ)^133 ≤ (2809712633367/10000000000000 : ℝ)^101 := by
    have hnat : (476677543 : ℕ)^133*10000000000000^101 ≤ 2809712633367^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476677543 1250000000 2809712633367 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2910922759/10000000000 : ℝ), (6105039669/10000000000 : ℝ), (476677543/1250000000 : ℝ)] ![(19688771573281/100000000000000 : ℝ), (52214102076411/100000000000000 : ℝ), (2809712633367/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2910922759/10000000000 : ℝ)|^133 ≤ (19688771573281/100000000000000 : ℝ)^101
        have hw : |(-2910922759/10000000000 : ℝ)|=(2910922759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6105039669/10000000000 : ℝ)|^133 ≤ (52214102076411/100000000000000 : ℝ)^101
        have hw : |(6105039669/10000000000 : ℝ)|=(6105039669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(476677543/1250000000 : ℝ)|^133 ≤ (2809712633367/10000000000000 : ℝ)^101
        have hw : |(476677543/1250000000 : ℝ)|=(476677543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1403378387/2000000000 : ℝ)*x 0 + (41934461/10000000000 : ℝ)*x 1 + (471990829/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1403378387/2000000000 : ℝ)^133 ≤ (7839865200031/12500000000000 : ℝ)^101 := by
    have hnat : (1403378387 : ℕ)^133*12500000000000^101 ≤ 7839865200031^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403378387 2000000000 7839865200031 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41934461/10000000000 : ℝ)^133 ≤ (9252013701/12500000000000 : ℝ)^101 := by
    have hnat : (41934461 : ℕ)^133*12500000000000^101 ≤ 9252013701^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41934461 10000000000 9252013701 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471990829/1000000000 : ℝ)^133 ≤ (18603531139533/50000000000000 : ℝ)^101 := by
    have hnat : (471990829 : ℕ)^133*50000000000000^101 ≤ 18603531139533^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471990829 1000000000 18603531139533 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1403378387/2000000000 : ℝ), (41934461/10000000000 : ℝ), (471990829/1000000000 : ℝ)] ![(7839865200031/12500000000000 : ℝ), (9252013701/12500000000000 : ℝ), (18603531139533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1403378387/2000000000 : ℝ)|^133 ≤ (7839865200031/12500000000000 : ℝ)^101
        have hw : |(1403378387/2000000000 : ℝ)|=(1403378387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41934461/10000000000 : ℝ)|^133 ≤ (9252013701/12500000000000 : ℝ)^101
        have hw : |(41934461/10000000000 : ℝ)|=(41934461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(471990829/1000000000 : ℝ)|^133 ≤ (18603531139533/50000000000000 : ℝ)^101
        have hw : |(471990829/1000000000 : ℝ)|=(471990829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (24751453/100000000 : ℝ)*x 0 + (863099097/1250000000 : ℝ)*x 1 + (-3242535177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (24751453/100000000 : ℝ)^133 ≤ (3975705403377/25000000000000 : ℝ)^101 := by
    have hnat : (24751453 : ℕ)^133*25000000000000^101 ≤ 3975705403377^101*100000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24751453 100000000 3975705403377 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (863099097/1250000000 : ℝ)^133 ≤ (12280568569069/20000000000000 : ℝ)^101 := by
    have hnat : (863099097 : ℕ)^133*20000000000000^101 ≤ 12280568569069^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863099097 1250000000 12280568569069 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3242535177/10000000000 : ℝ)^133 ≤ (22694335520697/100000000000000 : ℝ)^101 := by
    have hnat : (3242535177 : ℕ)^133*100000000000000^101 ≤ 22694335520697^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3242535177 10000000000 22694335520697 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(24751453/100000000 : ℝ), (863099097/1250000000 : ℝ), (-3242535177/10000000000 : ℝ)] ![(3975705403377/25000000000000 : ℝ), (12280568569069/20000000000000 : ℝ), (22694335520697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(24751453/100000000 : ℝ)|^133 ≤ (3975705403377/25000000000000 : ℝ)^101
        have hw : |(24751453/100000000 : ℝ)|=(24751453/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(863099097/1250000000 : ℝ)|^133 ≤ (12280568569069/20000000000000 : ℝ)^101
        have hw : |(863099097/1250000000 : ℝ)|=(863099097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3242535177/10000000000 : ℝ)|^133 ≤ (22694335520697/100000000000000 : ℝ)^101
        have hw : |(-3242535177/10000000000 : ℝ)|=(3242535177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304080_s2_s2_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1313338843/2500000000 : ℝ)*x 0 + (4183699321/10000000000 : ℝ)*x 1 + (3533666443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313338843/2500000000 : ℝ)^133 ≤ (1338789558749/3125000000000 : ℝ)^101 := by
    have hnat : (1313338843 : ℕ)^133*3125000000000^101 ≤ 1338789558749^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313338843 2500000000 1338789558749 3125000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4183699321/10000000000 : ℝ)^133 ≤ (31743793815047/100000000000000 : ℝ)^101 := by
    have hnat : (4183699321 : ℕ)^133*100000000000000^101 ≤ 31743793815047^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183699321 10000000000 31743793815047 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3533666443/10000000000 : ℝ)^133 ≤ (2541494028521/10000000000000 : ℝ)^101 := by
    have hnat : (3533666443 : ℕ)^133*10000000000000^101 ≤ 2541494028521^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3533666443 10000000000 2541494028521 10000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313338843/2500000000 : ℝ), (4183699321/10000000000 : ℝ), (3533666443/10000000000 : ℝ)] ![(1338789558749/3125000000000 : ℝ), (31743793815047/100000000000000 : ℝ), (2541494028521/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313338843/2500000000 : ℝ)|^133 ≤ (1338789558749/3125000000000 : ℝ)^101
        have hw : |(1313338843/2500000000 : ℝ)|=(1313338843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4183699321/10000000000 : ℝ)|^133 ≤ (31743793815047/100000000000000 : ℝ)^101
        have hw : |(4183699321/10000000000 : ℝ)|=(4183699321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3533666443/10000000000 : ℝ)|^133 ≤ (2541494028521/10000000000000 : ℝ)^101
        have hw : |(3533666443/10000000000 : ℝ)|=(3533666443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304080_s2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((38129/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38129/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((42861/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(42861/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85221/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85221/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((269/500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(269/500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((841/6250 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(841/6250 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61119/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61119/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (187821/100000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (38129/50000 : ℝ) ^ (33/8 : ℝ) ≤ (6538186669889841477/20000000000000000000 : ℝ) := by
    have hpowers : (38129/50000 : ℝ)^33 ≤ (6538186669889841477/20000000000000000000 : ℝ)^8 := by
      have hnat : (38129 : ℕ)^33*20000000000000000000^8 ≤ 6538186669889841477^8*50000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38129 50000 6538186669889841477 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38129/50000 : ℝ)) (X := (6538186669889841477/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (26538186669889841477/20000000000000000000 : ℝ) ≤ (10709758966178713/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (26538186669889841477/20000000000000000000 : ℝ)^8 ≤ (10709758966178713/10000000000000000 : ℝ)^33 := by
      have hnat : (26538186669889841477 : ℕ)^8*10000000000000000^33 ≤ 10709758966178713^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26538186669889841477 20000000000000000000 10709758966178713 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10709758966178713/10000000000000000 : ℝ)) (X := (26538186669889841477/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (16538186669889841477/10000000000000000000 : ℝ) ≤ (11297094486386119/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (16538186669889841477/10000000000000000000 : ℝ)^8 ≤ (11297094486386119/10000000000000000 : ℝ)^33 := by
      have hnat : (16538186669889841477 : ℕ)^8*10000000000000000^33 ≤ 11297094486386119^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16538186669889841477 10000000000000000000 11297094486386119 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11297094486386119/10000000000000000 : ℝ)) (X := (16538186669889841477/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(709758966178713/7625800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(293667760103703/3812900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (38129/50000 : ℝ)) (alpha := (709758966178713/7625800000000000 : ℝ)) (beta := (293667760103703/3812900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38129/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(709758966178713/7625800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(293667760103703/3812900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (42861/100000 : ℝ) ^ (33/8 : ℝ) ≤ (607137392195980243/20000000000000000000 : ℝ) := by
    have hpowers : (42861/100000 : ℝ)^33 ≤ (607137392195980243/20000000000000000000 : ℝ)^8 := by
      have hnat : (42861 : ℕ)^33*20000000000000000000^8 ≤ 607137392195980243^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42861 100000 607137392195980243 20000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42861/100000 : ℝ)) (X := (607137392195980243/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (20607137392195980243/20000000000000000000 : ℝ) ≤ (2518190231935183/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (20607137392195980243/20000000000000000000 : ℝ)^8 ≤ (2518190231935183/2500000000000000 : ℝ)^33 := by
      have hnat : (20607137392195980243 : ℕ)^8*2500000000000000^33 ≤ 2518190231935183^33*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20607137392195980243 20000000000000000000 2518190231935183 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2518190231935183/2500000000000000 : ℝ)) (X := (20607137392195980243/20000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (10607137392195980243/10000000000000000000 : ℝ) ≤ (5071957750143707/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (10607137392195980243/10000000000000000000 : ℝ)^8 ≤ (5071957750143707/5000000000000000 : ℝ)^33 := by
      have hnat : (10607137392195980243 : ℕ)^8*5000000000000000^33 ≤ 5071957750143707^33*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10607137392195980243 10000000000000000000 5071957750143707 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5071957750143707/5000000000000000 : ℝ)) (X := (10607137392195980243/10000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(866201520723/51025000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(11859095424447/714350000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (42861/100000 : ℝ)) (alpha := (866201520723/51025000000000 : ℝ)) (beta := (11859095424447/714350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (42861/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(866201520723/51025000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(11859095424447/714350000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (85221/100000 : ℝ) ^ (33/8 : ℝ) ≤ (51701701057007901137/100000000000000000000 : ℝ) := by
    have hpowers : (85221/100000 : ℝ)^33 ≤ (51701701057007901137/100000000000000000000 : ℝ)^8 := by
      have hnat : (85221 : ℕ)^33*100000000000000000000^8 ≤ 51701701057007901137^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85221 100000 51701701057007901137 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85221/100000 : ℝ)) (X := (51701701057007901137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (151701701057007901137/100000000000000000000 : ℝ) ≤ (2212618139697199/2000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (151701701057007901137/100000000000000000000 : ℝ)^8 ≤ (2212618139697199/2000000000000000 : ℝ)^33 := by
      have hnat : (151701701057007901137 : ℕ)^8*2000000000000000^33 ≤ 2212618139697199^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        151701701057007901137 100000000000000000000 2212618139697199 2000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2212618139697199/2000000000000000 : ℝ)) (X := (151701701057007901137/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (101701701057007901137/50000000000000000000 : ℝ) ≤ (2969569642061399/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (101701701057007901137/50000000000000000000 : ℝ)^8 ≤ (2969569642061399/2500000000000000 : ℝ)^33 := by
      have hnat : (101701701057007901137 : ℕ)^8*2500000000000000^33 ≤ 2969569642061399^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101701701057007901137 50000000000000000000 2969569642061399 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2969569642061399/2500000000000000 : ℝ)) (X := (101701701057007901137/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(212618139697199/1704420000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(90576429973289/946900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (85221/100000 : ℝ)) (alpha := (212618139697199/1704420000000000 : ℝ)) (beta := (90576429973289/946900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (85221/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(212618139697199/1704420000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(90576429973289/946900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3375633687/10000000000 : ℝ)*X 0 0+(5675962157/10000000000 : ℝ)*X 0 1+(3868700419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((612019787/2000000000 : ℝ)*X 2 0+(1249218653/2000000000 : ℝ)*X 2 1+(-701415327/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4290342739/10000000000 : ℝ)*X 0 0+(4910063971/10000000000 : ℝ)*X 0 1+(1901338159/5000000000 : ℝ)*X 0 2+(4290342739/10000000000 : ℝ)*X 1 0+(4910063971/10000000000 : ℝ)*X 1 1+(1901338159/5000000000 : ℝ)*X 1 2+(4290342739/10000000000 : ℝ)*X 2 0+(4910063971/10000000000 : ℝ)*X 2 1+(1901338159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-420384689/1250000000 : ℝ)*X 0 0+(8667283/15625000 : ℝ)*X 0 1+(80495007/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5740551237/10000000000 : ℝ)*X 1 0+(2028743/250000000 : ℝ)*X 1 1+(151427759/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1272214717/5000000000 : ℝ)*X 2 0+(7008187871/10000000000 : ℝ)*X 2 1+(-609007269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((947934237/2500000000 : ℝ)*X 0 0+(2596000753/5000000000 : ℝ)*X 0 1+(4000829921/10000000000 : ℝ)*X 0 2+(947934237/2500000000 : ℝ)*X 1 0+(2596000753/5000000000 : ℝ)*X 1 1+(4000829921/10000000000 : ℝ)*X 1 2+(947934237/2500000000 : ℝ)*X 2 0+(2596000753/5000000000 : ℝ)*X 2 1+(4000829921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-851102763/2000000000 : ℝ)*X 0 0+(561076727/1000000000 : ℝ)*X 0 1+(3036690827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((5735673639/10000000000 : ℝ)*X 1 0+(-264216223/10000000000 : ℝ)*X 1 1+(6003167221/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((142057069/625000000 : ℝ)*X 2 0+(6106998503/10000000000 : ℝ)*X 2 1+(-436321161/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((1079217313/2000000000 : ℝ)*X 0 0+(4447986581/10000000000 : ℝ)*X 0 1+(3080063841/10000000000 : ℝ)*X 0 2+(1079217313/2000000000 : ℝ)*X 1 0+(4447986581/10000000000 : ℝ)*X 1 1+(3080063841/10000000000 : ℝ)*X 1 2+(1079217313/2000000000 : ℝ)*X 2 0+(4447986581/10000000000 : ℝ)*X 2 1+(3080063841/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-2910922759/10000000000 : ℝ)*X 0 0+(6105039669/10000000000 : ℝ)*X 0 1+(476677543/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((1403378387/2000000000 : ℝ)*X 1 0+(41934461/10000000000 : ℝ)*X 1 1+(471990829/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((24751453/100000000 : ℝ)*X 2 0+(863099097/1250000000 : ℝ)*X 2 1+(-3242535177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((1313338843/2500000000 : ℝ)*X 0 0+(4183699321/10000000000 : ℝ)*X 0 1+(3533666443/10000000000 : ℝ)*X 0 2+(1313338843/2500000000 : ℝ)*X 1 0+(4183699321/10000000000 : ℝ)*X 1 1+(3533666443/10000000000 : ℝ)*X 1 2+(1313338843/2500000000 : ℝ)*X 2 0+(4183699321/10000000000 : ℝ)*X 2 1+(3533666443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304080_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((269/500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(269/500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7378885561441433441826717981/436029458900000000000000000000000 : ℝ) := by norm_num
    linear_combination (72605209027/250000000000 : ℝ)*(base7) + (741853/200000000000 : ℝ)*(base40) + (462672674443/200000000000 : ℝ)*(base49) + (221554014971/250000000000 : ℝ)*(base50) + (5172383978969/1000000000000 : ℝ)*(major_s2_0) + (5172383978969/1000000000000 : ℝ)*(major_s2_1) + (5172383978969/1000000000000 : ℝ)*(major_s2_2) + (379691/7812500000 : ℝ)*(sp_s2_0) + (6752558694407/1000000000000 : ℝ)*(sp_s2_7) + (6752695401681/1000000000000 : ℝ)*(sp_s2_8) + (844060831011/125000000000 : ℝ)*(sp_s2_9) + (1850331989263/500000000000 : ℝ)*(sp_s2_12) + (44053413/500000000000 : ℝ)*(sp_s2_20) + (208753593/1000000000000 : ℝ)*(sp_s2_22) + (1705121571209/500000000000 : ℝ)*(f.failure) + (6752695401681/1000000000000 : ℝ)*(f.sum) + (95648605181696181301/121755242700000000000000000000000 : ℝ)*base62 + (475314110096101/946900000000000000000000000 : ℝ)*base65 + (39168850528333/51025000000000000000000000 : ℝ)*base67 + (908176246601941/1704420000000000000000000000 : ℝ)*base69 + (951901758751466751/72208700200000000000000000000000 : ℝ)*base71 + (2153445659570467/3812900000000000000000000000 : ℝ)*base73 + (243813562722043/714350000000000000000000000 : ℝ)*base74 + (3553387612739137/7625800000000000000000000000 : ℝ)*base77 + (42820057571321113/119725060000000000000000000000 : ℝ)*base79 + (4819/6250000000000000 : ℝ)*base86 + (4819/6250000000000000 : ℝ)*base88 + (4819/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((841/6250 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(841/6250 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (64598755821414152370307313/20292540450000000000000000000000 : ℝ) := by norm_num
    linear_combination (185371381447/1000000000000 : ℝ)*(base40) + (866090860683/1000000000000 : ℝ)*(base49) + (89553/200000000000 : ℝ)*(base60) + (670556080267/250000000000 : ℝ)*(major_s2_0) + (670556080267/250000000000 : ℝ)*(major_s2_1) + (670556080267/250000000000 : ℝ)*(major_s2_2) + (2485779/500000000000 : ℝ)*(sp_s2_2) + (3993487/500000000000 : ℝ)*(sp_s2_8) + (1798005107731/500000000000 : ℝ)*(sp_s2_13) + (449498121203/125000000000 : ℝ)*(sp_s2_14) + (3596005243903/1000000000000 : ℝ)*(sp_s2_15) + (442088948521/250000000000 : ℝ)*(sp_s2_19) + (1078679/62500000000 : ℝ)*(sp_s2_21) + (4078573/50000000000 : ℝ)*(sp_s2_25) + (221054670693/125000000000 : ℝ)*(f.failure) + (1798005107731/500000000000 : ℝ)*(f.sum) + (4203816511258115861/15219405337500000000000000000000 : ℝ)*base63 + (33960901056027/236725000000000000000000000 : ℝ)*base64 + (14872360966791/51025000000000000000000000 : ℝ)*base67 + (34083043050037/53263125000000000000000000 : ℝ)*base69 + (5546787349405543427/18052175050000000000000000000000 : ℝ)*base70 + (166007229675921/953225000000000000000000000 : ℝ)*base73 + (130757838846017/357175000000000000000000000 : ℝ)*base75 + (116854578680071/119153125000000000000000000 : ℝ)*base77 + (13935869281985587/29931265000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (163/1562500000000000 : ℝ)*base86 + (163/1562500000000000 : ℝ)*base88 + (163/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61119/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61119/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (817016639880729425357118477/141709574142500000000000000000000 : ℝ) := by norm_num
    linear_combination (110714819851/500000000000 : ℝ)*(base7) + (130465831761/200000000000 : ℝ)*(base40) + (256807040813/100000000000 : ℝ)*(base49) + (806128430533/1000000000000 : ℝ)*(base50) + (3020916532293/500000000000 : ℝ)*(major_s2_0) + (3020916532293/500000000000 : ℝ)*(major_s2_1) + (3020916532293/500000000000 : ℝ)*(major_s2_2) + (18008791/1000000000000 : ℝ)*(sp_s2_6) + (1094323/250000000000 : ℝ)*(sp_s2_15) + (41536709/1000000000000 : ℝ)*(sp_s2_19) + (796154763503/100000000000 : ℝ)*(sp_s2_20) + (796154763503/100000000000 : ℝ)*(sp_s2_21) + (3980771628869/500000000000 : ℝ)*(sp_s2_22) + (1051214053/250000000 : ℝ)*(sp_s2_25) + (1991743058899/500000000000 : ℝ)*(f.failure) + (796154763503/100000000000 : ℝ)*(f.sum) + (1216434263137669753/6764180150000000000000000000000 : ℝ)*base62 + (375515901079023/473450000000000000000000000 : ℝ)*base64 + (56695925112391/102050000000000000000000000 : ℝ)*base66 + (79322268190373/94690000000000000000000000 : ℝ)*base68 + (11884205394091784213/36104350100000000000000000000000 : ℝ)*base70 + (254604955300259/476612500000000000000000000 : ℝ)*base72 + (65324562467289/89293750000000000000000000 : ℝ)*base74 + (3625839589485751/3812900000000000000000000000 : ℝ)*base76 + (7514109939553439/29931265000000000000000000000 : ℝ)*base79 + (3641/6250000000000000 : ℝ)*base87 + (3641/6250000000000000 : ℝ)*base89 + (3641/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((38129/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38129/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((42861/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(42861/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(85221/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(85221/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((269/500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(269/500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((841/6250 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(841/6250 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61119/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61119/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304080_s2 p hpa hpb X hX hprev1

#print axioms solution
