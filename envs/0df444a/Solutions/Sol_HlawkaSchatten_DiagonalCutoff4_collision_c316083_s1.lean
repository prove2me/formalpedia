-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316083_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:08:32.814352+00:00
-- url     : https://prove2.me/submissions/e7da2bb1-0419-479d-add2-03da9a636e51

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
theorem collision_support_c316083_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2237076053/10000000000 : ℝ)*x 0 + (483205907/1000000000 : ℝ)*x 1 + (5309102241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237076053/10000000000 : ℝ)^77 ≤ (7552230073037/50000000000000 : ℝ)^61 := by
    have hnat : (2237076053 : ℕ)^77*50000000000000^61 ≤ 7552230073037^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237076053 10000000000 7552230073037 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483205907/1000000000 : ℝ)^77 ≤ (3992837846121/10000000000000 : ℝ)^61 := by
    have hnat : (483205907 : ℕ)^77*10000000000000^61 ≤ 3992837846121^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483205907 1000000000 3992837846121 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5309102241/10000000000 : ℝ)^77 ≤ (44967161376823/100000000000000 : ℝ)^61 := by
    have hnat : (5309102241 : ℕ)^77*100000000000000^61 ≤ 44967161376823^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309102241 10000000000 44967161376823 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2237076053/10000000000 : ℝ), (483205907/1000000000 : ℝ), (5309102241/10000000000 : ℝ)] ![(7552230073037/50000000000000 : ℝ), (3992837846121/10000000000000 : ℝ), (44967161376823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2237076053/10000000000 : ℝ)|^77 ≤ (7552230073037/50000000000000 : ℝ)^61
        have hw : |(-2237076053/10000000000 : ℝ)|=(2237076053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(483205907/1000000000 : ℝ)|^77 ≤ (3992837846121/10000000000000 : ℝ)^61
        have hw : |(483205907/1000000000 : ℝ)|=(483205907/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5309102241/10000000000 : ℝ)|^77 ≤ (44967161376823/100000000000000 : ℝ)^61
        have hw : |(5309102241/10000000000 : ℝ)|=(5309102241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13358949/19531250 : ℝ)*x 0 + (-187113797/2500000000 : ℝ)*x 1 + (4283677937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13358949/19531250 : ℝ)^77 ≤ (61911973395093/100000000000000 : ℝ)^61 := by
    have hnat : (13358949 : ℕ)^77*100000000000000^61 ≤ 61911973395093^61*19531250^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13358949 19531250 61911973395093 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187113797/2500000000 : ℝ)^77 ≤ (37919711993/1000000000000 : ℝ)^61 := by
    have hnat : (187113797 : ℕ)^77*1000000000000^61 ≤ 37919711993^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187113797 2500000000 37919711993 1000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4283677937/10000000000 : ℝ)^77 ≤ (6859211077631/20000000000000 : ℝ)^61 := by
    have hnat : (4283677937 : ℕ)^77*20000000000000^61 ≤ 6859211077631^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283677937 10000000000 6859211077631 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13358949/19531250 : ℝ), (-187113797/2500000000 : ℝ), (4283677937/10000000000 : ℝ)] ![(61911973395093/100000000000000 : ℝ), (37919711993/1000000000000 : ℝ), (6859211077631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13358949/19531250 : ℝ)|^77 ≤ (61911973395093/100000000000000 : ℝ)^61
        have hw : |(13358949/19531250 : ℝ)|=(13358949/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-187113797/2500000000 : ℝ)|^77 ≤ (37919711993/1000000000000 : ℝ)^61
        have hw : |(-187113797/2500000000 : ℝ)|=(187113797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4283677937/10000000000 : ℝ)|^77 ≤ (6859211077631/20000000000000 : ℝ)^61
        have hw : |(4283677937/10000000000 : ℝ)|=(4283677937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (889173217/2500000000 : ℝ)*x 0 + (321776753/500000000 : ℝ)*x 1 + (-228927617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889173217/2500000000 : ℝ)^77 ≤ (27119896847413/100000000000000 : ℝ)^61 := by
    have hnat : (889173217 : ℕ)^77*100000000000000^61 ≤ 27119896847413^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889173217 2500000000 27119896847413 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321776753/500000000 : ℝ)^77 ≤ (3583087186159/6250000000000 : ℝ)^61 := by
    have hnat : (321776753 : ℕ)^77*6250000000000^61 ≤ 3583087186159^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321776753 500000000 3583087186159 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (228927617/1000000000 : ℝ)^77 ≤ (3110141632893/20000000000000 : ℝ)^61 := by
    have hnat : (228927617 : ℕ)^77*20000000000000^61 ≤ 3110141632893^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228927617 1000000000 3110141632893 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(889173217/2500000000 : ℝ), (321776753/500000000 : ℝ), (-228927617/1000000000 : ℝ)] ![(27119896847413/100000000000000 : ℝ), (3583087186159/6250000000000 : ℝ), (3110141632893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(889173217/2500000000 : ℝ)|^77 ≤ (27119896847413/100000000000000 : ℝ)^61
        have hw : |(889173217/2500000000 : ℝ)|=(889173217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321776753/500000000 : ℝ)|^77 ≤ (3583087186159/6250000000000 : ℝ)^61
        have hw : |(321776753/500000000 : ℝ)|=(321776753/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-228927617/1000000000 : ℝ)|^77 ≤ (3110141632893/20000000000000 : ℝ)^61
        have hw : |(-228927617/1000000000 : ℝ)|=(228927617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-88996391/400000000 : ℝ)*x 0 + (4800746993/10000000000 : ℝ)*x 1 + (5349276381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88996391/400000000 : ℝ)^77 ≤ (7500421359811/50000000000000 : ℝ)^61 := by
    have hnat : (88996391 : ℕ)^77*50000000000000^61 ≤ 7500421359811^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88996391 400000000 7500421359811 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4800746993/10000000000 : ℝ)^77 ≤ (19801025968643/50000000000000 : ℝ)^61 := by
    have hnat : (4800746993 : ℕ)^77*50000000000000^61 ≤ 19801025968643^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4800746993 10000000000 19801025968643 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5349276381/10000000000 : ℝ)^77 ≤ (45397105328003/100000000000000 : ℝ)^61 := by
    have hnat : (5349276381 : ℕ)^77*100000000000000^61 ≤ 45397105328003^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349276381 10000000000 45397105328003 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88996391/400000000 : ℝ), (4800746993/10000000000 : ℝ), (5349276381/10000000000 : ℝ)] ![(7500421359811/50000000000000 : ℝ), (19801025968643/50000000000000 : ℝ), (45397105328003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88996391/400000000 : ℝ)|^77 ≤ (7500421359811/50000000000000 : ℝ)^61
        have hw : |(-88996391/400000000 : ℝ)|=(88996391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4800746993/10000000000 : ℝ)|^77 ≤ (19801025968643/50000000000000 : ℝ)^61
        have hw : |(4800746993/10000000000 : ℝ)|=(4800746993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5349276381/10000000000 : ℝ)|^77 ≤ (45397105328003/100000000000000 : ℝ)^61
        have hw : |(5349276381/10000000000 : ℝ)|=(5349276381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (651654041/1000000000 : ℝ)*x 0 + (-914189/1000000000 : ℝ)*x 1 + (2502641211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (651654041/1000000000 : ℝ)^77 ≤ (58241786878509/100000000000000 : ℝ)^61 := by
    have hnat : (651654041 : ℕ)^77*100000000000000^61 ≤ 58241786878509^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651654041 1000000000 58241786878509 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914189/1000000000 : ℝ)^77 ≤ (7292907109/50000000000000 : ℝ)^61 := by
    have hnat : (914189 : ℕ)^77*50000000000000^61 ≤ 7292907109^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914189 1000000000 7292907109 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2502641211/5000000000 : ℝ)^77 ≤ (10435906823533/25000000000000 : ℝ)^61 := by
    have hnat : (2502641211 : ℕ)^77*25000000000000^61 ≤ 10435906823533^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502641211 5000000000 10435906823533 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(651654041/1000000000 : ℝ), (-914189/1000000000 : ℝ), (2502641211/5000000000 : ℝ)] ![(58241786878509/100000000000000 : ℝ), (7292907109/50000000000000 : ℝ), (10435906823533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(651654041/1000000000 : ℝ)|^77 ≤ (58241786878509/100000000000000 : ℝ)^61
        have hw : |(651654041/1000000000 : ℝ)|=(651654041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914189/1000000000 : ℝ)|^77 ≤ (7292907109/50000000000000 : ℝ)^61
        have hw : |(-914189/1000000000 : ℝ)|=(914189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2502641211/5000000000 : ℝ)|^77 ≤ (10435906823533/25000000000000 : ℝ)^61
        have hw : |(2502641211/5000000000 : ℝ)|=(2502641211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (309440099/1000000000 : ℝ)*x 0 + (7292001089/10000000000 : ℝ)*x 1 + (-814972787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309440099/1000000000 : ℝ)^77 ≤ (355449053927/1562500000000 : ℝ)^61 := by
    have hnat : (309440099 : ℕ)^77*1562500000000^61 ≤ 355449053927^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309440099 1000000000 355449053927 1562500000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7292001089/10000000000 : ℝ)^77 ≤ (16780778463497/25000000000000 : ℝ)^61 := by
    have hnat : (7292001089 : ℕ)^77*25000000000000^61 ≤ 16780778463497^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7292001089 10000000000 16780778463497 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814972787/5000000000 : ℝ)^77 ≤ (10128146682589/100000000000000 : ℝ)^61 := by
    have hnat : (814972787 : ℕ)^77*100000000000000^61 ≤ 10128146682589^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814972787 5000000000 10128146682589 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(309440099/1000000000 : ℝ), (7292001089/10000000000 : ℝ), (-814972787/5000000000 : ℝ)] ![(355449053927/1562500000000 : ℝ), (16780778463497/25000000000000 : ℝ), (10128146682589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(309440099/1000000000 : ℝ)|^77 ≤ (355449053927/1562500000000 : ℝ)^61
        have hw : |(309440099/1000000000 : ℝ)|=(309440099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7292001089/10000000000 : ℝ)|^77 ≤ (16780778463497/25000000000000 : ℝ)^61
        have hw : |(7292001089/10000000000 : ℝ)|=(7292001089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-814972787/5000000000 : ℝ)|^77 ≤ (10128146682589/100000000000000 : ℝ)^61
        have hw : |(-814972787/5000000000 : ℝ)|=(814972787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2882840609/10000000000 : ℝ)*x 0 + (232519813/500000000 : ℝ)*x 1 + (494915791/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2882840609/10000000000 : ℝ)^77 ≤ (20803396151169/100000000000000 : ℝ)^61 := by
    have hnat : (2882840609 : ℕ)^77*100000000000000^61 ≤ 20803396151169^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2882840609 10000000000 20803396151169 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (232519813/500000000 : ℝ)^77 ≤ (190214761467/500000000000 : ℝ)^61 := by
    have hnat : (232519813 : ℕ)^77*500000000000^61 ≤ 190214761467^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232519813 500000000 190214761467 500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (494915791/1000000000 : ℝ)^77 ≤ (41153651539671/100000000000000 : ℝ)^61 := by
    have hnat : (494915791 : ℕ)^77*100000000000000^61 ≤ 41153651539671^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      494915791 1000000000 41153651539671 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2882840609/10000000000 : ℝ), (232519813/500000000 : ℝ), (494915791/1000000000 : ℝ)] ![(20803396151169/100000000000000 : ℝ), (190214761467/500000000000 : ℝ), (41153651539671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2882840609/10000000000 : ℝ)|^77 ≤ (20803396151169/100000000000000 : ℝ)^61
        have hw : |(2882840609/10000000000 : ℝ)|=(2882840609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(232519813/500000000 : ℝ)|^77 ≤ (190214761467/500000000000 : ℝ)^61
        have hw : |(232519813/500000000 : ℝ)|=(232519813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(494915791/1000000000 : ℝ)|^77 ≤ (41153651539671/100000000000000 : ℝ)^61
        have hw : |(494915791/1000000000 : ℝ)|=(494915791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-164750381/1250000000 : ℝ)*x 0 + (921549839/2500000000 : ℝ)*x 1 + (3505806719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164750381/1250000000 : ℝ)^77 ≤ (774595230331/10000000000000 : ℝ)^61 := by
    have hnat : (164750381 : ℕ)^77*10000000000000^61 ≤ 774595230331^61*1250000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164750381 1250000000 774595230331 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921549839/2500000000 : ℝ)^77 ≤ (7093075512723/25000000000000 : ℝ)^61 := by
    have hnat : (921549839 : ℕ)^77*25000000000000^61 ≤ 7093075512723^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921549839 2500000000 7093075512723 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3505806719/5000000000 : ℝ)^77 ≤ (63881745625577/100000000000000 : ℝ)^61 := by
    have hnat : (3505806719 : ℕ)^77*100000000000000^61 ≤ 63881745625577^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3505806719 5000000000 63881745625577 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-164750381/1250000000 : ℝ), (921549839/2500000000 : ℝ), (3505806719/5000000000 : ℝ)] ![(774595230331/10000000000000 : ℝ), (7093075512723/25000000000000 : ℝ), (63881745625577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-164750381/1250000000 : ℝ)|^77 ≤ (774595230331/10000000000000 : ℝ)^61
        have hw : |(-164750381/1250000000 : ℝ)|=(164750381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921549839/2500000000 : ℝ)|^77 ≤ (7093075512723/25000000000000 : ℝ)^61
        have hw : |(921549839/2500000000 : ℝ)|=(921549839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3505806719/5000000000 : ℝ)|^77 ≤ (63881745625577/100000000000000 : ℝ)^61
        have hw : |(3505806719/5000000000 : ℝ)|=(3505806719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (319128341/400000000 : ℝ)*x 0 + (-127485873/2500000000 : ℝ)*x 1 + (3064444153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (319128341/400000000 : ℝ)^77 ≤ (9399086807559/12500000000000 : ℝ)^61 := by
    have hnat : (319128341 : ℕ)^77*12500000000000^61 ≤ 9399086807559^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319128341 400000000 9399086807559 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127485873/2500000000 : ℝ)^77 ≤ (2336207666143/100000000000000 : ℝ)^61 := by
    have hnat : (127485873 : ℕ)^77*100000000000000^61 ≤ 2336207666143^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127485873 2500000000 2336207666143 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3064444153/10000000000 : ℝ)^77 ≤ (5617774464939/25000000000000 : ℝ)^61 := by
    have hnat : (3064444153 : ℕ)^77*25000000000000^61 ≤ 5617774464939^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3064444153 10000000000 5617774464939 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(319128341/400000000 : ℝ), (-127485873/2500000000 : ℝ), (3064444153/10000000000 : ℝ)] ![(9399086807559/12500000000000 : ℝ), (2336207666143/100000000000000 : ℝ), (5617774464939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(319128341/400000000 : ℝ)|^77 ≤ (9399086807559/12500000000000 : ℝ)^61
        have hw : |(319128341/400000000 : ℝ)|=(319128341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127485873/2500000000 : ℝ)|^77 ≤ (2336207666143/100000000000000 : ℝ)^61
        have hw : |(-127485873/2500000000 : ℝ)|=(127485873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3064444153/10000000000 : ℝ)|^77 ≤ (5617774464939/25000000000000 : ℝ)^61
        have hw : |(3064444153/10000000000 : ℝ)|=(3064444153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3668577421/10000000000 : ℝ)*x 0 + (6947344381/10000000000 : ℝ)*x 1 + (-719575667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3668577421/10000000000 : ℝ)^77 ≤ (3525149884899/12500000000000 : ℝ)^61 := by
    have hnat : (3668577421 : ℕ)^77*12500000000000^61 ≤ 3525149884899^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668577421 10000000000 3525149884899 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6947344381/10000000000 : ℝ)^77 ≤ (63143504794519/100000000000000 : ℝ)^61 := by
    have hnat : (6947344381 : ℕ)^77*100000000000000^61 ≤ 63143504794519^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6947344381 10000000000 63143504794519 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719575667/5000000000 : ℝ)^77 ≤ (8655296118167/100000000000000 : ℝ)^61 := by
    have hnat : (719575667 : ℕ)^77*100000000000000^61 ≤ 8655296118167^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719575667 5000000000 8655296118167 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3668577421/10000000000 : ℝ), (6947344381/10000000000 : ℝ), (-719575667/5000000000 : ℝ)] ![(3525149884899/12500000000000 : ℝ), (63143504794519/100000000000000 : ℝ), (8655296118167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3668577421/10000000000 : ℝ)|^77 ≤ (3525149884899/12500000000000 : ℝ)^61
        have hw : |(3668577421/10000000000 : ℝ)|=(3668577421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6947344381/10000000000 : ℝ)|^77 ≤ (63143504794519/100000000000000 : ℝ)^61
        have hw : |(6947344381/10000000000 : ℝ)|=(6947344381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-719575667/5000000000 : ℝ)|^77 ≤ (8655296118167/100000000000000 : ℝ)^61
        have hw : |(-719575667/5000000000 : ℝ)|=(719575667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (613549167/2500000000 : ℝ)*x 0 + (74922709/200000000 : ℝ)*x 1 + (3071790617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (613549167/2500000000 : ℝ)^77 ≤ (16977963214491/100000000000000 : ℝ)^61 := by
    have hnat : (613549167 : ℕ)^77*100000000000000^61 ≤ 16977963214491^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      613549167 2500000000 16977963214491 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74922709/200000000 : ℝ)^77 ≤ (3619482924997/12500000000000 : ℝ)^61 := by
    have hnat : (74922709 : ℕ)^77*12500000000000^61 ≤ 3619482924997^61*200000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74922709 200000000 3619482924997 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3071790617/5000000000 : ℝ)^77 ≤ (13516543343257/25000000000000 : ℝ)^61 := by
    have hnat : (3071790617 : ℕ)^77*25000000000000^61 ≤ 13516543343257^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071790617 5000000000 13516543343257 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(613549167/2500000000 : ℝ), (74922709/200000000 : ℝ), (3071790617/5000000000 : ℝ)] ![(16977963214491/100000000000000 : ℝ), (3619482924997/12500000000000 : ℝ), (13516543343257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(613549167/2500000000 : ℝ)|^77 ≤ (16977963214491/100000000000000 : ℝ)^61
        have hw : |(613549167/2500000000 : ℝ)|=(613549167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(74922709/200000000 : ℝ)|^77 ≤ (3619482924997/12500000000000 : ℝ)^61
        have hw : |(74922709/200000000 : ℝ)|=(74922709/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3071790617/5000000000 : ℝ)|^77 ≤ (13516543343257/25000000000000 : ℝ)^61
        have hw : |(3071790617/5000000000 : ℝ)|=(3071790617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-826286691/5000000000 : ℝ)*x 0 + (5514939019/10000000000 : ℝ)*x 1 + (253921309/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826286691/5000000000 : ℝ)^77 ≤ (2576488288287/25000000000000 : ℝ)^61 := by
    have hnat : (826286691 : ℕ)^77*25000000000000^61 ≤ 2576488288287^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826286691 5000000000 2576488288287 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514939019/10000000000 : ℝ)^77 ≤ (23589466529253/50000000000000 : ℝ)^61 := by
    have hnat : (5514939019 : ℕ)^77*50000000000000^61 ≤ 23589466529253^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514939019 10000000000 23589466529253 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253921309/500000000 : ℝ)^77 ≤ (21257556886683/50000000000000 : ℝ)^61 := by
    have hnat : (253921309 : ℕ)^77*50000000000000^61 ≤ 21257556886683^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253921309 500000000 21257556886683 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-826286691/5000000000 : ℝ), (5514939019/10000000000 : ℝ), (253921309/500000000 : ℝ)] ![(2576488288287/25000000000000 : ℝ), (23589466529253/50000000000000 : ℝ), (21257556886683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-826286691/5000000000 : ℝ)|^77 ≤ (2576488288287/25000000000000 : ℝ)^61
        have hw : |(-826286691/5000000000 : ℝ)|=(826286691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514939019/10000000000 : ℝ)|^77 ≤ (23589466529253/50000000000000 : ℝ)^61
        have hw : |(5514939019/10000000000 : ℝ)|=(5514939019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(253921309/500000000 : ℝ)|^77 ≤ (21257556886683/50000000000000 : ℝ)^61
        have hw : |(253921309/500000000 : ℝ)|=(253921309/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7467984501/10000000000 : ℝ)*x 0 + (-2504739/2500000000 : ℝ)*x 1 + (3934858703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7467984501/10000000000 : ℝ)^77 ≤ (69174381613343/100000000000000 : ℝ)^61 := by
    have hnat : (7467984501 : ℕ)^77*100000000000000^61 ≤ 69174381613343^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7467984501 10000000000 69174381613343 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2504739/2500000000 : ℝ)^77 ≤ (16373930893/100000000000000 : ℝ)^61 := by
    have hnat : (2504739 : ℕ)^77*100000000000000^61 ≤ 16373930893^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504739 2500000000 16373930893 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3934858703/10000000000 : ℝ)^77 ≤ (7702311110889/25000000000000 : ℝ)^61 := by
    have hnat : (3934858703 : ℕ)^77*25000000000000^61 ≤ 7702311110889^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3934858703 10000000000 7702311110889 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7467984501/10000000000 : ℝ), (-2504739/2500000000 : ℝ), (3934858703/10000000000 : ℝ)] ![(69174381613343/100000000000000 : ℝ), (16373930893/100000000000000 : ℝ), (7702311110889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7467984501/10000000000 : ℝ)|^77 ≤ (69174381613343/100000000000000 : ℝ)^61
        have hw : |(7467984501/10000000000 : ℝ)|=(7467984501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2504739/2500000000 : ℝ)|^77 ≤ (16373930893/100000000000000 : ℝ)^61
        have hw : |(-2504739/2500000000 : ℝ)|=(2504739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3934858703/10000000000 : ℝ)|^77 ≤ (7702311110889/25000000000000 : ℝ)^61
        have hw : |(3934858703/10000000000 : ℝ)|=(3934858703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (690527063/2000000000 : ℝ)*x 0 + (3286573993/5000000000 : ℝ)*x 1 + (-1112208087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690527063/2000000000 : ℝ)^77 ≤ (6530552410937/25000000000000 : ℝ)^61 := by
    have hnat : (690527063 : ℕ)^77*25000000000000^61 ≤ 6530552410937^61*2000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690527063 2000000000 6530552410937 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3286573993/5000000000 : ℝ)^77 ≤ (14720287094813/25000000000000 : ℝ)^61 := by
    have hnat : (3286573993 : ℕ)^77*25000000000000^61 ≤ 14720287094813^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3286573993 5000000000 14720287094813 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1112208087/5000000000 : ℝ)^77 ≤ (2999328392567/20000000000000 : ℝ)^61 := by
    have hnat : (1112208087 : ℕ)^77*20000000000000^61 ≤ 2999328392567^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1112208087 5000000000 2999328392567 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690527063/2000000000 : ℝ), (3286573993/5000000000 : ℝ), (-1112208087/5000000000 : ℝ)] ![(6530552410937/25000000000000 : ℝ), (14720287094813/25000000000000 : ℝ), (2999328392567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690527063/2000000000 : ℝ)|^77 ≤ (6530552410937/25000000000000 : ℝ)^61
        have hw : |(690527063/2000000000 : ℝ)|=(690527063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3286573993/5000000000 : ℝ)|^77 ≤ (14720287094813/25000000000000 : ℝ)^61
        have hw : |(3286573993/5000000000 : ℝ)|=(3286573993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1112208087/5000000000 : ℝ)|^77 ≤ (2999328392567/20000000000000 : ℝ)^61
        have hw : |(-1112208087/5000000000 : ℝ)|=(1112208087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316083_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3450862871/10000000000 : ℝ)*x 0 + (1165007053/2500000000 : ℝ)*x 1 + (4427144477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3450862871/10000000000 : ℝ)^77 ≤ (26105283291637/100000000000000 : ℝ)^61 := by
    have hnat : (3450862871 : ℕ)^77*100000000000000^61 ≤ 26105283291637^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3450862871 10000000000 26105283291637 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1165007053/2500000000 : ℝ)^77 ≤ (9535610453891/25000000000000 : ℝ)^61 := by
    have hnat : (1165007053 : ℕ)^77*25000000000000^61 ≤ 9535610453891^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1165007053 2500000000 9535610453891 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4427144477/10000000000 : ℝ)^77 ≤ (3575227488133/10000000000000 : ℝ)^61 := by
    have hnat : (4427144477 : ℕ)^77*10000000000000^61 ≤ 3575227488133^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427144477 10000000000 3575227488133 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3450862871/10000000000 : ℝ), (1165007053/2500000000 : ℝ), (4427144477/10000000000 : ℝ)] ![(26105283291637/100000000000000 : ℝ), (9535610453891/25000000000000 : ℝ), (3575227488133/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3450862871/10000000000 : ℝ)|^77 ≤ (26105283291637/100000000000000 : ℝ)^61
        have hw : |(3450862871/10000000000 : ℝ)|=(3450862871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1165007053/2500000000 : ℝ)|^77 ≤ (9535610453891/25000000000000 : ℝ)^61
        have hw : |(1165007053/2500000000 : ℝ)|=(1165007053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4427144477/10000000000 : ℝ)|^77 ≤ (3575227488133/10000000000000 : ℝ)^61
        have hw : |(4427144477/10000000000 : ℝ)|=(4427144477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316083_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((17071/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17071/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((853/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(853/1250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18653/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18653/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31709/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31709/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6163/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6163/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(337/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(337/1000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (17071/25000 : ℝ) ^ (19/4 : ℝ) ≤ (16331084650536382799/100000000000000000000 : ℝ) := by
    have hpowers : (17071/25000 : ℝ)^19 ≤ (16331084650536382799/100000000000000000000 : ℝ)^4 := by
      have hnat : (17071 : ℕ)^19*100000000000000000000^4 ≤ 16331084650536382799^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17071 25000 16331084650536382799 100000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17071/25000 : ℝ)) (X := (16331084650536382799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (116331084650536382799/100000000000000000000 : ℝ) ≤ (5161794307213703/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (116331084650536382799/100000000000000000000 : ℝ)^4 ≤ (5161794307213703/5000000000000000 : ℝ)^19 := by
      have hnat : (116331084650536382799 : ℕ)^4*5000000000000000^19 ≤ 5161794307213703^19*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116331084650536382799 100000000000000000000 5161794307213703 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5161794307213703/5000000000000000 : ℝ)) (X := (116331084650536382799/100000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (66331084650536382799/50000000000000000000 : ℝ) ≤ (10613081361426987/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (66331084650536382799/50000000000000000000 : ℝ)^4 ≤ (10613081361426987/10000000000000000 : ℝ)^19 := by
      have hnat : (66331084650536382799 : ℕ)^4*10000000000000000^19 ≤ 10613081361426987^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66331084650536382799 50000000000000000000 10613081361426987 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10613081361426987/10000000000000000 : ℝ)) (X := (66331084650536382799/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(161794307213703/3414200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(289492746999581/6828400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (17071/25000 : ℝ)) (alpha := (161794307213703/3414200000000000 : ℝ)) (beta := (289492746999581/6828400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17071/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(161794307213703/3414200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(289492746999581/6828400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (853/1250 : ℝ) ^ (19/4 : ℝ) ≤ (1628115969975346593/10000000000000000000 : ℝ) := by
    have hpowers : (853/1250 : ℝ)^19 ≤ (1628115969975346593/10000000000000000000 : ℝ)^4 := by
      have hnat : (853 : ℕ)^19*10000000000000000000^4 ≤ 1628115969975346593^4*1250^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        853 1250 1628115969975346593 10000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (853/1250 : ℝ)) (X := (1628115969975346593/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (11628115969975346593/10000000000000000000 : ℝ) ≤ (2064531143985249/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (11628115969975346593/10000000000000000000 : ℝ)^4 ≤ (2064531143985249/2000000000000000 : ℝ)^19 := by
      have hnat : (11628115969975346593 : ℕ)^4*2000000000000000^19 ≤ 2064531143985249^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11628115969975346593 10000000000000000000 2064531143985249 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2064531143985249/2000000000000000 : ℝ)) (X := (11628115969975346593/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (6628115969975346593/5000000000000000000 : ℝ) ≤ (5305699580963137/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (6628115969975346593/5000000000000000000 : ℝ)^4 ≤ (5305699580963137/5000000000000000 : ℝ)^19 := by
      have hnat : (6628115969975346593 : ℕ)^4*5000000000000000^19 ≤ 5305699580963137^19*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6628115969975346593 5000000000000000000 5305699580963137 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5305699580963137/5000000000000000 : ℝ)) (X := (6628115969975346593/5000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(64531143985249/1364800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(288743442000029/6824000000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (853/1250 : ℝ)) (alpha := (64531143985249/1364800000000000 : ℝ)) (beta := (288743442000029/6824000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (853/1250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(64531143985249/1364800000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(288743442000029/6824000000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (18653/25000 : ℝ) ^ (19/4 : ℝ) ≤ (4975895293819091983/20000000000000000000 : ℝ) := by
    have hpowers : (18653/25000 : ℝ)^19 ≤ (4975895293819091983/20000000000000000000 : ℝ)^4 := by
      have hnat : (18653 : ℕ)^19*20000000000000000000^4 ≤ 4975895293819091983^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18653 25000 4975895293819091983 20000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18653/25000 : ℝ)) (X := (4975895293819091983/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (24975895293819091983/20000000000000000000 : ℝ) ≤ (2095771378547279/2000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (24975895293819091983/20000000000000000000 : ℝ)^4 ≤ (2095771378547279/2000000000000000 : ℝ)^19 := by
      have hnat : (24975895293819091983 : ℕ)^4*2000000000000000^19 ≤ 2095771378547279^19*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24975895293819091983 20000000000000000000 2095771378547279 2000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2095771378547279/2000000000000000 : ℝ)) (X := (24975895293819091983/20000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (14975895293819091983/10000000000000000000 : ℝ) ≤ (10887415539667097/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (14975895293819091983/10000000000000000000 : ℝ)^4 ≤ (10887415539667097/10000000000000000 : ℝ)^19 := by
      have hnat : (14975895293819091983 : ℕ)^4*10000000000000000^19 ≤ 10887415539667097^19*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14975895293819091983 10000000000000000000 10887415539667097 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10887415539667097/10000000000000000 : ℝ)) (X := (14975895293819091983/10000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(95771378547279/1492240000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(204279323465351/3730600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (18653/25000 : ℝ)) (alpha := (95771378547279/1492240000000000 : ℝ)) (beta := (204279323465351/3730600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (18653/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(95771378547279/1492240000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(204279323465351/3730600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-2237076053/10000000000 : ℝ)*X 0 0+(483205907/1000000000 : ℝ)*X 0 1+(5309102241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((13358949/19531250 : ℝ)*X 1 0+(-187113797/2500000000 : ℝ)*X 1 1+(4283677937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((889173217/2500000000 : ℝ)*X 2 0+(321776753/500000000 : ℝ)*X 2 1+(-228927617/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-88996391/400000000 : ℝ)*X 0 0+(4800746993/10000000000 : ℝ)*X 0 1+(5349276381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((651654041/1000000000 : ℝ)*X 1 0+(-914189/1000000000 : ℝ)*X 1 1+(2502641211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((309440099/1000000000 : ℝ)*X 2 0+(7292001089/10000000000 : ℝ)*X 2 1+(-814972787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2882840609/10000000000 : ℝ)*X 0 0+(232519813/500000000 : ℝ)*X 0 1+(494915791/1000000000 : ℝ)*X 0 2+(2882840609/10000000000 : ℝ)*X 1 0+(232519813/500000000 : ℝ)*X 1 1+(494915791/1000000000 : ℝ)*X 1 2+(2882840609/10000000000 : ℝ)*X 2 0+(232519813/500000000 : ℝ)*X 2 1+(494915791/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-164750381/1250000000 : ℝ)*X 0 0+(921549839/2500000000 : ℝ)*X 0 1+(3505806719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((319128341/400000000 : ℝ)*X 1 0+(-127485873/2500000000 : ℝ)*X 1 1+(3064444153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3668577421/10000000000 : ℝ)*X 2 0+(6947344381/10000000000 : ℝ)*X 2 1+(-719575667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((613549167/2500000000 : ℝ)*X 0 0+(74922709/200000000 : ℝ)*X 0 1+(3071790617/5000000000 : ℝ)*X 0 2+(613549167/2500000000 : ℝ)*X 1 0+(74922709/200000000 : ℝ)*X 1 1+(3071790617/5000000000 : ℝ)*X 1 2+(613549167/2500000000 : ℝ)*X 2 0+(74922709/200000000 : ℝ)*X 2 1+(3071790617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-826286691/5000000000 : ℝ)*X 0 0+(5514939019/10000000000 : ℝ)*X 0 1+(253921309/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7467984501/10000000000 : ℝ)*X 1 0+(-2504739/2500000000 : ℝ)*X 1 1+(3934858703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((690527063/2000000000 : ℝ)*X 2 0+(3286573993/5000000000 : ℝ)*X 2 1+(-1112208087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3450862871/10000000000 : ℝ)*X 0 0+(1165007053/2500000000 : ℝ)*X 0 1+(4427144477/10000000000 : ℝ)*X 0 2+(3450862871/10000000000 : ℝ)*X 1 0+(1165007053/2500000000 : ℝ)*X 1 1+(4427144477/10000000000 : ℝ)*X 1 2+(3450862871/10000000000 : ℝ)*X 2 0+(1165007053/2500000000 : ℝ)*X 2 1+(4427144477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316083_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((31709/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31709/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (278625652315381038019693999923/16976052164937500000000000000000000 : ℝ) := by norm_num
    linear_combination (7560843/1000000000000 : ℝ)*(base19) + (20461832059/100000000000 : ℝ)*(base40) + (647837378201/500000000000 : ℝ)*(base49) + (474018722323/1000000000000 : ℝ)*(base60) + (2299061755201/500000000000 : ℝ)*(major_s1_0) + (2299061755201/500000000000 : ℝ)*(major_s1_1) + (2299061755201/500000000000 : ℝ)*(major_s1_2) + (3385556737/1000000000000 : ℝ)*(sp_s1_0) + (1319729443189/200000000000 : ℝ)*(sp_s1_7) + (1650547647127/250000000000 : ℝ)*(sp_s1_8) + (825274768669/125000000000 : ℝ)*(sp_s1_9) + (2593867403627/1000000000000 : ℝ)*(sp_s1_13) + (8799843/50000000000 : ℝ)*(sp_s1_20) + (16537667/100000000000 : ℝ)*(sp_s1_21) + (2594043400487/1000000000000 : ℝ)*(f.failure) + (825274768669/125000000000 : ℝ)*(f.sum) + (31374941648716166163/63644036000000000000000000000000 : ℝ)*base63 + (321722461326301/1865300000000000000000000000 : ℝ)*base65 + (340183525396769/682400000000000000000000000 : ℝ)*base67 + (916148593549043/746120000000000000000000000 : ℝ)*base69 + (571621090516679601/1592126815000000000000000000000 : ℝ)*base70 + (4551173363246661/3414200000000000000000000000 : ℝ)*base73 + (1727502102315571/3412000000000000000000000000 : ℝ)*base75 + (628010357452223/1707100000000000000000000000 : ℝ)*base77 + (2933908005730750771/11649250400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (75841/100000000000000000 : ℝ)*base86 + (75841/100000000000000000 : ℝ)*base88 + (75841/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((6163/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6163/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14535041730376913919314739/1481048200000000000000000000000 : ℝ) := by norm_num
    linear_combination (6041723/500000000000 : ℝ)*(base21) + (83574246393/100000000000 : ℝ)*(base40) + (238899579491/250000000000 : ℝ)*(base49) + (179552286297/250000000000 : ℝ)*(base60) + (3267234664457/1000000000000 : ℝ)*(major_s1_0) + (3267234664457/1000000000000 : ℝ)*(major_s1_1) + (3267234664457/1000000000000 : ℝ)*(major_s1_2) + (9662359/1000000000000 : ℝ)*(sp_s1_1) + (139423/20000000000 : ℝ)*(sp_s1_2) + (4691247079217/1000000000000 : ℝ)*(sp_s1_14) + (4691194666541/1000000000000 : ℝ)*(sp_s1_15) + (234561401231/50000000000 : ℝ)*(sp_s1_16) + (115201186147/62500000000 : ℝ)*(sp_s1_20) + (10687579/250000000000 : ℝ)*(sp_s1_22) + (115201186147/62500000000 : ℝ)*(f.failure) + (4691247079217/1000000000000 : ℝ)*(f.sum) + (8328627474043454309/127288072000000000000000000000000 : ℝ)*base62 + (495355488225713/3730600000000000000000000000 : ℝ)*base64 + (672404326627927/1364800000000000000000000000 : ℝ)*base66 + (184598134845247/1492240000000000000000000000 : ℝ)*base69 + (5590021738729189/74052410000000000000000000000 : ℝ)*base70 + (27711284380559/158800000000000000000000000 : ℝ)*base73 + (2039636892196347/6824000000000000000000000000 : ℝ)*base75 + (7093263562003/79400000000000000000000000 : ℝ)*base76 + (229923821743169/541825600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (2529/6250000000000000 : ℝ)*base87 + (2529/6250000000000000 : ℝ)*base89 + (2529/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(337/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(337/1000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (208748643880223205096694709049/33952104329875000000000000000000000 : ℝ) := by norm_num
    linear_combination (2292843/1000000000000 : ℝ)*(base11) + (785597357727/1000000000000 : ℝ)*(base40) + (658957104429/500000000000 : ℝ)*(base49) + (954999/500000000000 : ℝ)*(base50) + (4931203328213/1000000000000 : ℝ)*(major_s1_0) + (4931203328213/1000000000000 : ℝ)*(major_s1_1) + (4931203328213/1000000000000 : ℝ)*(major_s1_2) + (25997813/250000000000 : ℝ)*(sp_s1_2) + (23622379/1000000000000 : ℝ)*(sp_s1_15) + (417963/12500000000 : ℝ)*(sp_s1_16) + (7080451063569/1000000000000 : ℝ)*(sp_s1_21) + (7080429734033/1000000000000 : ℝ)*(sp_s1_22) + (177007898203/25000000000 : ℝ)*(sp_s1_23) + (695487812641/250000000000 : ℝ)*(sp_s1_27) + (695487812641/250000000000 : ℝ)*(f.failure) + (1770113339103/250000000000 : ℝ)*(f.sum) + (36570941543482688319/127288072000000000000000000000000 : ℝ)*base63 + (1131963810258023/3730600000000000000000000000 : ℝ)*base65 + (1108335066306997/1364800000000000000000000000 : ℝ)*base67 + (597149867377979/1492240000000000000000000000 : ℝ)*base69 + (285570032864235261/3184253630000000000000000000000 : ℝ)*base71 + (3143857740190993/6828400000000000000000000000 : ℝ)*base73 + (4030546459993823/6824000000000000000000000000 : ℝ)*base75 + (1218825307530579/3414200000000000000000000000 : ℝ)*base77 + (11017515635433291023/23298500800000000000000000000000 : ℝ)*base79 + (19263/25000000000000000 : ℝ)*base86 + (19263/25000000000000000 : ℝ)*base88 + (19263/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((17071/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17071/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((853/1250 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(853/1250 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18653/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18653/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((31709/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31709/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((6163/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(6163/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(337/1000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(337/1000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316083_s1 p hpa hpb X hX hprev0

#print axioms solution
