-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c320052_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:35:34.306331+00:00
-- url     : https://prove2.me/submissions/11595911-1c15-4ffe-8930-6673653f135c

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
theorem collision_support_c320052_s1_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-966624359/5000000000 : ℝ)*x 0 + (142760609/400000000 : ℝ)*x 1 + (-1639814537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (966624359/5000000000 : ℝ)^41 ≤ (6489878691059/50000000000000 : ℝ)^33 := by
    have hnat : (966624359 : ℕ)^41*50000000000000^33 ≤ 6489878691059^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966624359 5000000000 6489878691059 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142760609/400000000 : ℝ)^41 ≤ (6950487942563/25000000000000 : ℝ)^33 := by
    have hnat : (142760609 : ℕ)^41*25000000000000^33 ≤ 6950487942563^33*400000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142760609 400000000 6950487942563 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1639814537/2500000000 : ℝ)^41 ≤ (14804572707233/25000000000000 : ℝ)^33 := by
    have hnat : (1639814537 : ℕ)^41*25000000000000^33 ≤ 14804572707233^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639814537 2500000000 14804572707233 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-966624359/5000000000 : ℝ), (142760609/400000000 : ℝ), (-1639814537/2500000000 : ℝ)] ![(6489878691059/50000000000000 : ℝ), (6950487942563/25000000000000 : ℝ), (14804572707233/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-966624359/5000000000 : ℝ)|^41 ≤ (6489878691059/50000000000000 : ℝ)^33
        have hw : |(-966624359/5000000000 : ℝ)|=(966624359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142760609/400000000 : ℝ)|^41 ≤ (6950487942563/25000000000000 : ℝ)^33
        have hw : |(142760609/400000000 : ℝ)|=(142760609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1639814537/2500000000 : ℝ)|^41 ≤ (14804572707233/25000000000000 : ℝ)^33
        have hw : |(-1639814537/2500000000 : ℝ)|=(1639814537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (236562213/500000000 : ℝ)*x 0 + (140868887/250000000 : ℝ)*x 1 + (175447279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (236562213/500000000 : ℝ)^41 ≤ (39462220620101/100000000000000 : ℝ)^33 := by
    have hnat : (236562213 : ℕ)^41*100000000000000^33 ≤ 39462220620101^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236562213 500000000 39462220620101 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140868887/250000000 : ℝ)^41 ≤ (24516087212571/50000000000000 : ℝ)^33 := by
    have hnat : (140868887 : ℕ)^41*50000000000000^33 ≤ 24516087212571^33*250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140868887 250000000 24516087212571 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175447279/1000000000 : ℝ)^41 ≤ (11505604950951/100000000000000 : ℝ)^33 := by
    have hnat : (175447279 : ℕ)^41*100000000000000^33 ≤ 11505604950951^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175447279 1000000000 11505604950951 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(236562213/500000000 : ℝ), (140868887/250000000 : ℝ), (175447279/1000000000 : ℝ)] ![(39462220620101/100000000000000 : ℝ), (24516087212571/50000000000000 : ℝ), (11505604950951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(236562213/500000000 : ℝ)|^41 ≤ (39462220620101/100000000000000 : ℝ)^33
        have hw : |(236562213/500000000 : ℝ)|=(236562213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140868887/250000000 : ℝ)|^41 ≤ (24516087212571/50000000000000 : ℝ)^33
        have hw : |(140868887/250000000 : ℝ)|=(140868887/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175447279/1000000000 : ℝ)|^41 ≤ (11505604950951/100000000000000 : ℝ)^33
        have hw : |(175447279/1000000000 : ℝ)|=(175447279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908557193/10000000000 : ℝ)*x 0 + (53090003/156250000 : ℝ)*x 1 + (-3361993819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908557193/10000000000 : ℝ)^41 ≤ (1277411073799/10000000000000 : ℝ)^33 := by
    have hnat : (1908557193 : ℕ)^41*10000000000000^33 ≤ 1277411073799^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908557193 10000000000 1277411073799 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53090003/156250000 : ℝ)^41 ≤ (13077131154879/50000000000000 : ℝ)^33 := by
    have hnat : (53090003 : ℕ)^41*50000000000000^33 ≤ 13077131154879^33*156250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53090003 156250000 13077131154879 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3361993819/5000000000 : ℝ)^41 ≤ (61071626936423/100000000000000 : ℝ)^33 := by
    have hnat : (3361993819 : ℕ)^41*100000000000000^33 ≤ 61071626936423^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3361993819 5000000000 61071626936423 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908557193/10000000000 : ℝ), (53090003/156250000 : ℝ), (-3361993819/5000000000 : ℝ)] ![(1277411073799/10000000000000 : ℝ), (13077131154879/50000000000000 : ℝ), (61071626936423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908557193/10000000000 : ℝ)|^41 ≤ (1277411073799/10000000000000 : ℝ)^33
        have hw : |(-1908557193/10000000000 : ℝ)|=(1908557193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53090003/156250000 : ℝ)|^41 ≤ (13077131154879/50000000000000 : ℝ)^33
        have hw : |(53090003/156250000 : ℝ)|=(53090003/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3361993819/5000000000 : ℝ)|^41 ≤ (61071626936423/100000000000000 : ℝ)^33
        have hw : |(-3361993819/5000000000 : ℝ)|=(3361993819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2239754251/5000000000 : ℝ)*x 0 + (-1309624567/5000000000 : ℝ)*x 1 + (-5183355447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2239754251/5000000000 : ℝ)^41 ≤ (7374119078347/20000000000000 : ℝ)^33 := by
    have hnat : (2239754251 : ℕ)^41*20000000000000^33 ≤ 7374119078347^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239754251 5000000000 7374119078347 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309624567/5000000000 : ℝ)^41 ≤ (9464523785969/50000000000000 : ℝ)^33 := by
    have hnat : (1309624567 : ℕ)^41*50000000000000^33 ≤ 9464523785969^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309624567 5000000000 9464523785969 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183355447/10000000000 : ℝ)^41 ≤ (11050089254677/25000000000000 : ℝ)^33 := by
    have hnat : (5183355447 : ℕ)^41*25000000000000^33 ≤ 11050089254677^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183355447 10000000000 11050089254677 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2239754251/5000000000 : ℝ), (-1309624567/5000000000 : ℝ), (-5183355447/10000000000 : ℝ)] ![(7374119078347/20000000000000 : ℝ), (9464523785969/50000000000000 : ℝ), (11050089254677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2239754251/5000000000 : ℝ)|^41 ≤ (7374119078347/20000000000000 : ℝ)^33
        have hw : |(2239754251/5000000000 : ℝ)|=(2239754251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1309624567/5000000000 : ℝ)|^41 ≤ (9464523785969/50000000000000 : ℝ)^33
        have hw : |(-1309624567/5000000000 : ℝ)|=(1309624567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5183355447/10000000000 : ℝ)|^41 ≤ (11050089254677/25000000000000 : ℝ)^33
        have hw : |(-5183355447/10000000000 : ℝ)|=(5183355447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (289433201/625000000 : ℝ)*x 0 + (3007617311/5000000000 : ℝ)*x 1 + (680729091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (289433201/625000000 : ℝ)^41 ≤ (1537015403887/4000000000000 : ℝ)^33 := by
    have hnat : (289433201 : ℕ)^41*4000000000000^33 ≤ 1537015403887^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289433201 625000000 1537015403887 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3007617311/5000000000 : ℝ)^41 ≤ (53178740036441/100000000000000 : ℝ)^33 := by
    have hnat : (3007617311 : ℕ)^41*100000000000000^33 ≤ 53178740036441^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007617311 5000000000 53178740036441 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680729091/5000000000 : ℝ)^41 ≤ (839587484927/10000000000000 : ℝ)^33 := by
    have hnat : (680729091 : ℕ)^41*10000000000000^33 ≤ 839587484927^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680729091 5000000000 839587484927 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(289433201/625000000 : ℝ), (3007617311/5000000000 : ℝ), (680729091/5000000000 : ℝ)] ![(1537015403887/4000000000000 : ℝ), (53178740036441/100000000000000 : ℝ), (839587484927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(289433201/625000000 : ℝ)|^41 ≤ (1537015403887/4000000000000 : ℝ)^33
        have hw : |(289433201/625000000 : ℝ)|=(289433201/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3007617311/5000000000 : ℝ)|^41 ≤ (53178740036441/100000000000000 : ℝ)^33
        have hw : |(3007617311/5000000000 : ℝ)|=(3007617311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680729091/5000000000 : ℝ)|^41 ≤ (839587484927/10000000000000 : ℝ)^33
        have hw : |(680729091/5000000000 : ℝ)|=(680729091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6470071201/10000000000 : ℝ)*x 0 + (2201192953/5000000000 : ℝ)*x 1 + (-996414053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6470071201/10000000000 : ℝ)^41 ≤ (58219548361623/100000000000000 : ℝ)^33 := by
    have hnat : (6470071201 : ℕ)^41*100000000000000^33 ≤ 58219548361623^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6470071201 10000000000 58219548361623 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2201192953/5000000000 : ℝ)^41 ≤ (18041783774961/50000000000000 : ℝ)^33 := by
    have hnat : (2201192953 : ℕ)^41*50000000000000^33 ≤ 18041783774961^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201192953 5000000000 18041783774961 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (996414053/10000000000 : ℝ)^41 ≤ (1139376814471/20000000000000 : ℝ)^33 := by
    have hnat : (996414053 : ℕ)^41*20000000000000^33 ≤ 1139376814471^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996414053 10000000000 1139376814471 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6470071201/10000000000 : ℝ), (2201192953/5000000000 : ℝ), (-996414053/10000000000 : ℝ)] ![(58219548361623/100000000000000 : ℝ), (18041783774961/50000000000000 : ℝ), (1139376814471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6470071201/10000000000 : ℝ)|^41 ≤ (58219548361623/100000000000000 : ℝ)^33
        have hw : |(6470071201/10000000000 : ℝ)|=(6470071201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2201192953/5000000000 : ℝ)|^41 ≤ (18041783774961/50000000000000 : ℝ)^33
        have hw : |(2201192953/5000000000 : ℝ)|=(2201192953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-996414053/10000000000 : ℝ)|^41 ≤ (1139376814471/20000000000000 : ℝ)^33
        have hw : |(-996414053/10000000000 : ℝ)|=(996414053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-402435063/2500000000 : ℝ)*x 0 + (3627479709/10000000000 : ℝ)*x 1 + (-6743569389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (402435063/2500000000 : ℝ)^41 ≤ (2584605053907/25000000000000 : ℝ)^33 := by
    have hnat : (402435063 : ℕ)^41*25000000000000^33 ≤ 2584605053907^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402435063 2500000000 2584605053907 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3627479709/10000000000 : ℝ)^41 ≤ (28368904517821/100000000000000 : ℝ)^33 := by
    have hnat : (3627479709 : ℕ)^41*100000000000000^33 ≤ 28368904517821^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3627479709 10000000000 28368904517821 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6743569389/10000000000 : ℝ)^41 ≤ (61292675241343/100000000000000 : ℝ)^33 := by
    have hnat : (6743569389 : ℕ)^41*100000000000000^33 ≤ 61292675241343^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6743569389 10000000000 61292675241343 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-402435063/2500000000 : ℝ), (3627479709/10000000000 : ℝ), (-6743569389/10000000000 : ℝ)] ![(2584605053907/25000000000000 : ℝ), (28368904517821/100000000000000 : ℝ), (61292675241343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-402435063/2500000000 : ℝ)|^41 ≤ (2584605053907/25000000000000 : ℝ)^33
        have hw : |(-402435063/2500000000 : ℝ)|=(402435063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3627479709/10000000000 : ℝ)|^41 ≤ (28368904517821/100000000000000 : ℝ)^33
        have hw : |(3627479709/10000000000 : ℝ)|=(3627479709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6743569389/10000000000 : ℝ)|^41 ≤ (61292675241343/100000000000000 : ℝ)^33
        have hw : |(-6743569389/10000000000 : ℝ)|=(6743569389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (550892059/1250000000 : ℝ)*x 0 + (-2760756841/10000000000 : ℝ)*x 1 + (-5132311361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550892059/1250000000 : ℝ)^41 ≤ (36131950619597/100000000000000 : ℝ)^33 := by
    have hnat : (550892059 : ℕ)^41*100000000000000^33 ≤ 36131950619597^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550892059 1250000000 36131950619597 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2760756841/10000000000 : ℝ)^41 ≤ (20207837060093/100000000000000 : ℝ)^33 := by
    have hnat : (2760756841 : ℕ)^41*100000000000000^33 ≤ 20207837060093^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760756841 10000000000 20207837060093 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5132311361/10000000000 : ℝ)^41 ≤ (8732042461363/20000000000000 : ℝ)^33 := by
    have hnat : (5132311361 : ℕ)^41*20000000000000^33 ≤ 8732042461363^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5132311361 10000000000 8732042461363 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(550892059/1250000000 : ℝ), (-2760756841/10000000000 : ℝ), (-5132311361/10000000000 : ℝ)] ![(36131950619597/100000000000000 : ℝ), (20207837060093/100000000000000 : ℝ), (8732042461363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(550892059/1250000000 : ℝ)|^41 ≤ (36131950619597/100000000000000 : ℝ)^33
        have hw : |(550892059/1250000000 : ℝ)|=(550892059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2760756841/10000000000 : ℝ)|^41 ≤ (20207837060093/100000000000000 : ℝ)^33
        have hw : |(-2760756841/10000000000 : ℝ)|=(2760756841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5132311361/10000000000 : ℝ)|^41 ≤ (8732042461363/20000000000000 : ℝ)^33
        have hw : |(-5132311361/10000000000 : ℝ)|=(5132311361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (632629037/1250000000 : ℝ)*x 0 + (2785691953/5000000000 : ℝ)*x 1 + (703349993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (632629037/1250000000 : ℝ)^41 ≤ (21454060599519/50000000000000 : ℝ)^33 := by
    have hnat : (632629037 : ℕ)^41*50000000000000^33 ≤ 21454060599519^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632629037 1250000000 21454060599519 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785691953/5000000000 : ℝ)^41 ≤ (48347985003229/100000000000000 : ℝ)^33 := by
    have hnat : (2785691953 : ℕ)^41*100000000000000^33 ≤ 48347985003229^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785691953 5000000000 48347985003229 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (703349993/5000000000 : ℝ)^41 ≤ (4371946887809/50000000000000 : ℝ)^33 := by
    have hnat : (703349993 : ℕ)^41*50000000000000^33 ≤ 4371946887809^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703349993 5000000000 4371946887809 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(632629037/1250000000 : ℝ), (2785691953/5000000000 : ℝ), (703349993/5000000000 : ℝ)] ![(21454060599519/50000000000000 : ℝ), (48347985003229/100000000000000 : ℝ), (4371946887809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(632629037/1250000000 : ℝ)|^41 ≤ (21454060599519/50000000000000 : ℝ)^33
        have hw : |(632629037/1250000000 : ℝ)|=(632629037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785691953/5000000000 : ℝ)|^41 ≤ (48347985003229/100000000000000 : ℝ)^33
        have hw : |(2785691953/5000000000 : ℝ)|=(2785691953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(703349993/5000000000 : ℝ)|^41 ≤ (4371946887809/50000000000000 : ℝ)^33
        have hw : |(703349993/5000000000 : ℝ)|=(703349993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1757753321/2500000000 : ℝ)*x 0 + (3796082127/10000000000 : ℝ)*x 1 + (-95846001/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1757753321/2500000000 : ℝ)^41 ≤ (16138804544289/25000000000000 : ℝ)^33 := by
    have hnat : (1757753321 : ℕ)^41*25000000000000^33 ≤ 16138804544289^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757753321 2500000000 16138804544289 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3796082127/10000000000 : ℝ)^41 ≤ (6003248855979/20000000000000 : ℝ)^33 := by
    have hnat : (3796082127 : ℕ)^41*20000000000000^33 ≤ 6003248855979^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3796082127 10000000000 6003248855979 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95846001/1000000000 : ℝ)^41 ≤ (5428537538211/100000000000000 : ℝ)^33 := by
    have hnat : (95846001 : ℕ)^41*100000000000000^33 ≤ 5428537538211^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95846001 1000000000 5428537538211 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1757753321/2500000000 : ℝ), (3796082127/10000000000 : ℝ), (-95846001/1000000000 : ℝ)] ![(16138804544289/25000000000000 : ℝ), (6003248855979/20000000000000 : ℝ), (5428537538211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1757753321/2500000000 : ℝ)|^41 ≤ (16138804544289/25000000000000 : ℝ)^33
        have hw : |(1757753321/2500000000 : ℝ)|=(1757753321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3796082127/10000000000 : ℝ)|^41 ≤ (6003248855979/20000000000000 : ℝ)^33
        have hw : |(3796082127/10000000000 : ℝ)|=(3796082127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95846001/1000000000 : ℝ)|^41 ≤ (5428537538211/100000000000000 : ℝ)^33
        have hw : |(-95846001/1000000000 : ℝ)|=(95846001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-297685717/2000000000 : ℝ)*x 0 + (3860866831/10000000000 : ℝ)*x 1 + (-3312942391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (297685717/2000000000 : ℝ)^41 ≤ (375177863483/4000000000000 : ℝ)^33 := by
    have hnat : (297685717 : ℕ)^41*4000000000000^33 ≤ 375177863483^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297685717 2000000000 375177863483 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3860866831/10000000000 : ℝ)^41 ≤ (3831750443551/12500000000000 : ℝ)^33 := by
    have hnat : (3860866831 : ℕ)^41*12500000000000^33 ≤ 3831750443551^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3860866831 10000000000 3831750443551 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3312942391/5000000000 : ℝ)^41 ≤ (7495818730667/12500000000000 : ℝ)^33 := by
    have hnat : (3312942391 : ℕ)^41*12500000000000^33 ≤ 7495818730667^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3312942391 5000000000 7495818730667 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-297685717/2000000000 : ℝ), (3860866831/10000000000 : ℝ), (-3312942391/5000000000 : ℝ)] ![(375177863483/4000000000000 : ℝ), (3831750443551/12500000000000 : ℝ), (7495818730667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-297685717/2000000000 : ℝ)|^41 ≤ (375177863483/4000000000000 : ℝ)^33
        have hw : |(-297685717/2000000000 : ℝ)|=(297685717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3860866831/10000000000 : ℝ)|^41 ≤ (3831750443551/12500000000000 : ℝ)^33
        have hw : |(3860866831/10000000000 : ℝ)|=(3860866831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3312942391/5000000000 : ℝ)|^41 ≤ (7495818730667/12500000000000 : ℝ)^33
        have hw : |(-3312942391/5000000000 : ℝ)|=(3312942391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (628864881/1250000000 : ℝ)*x 0 + (-1336870833/5000000000 : ℝ)*x 1 + (-1147145511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (628864881/1250000000 : ℝ)^41 ≤ (8518230831997/20000000000000 : ℝ)^33 := by
    have hnat : (628864881 : ℕ)^41*20000000000000^33 ≤ 8518230831997^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628864881 1250000000 8518230831997 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1336870833/5000000000 : ℝ)^41 ≤ (9709778288619/50000000000000 : ℝ)^33 := by
    have hnat : (1336870833 : ℕ)^41*50000000000000^33 ≤ 9709778288619^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336870833 5000000000 9709778288619 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147145511/2500000000 : ℝ)^41 ≤ (18994644623879/50000000000000 : ℝ)^33 := by
    have hnat : (1147145511 : ℕ)^41*50000000000000^33 ≤ 18994644623879^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147145511 2500000000 18994644623879 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(628864881/1250000000 : ℝ), (-1336870833/5000000000 : ℝ), (-1147145511/2500000000 : ℝ)] ![(8518230831997/20000000000000 : ℝ), (9709778288619/50000000000000 : ℝ), (18994644623879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(628864881/1250000000 : ℝ)|^41 ≤ (8518230831997/20000000000000 : ℝ)^33
        have hw : |(628864881/1250000000 : ℝ)|=(628864881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1336870833/5000000000 : ℝ)|^41 ≤ (9709778288619/50000000000000 : ℝ)^33
        have hw : |(-1336870833/5000000000 : ℝ)|=(1336870833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1147145511/2500000000 : ℝ)|^41 ≤ (18994644623879/50000000000000 : ℝ)^33
        have hw : |(-1147145511/2500000000 : ℝ)|=(1147145511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4511384341/10000000000 : ℝ)*x 0 + (2904994611/5000000000 : ℝ)*x 1 + (449746589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4511384341/10000000000 : ℝ)^41 ≤ (929921220609/2500000000000 : ℝ)^33 := by
    have hnat : (4511384341 : ℕ)^41*2500000000000^33 ≤ 929921220609^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511384341 10000000000 929921220609 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2904994611/5000000000 : ℝ)^41 ≤ (50933756646501/100000000000000 : ℝ)^33 := by
    have hnat : (2904994611 : ℕ)^41*100000000000000^33 ≤ 50933756646501^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2904994611 5000000000 50933756646501 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449746589/2500000000 : ℝ)^41 ≤ (11869394515993/100000000000000 : ℝ)^33 := by
    have hnat : (449746589 : ℕ)^41*100000000000000^33 ≤ 11869394515993^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449746589 2500000000 11869394515993 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4511384341/10000000000 : ℝ), (2904994611/5000000000 : ℝ), (449746589/2500000000 : ℝ)] ![(929921220609/2500000000000 : ℝ), (50933756646501/100000000000000 : ℝ), (11869394515993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4511384341/10000000000 : ℝ)|^41 ≤ (929921220609/2500000000000 : ℝ)^33
        have hw : |(4511384341/10000000000 : ℝ)|=(4511384341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2904994611/5000000000 : ℝ)|^41 ≤ (50933756646501/100000000000000 : ℝ)^33
        have hw : |(2904994611/5000000000 : ℝ)|=(2904994611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449746589/2500000000 : ℝ)|^41 ≤ (11869394515993/100000000000000 : ℝ)^33
        have hw : |(449746589/2500000000 : ℝ)|=(449746589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320052_s1_s1_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7160954963/10000000000 : ℝ)*x 0 + (3542040261/10000000000 : ℝ)*x 1 + (-1096745941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7160954963/10000000000 : ℝ)^41 ≤ (66040808724631/100000000000000 : ℝ)^33 := by
    have hnat : (7160954963 : ℕ)^41*100000000000000^33 ≤ 66040808724631^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7160954963 10000000000 66040808724631 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3542040261/10000000000 : ℝ)^41 ≤ (27541120978837/100000000000000 : ℝ)^33 := by
    have hnat : (3542040261 : ℕ)^41*100000000000000^33 ≤ 27541120978837^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3542040261 10000000000 27541120978837 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096745941/10000000000 : ℝ)^41 ≤ (200564696361/3125000000000 : ℝ)^33 := by
    have hnat : (1096745941 : ℕ)^41*3125000000000^33 ≤ 200564696361^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096745941 10000000000 200564696361 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7160954963/10000000000 : ℝ), (3542040261/10000000000 : ℝ), (-1096745941/10000000000 : ℝ)] ![(66040808724631/100000000000000 : ℝ), (27541120978837/100000000000000 : ℝ), (200564696361/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7160954963/10000000000 : ℝ)|^41 ≤ (66040808724631/100000000000000 : ℝ)^33
        have hw : |(7160954963/10000000000 : ℝ)|=(7160954963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3542040261/10000000000 : ℝ)|^41 ≤ (27541120978837/100000000000000 : ℝ)^33
        have hw : |(3542040261/10000000000 : ℝ)|=(3542040261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1096745941/10000000000 : ℝ)|^41 ≤ (200564696361/3125000000000 : ℝ)^33
        have hw : |(-1096745941/10000000000 : ℝ)|=(1096745941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320052_s1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((68317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13859/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13859/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5741/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5741/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6341/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6341/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29131/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29131/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3263/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3263/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  have s1_pow0 : (68317/100000 : ℝ) ^ (5 : ℝ) ≤ (3720351237362038749/25000000000000000000 : ℝ) := by
    have hpowers : (68317/100000 : ℝ)^5 ≤ (3720351237362038749/25000000000000000000 : ℝ)^1 := by
      have hnat : (68317 : ℕ)^5*25000000000000000000^1 ≤ 3720351237362038749^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        68317 100000 3720351237362038749 25000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (68317/100000 : ℝ)) (X := (3720351237362038749/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (28720351237362038749/25000000000000000000 : ℝ) ≤ (5140672678584653/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (28720351237362038749/25000000000000000000 : ℝ)^1 ≤ (5140672678584653/5000000000000000 : ℝ)^5 := by
      have hnat : (28720351237362038749 : ℕ)^1*5000000000000000^5 ≤ 5140672678584653^5*25000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28720351237362038749 25000000000000000000 5140672678584653 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5140672678584653/5000000000000000 : ℝ)) (X := (28720351237362038749/25000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (16220351237362038749/12500000000000000000 : ℝ) ≤ (5267445521077231/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (16220351237362038749/12500000000000000000 : ℝ)^1 ≤ (5267445521077231/5000000000000000 : ℝ)^5 := by
      have hnat : (16220351237362038749 : ℕ)^1*5000000000000000^5 ≤ 5267445521077231^5*12500000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16220351237362038749 12500000000000000000 5267445521077231 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5267445521077231/5000000000000000 : ℝ)) (X := (16220351237362038749/12500000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(140672678584653/3415850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(63386421246289/1707925000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (68317/100000 : ℝ)) (alpha := (140672678584653/3415850000000000 : ℝ)) (beta := (63386421246289/1707925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (68317/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(140672678584653/3415850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(63386421246289/1707925000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (13859/20000 : ℝ) ^ (5 : ℝ) ≤ (15977524623090638541/100000000000000000000 : ℝ) := by
    have hpowers : (13859/20000 : ℝ)^5 ≤ (15977524623090638541/100000000000000000000 : ℝ)^1 := by
      have hnat : (13859 : ℕ)^5*100000000000000000000^1 ≤ 15977524623090638541^1*20000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13859 20000 15977524623090638541 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13859/20000 : ℝ)) (X := (15977524623090638541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (115977524623090638541/100000000000000000000 : ℝ) ≤ (412035616623039/400000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (115977524623090638541/100000000000000000000 : ℝ)^1 ≤ (412035616623039/400000000000000 : ℝ)^5 := by
      have hnat : (115977524623090638541 : ℕ)^1*400000000000000^5 ≤ 412035616623039^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115977524623090638541 100000000000000000000 412035616623039 400000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (412035616623039/400000000000000 : ℝ)) (X := (115977524623090638541/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (65977524623090638541/50000000000000000000 : ℝ) ≤ (10570248626549849/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (65977524623090638541/50000000000000000000 : ℝ)^1 ≤ (10570248626549849/10000000000000000 : ℝ)^5 := by
      have hnat : (65977524623090638541 : ℕ)^1*10000000000000000^5 ≤ 10570248626549849^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65977524623090638541 50000000000000000000 10570248626549849 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10570248626549849/10000000000000000 : ℝ)) (X := (65977524623090638541/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(12035616623039/277180000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(134679105486937/3464750000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (13859/20000 : ℝ)) (alpha := (12035616623039/277180000000000 : ℝ)) (beta := (134679105486937/3464750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13859/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(12035616623039/277180000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(134679105486937/3464750000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (5741/10000 : ℝ) ^ (5 : ℝ) ≤ (6236454157912944701/100000000000000000000 : ℝ) := by
    have hpowers : (5741/10000 : ℝ)^5 ≤ (6236454157912944701/100000000000000000000 : ℝ)^1 := by
      have hnat : (5741 : ℕ)^5*100000000000000000000^1 ≤ 6236454157912944701^1*10000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5741 10000 6236454157912944701 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5741/10000 : ℝ)) (X := (6236454157912944701/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (106236454157912944701/100000000000000000000 : ℝ) ≤ (10121729188341071/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (106236454157912944701/100000000000000000000 : ℝ)^1 ≤ (10121729188341071/10000000000000000 : ℝ)^5 := by
      have hnat : (106236454157912944701 : ℕ)^1*10000000000000000^5 ≤ 10121729188341071^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106236454157912944701 100000000000000000000 10121729188341071 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10121729188341071/10000000000000000 : ℝ)) (X := (106236454157912944701/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (56236454157912944701/50000000000000000000 : ℝ) ≤ (10237869397694687/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (56236454157912944701/50000000000000000000 : ℝ)^1 ≤ (10237869397694687/10000000000000000 : ℝ)^5 := by
      have hnat : (56236454157912944701 : ℕ)^1*10000000000000000^5 ≤ 10237869397694687^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56236454157912944701 50000000000000000000 10237869397694687 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10237869397694687/10000000000000000 : ℝ)) (X := (56236454157912944701/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(121729188341071/5741000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(7258763084601/358812500000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (5741/10000 : ℝ)) (alpha := (121729188341071/5741000000000000 : ℝ)) (beta := (7258763084601/358812500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5741/10000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(121729188341071/5741000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(7258763084601/358812500000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-966624359/5000000000 : ℝ)*X 0 0+(142760609/400000000 : ℝ)*X 0 1+(-1639814537/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((236562213/500000000 : ℝ)*X 2 0+(140868887/250000000 : ℝ)*X 2 1+(175447279/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1908557193/10000000000 : ℝ)*X 0 0+(53090003/156250000 : ℝ)*X 0 1+(-3361993819/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2239754251/5000000000 : ℝ)*X 1 0+(-1309624567/5000000000 : ℝ)*X 1 1+(-5183355447/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((289433201/625000000 : ℝ)*X 2 0+(3007617311/5000000000 : ℝ)*X 2 1+(680729091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((6470071201/10000000000 : ℝ)*X 0 0+(2201192953/5000000000 : ℝ)*X 0 1+(-996414053/10000000000 : ℝ)*X 0 2+(6470071201/10000000000 : ℝ)*X 1 0+(2201192953/5000000000 : ℝ)*X 1 1+(-996414053/10000000000 : ℝ)*X 1 2+(6470071201/10000000000 : ℝ)*X 2 0+(2201192953/5000000000 : ℝ)*X 2 1+(-996414053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-402435063/2500000000 : ℝ)*X 0 0+(3627479709/10000000000 : ℝ)*X 0 1+(-6743569389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((550892059/1250000000 : ℝ)*X 1 0+(-2760756841/10000000000 : ℝ)*X 1 1+(-5132311361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((632629037/1250000000 : ℝ)*X 2 0+(2785691953/5000000000 : ℝ)*X 2 1+(703349993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1757753321/2500000000 : ℝ)*X 0 0+(3796082127/10000000000 : ℝ)*X 0 1+(-95846001/1000000000 : ℝ)*X 0 2+(1757753321/2500000000 : ℝ)*X 1 0+(3796082127/10000000000 : ℝ)*X 1 1+(-95846001/1000000000 : ℝ)*X 1 2+(1757753321/2500000000 : ℝ)*X 2 0+(3796082127/10000000000 : ℝ)*X 2 1+(-95846001/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-297685717/2000000000 : ℝ)*X 0 0+(3860866831/10000000000 : ℝ)*X 0 1+(-3312942391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((628864881/1250000000 : ℝ)*X 1 0+(-1336870833/5000000000 : ℝ)*X 1 1+(-1147145511/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4511384341/10000000000 : ℝ)*X 2 0+(2904994611/5000000000 : ℝ)*X 2 1+(449746589/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7160954963/10000000000 : ℝ)*X 0 0+(3542040261/10000000000 : ℝ)*X 0 1+(-1096745941/10000000000 : ℝ)*X 0 2+(7160954963/10000000000 : ℝ)*X 1 0+(3542040261/10000000000 : ℝ)*X 1 1+(-1096745941/10000000000 : ℝ)*X 1 2+(7160954963/10000000000 : ℝ)*X 2 0+(3542040261/10000000000 : ℝ)*X 2 1+(-1096745941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320052_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((6341/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6341/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (246510402305430735293217753/39782259500000000000000000000000 : ℝ) := by norm_num
    linear_combination (9826505937/5000000000 : ℝ)*(base39) + (10711979329/1000000000000 : ℝ)*(base49) + (3248346595943/1000000000000 : ℝ)*(base59) + (13167157160249/1000000000000 : ℝ)*(major_s1_0) + (13167157160249/1000000000000 : ℝ)*(major_s1_1) + (13167157160249/1000000000000 : ℝ)*(major_s1_2) + (51286843/1000000000000 : ℝ)*(sp_s1_0) + (2414996291789/125000000000 : ℝ)*(sp_s1_7) + (19319779663173/1000000000000 : ℝ)*(sp_s1_8) + (1931994987861/100000000000 : ℝ)*(sp_s1_9) + (7014253761053/1000000000000 : ℝ)*(sp_s1_13) + (3687279/100000000000 : ℝ)*(sp_s1_14) + (69707693/250000000000 : ℝ)*(sp_s1_15) + (21723067/200000000000 : ℝ)*(sp_s1_23) + (7014253761053/1000000000000 : ℝ)*(f.failure) + (3864011698789/200000000000 : ℝ)*(f.sum) + (5952873131258269111/79564519000000000000000000000000 : ℝ)*base63 + (190124783599771/1435250000000000000000000000 : ℝ)*base64 + (174190570740911/433093750000000000000000000 : ℝ)*base66 + (948867965656379/5741000000000000000000000000 : ℝ)*base69 + (21007887323256545247/98051974250000000000000000000000 : ℝ)*base70 + (396009385482821/1707925000000000000000000000 : ℝ)*base73 + (47057300241447/277180000000000000000000000 : ℝ)*base75 + (489872851352917/3415850000000000000000000000 : ℝ)*base77 + (388614500749947507/29587665718750000000000000000000 : ℝ)*base78 + (771/2500000000000000 : ℝ)*base86 + (771/2500000000000000 : ℝ)*base88 + (771/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29131/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29131/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (317485934294894537871/35881250000000000000000000 : ℝ) := by norm_num
    linear_combination (2153473064043/1000000000000 : ℝ)*(base39) + (22581557179/1000000000000 : ℝ)*(base49) + (303572723981/100000000000 : ℝ)*(base59) + (1695444001509/125000000000 : ℝ)*(major_s1_0) + (1695444001509/125000000000 : ℝ)*(major_s1_1) + (1695444001509/125000000000 : ℝ)*(major_s1_2) + (748321/10000000000 : ℝ)*(sp_s1_2) + (356884623/1000000000000 : ℝ)*(sp_s1_8) + (3786301/500000000000 : ℝ)*(sp_s1_9) + (159212963683/8000000000 : ℝ)*(sp_s1_14) + (19901327605791/1000000000000 : ℝ)*(sp_s1_15) + (19901602085711/1000000000000 : ℝ)*(sp_s1_16) + (7225416584313/1000000000000 : ℝ)*(sp_s1_20) + (64030039/1000000000000 : ℝ)*(sp_s1_21) + (7225416584313/1000000000000 : ℝ)*(f.failure) + (9950842245207/500000000000 : ℝ)*(f.sum) + (302004177708056673/19891129750000000000000000000000 : ℝ)*base62 + (818900366761463/1435250000000000000000000000 : ℝ)*base64 + (282539580723461/3464750000000000000000000000 : ℝ)*base67 + (72523349051559/179406250000000000000000000 : ℝ)*base68 + (9295541759728072883/49025987125000000000000000000000 : ℝ)*base70 + (346995994874193/1707925000000000000000000000 : ℝ)*base73 + (1217341507873/17323750000000000000000000 : ℝ)*base75 + (533183313243831/3415850000000000000000000000 : ℝ)*base77 + (5926959144496830023/14793832859375000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (909/2500000000000000 : ℝ)*base87 + (909/2500000000000000 : ℝ)*base89 + (909/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3263/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3263/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2589899266886044874962650837/196103948500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6988033/1000000000000 : ℝ)*(base11) + (2185110902653/1000000000000 : ℝ)*(base39) + (39741790061/500000000000 : ℝ)*(base49) + (57029779169/25000000000 : ℝ)*(base59) + (10157554988863/1000000000000 : ℝ)*(major_s1_0) + (10157554988863/1000000000000 : ℝ)*(major_s1_1) + (10157554988863/1000000000000 : ℝ)*(major_s1_2) + (56481009/1000000000000 : ℝ)*(sp_s1_0) + (110147/25000000000 : ℝ)*(sp_s1_2) + (67039363/500000000000 : ℝ)*(sp_s1_9) + (14904028368483/1000000000000 : ℝ)*(sp_s1_21) + (596163673501/40000000000 : ℝ)*(sp_s1_22) + (372598833823/25000000000 : ℝ)*(sp_s1_23) + (5411013737941/1000000000000 : ℝ)*(sp_s1_27) + (5411013737941/1000000000000 : ℝ)*(f.failure) + (596163673501/40000000000 : ℝ)*(f.sum) + (4169180807429487957/79564519000000000000000000000000 : ℝ)*base63 + (46663281351127/1435250000000000000000000000 : ℝ)*base64 + (386451446631053/1732375000000000000000000000 : ℝ)*base66 + (189846229911973/5741000000000000000000000000 : ℝ)*base69 + (3352431108910493767/12256496781250000000000000000000 : ℝ)*base71 + (1710121077699699/3415850000000000000000000000 : ℝ)*base73 + (25037007963797/55436000000000000000000000 : ℝ)*base74 + (1094756016114533/1707925000000000000000000000 : ℝ)*base76 + (19215196806889726889/118350662875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (387/2500000000000000 : ℝ)*base86 + (387/2500000000000000 : ℝ)*base88 + (387/2500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((68317/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68317/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13859/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13859/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-5741/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-5741/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6341/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6341/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29131/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29131/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3263/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3263/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c320052_s1 p hpa hpb X hX hprev0

#print axioms solution
