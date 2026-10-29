-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c327053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:16:50.645378+00:00
-- url     : https://prove2.me/submissions/961579ab-0f7d-4cd4-b2db-e13064b94c05

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
theorem collision_support_c327053_s1_s1_0 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951848989/10000000000 : ℝ)*x 0 + (199474693/400000000 : ℝ)*x 1 + (5010387389/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951848989/10000000000 : ℝ)^91 ≤ (6887232497821/50000000000000 : ℝ)^75 := by
    have hnat : (1951848989 : ℕ)^91*50000000000000^75 ≤ 6887232497821^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951848989 10000000000 6887232497821 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199474693/400000000 : ℝ)^91 ≤ (42989699990521/100000000000000 : ℝ)^75 := by
    have hnat : (199474693 : ℕ)^91*100000000000000^75 ≤ 42989699990521^75*400000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199474693 400000000 42989699990521 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5010387389/10000000000 : ℝ)^91 ≤ (21617917499779/50000000000000 : ℝ)^75 := by
    have hnat : (5010387389 : ℕ)^91*50000000000000^75 ≤ 21617917499779^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010387389 10000000000 21617917499779 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951848989/10000000000 : ℝ), (199474693/400000000 : ℝ), (5010387389/10000000000 : ℝ)] ![(6887232497821/50000000000000 : ℝ), (42989699990521/100000000000000 : ℝ), (21617917499779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951848989/10000000000 : ℝ)|^91 ≤ (6887232497821/50000000000000 : ℝ)^75
        have hw : |(-1951848989/10000000000 : ℝ)|=(1951848989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199474693/400000000 : ℝ)|^91 ≤ (42989699990521/100000000000000 : ℝ)^75
        have hw : |(199474693/400000000 : ℝ)|=(199474693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5010387389/10000000000 : ℝ)|^91 ≤ (21617917499779/50000000000000 : ℝ)^75
        have hw : |(5010387389/10000000000 : ℝ)|=(5010387389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2219520767/5000000000 : ℝ)*x 0 + (-43944863/312500000 : ℝ)*x 1 + (1192872291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2219520767/5000000000 : ℝ)^91 ≤ (9332204527447/25000000000000 : ℝ)^75 := by
    have hnat : (2219520767 : ℕ)^91*25000000000000^75 ≤ 9332204527447^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219520767 5000000000 9332204527447 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43944863/312500000 : ℝ)^91 ≤ (9253594968099/100000000000000 : ℝ)^75 := by
    have hnat : (43944863 : ℕ)^91*100000000000000^75 ≤ 9253594968099^75*312500000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43944863 312500000 9253594968099 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192872291/2000000000 : ℝ)^91 ≤ (26708793454631/50000000000000 : ℝ)^75 := by
    have hnat : (1192872291 : ℕ)^91*50000000000000^75 ≤ 26708793454631^75*2000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192872291 2000000000 26708793454631 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2219520767/5000000000 : ℝ), (-43944863/312500000 : ℝ), (1192872291/2000000000 : ℝ)] ![(9332204527447/25000000000000 : ℝ), (9253594968099/100000000000000 : ℝ), (26708793454631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2219520767/5000000000 : ℝ)|^91 ≤ (9332204527447/25000000000000 : ℝ)^75
        have hw : |(2219520767/5000000000 : ℝ)|=(2219520767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43944863/312500000 : ℝ)|^91 ≤ (9253594968099/100000000000000 : ℝ)^75
        have hw : |(-43944863/312500000 : ℝ)|=(43944863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192872291/2000000000 : ℝ)|^91 ≤ (26708793454631/50000000000000 : ℝ)^75
        have hw : |(1192872291/2000000000 : ℝ)|=(1192872291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_2 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4454717877/10000000000 : ℝ)*x 0 + (1490307721/2500000000 : ℝ)*x 1 + (-1390436587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4454717877/10000000000 : ℝ)^91 ≤ (7497765342289/20000000000000 : ℝ)^75 := by
    have hnat : (4454717877 : ℕ)^91*20000000000000^75 ≤ 7497765342289^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454717877 10000000000 7497765342289 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1490307721/2500000000 : ℝ)^91 ≤ (26691784810971/50000000000000 : ℝ)^75 := by
    have hnat : (1490307721 : ℕ)^91*50000000000000^75 ≤ 26691784810971^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1490307721 2500000000 26691784810971 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390436587/10000000000 : ℝ)^91 ≤ (4563801826979/50000000000000 : ℝ)^75 := by
    have hnat : (1390436587 : ℕ)^91*50000000000000^75 ≤ 4563801826979^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390436587 10000000000 4563801826979 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4454717877/10000000000 : ℝ), (1490307721/2500000000 : ℝ), (-1390436587/10000000000 : ℝ)] ![(7497765342289/20000000000000 : ℝ), (26691784810971/50000000000000 : ℝ), (4563801826979/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4454717877/10000000000 : ℝ)|^91 ≤ (7497765342289/20000000000000 : ℝ)^75
        have hw : |(4454717877/10000000000 : ℝ)|=(4454717877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1490307721/2500000000 : ℝ)|^91 ≤ (26691784810971/50000000000000 : ℝ)^75
        have hw : |(1490307721/2500000000 : ℝ)|=(1490307721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1390436587/10000000000 : ℝ)|^91 ≤ (4563801826979/50000000000000 : ℝ)^75
        have hw : |(-1390436587/10000000000 : ℝ)|=(1390436587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_7 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1933755141/10000000000 : ℝ)*x 0 + (2171143989/5000000000 : ℝ)*x 1 + (565143439/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933755141/10000000000 : ℝ)^91 ≤ (13619687115149/100000000000000 : ℝ)^75 := by
    have hnat : (1933755141 : ℕ)^91*100000000000000^75 ≤ 13619687115149^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933755141 10000000000 13619687115149 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171143989/5000000000 : ℝ)^91 ≤ (36343933428417/100000000000000 : ℝ)^75 := by
    have hnat : (2171143989 : ℕ)^91*100000000000000^75 ≤ 36343933428417^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171143989 5000000000 36343933428417 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565143439/1000000000 : ℝ)^91 ≤ (50036379442537/100000000000000 : ℝ)^75 := by
    have hnat : (565143439 : ℕ)^91*100000000000000^75 ≤ 50036379442537^75*1000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565143439 1000000000 50036379442537 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1933755141/10000000000 : ℝ), (2171143989/5000000000 : ℝ), (565143439/1000000000 : ℝ)] ![(13619687115149/100000000000000 : ℝ), (36343933428417/100000000000000 : ℝ), (50036379442537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1933755141/10000000000 : ℝ)|^91 ≤ (13619687115149/100000000000000 : ℝ)^75
        have hw : |(-1933755141/10000000000 : ℝ)|=(1933755141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2171143989/5000000000 : ℝ)|^91 ≤ (36343933428417/100000000000000 : ℝ)^75
        have hw : |(2171143989/5000000000 : ℝ)|=(2171143989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565143439/1000000000 : ℝ)|^91 ≤ (50036379442537/100000000000000 : ℝ)^75
        have hw : |(565143439/1000000000 : ℝ)|=(565143439/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_8 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2138367681/5000000000 : ℝ)*x 0 + (-154835373/1250000000 : ℝ)*x 1 + (3118169723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138367681/5000000000 : ℝ)^91 ≤ (35679302153403/100000000000000 : ℝ)^75 := by
    have hnat : (2138367681 : ℕ)^91*100000000000000^75 ≤ 35679302153403^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138367681 5000000000 35679302153403 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (154835373/1250000000 : ℝ)^91 ≤ (7933381545571/100000000000000 : ℝ)^75 := by
    have hnat : (154835373 : ℕ)^91*100000000000000^75 ≤ 7933381545571^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      154835373 1250000000 7933381545571 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3118169723/5000000000 : ℝ)^91 ≤ (7048414534817/12500000000000 : ℝ)^75 := by
    have hnat : (3118169723 : ℕ)^91*12500000000000^75 ≤ 7048414534817^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118169723 5000000000 7048414534817 12500000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2138367681/5000000000 : ℝ), (-154835373/1250000000 : ℝ), (3118169723/5000000000 : ℝ)] ![(35679302153403/100000000000000 : ℝ), (7933381545571/100000000000000 : ℝ), (7048414534817/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2138367681/5000000000 : ℝ)|^91 ≤ (35679302153403/100000000000000 : ℝ)^75
        have hw : |(2138367681/5000000000 : ℝ)|=(2138367681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-154835373/1250000000 : ℝ)|^91 ≤ (7933381545571/100000000000000 : ℝ)^75
        have hw : |(-154835373/1250000000 : ℝ)|=(154835373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3118169723/5000000000 : ℝ)|^91 ≤ (7048414534817/12500000000000 : ℝ)^75
        have hw : |(3118169723/5000000000 : ℝ)|=(3118169723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_9 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4292455459/10000000000 : ℝ)*x 0 + (6540077859/10000000000 : ℝ)*x 1 + (-765571919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292455459/10000000000 : ℝ)^91 ≤ (2239905613459/6250000000000 : ℝ)^75 := by
    have hnat : (4292455459 : ℕ)^91*6250000000000^75 ≤ 2239905613459^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292455459 10000000000 2239905613459 6250000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6540077859/10000000000 : ℝ)^91 ≤ (29868307389919/50000000000000 : ℝ)^75 := by
    have hnat : (6540077859 : ℕ)^91*50000000000000^75 ≤ 29868307389919^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6540077859 10000000000 29868307389919 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (765571919/10000000000 : ℝ)^91 ≤ (2212447693277/50000000000000 : ℝ)^75 := by
    have hnat : (765571919 : ℕ)^91*50000000000000^75 ≤ 2212447693277^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765571919 10000000000 2212447693277 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292455459/10000000000 : ℝ), (6540077859/10000000000 : ℝ), (-765571919/10000000000 : ℝ)] ![(2239905613459/6250000000000 : ℝ), (29868307389919/50000000000000 : ℝ), (2212447693277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292455459/10000000000 : ℝ)|^91 ≤ (2239905613459/6250000000000 : ℝ)^75
        have hw : |(4292455459/10000000000 : ℝ)|=(4292455459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6540077859/10000000000 : ℝ)|^91 ≤ (29868307389919/50000000000000 : ℝ)^75
        have hw : |(6540077859/10000000000 : ℝ)|=(6540077859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-765571919/10000000000 : ℝ)|^91 ≤ (2212447693277/50000000000000 : ℝ)^75
        have hw : |(-765571919/10000000000 : ℝ)|=(765571919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_13 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7103785677/10000000000 : ℝ)*x 0 + (393037413/1250000000 : ℝ)*x 1 + (1423824503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7103785677/10000000000 : ℝ)^91 ≤ (3302004716319/5000000000000 : ℝ)^75 := by
    have hnat : (7103785677 : ℕ)^91*5000000000000^75 ≤ 3302004716319^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7103785677 10000000000 3302004716319 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (393037413/1250000000 : ℝ)^91 ≤ (24565690384277/100000000000000 : ℝ)^75 := by
    have hnat : (393037413 : ℕ)^91*100000000000000^75 ≤ 24565690384277^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393037413 1250000000 24565690384277 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1423824503/10000000000 : ℝ)^91 ≤ (4697107635191/50000000000000 : ℝ)^75 := by
    have hnat : (1423824503 : ℕ)^91*50000000000000^75 ≤ 4697107635191^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423824503 10000000000 4697107635191 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7103785677/10000000000 : ℝ), (393037413/1250000000 : ℝ), (1423824503/10000000000 : ℝ)] ![(3302004716319/5000000000000 : ℝ), (24565690384277/100000000000000 : ℝ), (4697107635191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7103785677/10000000000 : ℝ)|^91 ≤ (3302004716319/5000000000000 : ℝ)^75
        have hw : |(7103785677/10000000000 : ℝ)|=(7103785677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(393037413/1250000000 : ℝ)|^91 ≤ (24565690384277/100000000000000 : ℝ)^75
        have hw : |(393037413/1250000000 : ℝ)|=(393037413/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1423824503/10000000000 : ℝ)|^91 ≤ (4697107635191/50000000000000 : ℝ)^75
        have hw : |(1423824503/10000000000 : ℝ)|=(1423824503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_14 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-669680411/5000000000 : ℝ)*x 0 + (39047099/80000000 : ℝ)*x 1 + (5591558641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669680411/5000000000 : ℝ)^91 ≤ (4361197437449/50000000000000 : ℝ)^75 := by
    have hnat : (669680411 : ℕ)^91*50000000000000^75 ≤ 4361197437449^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669680411 5000000000 4361197437449 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (39047099/80000000 : ℝ)^91 ≤ (41883714865791/100000000000000 : ℝ)^75 := by
    have hnat : (39047099 : ℕ)^91*100000000000000^75 ≤ 41883714865791^75*80000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39047099 80000000 41883714865791 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5591558641/10000000000 : ℝ)^91 ≤ (49393890252029/100000000000000 : ℝ)^75 := by
    have hnat : (5591558641 : ℕ)^91*100000000000000^75 ≤ 49393890252029^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591558641 10000000000 49393890252029 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-669680411/5000000000 : ℝ), (39047099/80000000 : ℝ), (5591558641/10000000000 : ℝ)] ![(4361197437449/50000000000000 : ℝ), (41883714865791/100000000000000 : ℝ), (49393890252029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-669680411/5000000000 : ℝ)|^91 ≤ (4361197437449/50000000000000 : ℝ)^75
        have hw : |(-669680411/5000000000 : ℝ)|=(669680411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(39047099/80000000 : ℝ)|^91 ≤ (41883714865791/100000000000000 : ℝ)^75
        have hw : |(39047099/80000000 : ℝ)|=(39047099/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5591558641/10000000000 : ℝ)|^91 ≤ (49393890252029/100000000000000 : ℝ)^75
        have hw : |(5591558641/10000000000 : ℝ)|=(5591558641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_15 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2110388323/5000000000 : ℝ)*x 0 + (-63866731/500000000 : ℝ)*x 1 + (6260420167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2110388323/5000000000 : ℝ)^91 ≤ (7022731628851/20000000000000 : ℝ)^75 := by
    have hnat : (2110388323 : ℕ)^91*20000000000000^75 ≤ 7022731628851^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110388323 5000000000 7022731628851 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63866731/500000000 : ℝ)^91 ≤ (8234736031899/100000000000000 : ℝ)^75 := by
    have hnat : (63866731 : ℕ)^91*100000000000000^75 ≤ 8234736031899^75*500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63866731 500000000 8234736031899 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6260420167/10000000000 : ℝ)^91 ≤ (28325802902489/50000000000000 : ℝ)^75 := by
    have hnat : (6260420167 : ℕ)^91*50000000000000^75 ≤ 28325802902489^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6260420167 10000000000 28325802902489 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2110388323/5000000000 : ℝ), (-63866731/500000000 : ℝ), (6260420167/10000000000 : ℝ)] ![(7022731628851/20000000000000 : ℝ), (8234736031899/100000000000000 : ℝ), (28325802902489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2110388323/5000000000 : ℝ)|^91 ≤ (7022731628851/20000000000000 : ℝ)^75
        have hw : |(2110388323/5000000000 : ℝ)|=(2110388323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63866731/500000000 : ℝ)|^91 ≤ (8234736031899/100000000000000 : ℝ)^75
        have hw : |(-63866731/500000000 : ℝ)|=(63866731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6260420167/10000000000 : ℝ)|^91 ≤ (28325802902489/50000000000000 : ℝ)^75
        have hw : |(6260420167/10000000000 : ℝ)|=(6260420167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_16 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5083400547/10000000000 : ℝ)*x 0 + (5754926731/10000000000 : ℝ)*x 1 + (-825444799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5083400547/10000000000 : ℝ)^91 ≤ (44001477062967/100000000000000 : ℝ)^75 := by
    have hnat : (5083400547 : ℕ)^91*100000000000000^75 ≤ 44001477062967^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5083400547 10000000000 44001477062967 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5754926731/10000000000 : ℝ)^91 ≤ (25575156121579/50000000000000 : ℝ)^75 := by
    have hnat : (5754926731 : ℕ)^91*50000000000000^75 ≤ 25575156121579^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5754926731 10000000000 25575156121579 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (825444799/10000000000 : ℝ)^91 ≤ (2424105334929/50000000000000 : ℝ)^75 := by
    have hnat : (825444799 : ℕ)^91*50000000000000^75 ≤ 2424105334929^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825444799 10000000000 2424105334929 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5083400547/10000000000 : ℝ), (5754926731/10000000000 : ℝ), (-825444799/10000000000 : ℝ)] ![(44001477062967/100000000000000 : ℝ), (25575156121579/50000000000000 : ℝ), (2424105334929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5083400547/10000000000 : ℝ)|^91 ≤ (44001477062967/100000000000000 : ℝ)^75
        have hw : |(5083400547/10000000000 : ℝ)|=(5083400547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5754926731/10000000000 : ℝ)|^91 ≤ (25575156121579/50000000000000 : ℝ)^75
        have hw : |(5754926731/10000000000 : ℝ)|=(5754926731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-825444799/10000000000 : ℝ)|^91 ≤ (2424105334929/50000000000000 : ℝ)^75
        have hw : |(-825444799/10000000000 : ℝ)|=(825444799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_20 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3959971801/5000000000 : ℝ)*x 0 + (548359459/2500000000 : ℝ)*x 1 + (168247369/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3959971801/5000000000 : ℝ)^91 ≤ (75355704539229/100000000000000 : ℝ)^75 := by
    have hnat : (3959971801 : ℕ)^91*100000000000000^75 ≤ 75355704539229^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3959971801 5000000000 75355704539229 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548359459/2500000000 : ℝ)^91 ≤ (7934789418349/50000000000000 : ℝ)^75 := by
    have hnat : (548359459 : ℕ)^91*50000000000000^75 ≤ 7934789418349^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548359459 2500000000 7934789418349 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168247369/1250000000 : ℝ)^91 ≤ (8774716608107/100000000000000 : ℝ)^75 := by
    have hnat : (168247369 : ℕ)^91*100000000000000^75 ≤ 8774716608107^75*1250000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168247369 1250000000 8774716608107 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3959971801/5000000000 : ℝ), (548359459/2500000000 : ℝ), (168247369/1250000000 : ℝ)] ![(75355704539229/100000000000000 : ℝ), (7934789418349/50000000000000 : ℝ), (8774716608107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3959971801/5000000000 : ℝ)|^91 ≤ (75355704539229/100000000000000 : ℝ)^75
        have hw : |(3959971801/5000000000 : ℝ)|=(3959971801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548359459/2500000000 : ℝ)|^91 ≤ (7934789418349/50000000000000 : ℝ)^75
        have hw : |(548359459/2500000000 : ℝ)|=(548359459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168247369/1250000000 : ℝ)|^91 ≤ (8774716608107/100000000000000 : ℝ)^75
        have hw : |(168247369/1250000000 : ℝ)|=(168247369/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_21 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1256179607/10000000000 : ℝ)*x 0 + (5230074529/10000000000 : ℝ)*x 1 + (5309178743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1256179607/10000000000 : ℝ)^91 ≤ (4034776171573/50000000000000 : ℝ)^75 := by
    have hnat : (1256179607 : ℕ)^91*50000000000000^75 ≤ 4034776171573^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256179607 10000000000 4034776171573 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230074529/10000000000 : ℝ)^91 ≤ (2277331373479/5000000000000 : ℝ)^75 := by
    have hnat : (5230074529 : ℕ)^91*5000000000000^75 ≤ 2277331373479^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230074529 10000000000 2277331373479 5000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5309178743/10000000000 : ℝ)^91 ≤ (46383820166677/100000000000000 : ℝ)^75 := by
    have hnat : (5309178743 : ℕ)^91*100000000000000^75 ≤ 46383820166677^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309178743 10000000000 46383820166677 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1256179607/10000000000 : ℝ), (5230074529/10000000000 : ℝ), (5309178743/10000000000 : ℝ)] ![(4034776171573/50000000000000 : ℝ), (2277331373479/5000000000000 : ℝ), (46383820166677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1256179607/10000000000 : ℝ)|^91 ≤ (4034776171573/50000000000000 : ℝ)^75
        have hw : |(-1256179607/10000000000 : ℝ)|=(1256179607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230074529/10000000000 : ℝ)|^91 ≤ (2277331373479/5000000000000 : ℝ)^75
        have hw : |(5230074529/10000000000 : ℝ)|=(5230074529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5309178743/10000000000 : ℝ)|^91 ≤ (46383820166677/100000000000000 : ℝ)^75
        have hw : |(5309178743/10000000000 : ℝ)|=(5309178743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_22 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2575432479/5000000000 : ℝ)*x 0 + (-463572381/5000000000 : ℝ)*x 1 + (5620734329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2575432479/5000000000 : ℝ)^91 ≤ (44711022198081/100000000000000 : ℝ)^75 := by
    have hnat : (2575432479 : ℕ)^91*100000000000000^75 ≤ 44711022198081^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575432479 5000000000 44711022198081 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463572381/5000000000 : ℝ)^91 ≤ (558220386191/10000000000000 : ℝ)^75 := by
    have hnat : (463572381 : ℕ)^91*10000000000000^75 ≤ 558220386191^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463572381 5000000000 558220386191 10000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5620734329/10000000000 : ℝ)^91 ≤ (12426693481077/25000000000000 : ℝ)^75 := by
    have hnat : (5620734329 : ℕ)^91*25000000000000^75 ≤ 12426693481077^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620734329 10000000000 12426693481077 25000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2575432479/5000000000 : ℝ), (-463572381/5000000000 : ℝ), (5620734329/10000000000 : ℝ)] ![(44711022198081/100000000000000 : ℝ), (558220386191/10000000000000 : ℝ), (12426693481077/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2575432479/5000000000 : ℝ)|^91 ≤ (44711022198081/100000000000000 : ℝ)^75
        have hw : |(2575432479/5000000000 : ℝ)|=(2575432479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-463572381/5000000000 : ℝ)|^91 ≤ (558220386191/10000000000000 : ℝ)^75
        have hw : |(-463572381/5000000000 : ℝ)|=(463572381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5620734329/10000000000 : ℝ)|^91 ≤ (12426693481077/25000000000000 : ℝ)^75
        have hw : |(5620734329/10000000000 : ℝ)|=(5620734329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_23 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2100535501/5000000000 : ℝ)*x 0 + (6412944427/10000000000 : ℝ)*x 1 + (-542440411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100535501/5000000000 : ℝ)^91 ≤ (34914848306673/100000000000000 : ℝ)^75 := by
    have hnat : (2100535501 : ℕ)^91*100000000000000^75 ≤ 34914848306673^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100535501 5000000000 34914848306673 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6412944427/10000000000 : ℝ)^91 ≤ (29165297385041/50000000000000 : ℝ)^75 := by
    have hnat : (6412944427 : ℕ)^91*50000000000000^75 ≤ 29165297385041^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6412944427 10000000000 29165297385041 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542440411/5000000000 : ℝ)^91 ≤ (6754556915701/100000000000000 : ℝ)^75 := by
    have hnat : (542440411 : ℕ)^91*100000000000000^75 ≤ 6754556915701^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542440411 5000000000 6754556915701 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100535501/5000000000 : ℝ), (6412944427/10000000000 : ℝ), (-542440411/5000000000 : ℝ)] ![(34914848306673/100000000000000 : ℝ), (29165297385041/50000000000000 : ℝ), (6754556915701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100535501/5000000000 : ℝ)|^91 ≤ (34914848306673/100000000000000 : ℝ)^75
        have hw : |(2100535501/5000000000 : ℝ)|=(2100535501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6412944427/10000000000 : ℝ)|^91 ≤ (29165297385041/50000000000000 : ℝ)^75
        have hw : |(6412944427/10000000000 : ℝ)|=(6412944427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542440411/5000000000 : ℝ)|^91 ≤ (6754556915701/100000000000000 : ℝ)^75
        have hw : |(-542440411/5000000000 : ℝ)|=(542440411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c327053_s1_s1_27 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8034435231/10000000000 : ℝ)*x 0 + (846332987/5000000000 : ℝ)*x 1 + (427525347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8034435231/10000000000 : ℝ)^91 ≤ (15335896136997/20000000000000 : ℝ)^75 := by
    have hnat : (8034435231 : ℕ)^91*20000000000000^75 ≤ 15335896136997^75*10000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8034435231 10000000000 15335896136997 20000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846332987/5000000000 : ℝ)^91 ≤ (5793884118443/50000000000000 : ℝ)^75 := by
    have hnat : (846332987 : ℕ)^91*50000000000000^75 ≤ 5793884118443^75*5000000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846332987 5000000000 5793884118443 50000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (427525347/2500000000 : ℝ)^91 ≤ (11732751061573/100000000000000 : ℝ)^75 := by
    have hnat : (427525347 : ℕ)^91*100000000000000^75 ≤ 11732751061573^75*2500000000^91 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427525347 2500000000 11732751061573 100000000000000 91 75 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (91/16 : ℝ)) 91 75 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8034435231/10000000000 : ℝ), (846332987/5000000000 : ℝ), (427525347/2500000000 : ℝ)] ![(15335896136997/20000000000000 : ℝ), (5793884118443/50000000000000 : ℝ), (11732751061573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8034435231/10000000000 : ℝ)|^91 ≤ (15335896136997/20000000000000 : ℝ)^75
        have hw : |(8034435231/10000000000 : ℝ)|=(8034435231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846332987/5000000000 : ℝ)|^91 ≤ (5793884118443/50000000000000 : ℝ)^75
        have hw : |(846332987/5000000000 : ℝ)|=(846332987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(427525347/2500000000 : ℝ)|^91 ≤ (11732751061573/100000000000000 : ℝ)^75
        have hw : |(427525347/2500000000 : ℝ)|=(427525347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c327053_s1 (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((31447/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31447/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63123/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63123/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61439/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61439/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2373/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29643/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29643/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14241/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14241/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (20519/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (20519/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (20519/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
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
  have s1_pow0 : (31447/50000 : ℝ) ^ (89/16 : ℝ) ≤ (3790825297723303219/50000000000000000000 : ℝ) := by
    have hpowers : (31447/50000 : ℝ)^89 ≤ (3790825297723303219/50000000000000000000 : ℝ)^16 := by
      have hnat : (31447 : ℕ)^89*50000000000000000000^16 ≤ 3790825297723303219^16*50000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31447 50000 3790825297723303219 50000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31447/50000 : ℝ)) (X := (3790825297723303219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (53790825297723303219/50000000000000000000 : ℝ) ≤ (506612322114609/500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (53790825297723303219/50000000000000000000 : ℝ)^16 ≤ (506612322114609/500000000000000 : ℝ)^89 := by
      have hnat : (53790825297723303219 : ℕ)^16*500000000000000^89 ≤ 506612322114609^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53790825297723303219 50000000000000000000 506612322114609 500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (506612322114609/500000000000000 : ℝ)) (X := (53790825297723303219/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (28790825297723303219/25000000000000000000 : ℝ) ≤ (10257056801352561/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (28790825297723303219/25000000000000000000 : ℝ)^16 ≤ (10257056801352561/10000000000000000 : ℝ)^89 := by
      have hnat : (28790825297723303219 : ℕ)^16*10000000000000000^89 ≤ 10257056801352561^89*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28790825297723303219 25000000000000000000 10257056801352561 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10257056801352561/10000000000000000 : ℝ)) (X := (28790825297723303219/25000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6612322114609/314470000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(124810359060381/6289400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (31447/50000 : ℝ)) (alpha := (6612322114609/314470000000000 : ℝ)) (beta := (124810359060381/6289400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (31447/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6612322114609/314470000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(124810359060381/6289400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (63123/100000 : ℝ) ^ (89/16 : ℝ) ≤ (1547297035865202669/20000000000000000000 : ℝ) := by
    have hpowers : (63123/100000 : ℝ)^89 ≤ (1547297035865202669/20000000000000000000 : ℝ)^16 := by
      have hnat : (63123 : ℕ)^89*20000000000000000000^16 ≤ 1547297035865202669^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63123 100000 1547297035865202669 20000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63123/100000 : ℝ)) (X := (1547297035865202669/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (21547297035865202669/20000000000000000000 : ℝ) ≤ (10134866490584091/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (21547297035865202669/20000000000000000000 : ℝ)^16 ≤ (10134866490584091/10000000000000000 : ℝ)^89 := by
      have hnat : (21547297035865202669 : ℕ)^16*10000000000000000^89 ≤ 10134866490584091^89*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21547297035865202669 20000000000000000000 10134866490584091 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10134866490584091/10000000000000000 : ℝ)) (X := (21547297035865202669/20000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (11547297035865202669/10000000000000000000 : ℝ) ≤ (2565502421420569/2500000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (11547297035865202669/10000000000000000000 : ℝ)^16 ≤ (2565502421420569/2500000000000000 : ℝ)^89 := by
      have hnat : (11547297035865202669 : ℕ)^16*2500000000000000^89 ≤ 2565502421420569^89*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11547297035865202669 10000000000000000000 2565502421420569 2500000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2565502421420569/2500000000000000 : ℝ)) (X := (11547297035865202669/10000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(134866490584091/6312300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(25428639019637/1262460000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (63123/100000 : ℝ)) (alpha := (134866490584091/6312300000000000 : ℝ)) (beta := (25428639019637/1262460000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (63123/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(134866490584091/6312300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(25428639019637/1262460000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (61439/100000 : ℝ) ^ (89/16 : ℝ) ≤ (6656110446327968349/100000000000000000000 : ℝ) := by
    have hpowers : (61439/100000 : ℝ)^89 ≤ (6656110446327968349/100000000000000000000 : ℝ)^16 := by
      have hnat : (61439 : ℕ)^89*100000000000000000000^16 ≤ 6656110446327968349^16*100000^89 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61439 100000 6656110446327968349 100000000000000000000 89 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61439/100000 : ℝ)) (X := (6656110446327968349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (106656110446327968349/100000000000000000000 : ℝ) ≤ (10116520002972881/10000000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (106656110446327968349/100000000000000000000 : ℝ)^16 ≤ (10116520002972881/10000000000000000 : ℝ)^89 := by
      have hnat : (106656110446327968349 : ℕ)^16*10000000000000000^89 ≤ 10116520002972881^89*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106656110446327968349 100000000000000000000 10116520002972881 10000000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10116520002972881/10000000000000000 : ℝ)) (X := (106656110446327968349/100000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (56656110446327968349/50000000000000000000 : ℝ) ≤ (639201279478977/625000000000000 : ℝ) ^ (89/16 : ℝ) := by
    have hpowers : (56656110446327968349/50000000000000000000 : ℝ)^16 ≤ (639201279478977/625000000000000 : ℝ)^89 := by
      have hnat : (56656110446327968349 : ℕ)^16*625000000000000^89 ≤ 639201279478977^89*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56656110446327968349 50000000000000000000 639201279478977 625000000000000 16 89 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (639201279478977/625000000000000 : ℝ)) (X := (56656110446327968349/50000000000000000000 : ℝ)) (by norm_num) 89 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(116520002972881/6143900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(110700468690751/6143900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (89/16 : ℝ)) (rho := (61439/100000 : ℝ)) (alpha := (116520002972881/6143900000000000 : ℝ)) (beta := (110700468690751/6143900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61439/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(116520002972881/6143900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(110700468690751/6143900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1951848989/10000000000 : ℝ)*X 0 0+(199474693/400000000 : ℝ)*X 0 1+(5010387389/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2219520767/5000000000 : ℝ)*X 1 0+(-43944863/312500000 : ℝ)*X 1 1+(1192872291/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4454717877/10000000000 : ℝ)*X 2 0+(1490307721/2500000000 : ℝ)*X 2 1+(-1390436587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1933755141/10000000000 : ℝ)*X 0 0+(2171143989/5000000000 : ℝ)*X 0 1+(565143439/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2138367681/5000000000 : ℝ)*X 1 0+(-154835373/1250000000 : ℝ)*X 1 1+(3118169723/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4292455459/10000000000 : ℝ)*X 2 0+(6540077859/10000000000 : ℝ)*X 2 1+(-765571919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((7103785677/10000000000 : ℝ)*X 0 0+(393037413/1250000000 : ℝ)*X 0 1+(1423824503/10000000000 : ℝ)*X 0 2+(7103785677/10000000000 : ℝ)*X 1 0+(393037413/1250000000 : ℝ)*X 1 1+(1423824503/10000000000 : ℝ)*X 1 2+(7103785677/10000000000 : ℝ)*X 2 0+(393037413/1250000000 : ℝ)*X 2 1+(1423824503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-669680411/5000000000 : ℝ)*X 0 0+(39047099/80000000 : ℝ)*X 0 1+(5591558641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2110388323/5000000000 : ℝ)*X 1 0+(-63866731/500000000 : ℝ)*X 1 1+(6260420167/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5083400547/10000000000 : ℝ)*X 2 0+(5754926731/10000000000 : ℝ)*X 2 1+(-825444799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3959971801/5000000000 : ℝ)*X 0 0+(548359459/2500000000 : ℝ)*X 0 1+(168247369/1250000000 : ℝ)*X 0 2+(3959971801/5000000000 : ℝ)*X 1 0+(548359459/2500000000 : ℝ)*X 1 1+(168247369/1250000000 : ℝ)*X 1 2+(3959971801/5000000000 : ℝ)*X 2 0+(548359459/2500000000 : ℝ)*X 2 1+(168247369/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1256179607/10000000000 : ℝ)*X 0 0+(5230074529/10000000000 : ℝ)*X 0 1+(5309178743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((2575432479/5000000000 : ℝ)*X 1 0+(-463572381/5000000000 : ℝ)*X 1 1+(5620734329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((2100535501/5000000000 : ℝ)*X 2 0+(6412944427/10000000000 : ℝ)*X 2 1+(-542440411/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((8034435231/10000000000 : ℝ)*X 0 0+(846332987/5000000000 : ℝ)*X 0 1+(427525347/2500000000 : ℝ)*X 0 2+(8034435231/10000000000 : ℝ)*X 1 0+(846332987/5000000000 : ℝ)*X 1 1+(427525347/2500000000 : ℝ)*X 1 2+(8034435231/10000000000 : ℝ)*X 2 0+(846332987/5000000000 : ℝ)*X 2 1+(427525347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c327053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((2373/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29307207922793209484768891225199/2032636592727650000000000000000000000 : ℝ) := by norm_num
    linear_combination (3192019/1000000000000 : ℝ)*(base5) + (6651421/1000000000000 : ℝ)*(base8) + (195060323889/500000000000 : ℝ)*(base49) + (672395608767/500000000000 : ℝ)*(base59) + (7904215034787/1000000000000 : ℝ)*(major_s1_0) + (7904215034787/1000000000000 : ℝ)*(major_s1_1) + (7904215034787/1000000000000 : ℝ)*(major_s1_2) + (249101579/1000000000000 : ℝ)*(sp_s1_0) + (12646743/250000000000 : ℝ)*(sp_s1_1) + (12072912347657/1000000000000 : ℝ)*(sp_s1_7) + (2414623502737/200000000000 : ℝ)*(sp_s1_8) + (2414513483913/200000000000 : ℝ)*(sp_s1_9) + (933813492697/250000000000 : ℝ)*(sp_s1_13) + (603873111/1000000000000 : ℝ)*(sp_s1_23) + (3735257162807/1000000000000 : ℝ)*(f.failure) + (12073168100657/1000000000000 : ℝ)*(f.sum) + (3828414640826126991/16159224987500000000000000000000 : ℝ)*base63 + (5430421563166493/6143900000000000000000000000 : ℝ)*base65 + (72934986733577/420820000000000000000000000 : ℝ)*base67 + (572733505572687/6143900000000000000000000000 : ℝ)*base69 + (80369261286410623031/193207223300000000000000000000000 : ℝ)*base71 + (1199119709255887/6289400000000000000000000000 : ℝ)*base73 + (52742455721009/2104100000000000000000000000 : ℝ)*base75 + (2242634691467/62894000000000000000000000 : ℝ)*base77 + (33341591134691111563/132335265400000000000000000000000 : ℝ)*base78 + (52077/100000000000000000 : ℝ)*base87 + (52077/100000000000000000 : ℝ)*base89 + (52077/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29643/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29643/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7225157681338223789292962049/530022579590000000000000000000000 : ℝ) := by norm_num
    linear_combination (60082090753/125000000000 : ℝ)*(base49) + (182553253599/250000000000 : ℝ)*(base59) + (773042040537/100000000000 : ℝ)*(major_s1_0) + (773042040537/100000000000 : ℝ)*(major_s1_1) + (773042040537/100000000000 : ℝ)*(major_s1_2) + (20485413/1000000000000 : ℝ)*(sp_s1_1) + (9048251/200000000000 : ℝ)*(sp_s1_2) + (89272177/1000000000000 : ℝ)*(sp_s1_7) + (158191527/1000000000000 : ℝ)*(sp_s1_8) + (46123512227/3906250000 : ℝ)*(sp_s1_14) + (2951882431337/250000000000 : ℝ)*(sp_s1_15) + (11807663161033/1000000000000 : ℝ)*(sp_s1_16) + (3653038287151/1000000000000 : ℝ)*(sp_s1_20) + (89577359/1000000000000 : ℝ)*(sp_s1_27) + (3653127864511/1000000000000 : ℝ)*(f.failure) + (11807708402289/1000000000000 : ℝ)*(f.sum) + (3958075482538465329/6463689995000000000000000000000 : ℝ)*base63 + (123792373907201/614390000000000000000000000 : ℝ)*base65 + (138170979859379/210410000000000000000000000 : ℝ)*base67 + (172680409099713/153597500000000000000000000 : ℝ)*base69 + (1258068418673531/1486209410000000000000000000000 : ℝ)*base71 + (39701252804923/48380000000000000000000000 : ℝ)*base73 + (61423598585273/52602500000000000000000000 : ℝ)*base75 + (3948893661791/4838000000000000000000000 : ℝ)*base77 + (493559724096569223/1017963580000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (37221/100000000000000000 : ℝ)*base87 + (37221/100000000000000000 : ℝ)*base89 + (37221/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14241/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14241/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3729455044976427877782993/258547599800000000000000000000 : ℝ) := by norm_num
    linear_combination (261052877359/1000000000000 : ℝ)*(base40) + (312598000511/1000000000000 : ℝ)*(base49) + (699317029711/1000000000000 : ℝ)*(base59) + (3390415464273/500000000000 : ℝ)*(major_s1_0) + (3390415464273/500000000000 : ℝ)*(major_s1_1) + (3390415464273/500000000000 : ℝ)*(major_s1_2) + (12718739/250000000000 : ℝ)*(sp_s1_0) + (1409149/20000000000 : ℝ)*(sp_s1_2) + (35496983/1000000000000 : ℝ)*(sp_s1_16) + (252102693/1000000000000 : ℝ)*(sp_s1_20) + (10357221274957/1000000000000 : ℝ)*(sp_s1_21) + (10357272149913/1000000000000 : ℝ)*(sp_s1_22) + (258929154887/25000000000 : ℝ)*(sp_s1_23) + (3204132796271/1000000000000 : ℝ)*(sp_s1_27) + (801096224741/250000000000 : ℝ)*(f.failure) + (10357272149913/1000000000000 : ℝ)*(f.sum) + (5132586379640167397/16159224987500000000000000000000 : ℝ)*base62 + (454847309454063/767987500000000000000000000 : ℝ)*base65 + (30327279542773/105205000000000000000000000 : ℝ)*base66 + (126843140766241/1535975000000000000000000000 : ℝ)*base68 + (3840489101400562609/96603611650000000000000000000000 : ℝ)*base71 + (1477845519841343/3144700000000000000000000000 : ℝ)*base73 + (85806329839809/1052050000000000000000000000 : ℝ)*base74 + (44426070081331/314470000000000000000000000 : ℝ)*base76 + (15817907072078206347/66167632700000000000000000000000 : ℝ)*base78 + (17751/25000000000000000 : ℝ)*base87 + (17751/25000000000000000 : ℝ)*base89 + (17751/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (89/16 : ℝ) ≤ p) (hpb : p ≤ (91/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (211611/100000 : ℝ) (32523/20000 : ℝ) (20519/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((31447/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(31447/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63123/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63123/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61439/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61439/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2373/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29643/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29643/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14241/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14241/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c327053_s1 p hpa hpb X hX hprev0

#print axioms solution
