-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306082_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:00:22.12782+00:00
-- url     : https://prove2.me/submissions/6875daac-9283-4d9e-bb75-a207b2e7093f

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
theorem collision_support_c306082_s1_s1_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-378432351/1000000000 : ℝ)*x 0 + (200063469/625000000 : ℝ)*x 1 + (1170444667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (378432351/1000000000 : ℝ)^135 ≤ (27981939353809/100000000000000 : ℝ)^103 := by
    have hnat : (378432351 : ℕ)^135*100000000000000^103 ≤ 27981939353809^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378432351 1000000000 27981939353809 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200063469/625000000 : ℝ)^135 ≤ (11234681915113/50000000000000 : ℝ)^103 := by
    have hnat : (200063469 : ℕ)^135*50000000000000^103 ≤ 11234681915113^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200063469 625000000 11234681915113 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1170444667/2000000000 : ℝ)^135 ≤ (49548696801077/100000000000000 : ℝ)^103 := by
    have hnat : (1170444667 : ℕ)^135*100000000000000^103 ≤ 49548696801077^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170444667 2000000000 49548696801077 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-378432351/1000000000 : ℝ), (200063469/625000000 : ℝ), (1170444667/2000000000 : ℝ)] ![(27981939353809/100000000000000 : ℝ), (11234681915113/50000000000000 : ℝ), (49548696801077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-378432351/1000000000 : ℝ)|^135 ≤ (27981939353809/100000000000000 : ℝ)^103
        have hw : |(-378432351/1000000000 : ℝ)|=(378432351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200063469/625000000 : ℝ)|^135 ≤ (11234681915113/50000000000000 : ℝ)^103
        have hw : |(200063469/625000000 : ℝ)|=(200063469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1170444667/2000000000 : ℝ)|^135 ≤ (49548696801077/100000000000000 : ℝ)^103
        have hw : |(1170444667/2000000000 : ℝ)|=(1170444667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (107548797/250000000 : ℝ)*x 0 + (-3244902979/10000000000 : ℝ)*x 1 + (5347478821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107548797/250000000 : ℝ)^135 ≤ (33101898526151/100000000000000 : ℝ)^103 := by
    have hnat : (107548797 : ℕ)^135*100000000000000^103 ≤ 33101898526151^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107548797 250000000 33101898526151 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3244902979/10000000000 : ℝ)^135 ≤ (11436998376783/50000000000000 : ℝ)^103 := by
    have hnat : (3244902979 : ℕ)^135*50000000000000^103 ≤ 11436998376783^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3244902979 10000000000 11436998376783 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5347478821/10000000000 : ℝ)^135 ≤ (5503013089667/12500000000000 : ℝ)^103 := by
    have hnat : (5347478821 : ℕ)^135*12500000000000^103 ≤ 5503013089667^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347478821 10000000000 5503013089667 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107548797/250000000 : ℝ), (-3244902979/10000000000 : ℝ), (5347478821/10000000000 : ℝ)] ![(33101898526151/100000000000000 : ℝ), (11436998376783/50000000000000 : ℝ), (5503013089667/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107548797/250000000 : ℝ)|^135 ≤ (33101898526151/100000000000000 : ℝ)^103
        have hw : |(107548797/250000000 : ℝ)|=(107548797/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3244902979/10000000000 : ℝ)|^135 ≤ (11436998376783/50000000000000 : ℝ)^103
        have hw : |(-3244902979/10000000000 : ℝ)|=(3244902979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5347478821/10000000000 : ℝ)|^135 ≤ (5503013089667/12500000000000 : ℝ)^103
        have hw : |(5347478821/10000000000 : ℝ)|=(5347478821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3127000707/5000000000 : ℝ)*x 0 + (1300099481/2500000000 : ℝ)*x 1 + (-15502547/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3127000707/5000000000 : ℝ)^135 ≤ (54054071773697/100000000000000 : ℝ)^103 := by
    have hnat : (3127000707 : ℕ)^135*100000000000000^103 ≤ 54054071773697^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3127000707 5000000000 54054071773697 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300099481/2500000000 : ℝ)^135 ≤ (42443865539139/100000000000000 : ℝ)^103 := by
    have hnat : (1300099481 : ℕ)^135*100000000000000^103 ≤ 42443865539139^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300099481 2500000000 42443865539139 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15502547/200000000 : ℝ)^135 ≤ (700412536189/20000000000000 : ℝ)^103 := by
    have hnat : (15502547 : ℕ)^135*20000000000000^103 ≤ 700412536189^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15502547 200000000 700412536189 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3127000707/5000000000 : ℝ), (1300099481/2500000000 : ℝ), (-15502547/200000000 : ℝ)] ![(54054071773697/100000000000000 : ℝ), (42443865539139/100000000000000 : ℝ), (700412536189/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3127000707/5000000000 : ℝ)|^135 ≤ (54054071773697/100000000000000 : ℝ)^103
        have hw : |(3127000707/5000000000 : ℝ)|=(3127000707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1300099481/2500000000 : ℝ)|^135 ≤ (42443865539139/100000000000000 : ℝ)^103
        have hw : |(1300099481/2500000000 : ℝ)|=(1300099481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15502547/200000000 : ℝ)|^135 ≤ (700412536189/20000000000000 : ℝ)^103
        have hw : |(-15502547/200000000 : ℝ)|=(15502547/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3020518617/10000000000 : ℝ)*x 0 + (2502341527/10000000000 : ℝ)*x 1 + (1404218823/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3020518617/10000000000 : ℝ)^135 ≤ (2602935804933/12500000000000 : ℝ)^103 := by
    have hnat : (3020518617 : ℕ)^135*12500000000000^103 ≤ 2602935804933^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3020518617 10000000000 2602935804933 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502341527/10000000000 : ℝ)^135 ≤ (16271407937197/100000000000000 : ℝ)^103 := by
    have hnat : (2502341527 : ℕ)^135*100000000000000^103 ≤ 16271407937197^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502341527 10000000000 16271407937197 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1404218823/2000000000 : ℝ)^135 ≤ (62905105616687/100000000000000 : ℝ)^103 := by
    have hnat : (1404218823 : ℕ)^135*100000000000000^103 ≤ 62905105616687^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404218823 2000000000 62905105616687 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3020518617/10000000000 : ℝ), (2502341527/10000000000 : ℝ), (1404218823/2000000000 : ℝ)] ![(2602935804933/12500000000000 : ℝ), (16271407937197/100000000000000 : ℝ), (62905105616687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3020518617/10000000000 : ℝ)|^135 ≤ (2602935804933/12500000000000 : ℝ)^103
        have hw : |(-3020518617/10000000000 : ℝ)|=(3020518617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2502341527/10000000000 : ℝ)|^135 ≤ (16271407937197/100000000000000 : ℝ)^103
        have hw : |(2502341527/10000000000 : ℝ)|=(2502341527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1404218823/2000000000 : ℝ)|^135 ≤ (62905105616687/100000000000000 : ℝ)^103
        have hw : |(1404218823/2000000000 : ℝ)|=(1404218823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (82988141/200000000 : ℝ)*x 0 + (-196592329/1000000000 : ℝ)*x 1 + (6474698021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82988141/200000000 : ℝ)^135 ≤ (31571999838193/100000000000000 : ℝ)^103 := by
    have hnat : (82988141 : ℕ)^135*100000000000000^103 ≤ 31571999838193^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82988141 200000000 31571999838193 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196592329/1000000000 : ℝ)^135 ≤ (5930101238227/50000000000000 : ℝ)^103 := by
    have hnat : (196592329 : ℕ)^135*50000000000000^103 ≤ 5930101238227^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196592329 1000000000 5930101238227 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6474698021/10000000000 : ℝ)^135 ≤ (56567797673351/100000000000000 : ℝ)^103 := by
    have hnat : (6474698021 : ℕ)^135*100000000000000^103 ≤ 56567797673351^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6474698021 10000000000 56567797673351 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82988141/200000000 : ℝ), (-196592329/1000000000 : ℝ), (6474698021/10000000000 : ℝ)] ![(31571999838193/100000000000000 : ℝ), (5930101238227/50000000000000 : ℝ), (56567797673351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82988141/200000000 : ℝ)|^135 ≤ (31571999838193/100000000000000 : ℝ)^103
        have hw : |(82988141/200000000 : ℝ)|=(82988141/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196592329/1000000000 : ℝ)|^135 ≤ (5930101238227/50000000000000 : ℝ)^103
        have hw : |(-196592329/1000000000 : ℝ)|=(196592329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6474698021/10000000000 : ℝ)|^135 ≤ (56567797673351/100000000000000 : ℝ)^103
        have hw : |(6474698021/10000000000 : ℝ)|=(6474698021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (270581407/500000000 : ℝ)*x 0 + (1581348139/2500000000 : ℝ)*x 1 + (-153170879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270581407/500000000 : ℝ)^135 ≤ (894351772451/2000000000000 : ℝ)^103 := by
    have hnat : (270581407 : ℕ)^135*2000000000000^103 ≤ 894351772451^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270581407 500000000 894351772451 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1581348139/2500000000 : ℝ)^135 ≤ (2194569863223/4000000000000 : ℝ)^103 := by
    have hnat : (1581348139 : ℕ)^135*4000000000000^103 ≤ 2194569863223^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581348139 2500000000 2194569863223 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (153170879/10000000000 : ℝ)^135 ≤ (13067649411/3125000000000 : ℝ)^103 := by
    have hnat : (153170879 : ℕ)^135*3125000000000^103 ≤ 13067649411^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153170879 10000000000 13067649411 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270581407/500000000 : ℝ), (1581348139/2500000000 : ℝ), (-153170879/10000000000 : ℝ)] ![(894351772451/2000000000000 : ℝ), (2194569863223/4000000000000 : ℝ), (13067649411/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270581407/500000000 : ℝ)|^135 ≤ (894351772451/2000000000000 : ℝ)^103
        have hw : |(270581407/500000000 : ℝ)|=(270581407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1581348139/2500000000 : ℝ)|^135 ≤ (2194569863223/4000000000000 : ℝ)^103
        have hw : |(1581348139/2500000000 : ℝ)|=(1581348139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-153170879/10000000000 : ℝ)|^135 ≤ (13067649411/3125000000000 : ℝ)^103
        have hw : |(-153170879/10000000000 : ℝ)|=(153170879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (56831/62500000 : ℝ)*x 0 + (403307327/500000000 : ℝ)*x 1 + (1711745647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56831/62500000 : ℝ)^135 ≤ (5161869523/50000000000000 : ℝ)^103 := by
    have hnat : (56831 : ℕ)^135*50000000000000^103 ≤ 5161869523^103*62500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56831 62500000 5161869523 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403307327/500000000 : ℝ)^135 ≤ (75451724493551/100000000000000 : ℝ)^103 := by
    have hnat : (403307327 : ℕ)^135*100000000000000^103 ≤ 75451724493551^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403307327 500000000 75451724493551 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1711745647/5000000000 : ℝ)^135 ≤ (12268975878067/50000000000000 : ℝ)^103 := by
    have hnat : (1711745647 : ℕ)^135*50000000000000^103 ≤ 12268975878067^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1711745647 5000000000 12268975878067 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56831/62500000 : ℝ), (403307327/500000000 : ℝ), (1711745647/5000000000 : ℝ)] ![(5161869523/50000000000000 : ℝ), (75451724493551/100000000000000 : ℝ), (12268975878067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56831/62500000 : ℝ)|^135 ≤ (5161869523/50000000000000 : ℝ)^103
        have hw : |(56831/62500000 : ℝ)|=(56831/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403307327/500000000 : ℝ)|^135 ≤ (75451724493551/100000000000000 : ℝ)^103
        have hw : |(403307327/500000000 : ℝ)|=(403307327/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1711745647/5000000000 : ℝ)|^135 ≤ (12268975878067/50000000000000 : ℝ)^103
        have hw : |(1711745647/5000000000 : ℝ)|=(1711745647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1562045849/5000000000 : ℝ)*x 0 + (1276231227/5000000000 : ℝ)*x 1 + (3452092161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1562045849/5000000000 : ℝ)^135 ≤ (2720537795001/12500000000000 : ℝ)^103 := by
    have hnat : (1562045849 : ℕ)^135*12500000000000^103 ≤ 2720537795001^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562045849 5000000000 2720537795001 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1276231227/5000000000 : ℝ)^135 ≤ (16699894498087/100000000000000 : ℝ)^103 := by
    have hnat : (1276231227 : ℕ)^135*100000000000000^103 ≤ 16699894498087^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276231227 5000000000 16699894498087 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3452092161/5000000000 : ℝ)^135 ≤ (30767901565459/50000000000000 : ℝ)^103 := by
    have hnat : (3452092161 : ℕ)^135*50000000000000^103 ≤ 30767901565459^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3452092161 5000000000 30767901565459 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1562045849/5000000000 : ℝ), (1276231227/5000000000 : ℝ), (3452092161/5000000000 : ℝ)] ![(2720537795001/12500000000000 : ℝ), (16699894498087/100000000000000 : ℝ), (30767901565459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1562045849/5000000000 : ℝ)|^135 ≤ (2720537795001/12500000000000 : ℝ)^103
        have hw : |(-1562045849/5000000000 : ℝ)|=(1562045849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1276231227/5000000000 : ℝ)|^135 ≤ (16699894498087/100000000000000 : ℝ)^103
        have hw : |(1276231227/5000000000 : ℝ)|=(1276231227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3452092161/5000000000 : ℝ)|^135 ≤ (30767901565459/50000000000000 : ℝ)^103
        have hw : |(3452092161/5000000000 : ℝ)|=(3452092161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (30625223/50000000 : ℝ)*x 0 + (-2829573829/10000000000 : ℝ)*x 1 + (190786789/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30625223/50000000 : ℝ)^135 ≤ (13149476104729/25000000000000 : ℝ)^103 := by
    have hnat : (30625223 : ℕ)^135*25000000000000^103 ≤ 13149476104729^103*50000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30625223 50000000 13149476104729 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829573829/10000000000 : ℝ)^135 ≤ (4778833959053/25000000000000 : ℝ)^103 := by
    have hnat : (2829573829 : ℕ)^135*25000000000000^103 ≤ 4778833959053^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829573829 10000000000 4778833959053 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190786789/500000000 : ℝ)^135 ≤ (1767922482667/6250000000000 : ℝ)^103 := by
    have hnat : (190786789 : ℕ)^135*6250000000000^103 ≤ 1767922482667^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190786789 500000000 1767922482667 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30625223/50000000 : ℝ), (-2829573829/10000000000 : ℝ), (190786789/500000000 : ℝ)] ![(13149476104729/25000000000000 : ℝ), (4778833959053/25000000000000 : ℝ), (1767922482667/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30625223/50000000 : ℝ)|^135 ≤ (13149476104729/25000000000000 : ℝ)^103
        have hw : |(30625223/50000000 : ℝ)|=(30625223/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2829573829/10000000000 : ℝ)|^135 ≤ (4778833959053/25000000000000 : ℝ)^103
        have hw : |(-2829573829/10000000000 : ℝ)|=(2829573829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190786789/500000000 : ℝ)|^135 ≤ (1767922482667/6250000000000 : ℝ)^103
        have hw : |(190786789/500000000 : ℝ)|=(190786789/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3717168783/5000000000 : ℝ)*x 0 + (6151781/15625000 : ℝ)*x 1 + (-640318573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3717168783/5000000000 : ℝ)^135 ≤ (67801589843221/100000000000000 : ℝ)^103 := by
    have hnat : (3717168783 : ℕ)^135*100000000000000^103 ≤ 67801589843221^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717168783 5000000000 67801589843221 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6151781/15625000 : ℝ)^135 ≤ (2947214743703/10000000000000 : ℝ)^103 := by
    have hnat : (6151781 : ℕ)^135*10000000000000^103 ≤ 2947214743703^103*15625000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6151781 15625000 2947214743703 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640318573/10000000000 : ℝ)^135 ≤ (681565676563/25000000000000 : ℝ)^103 := by
    have hnat : (640318573 : ℕ)^135*25000000000000^103 ≤ 681565676563^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640318573 10000000000 681565676563 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3717168783/5000000000 : ℝ), (6151781/15625000 : ℝ), (-640318573/10000000000 : ℝ)] ![(67801589843221/100000000000000 : ℝ), (2947214743703/10000000000000 : ℝ), (681565676563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3717168783/5000000000 : ℝ)|^135 ≤ (67801589843221/100000000000000 : ℝ)^103
        have hw : |(3717168783/5000000000 : ℝ)|=(3717168783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6151781/15625000 : ℝ)|^135 ≤ (2947214743703/10000000000000 : ℝ)^103
        have hw : |(6151781/15625000 : ℝ)|=(6151781/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-640318573/10000000000 : ℝ)|^135 ≤ (681565676563/25000000000000 : ℝ)^103
        have hw : |(-640318573/10000000000 : ℝ)|=(640318573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-22272307/10000000000 : ℝ)*x 0 + (4559961949/10000000000 : ℝ)*x 1 + (7134376973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22272307/10000000000 : ℝ)^135 ≤ (33401804357/100000000000000 : ℝ)^103 := by
    have hnat : (22272307 : ℕ)^135*100000000000000^103 ≤ 33401804357^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22272307 10000000000 33401804357 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4559961949/10000000000 : ℝ)^135 ≤ (7145578887141/20000000000000 : ℝ)^103 := by
    have hnat : (4559961949 : ℕ)^135*20000000000000^103 ≤ 7145578887141^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4559961949 10000000000 7145578887141 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7134376973/10000000000 : ℝ)^135 ≤ (6423870374543/10000000000000 : ℝ)^103 := by
    have hnat : (7134376973 : ℕ)^135*10000000000000^103 ≤ 6423870374543^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7134376973 10000000000 6423870374543 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22272307/10000000000 : ℝ), (4559961949/10000000000 : ℝ), (7134376973/10000000000 : ℝ)] ![(33401804357/100000000000000 : ℝ), (7145578887141/20000000000000 : ℝ), (6423870374543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22272307/10000000000 : ℝ)|^135 ≤ (33401804357/100000000000000 : ℝ)^103
        have hw : |(-22272307/10000000000 : ℝ)|=(22272307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4559961949/10000000000 : ℝ)|^135 ≤ (7145578887141/20000000000000 : ℝ)^103
        have hw : |(4559961949/10000000000 : ℝ)|=(4559961949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7134376973/10000000000 : ℝ)|^135 ≤ (6423870374543/10000000000000 : ℝ)^103
        have hw : |(7134376973/10000000000 : ℝ)|=(7134376973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-4475873427/10000000000 : ℝ)*x 0 + (1932112761/5000000000 : ℝ)*x 1 + (4622775737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4475873427/10000000000 : ℝ)^135 ≤ (17433422298379/50000000000000 : ℝ)^103 := by
    have hnat : (4475873427 : ℕ)^135*50000000000000^103 ≤ 17433422298379^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475873427 10000000000 17433422298379 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932112761/5000000000 : ℝ)^135 ≤ (28758828530917/100000000000000 : ℝ)^103 := by
    have hnat : (1932112761 : ℕ)^135*100000000000000^103 ≤ 28758828530917^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932112761 5000000000 28758828530917 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4622775737/10000000000 : ℝ)^135 ≤ (7274865371849/20000000000000 : ℝ)^103 := by
    have hnat : (4622775737 : ℕ)^135*20000000000000^103 ≤ 7274865371849^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4622775737 10000000000 7274865371849 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4475873427/10000000000 : ℝ), (1932112761/5000000000 : ℝ), (4622775737/10000000000 : ℝ)] ![(17433422298379/50000000000000 : ℝ), (28758828530917/100000000000000 : ℝ), (7274865371849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4475873427/10000000000 : ℝ)|^135 ≤ (17433422298379/50000000000000 : ℝ)^103
        have hw : |(-4475873427/10000000000 : ℝ)|=(4475873427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1932112761/5000000000 : ℝ)|^135 ≤ (28758828530917/100000000000000 : ℝ)^103
        have hw : |(1932112761/5000000000 : ℝ)|=(1932112761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4622775737/10000000000 : ℝ)|^135 ≤ (7274865371849/20000000000000 : ℝ)^103
        have hw : |(4622775737/10000000000 : ℝ)|=(4622775737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1178014703/2500000000 : ℝ)*x 0 + (-1729938181/5000000000 : ℝ)*x 1 + (4762478489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1178014703/2500000000 : ℝ)^135 ≤ (9324465338213/25000000000000 : ℝ)^103 := by
    have hnat : (1178014703 : ℕ)^135*25000000000000^103 ≤ 9324465338213^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178014703 2500000000 9324465338213 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1729938181/5000000000 : ℝ)^135 ≤ (6220081973139/25000000000000 : ℝ)^103 := by
    have hnat : (1729938181 : ℕ)^135*25000000000000^103 ≤ 6220081973139^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1729938181 5000000000 6220081973139 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4762478489/10000000000 : ℝ)^135 ≤ (37821810736057/100000000000000 : ℝ)^103 := by
    have hnat : (4762478489 : ℕ)^135*100000000000000^103 ≤ 37821810736057^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4762478489 10000000000 37821810736057 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1178014703/2500000000 : ℝ), (-1729938181/5000000000 : ℝ), (4762478489/10000000000 : ℝ)] ![(9324465338213/25000000000000 : ℝ), (6220081973139/25000000000000 : ℝ), (37821810736057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1178014703/2500000000 : ℝ)|^135 ≤ (9324465338213/25000000000000 : ℝ)^103
        have hw : |(1178014703/2500000000 : ℝ)|=(1178014703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1729938181/5000000000 : ℝ)|^135 ≤ (6220081973139/25000000000000 : ℝ)^103
        have hw : |(-1729938181/5000000000 : ℝ)|=(1729938181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4762478489/10000000000 : ℝ)|^135 ≤ (37821810736057/100000000000000 : ℝ)^103
        have hw : |(4762478489/10000000000 : ℝ)|=(4762478489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7415977379/10000000000 : ℝ)*x 0 + (4025063107/10000000000 : ℝ)*x 1 + (-130223311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7415977379/10000000000 : ℝ)^135 ≤ (67582206067011/100000000000000 : ℝ)^103 := by
    have hnat : (7415977379 : ℕ)^135*100000000000000^103 ≤ 67582206067011^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7415977379 10000000000 67582206067011 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4025063107/10000000000 : ℝ)^135 ≤ (30337768139731/100000000000000 : ℝ)^103 := by
    have hnat : (4025063107 : ℕ)^135*100000000000000^103 ≤ 30337768139731^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025063107 10000000000 30337768139731 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130223311/2500000000 : ℝ)^135 ≤ (520006443933/25000000000000 : ℝ)^103 := by
    have hnat : (130223311 : ℕ)^135*25000000000000^103 ≤ 520006443933^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130223311 2500000000 520006443933 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7415977379/10000000000 : ℝ), (4025063107/10000000000 : ℝ), (-130223311/2500000000 : ℝ)] ![(67582206067011/100000000000000 : ℝ), (30337768139731/100000000000000 : ℝ), (520006443933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7415977379/10000000000 : ℝ)|^135 ≤ (67582206067011/100000000000000 : ℝ)^103
        have hw : |(7415977379/10000000000 : ℝ)|=(7415977379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4025063107/10000000000 : ℝ)|^135 ≤ (30337768139731/100000000000000 : ℝ)^103
        have hw : |(4025063107/10000000000 : ℝ)|=(4025063107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130223311/2500000000 : ℝ)|^135 ≤ (520006443933/25000000000000 : ℝ)^103
        have hw : |(-130223311/2500000000 : ℝ)|=(130223311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306082_s1_s1_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-93333277/10000000000 : ℝ)*x 0 + (893616877/1250000000 : ℝ)*x 1 + (905033/2000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93333277/10000000000 : ℝ)^135 ≤ (54614536949/25000000000000 : ℝ)^103 := by
    have hnat : (93333277 : ℕ)^135*25000000000000^103 ≤ 54614536949^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93333277 10000000000 54614536949 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (893616877/1250000000 : ℝ)^135 ≤ (12882112988533/20000000000000 : ℝ)^103 := by
    have hnat : (893616877 : ℕ)^135*20000000000000^103 ≤ 12882112988533^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893616877 1250000000 12882112988533 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (905033/2000000 : ℝ)^135 ≤ (35370976894731/100000000000000 : ℝ)^103 := by
    have hnat : (905033 : ℕ)^135*100000000000000^103 ≤ 35370976894731^103*2000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905033 2000000 35370976894731 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93333277/10000000000 : ℝ), (893616877/1250000000 : ℝ), (905033/2000000 : ℝ)] ![(54614536949/25000000000000 : ℝ), (12882112988533/20000000000000 : ℝ), (35370976894731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93333277/10000000000 : ℝ)|^135 ≤ (54614536949/25000000000000 : ℝ)^103
        have hw : |(-93333277/10000000000 : ℝ)|=(93333277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(893616877/1250000000 : ℝ)|^135 ≤ (12882112988533/20000000000000 : ℝ)^103
        have hw : |(893616877/1250000000 : ℝ)|=(893616877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(905033/2000000 : ℝ)|^135 ≤ (35370976894731/100000000000000 : ℝ)^103
        have hw : |(905033/2000000 : ℝ)|=(905033/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306082_s1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((41581/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41581/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((47363/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(47363/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(85881/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(85881/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12621/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12621/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((77549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(77549/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(64439/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(64439/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (41581/50000 : ℝ) ^ (67/16 : ℝ) ≤ (46204643615624736461/100000000000000000000 : ℝ) := by
    have hpowers : (41581/50000 : ℝ)^67 ≤ (46204643615624736461/100000000000000000000 : ℝ)^16 := by
      have hnat : (41581 : ℕ)^67*100000000000000000000^16 ≤ 46204643615624736461^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41581 50000 46204643615624736461 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41581/50000 : ℝ)) (X := (46204643615624736461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (146204643615624736461/100000000000000000000 : ℝ) ≤ (10949485464629031/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (146204643615624736461/100000000000000000000 : ℝ)^16 ≤ (10949485464629031/10000000000000000 : ℝ)^67 := by
      have hnat : (146204643615624736461 : ℕ)^16*10000000000000000^67 ≤ 10949485464629031^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        146204643615624736461 100000000000000000000 10949485464629031 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10949485464629031/10000000000000000 : ℝ)) (X := (146204643615624736461/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (96204643615624736461/50000000000000000000 : ℝ) ≤ (467664995454533/400000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (96204643615624736461/50000000000000000000 : ℝ)^16 ≤ (467664995454533/400000000000000 : ℝ)^67 := by
      have hnat : (96204643615624736461 : ℕ)^16*400000000000000^67 ≤ 467664995454533^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96204643615624736461 50000000000000000000 467664995454533 400000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (467664995454533/400000000000000 : ℝ)) (X := (96204643615624736461/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(949485464629031/8316200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(371069710867147/4158100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (41581/50000 : ℝ)) (alpha := (949485464629031/8316200000000000 : ℝ)) (beta := (371069710867147/4158100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (41581/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(949485464629031/8316200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(371069710867147/4158100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (47363/50000 : ℝ) ^ (67/16 : ℝ) ≤ (15940236672285547601/20000000000000000000 : ℝ) := by
    have hpowers : (47363/50000 : ℝ)^67 ≤ (15940236672285547601/20000000000000000000 : ℝ)^16 := by
      have hnat : (47363 : ℕ)^67*20000000000000000000^16 ≤ 15940236672285547601^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47363 50000 15940236672285547601 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47363/50000 : ℝ)) (X := (15940236672285547601/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (35940236672285547601/20000000000000000000 : ℝ) ≤ (5751197579241831/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (35940236672285547601/20000000000000000000 : ℝ)^16 ≤ (5751197579241831/5000000000000000 : ℝ)^67 := by
      have hnat : (35940236672285547601 : ℕ)^16*5000000000000000^67 ≤ 5751197579241831^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35940236672285547601 20000000000000000000 5751197579241831 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5751197579241831/5000000000000000 : ℝ)) (X := (35940236672285547601/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (25940236672285547601/10000000000000000000 : ℝ) ≤ (6278117668997653/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (25940236672285547601/10000000000000000000 : ℝ)^16 ≤ (6278117668997653/5000000000000000 : ℝ)^67 := by
      have hnat : (25940236672285547601 : ℕ)^16*5000000000000000^67 ≤ 6278117668997653^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25940236672285547601 10000000000000000000 6278117668997653 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6278117668997653/5000000000000000 : ℝ)) (X := (25940236672285547601/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(751197579241831/4736300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(263460044877911/2368150000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (47363/50000 : ℝ)) (alpha := (751197579241831/4736300000000000 : ℝ)) (beta := (263460044877911/2368150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (47363/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(751197579241831/4736300000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(263460044877911/2368150000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (85881/100000 : ℝ) ^ (67/16 : ℝ) ≤ (26434072703191640353/50000000000000000000 : ℝ) := by
    have hpowers : (85881/100000 : ℝ)^67 ≤ (26434072703191640353/50000000000000000000 : ℝ)^16 := by
      have hnat : (85881 : ℕ)^67*50000000000000000000^16 ≤ 26434072703191640353^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        85881 100000 26434072703191640353 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (85881/100000 : ℝ)) (X := (26434072703191640353/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (76434072703191640353/50000000000000000000 : ℝ) ≤ (2766661380704021/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (76434072703191640353/50000000000000000000 : ℝ)^16 ≤ (2766661380704021/2500000000000000 : ℝ)^67 := by
      have hnat : (76434072703191640353 : ℕ)^16*2500000000000000^67 ≤ 2766661380704021^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76434072703191640353 50000000000000000000 2766661380704021 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2766661380704021/2500000000000000 : ℝ)) (X := (76434072703191640353/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51434072703191640353/25000000000000000000 : ℝ) ≤ (2376022289592573/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (51434072703191640353/25000000000000000000 : ℝ)^16 ≤ (2376022289592573/2000000000000000 : ℝ)^67 := by
      have hnat : (51434072703191640353 : ℕ)^16*2000000000000000^67 ≤ 2376022289592573^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51434072703191640353 25000000000000000000 2376022289592573 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2376022289592573/2000000000000000 : ℝ)) (X := (51434072703191640353/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(266661380704021/2147025000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(813465925146781/8588100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (85881/100000 : ℝ)) (alpha := (266661380704021/2147025000000000 : ℝ)) (beta := (813465925146781/8588100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (85881/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(266661380704021/2147025000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(813465925146781/8588100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-378432351/1000000000 : ℝ)*X 0 0+(200063469/625000000 : ℝ)*X 0 1+(1170444667/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((107548797/250000000 : ℝ)*X 1 0+(-3244902979/10000000000 : ℝ)*X 1 1+(5347478821/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3127000707/5000000000 : ℝ)*X 2 0+(1300099481/2500000000 : ℝ)*X 2 1+(-15502547/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-3020518617/10000000000 : ℝ)*X 0 0+(2502341527/10000000000 : ℝ)*X 0 1+(1404218823/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((82988141/200000000 : ℝ)*X 1 0+(-196592329/1000000000 : ℝ)*X 1 1+(6474698021/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((270581407/500000000 : ℝ)*X 2 0+(1581348139/2500000000 : ℝ)*X 2 1+(-153170879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((56831/62500000 : ℝ)*X 0 0+(403307327/500000000 : ℝ)*X 0 1+(1711745647/5000000000 : ℝ)*X 0 2+(56831/62500000 : ℝ)*X 1 0+(403307327/500000000 : ℝ)*X 1 1+(1711745647/5000000000 : ℝ)*X 1 2+(56831/62500000 : ℝ)*X 2 0+(403307327/500000000 : ℝ)*X 2 1+(1711745647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1562045849/5000000000 : ℝ)*X 0 0+(1276231227/5000000000 : ℝ)*X 0 1+(3452092161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((30625223/50000000 : ℝ)*X 1 0+(-2829573829/10000000000 : ℝ)*X 1 1+(190786789/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3717168783/5000000000 : ℝ)*X 2 0+(6151781/15625000 : ℝ)*X 2 1+(-640318573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-22272307/10000000000 : ℝ)*X 0 0+(4559961949/10000000000 : ℝ)*X 0 1+(7134376973/10000000000 : ℝ)*X 0 2+(-22272307/10000000000 : ℝ)*X 1 0+(4559961949/10000000000 : ℝ)*X 1 1+(7134376973/10000000000 : ℝ)*X 1 2+(-22272307/10000000000 : ℝ)*X 2 0+(4559961949/10000000000 : ℝ)*X 2 1+(7134376973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-4475873427/10000000000 : ℝ)*X 0 0+(1932112761/5000000000 : ℝ)*X 0 1+(4622775737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1178014703/2500000000 : ℝ)*X 1 0+(-1729938181/5000000000 : ℝ)*X 1 1+(4762478489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((7415977379/10000000000 : ℝ)*X 2 0+(4025063107/10000000000 : ℝ)*X 2 1+(-130223311/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((-93333277/10000000000 : ℝ)*X 0 0+(893616877/1250000000 : ℝ)*X 0 1+(905033/2000000 : ℝ)*X 0 2+(-93333277/10000000000 : ℝ)*X 1 0+(893616877/1250000000 : ℝ)*X 1 1+(905033/2000000 : ℝ)*X 1 2+(-93333277/10000000000 : ℝ)*X 2 0+(893616877/1250000000 : ℝ)*X 2 1+(905033/2000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306082_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((12621/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12621/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5893226874429741067851929669373/704725495627262500000000000000000000 : ℝ) := by norm_num
    linear_combination (414907809177/1000000000000 : ℝ)*(base7) + (465153/25000000000 : ℝ)*(base19) + (3305061/200000000000 : ℝ)*(base23) + (2802217/500000000000 : ℝ)*(base39) + (231153884663/500000000000 : ℝ)*(base60) + (784706191753/250000000000 : ℝ)*(major_s1_0) + (784706191753/250000000000 : ℝ)*(major_s1_1) + (784706191753/250000000000 : ℝ)*(major_s1_2) + (3062419/200000000000 : ℝ)*(sp_s1_1) + (3984673052233/1000000000000 : ℝ)*(sp_s1_7) + (1992319567009/500000000000 : ℝ)*(sp_s1_8) + (249041032933/62500000000 : ℝ)*(sp_s1_9) + (76581983091/31250000000 : ℝ)*(sp_s1_13) + (23501039/1000000000000 : ℝ)*(sp_s1_27) + (1017869575387/500000000000 : ℝ)*(f.failure) + (3984673052233/1000000000000 : ℝ)*(f.sum) + (7309541366137755173/25422386268750000000000000000000 : ℝ)*base62 + (777171948048289/4294050000000000000000000000 : ℝ)*base64 + (9209588765759/2368150000000000000000000000 : ℝ)*base66 + (1152283894791389/4294050000000000000000000000 : ℝ)*base68 + (20926682897713353923/89275446525000000000000000000000 : ℝ)*base70 + (955331733408023/2079050000000000000000000000 : ℝ)*base72 + (103244443093087/2368150000000000000000000000 : ℝ)*base74 + (255086723042183/2079050000000000000000000000 : ℝ)*base77 + (1237006892527160069/3077188910937500000000000000000 : ℝ)*base78 + (9991/25000000000000000 : ℝ)*base87 + (9991/25000000000000000 : ℝ)*base89 + (9991/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((77549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(77549/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3855466952214992782307/286270000000000000000000000 : ℝ) := by norm_num
    linear_combination (32212073387/1000000000000 : ℝ)*(base1) + (160832824843/200000000000 : ℝ)*(base7) + (8140453/1000000000000 : ℝ)*(base15) + (117006178661/250000000000 : ℝ)*(base60) + (162598819747/50000000000 : ℝ)*(major_s1_0) + (162598819747/50000000000 : ℝ)*(major_s1_1) + (162598819747/50000000000 : ℝ)*(major_s1_2) + (14375963/500000000000 : ℝ)*(sp_s1_0) + (11709517/500000000000 : ℝ)*(sp_s1_2) + (395533/12500000000 : ℝ)*(sp_s1_8) + (3928440350029/1000000000000 : ℝ)*(sp_s1_14) + (155848689819/40000000000 : ℝ)*(sp_s1_15) + (1948116804767/500000000000 : ℝ)*(sp_s1_16) + (720269412273/250000000000 : ℝ)*(sp_s1_20) + (263640699783/125000000000 : ℝ)*(f.failure) + (487032128571/125000000000 : ℝ)*(f.sum) + (269572095793409041/20337909015000000000000000000000 : ℝ)*base63 + (54684175837499/214702500000000000000000000 : ℝ)*base65 + (23074247865641/236815000000000000000000000 : ℝ)*base67 + (16561628032133/214702500000000000000000000 : ℝ)*base68 + (2281923071661954469/17855089305000000000000000000000 : ℝ)*base71 + (29427658676841/207905000000000000000000000 : ℝ)*base73 + (519771377041/29601875000000000000000000 : ℝ)*base74 + (11318430453847/415810000000000000000000000 : ℝ)*base76 + (188808263307368267/9847004515000000000000000000000 : ℝ)*base78 + (4181/6250000000000000 : ℝ)*base86 + (4181/6250000000000000 : ℝ)*base88 + (4181/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(64439/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(64439/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (59830972871040189/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (91131098819/125000000000 : ℝ)*(base7) + (137318347991/500000000000 : ℝ)*(base39) + (4931739/1000000000000 : ℝ)*(base44) + (360307/250000000000 : ℝ)*(base60) + (159194895883/50000000000 : ℝ)*(major_s1_0) + (3183892985921/1000000000000 : ℝ)*(major_s1_1) + (159194895883/50000000000 : ℝ)*(major_s1_2) + (25082559/1000000000000 : ℝ)*(sp_s1_0) + (35937787/1000000000000 : ℝ)*(sp_s1_13) + (100131/4000000000 : ℝ)*(sp_s1_15) + (3850798971799/1000000000000 : ℝ)*(sp_s1_21) + (3850794089869/1000000000000 : ℝ)*(sp_s1_22) + (1925412027179/500000000000 : ℝ)*(sp_s1_23) + (1396990022043/500000000000 : ℝ)*(sp_s1_27) + (2064972123059/1000000000000 : ℝ)*(f.failure) + (1925412027179/500000000000 : ℝ)*(f.sum) + (14787083286874397701/50844772537500000000000000000000 : ℝ)*base63 + (93307409086381/214702500000000000000000000 : ℝ)*base64 + (2383969630125429/4736300000000000000000000000 : ℝ)*base66 + (2326591836331/17176200000000000000000000 : ℝ)*base68 + (42214139799447917/830469270000000000000000000000 : ℝ)*base71 + (153236344459/9670000000000000000000000 : ℝ)*base72 + (988358374435731/2368150000000000000000000000 : ℝ)*base74 + (6001499941843/9670000000000000000000000 : ℝ)*base76 + (1493669336946471777/4580002100000000000000000000000 : ℝ)*base79 + (12513/50000000000000000 : ℝ)*base86 + (12513/50000000000000000 : ℝ)*base88 + (12513/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((41581/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41581/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((47363/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(47363/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(85881/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(85881/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((12621/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12621/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((77549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(77549/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(64439/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(64439/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306082_s1 p hpa hpb X hX hprev0

#print axioms solution
