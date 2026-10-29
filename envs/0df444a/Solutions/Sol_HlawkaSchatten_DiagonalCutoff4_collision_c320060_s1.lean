-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c320060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:36:41.234585+00:00
-- url     : https://prove2.me/submissions/50f8fef1-6e4e-4695-bb94-90b9eb4774f5

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
theorem collision_support_c320060_s1_s1_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-976599797/5000000000 : ℝ)*x 0 + (125228839/312500000 : ℝ)*x 1 + (-1236751887/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (976599797/5000000000 : ℝ)^81 ≤ (3266639339909/25000000000000 : ℝ)^65 := by
    have hnat : (976599797 : ℕ)^81*25000000000000^65 ≤ 3266639339909^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976599797 5000000000 3266639339909 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125228839/312500000 : ℝ)^81 ≤ (15997989351419/50000000000000 : ℝ)^65 := by
    have hnat : (125228839 : ℕ)^81*50000000000000^65 ≤ 15997989351419^65*312500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125228839 312500000 15997989351419 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1236751887/2000000000 : ℝ)^81 ≤ (54937463917599/100000000000000 : ℝ)^65 := by
    have hnat : (1236751887 : ℕ)^81*100000000000000^65 ≤ 54937463917599^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236751887 2000000000 54937463917599 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-976599797/5000000000 : ℝ), (125228839/312500000 : ℝ), (-1236751887/2000000000 : ℝ)] ![(3266639339909/25000000000000 : ℝ), (15997989351419/50000000000000 : ℝ), (54937463917599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-976599797/5000000000 : ℝ)|^81 ≤ (3266639339909/25000000000000 : ℝ)^65
        have hw : |(-976599797/5000000000 : ℝ)|=(976599797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125228839/312500000 : ℝ)|^81 ≤ (15997989351419/50000000000000 : ℝ)^65
        have hw : |(125228839/312500000 : ℝ)|=(125228839/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1236751887/2000000000 : ℝ)|^81 ≤ (54937463917599/100000000000000 : ℝ)^65
        have hw : |(-1236751887/2000000000 : ℝ)|=(1236751887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4639674693/10000000000 : ℝ)*x 0 + (1147599867/2000000000 : ℝ)*x 1 + (1768794937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4639674693/10000000000 : ℝ)^81 ≤ (7681077555801/20000000000000 : ℝ)^65 := by
    have hnat : (4639674693 : ℕ)^81*20000000000000^65 ≤ 7681077555801^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4639674693 10000000000 7681077555801 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1147599867/2000000000 : ℝ)^81 ≤ (25023523729131/50000000000000 : ℝ)^65 := by
    have hnat : (1147599867 : ℕ)^81*50000000000000^65 ≤ 25023523729131^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147599867 2000000000 25023523729131 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1768794937/10000000000 : ℝ)^81 ≤ (11547564751821/100000000000000 : ℝ)^65 := by
    have hnat : (1768794937 : ℕ)^81*100000000000000^65 ≤ 11547564751821^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1768794937 10000000000 11547564751821 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4639674693/10000000000 : ℝ), (1147599867/2000000000 : ℝ), (1768794937/10000000000 : ℝ)] ![(7681077555801/20000000000000 : ℝ), (25023523729131/50000000000000 : ℝ), (11547564751821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4639674693/10000000000 : ℝ)|^81 ≤ (7681077555801/20000000000000 : ℝ)^65
        have hw : |(4639674693/10000000000 : ℝ)|=(4639674693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1147599867/2000000000 : ℝ)|^81 ≤ (25023523729131/50000000000000 : ℝ)^65
        have hw : |(1147599867/2000000000 : ℝ)|=(1147599867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1768794937/10000000000 : ℝ)|^81 ≤ (11547564751821/100000000000000 : ℝ)^65
        have hw : |(1768794937/10000000000 : ℝ)|=(1768794937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3486141459/5000000000 : ℝ)*x 0 + (1979772103/5000000000 : ℝ)*x 1 + (-428333341/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3486141459/5000000000 : ℝ)^81 ≤ (6380007005301/10000000000000 : ℝ)^65 := by
    have hnat : (3486141459 : ℕ)^81*10000000000000^65 ≤ 6380007005301^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3486141459 5000000000 6380007005301 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1979772103/5000000000 : ℝ)^81 ≤ (31521292241399/100000000000000 : ℝ)^65 := by
    have hnat : (1979772103 : ℕ)^81*100000000000000^65 ≤ 31521292241399^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1979772103 5000000000 31521292241399 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428333341/5000000000 : ℝ)^81 ≤ (467863769123/10000000000000 : ℝ)^65 := by
    have hnat : (428333341 : ℕ)^81*10000000000000^65 ≤ 467863769123^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428333341 5000000000 467863769123 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3486141459/5000000000 : ℝ), (1979772103/5000000000 : ℝ), (-428333341/5000000000 : ℝ)] ![(6380007005301/10000000000000 : ℝ), (31521292241399/100000000000000 : ℝ), (467863769123/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3486141459/5000000000 : ℝ)|^81 ≤ (6380007005301/10000000000000 : ℝ)^65
        have hw : |(3486141459/5000000000 : ℝ)|=(3486141459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1979772103/5000000000 : ℝ)|^81 ≤ (31521292241399/100000000000000 : ℝ)^65
        have hw : |(1979772103/5000000000 : ℝ)|=(1979772103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428333341/5000000000 : ℝ)|^81 ≤ (467863769123/10000000000000 : ℝ)^65
        have hw : |(-428333341/5000000000 : ℝ)|=(428333341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-383776317/2000000000 : ℝ)*x 0 + (3898156507/10000000000 : ℝ)*x 1 + (-1261404593/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383776317/2000000000 : ℝ)^81 ≤ (3195271270151/25000000000000 : ℝ)^65 := by
    have hnat : (383776317 : ℕ)^81*25000000000000^65 ≤ 3195271270151^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383776317 2000000000 3195271270151 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3898156507/10000000000 : ℝ)^81 ≤ (15456733251263/50000000000000 : ℝ)^65 := by
    have hnat : (3898156507 : ℕ)^81*50000000000000^65 ≤ 15456733251263^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3898156507 10000000000 15456733251263 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1261404593/2000000000 : ℝ)^81 ≤ (28152724207519/50000000000000 : ℝ)^65 := by
    have hnat : (1261404593 : ℕ)^81*50000000000000^65 ≤ 28152724207519^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261404593 2000000000 28152724207519 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-383776317/2000000000 : ℝ), (3898156507/10000000000 : ℝ), (-1261404593/2000000000 : ℝ)] ![(3195271270151/25000000000000 : ℝ), (15456733251263/50000000000000 : ℝ), (28152724207519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-383776317/2000000000 : ℝ)|^81 ≤ (3195271270151/25000000000000 : ℝ)^65
        have hw : |(-383776317/2000000000 : ℝ)|=(383776317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3898156507/10000000000 : ℝ)|^81 ≤ (15456733251263/50000000000000 : ℝ)^65
        have hw : |(3898156507/10000000000 : ℝ)|=(3898156507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1261404593/2000000000 : ℝ)|^81 ≤ (28152724207519/50000000000000 : ℝ)^65
        have hw : |(-1261404593/2000000000 : ℝ)|=(1261404593/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4381870671/10000000000 : ℝ)*x 0 + (-40677009/200000000 : ℝ)*x 1 + (-5779008559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4381870671/10000000000 : ℝ)^81 ≤ (1788227136571/5000000000000 : ℝ)^65 := by
    have hnat : (4381870671 : ℕ)^81*5000000000000^65 ≤ 1788227136571^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4381870671 10000000000 1788227136571 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40677009/200000000 : ℝ)^81 ≤ (1717786140121/12500000000000 : ℝ)^65 := by
    have hnat : (40677009 : ℕ)^81*12500000000000^65 ≤ 1717786140121^65*200000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40677009 200000000 1717786140121 12500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5779008559/10000000000 : ℝ)^81 ≤ (12623292032237/25000000000000 : ℝ)^65 := by
    have hnat : (5779008559 : ℕ)^81*25000000000000^65 ≤ 12623292032237^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5779008559 10000000000 12623292032237 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4381870671/10000000000 : ℝ), (-40677009/200000000 : ℝ), (-5779008559/10000000000 : ℝ)] ![(1788227136571/5000000000000 : ℝ), (1717786140121/12500000000000 : ℝ), (12623292032237/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4381870671/10000000000 : ℝ)|^81 ≤ (1788227136571/5000000000000 : ℝ)^65
        have hw : |(4381870671/10000000000 : ℝ)|=(4381870671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40677009/200000000 : ℝ)|^81 ≤ (1717786140121/12500000000000 : ℝ)^65
        have hw : |(-40677009/200000000 : ℝ)|=(40677009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5779008559/10000000000 : ℝ)|^81 ≤ (12623292032237/25000000000000 : ℝ)^65
        have hw : |(-5779008559/10000000000 : ℝ)|=(5779008559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4527327481/10000000000 : ℝ)*x 0 + (6144485193/10000000000 : ℝ)*x 1 + (675043559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4527327481/10000000000 : ℝ)^81 ≤ (37249982450597/100000000000000 : ℝ)^65 := by
    have hnat : (4527327481 : ℕ)^81*100000000000000^65 ≤ 37249982450597^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527327481 10000000000 37249982450597 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6144485193/10000000000 : ℝ)^81 ≤ (54502998376107/100000000000000 : ℝ)^65 := by
    have hnat : (6144485193 : ℕ)^81*100000000000000^65 ≤ 54502998376107^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6144485193 10000000000 54502998376107 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675043559/5000000000 : ℝ)^81 ≤ (1649403834129/20000000000000 : ℝ)^65 := by
    have hnat : (675043559 : ℕ)^81*20000000000000^65 ≤ 1649403834129^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675043559 5000000000 1649403834129 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4527327481/10000000000 : ℝ), (6144485193/10000000000 : ℝ), (675043559/5000000000 : ℝ)] ![(37249982450597/100000000000000 : ℝ), (54502998376107/100000000000000 : ℝ), (1649403834129/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4527327481/10000000000 : ℝ)|^81 ≤ (37249982450597/100000000000000 : ℝ)^65
        have hw : |(4527327481/10000000000 : ℝ)|=(4527327481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6144485193/10000000000 : ℝ)|^81 ≤ (54502998376107/100000000000000 : ℝ)^65
        have hw : |(6144485193/10000000000 : ℝ)|=(6144485193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675043559/5000000000 : ℝ)|^81 ≤ (1649403834129/20000000000000 : ℝ)^65
        have hw : |(675043559/5000000000 : ℝ)|=(675043559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1717985653/2500000000 : ℝ)*x 0 + (856102211/2000000000 : ℝ)*x 1 + (-535553341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1717985653/2500000000 : ℝ)^81 ≤ (3132896348767/5000000000000 : ℝ)^65 := by
    have hnat : (1717985653 : ℕ)^81*5000000000000^65 ≤ 3132896348767^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717985653 2500000000 3132896348767 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (856102211/2000000000 : ℝ)^81 ≤ (34736563656483/100000000000000 : ℝ)^65 := by
    have hnat : (856102211 : ℕ)^81*100000000000000^65 ≤ 34736563656483^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856102211 2000000000 34736563656483 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535553341/10000000000 : ℝ)^81 ≤ (1302754676399/50000000000000 : ℝ)^65 := by
    have hnat : (535553341 : ℕ)^81*50000000000000^65 ≤ 1302754676399^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535553341 10000000000 1302754676399 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1717985653/2500000000 : ℝ), (856102211/2000000000 : ℝ), (-535553341/10000000000 : ℝ)] ![(3132896348767/5000000000000 : ℝ), (34736563656483/100000000000000 : ℝ), (1302754676399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1717985653/2500000000 : ℝ)|^81 ≤ (3132896348767/5000000000000 : ℝ)^65
        have hw : |(1717985653/2500000000 : ℝ)|=(1717985653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(856102211/2000000000 : ℝ)|^81 ≤ (34736563656483/100000000000000 : ℝ)^65
        have hw : |(856102211/2000000000 : ℝ)|=(856102211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535553341/10000000000 : ℝ)|^81 ≤ (1302754676399/50000000000000 : ℝ)^65
        have hw : |(-535553341/10000000000 : ℝ)|=(535553341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1614302919/10000000000 : ℝ)*x 0 + (4137959621/10000000000 : ℝ)*x 1 + (-6315029059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614302919/10000000000 : ℝ)^81 ≤ (5152256856119/50000000000000 : ℝ)^65 := by
    have hnat : (1614302919 : ℕ)^81*50000000000000^65 ≤ 5152256856119^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614302919 10000000000 5152256856119 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137959621/10000000000 : ℝ)^81 ≤ (33300956629591/100000000000000 : ℝ)^65 := by
    have hnat : (4137959621 : ℕ)^81*100000000000000^65 ≤ 33300956629591^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137959621 10000000000 33300956629591 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6315029059/10000000000 : ℝ)^81 ≤ (56394529640023/100000000000000 : ℝ)^65 := by
    have hnat : (6315029059 : ℕ)^81*100000000000000^65 ≤ 56394529640023^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6315029059 10000000000 56394529640023 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1614302919/10000000000 : ℝ), (4137959621/10000000000 : ℝ), (-6315029059/10000000000 : ℝ)] ![(5152256856119/50000000000000 : ℝ), (33300956629591/100000000000000 : ℝ), (56394529640023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1614302919/10000000000 : ℝ)|^81 ≤ (5152256856119/50000000000000 : ℝ)^65
        have hw : |(-1614302919/10000000000 : ℝ)|=(1614302919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137959621/10000000000 : ℝ)|^81 ≤ (33300956629591/100000000000000 : ℝ)^65
        have hw : |(4137959621/10000000000 : ℝ)|=(4137959621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6315029059/10000000000 : ℝ)|^81 ≤ (56394529640023/100000000000000 : ℝ)^65
        have hw : |(-6315029059/10000000000 : ℝ)|=(6315029059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (867973433/2000000000 : ℝ)*x 0 + (-1070498523/5000000000 : ℝ)*x 1 + (-5734768521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (867973433/2000000000 : ℝ)^81 ≤ (17668914603117/50000000000000 : ℝ)^65 := by
    have hnat : (867973433 : ℕ)^81*50000000000000^65 ≤ 17668914603117^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      867973433 2000000000 17668914603117 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070498523/5000000000 : ℝ)^81 ≤ (14650236604299/100000000000000 : ℝ)^65 := by
    have hnat : (1070498523 : ℕ)^81*100000000000000^65 ≤ 14650236604299^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070498523 5000000000 14650236604299 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5734768521/10000000000 : ℝ)^81 ≤ (10002386834281/20000000000000 : ℝ)^65 := by
    have hnat : (5734768521 : ℕ)^81*20000000000000^65 ≤ 10002386834281^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5734768521 10000000000 10002386834281 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(867973433/2000000000 : ℝ), (-1070498523/5000000000 : ℝ), (-5734768521/10000000000 : ℝ)] ![(17668914603117/50000000000000 : ℝ), (14650236604299/100000000000000 : ℝ), (10002386834281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(867973433/2000000000 : ℝ)|^81 ≤ (17668914603117/50000000000000 : ℝ)^65
        have hw : |(867973433/2000000000 : ℝ)|=(867973433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070498523/5000000000 : ℝ)|^81 ≤ (14650236604299/100000000000000 : ℝ)^65
        have hw : |(-1070498523/5000000000 : ℝ)|=(1070498523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5734768521/10000000000 : ℝ)|^81 ≤ (10002386834281/20000000000000 : ℝ)^65
        have hw : |(-5734768521/10000000000 : ℝ)|=(5734768521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4985696219/10000000000 : ℝ)*x 0 + (1419783483/2500000000 : ℝ)*x 1 + (697163433/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4985696219/10000000000 : ℝ)^81 ≤ (42006825193147/100000000000000 : ℝ)^65 := by
    have hnat : (4985696219 : ℕ)^81*100000000000000^65 ≤ 42006825193147^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4985696219 10000000000 42006825193147 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1419783483/2500000000 : ℝ)^81 ≤ (49408049265611/100000000000000 : ℝ)^65 := by
    have hnat : (1419783483 : ℕ)^81*100000000000000^65 ≤ 49408049265611^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1419783483 2500000000 49408049265611 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697163433/5000000000 : ℝ)^81 ≤ (8585125530543/100000000000000 : ℝ)^65 := by
    have hnat : (697163433 : ℕ)^81*100000000000000^65 ≤ 8585125530543^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697163433 5000000000 8585125530543 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4985696219/10000000000 : ℝ), (1419783483/2500000000 : ℝ), (697163433/5000000000 : ℝ)] ![(42006825193147/100000000000000 : ℝ), (49408049265611/100000000000000 : ℝ), (8585125530543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4985696219/10000000000 : ℝ)|^81 ≤ (42006825193147/100000000000000 : ℝ)^65
        have hw : |(4985696219/10000000000 : ℝ)|=(4985696219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1419783483/2500000000 : ℝ)|^81 ≤ (49408049265611/100000000000000 : ℝ)^65
        have hw : |(1419783483/2500000000 : ℝ)|=(1419783483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(697163433/5000000000 : ℝ)|^81 ≤ (8585125530543/100000000000000 : ℝ)^65
        have hw : |(697163433/5000000000 : ℝ)|=(697163433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3705617017/5000000000 : ℝ)*x 0 + (73417779/200000000 : ℝ)*x 1 + (-513503031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3705617017/5000000000 : ℝ)^81 ≤ (6884360129539/10000000000000 : ℝ)^65 := by
    have hnat : (3705617017 : ℕ)^81*10000000000000^65 ≤ 6884360129539^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3705617017 5000000000 6884360129539 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73417779/200000000 : ℝ)^81 ≤ (14341943899583/50000000000000 : ℝ)^65 := by
    have hnat : (73417779 : ℕ)^81*50000000000000^65 ≤ 14341943899583^65*200000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73417779 200000000 14341943899583 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513503031/10000000000 : ℝ)^81 ≤ (1236255448187/50000000000000 : ℝ)^65 := by
    have hnat : (513503031 : ℕ)^81*50000000000000^65 ≤ 1236255448187^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513503031 10000000000 1236255448187 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3705617017/5000000000 : ℝ), (73417779/200000000 : ℝ), (-513503031/10000000000 : ℝ)] ![(6884360129539/10000000000000 : ℝ), (14341943899583/50000000000000 : ℝ), (1236255448187/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3705617017/5000000000 : ℝ)|^81 ≤ (6884360129539/10000000000000 : ℝ)^65
        have hw : |(3705617017/5000000000 : ℝ)|=(3705617017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73417779/200000000 : ℝ)|^81 ≤ (14341943899583/50000000000000 : ℝ)^65
        have hw : |(73417779/200000000 : ℝ)|=(73417779/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513503031/10000000000 : ℝ)|^81 ≤ (1236255448187/50000000000000 : ℝ)^65
        have hw : |(-513503031/10000000000 : ℝ)|=(513503031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1504143319/10000000000 : ℝ)*x 0 + (219738761/500000000 : ℝ)*x 1 + (-6159446103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1504143319/10000000000 : ℝ)^81 ≤ (9435736318179/100000000000000 : ℝ)^65 := by
    have hnat : (1504143319 : ℕ)^81*100000000000000^65 ≤ 9435736318179^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1504143319 10000000000 9435736318179 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219738761/500000000 : ℝ)^81 ≤ (17947921389593/50000000000000 : ℝ)^65 := by
    have hnat : (219738761 : ℕ)^81*50000000000000^65 ≤ 17947921389593^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219738761 500000000 17947921389593 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6159446103/10000000000 : ℝ)^81 ≤ (27334210444381/50000000000000 : ℝ)^65 := by
    have hnat : (6159446103 : ℕ)^81*50000000000000^65 ≤ 27334210444381^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6159446103 10000000000 27334210444381 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1504143319/10000000000 : ℝ), (219738761/500000000 : ℝ), (-6159446103/10000000000 : ℝ)] ![(9435736318179/100000000000000 : ℝ), (17947921389593/50000000000000 : ℝ), (27334210444381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1504143319/10000000000 : ℝ)|^81 ≤ (9435736318179/100000000000000 : ℝ)^65
        have hw : |(-1504143319/10000000000 : ℝ)|=(1504143319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219738761/500000000 : ℝ)|^81 ≤ (17947921389593/50000000000000 : ℝ)^65
        have hw : |(219738761/500000000 : ℝ)|=(219738761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6159446103/10000000000 : ℝ)|^81 ≤ (27334210444381/50000000000000 : ℝ)^65
        have hw : |(-6159446103/10000000000 : ℝ)|=(6159446103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1237599581/2500000000 : ℝ)*x 0 + (-410808937/2000000000 : ℝ)*x 1 + (-521717291/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1237599581/2500000000 : ℝ)^81 ≤ (4163654093787/10000000000000 : ℝ)^65 := by
    have hnat : (1237599581 : ℕ)^81*10000000000000^65 ≤ 4163654093787^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237599581 2500000000 4163654093787 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410808937/2000000000 : ℝ)^81 ≤ (6956265855401/50000000000000 : ℝ)^65 := by
    have hnat : (410808937 : ℕ)^81*50000000000000^65 ≤ 6956265855401^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410808937 2000000000 6956265855401 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521717291/1000000000 : ℝ)^81 ≤ (44450927346899/100000000000000 : ℝ)^65 := by
    have hnat : (521717291 : ℕ)^81*100000000000000^65 ≤ 44450927346899^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521717291 1000000000 44450927346899 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1237599581/2500000000 : ℝ), (-410808937/2000000000 : ℝ), (-521717291/1000000000 : ℝ)] ![(4163654093787/10000000000000 : ℝ), (6956265855401/50000000000000 : ℝ), (44450927346899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1237599581/2500000000 : ℝ)|^81 ≤ (4163654093787/10000000000000 : ℝ)^65
        have hw : |(1237599581/2500000000 : ℝ)|=(1237599581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410808937/2000000000 : ℝ)|^81 ≤ (6956265855401/50000000000000 : ℝ)^65
        have hw : |(-410808937/2000000000 : ℝ)|=(410808937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521717291/1000000000 : ℝ)|^81 ≤ (44450927346899/100000000000000 : ℝ)^65
        have hw : |(-521717291/1000000000 : ℝ)|=(521717291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4434762293/10000000000 : ℝ)*x 0 + (5923516191/10000000000 : ℝ)*x 1 + (889172361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4434762293/10000000000 : ℝ)^81 ≤ (36303301606553/100000000000000 : ℝ)^65 := by
    have hnat : (4434762293 : ℕ)^81*100000000000000^65 ≤ 36303301606553^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434762293 10000000000 36303301606553 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5923516191/10000000000 : ℝ)^81 ≤ (26035694869339/50000000000000 : ℝ)^65 := by
    have hnat : (5923516191 : ℕ)^81*50000000000000^65 ≤ 26035694869339^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5923516191 10000000000 26035694869339 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (889172361/5000000000 : ℝ)^81 ≤ (2906327160899/25000000000000 : ℝ)^65 := by
    have hnat : (889172361 : ℕ)^81*25000000000000^65 ≤ 2906327160899^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889172361 5000000000 2906327160899 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4434762293/10000000000 : ℝ), (5923516191/10000000000 : ℝ), (889172361/5000000000 : ℝ)] ![(36303301606553/100000000000000 : ℝ), (26035694869339/50000000000000 : ℝ), (2906327160899/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4434762293/10000000000 : ℝ)|^81 ≤ (36303301606553/100000000000000 : ℝ)^65
        have hw : |(4434762293/10000000000 : ℝ)|=(4434762293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5923516191/10000000000 : ℝ)|^81 ≤ (26035694869339/50000000000000 : ℝ)^65
        have hw : |(5923516191/10000000000 : ℝ)|=(5923516191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(889172361/5000000000 : ℝ)|^81 ≤ (2906327160899/25000000000000 : ℝ)^65
        have hw : |(889172361/5000000000 : ℝ)|=(889172361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320060_s1_s1_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (302020047/400000000 : ℝ)*x 0 + (3465637983/10000000000 : ℝ)*x 1 + (-574115423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (302020047/400000000 : ℝ)^81 ≤ (70459417468843/100000000000000 : ℝ)^65 := by
    have hnat : (302020047 : ℕ)^81*100000000000000^65 ≤ 70459417468843^65*400000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302020047 400000000 70459417468843 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3465637983/10000000000 : ℝ)^81 ≤ (13349624883577/50000000000000 : ℝ)^65 := by
    have hnat : (3465637983 : ℕ)^81*50000000000000^65 ≤ 13349624883577^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3465637983 10000000000 13349624883577 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574115423/10000000000 : ℝ)^81 ≤ (2841332750919/100000000000000 : ℝ)^65 := by
    have hnat : (574115423 : ℕ)^81*100000000000000^65 ≤ 2841332750919^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574115423 10000000000 2841332750919 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(302020047/400000000 : ℝ), (3465637983/10000000000 : ℝ), (-574115423/10000000000 : ℝ)] ![(70459417468843/100000000000000 : ℝ), (13349624883577/50000000000000 : ℝ), (2841332750919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(302020047/400000000 : ℝ)|^81 ≤ (70459417468843/100000000000000 : ℝ)^65
        have hw : |(302020047/400000000 : ℝ)|=(302020047/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3465637983/10000000000 : ℝ)|^81 ≤ (13349624883577/50000000000000 : ℝ)^65
        have hw : |(3465637983/10000000000 : ℝ)|=(3465637983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-574115423/10000000000 : ℝ)|^81 ≤ (2841332750919/100000000000000 : ℝ)^65
        have hw : |(-574115423/10000000000 : ℝ)|=(574115423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320060_s1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((73443/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73443/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36563/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36563/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31839/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31839/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14879/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14879/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8487/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8487/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10103/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10103/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (73443/100000 : ℝ) ^ (5 : ℝ) ≤ (10683708929021305681/50000000000000000000 : ℝ) := by
    have hpowers : (73443/100000 : ℝ)^5 ≤ (10683708929021305681/50000000000000000000 : ℝ)^1 := by
      have hnat : (73443 : ℕ)^5*50000000000000000000^1 ≤ 10683708929021305681^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73443 100000 10683708929021305681 50000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (73443/100000 : ℝ)) (X := (10683708929021305681/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0a : (60683708929021305681/50000000000000000000 : ℝ) ≤ (5197451277162437/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (60683708929021305681/50000000000000000000 : ℝ)^1 ≤ (5197451277162437/5000000000000000 : ℝ)^5 := by
      have hnat : (60683708929021305681 : ℕ)^1*5000000000000000^5 ≤ 5197451277162437^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60683708929021305681 50000000000000000000 5197451277162437 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5197451277162437/5000000000000000 : ℝ)) (X := (60683708929021305681/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner0b : (35683708929021305681/25000000000000000000 : ℝ) ≤ (10737569698764587/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (35683708929021305681/25000000000000000000 : ℝ)^1 ≤ (10737569698764587/10000000000000000 : ℝ)^5 := by
      have hnat : (35683708929021305681 : ℕ)^1*10000000000000000^5 ≤ 10737569698764587^5*25000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35683708929021305681 25000000000000000000 10737569698764587 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10737569698764587/10000000000000000 : ℝ)) (X := (35683708929021305681/25000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(65817092387479/1224050000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(342667144439713/7344300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (73443/100000 : ℝ)) (alpha := (65817092387479/1224050000000000 : ℝ)) (beta := (342667144439713/7344300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (73443/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(65817092387479/1224050000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(342667144439713/7344300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (36563/50000 : ℝ) ^ (5 : ℝ) ≤ (20910243518609860903/100000000000000000000 : ℝ) := by
    have hpowers : (36563/50000 : ℝ)^5 ≤ (20910243518609860903/100000000000000000000 : ℝ)^1 := by
      have hnat : (36563 : ℕ)^5*100000000000000000000^1 ≤ 20910243518609860903^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36563 50000 20910243518609860903 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36563/50000 : ℝ)) (X := (20910243518609860903/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1a : (120910243518609860903/100000000000000000000 : ℝ) ≤ (5193529747400409/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (120910243518609860903/100000000000000000000 : ℝ)^1 ≤ (5193529747400409/5000000000000000 : ℝ)^5 := by
      have hnat : (120910243518609860903 : ℕ)^1*5000000000000000^5 ≤ 5193529747400409^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120910243518609860903 100000000000000000000 5193529747400409 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5193529747400409/5000000000000000 : ℝ)) (X := (120910243518609860903/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner1b : (70910243518609860903/50000000000000000000 : ℝ) ≤ (10723777498989589/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (70910243518609860903/50000000000000000000 : ℝ)^1 ≤ (10723777498989589/10000000000000000 : ℝ)^5 := by
      have hnat : (70910243518609860903 : ℕ)^1*10000000000000000^5 ≤ 10723777498989589^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70910243518609860903 50000000000000000000 10723777498989589 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10723777498989589/10000000000000000 : ℝ)) (X := (70910243518609860903/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(193529747400409/3656300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(336718004188771/7312600000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (36563/50000 : ℝ)) (alpha := (193529747400409/3656300000000000 : ℝ)) (beta := (336718004188771/7312600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (36563/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(193529747400409/3656300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(336718004188771/7312600000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (31839/50000 : ℝ) ^ (5 : ℝ) ≤ (5235004717804496471/50000000000000000000 : ℝ) := by
    have hpowers : (31839/50000 : ℝ)^5 ≤ (5235004717804496471/50000000000000000000 : ℝ)^1 := by
      have hnat : (31839 : ℕ)^5*50000000000000000000^1 ≤ 5235004717804496471^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31839 50000 5235004717804496471 50000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31839/50000 : ℝ)) (X := (5235004717804496471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2a : (55235004717804496471/50000000000000000000 : ℝ) ≤ (10201144001959301/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (55235004717804496471/50000000000000000000 : ℝ)^1 ≤ (10201144001959301/10000000000000000 : ℝ)^5 := by
      have hnat : (55235004717804496471 : ℕ)^1*10000000000000000^5 ≤ 10201144001959301^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55235004717804496471 50000000000000000000 10201144001959301 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10201144001959301/10000000000000000 : ℝ)) (X := (55235004717804496471/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s1_corner2b : (30235004717804496471/25000000000000000000 : ℝ) ≤ (2077514205560289/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (30235004717804496471/25000000000000000000 : ℝ)^1 ≤ (2077514205560289/2000000000000000 : ℝ)^5 := by
      have hnat : (30235004717804496471 : ℕ)^1*2000000000000000^5 ≤ 2077514205560289^5*25000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30235004717804496471 25000000000000000000 2077514205560289 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2077514205560289/2000000000000000 : ℝ)) (X := (30235004717804496471/25000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(201144001959301/6367800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(5825844557567/198993750000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (31839/50000 : ℝ)) (alpha := (201144001959301/6367800000000000 : ℝ)) (beta := (5825844557567/198993750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31839/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(201144001959301/6367800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(5825844557567/198993750000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-976599797/5000000000 : ℝ)*X 0 0+(125228839/312500000 : ℝ)*X 0 1+(-1236751887/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4639674693/10000000000 : ℝ)*X 2 0+(1147599867/2000000000 : ℝ)*X 2 1+(1768794937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3486141459/5000000000 : ℝ)*X 0 0+(1979772103/5000000000 : ℝ)*X 0 1+(-428333341/5000000000 : ℝ)*X 0 2+(3486141459/5000000000 : ℝ)*X 1 0+(1979772103/5000000000 : ℝ)*X 1 1+(-428333341/5000000000 : ℝ)*X 1 2+(3486141459/5000000000 : ℝ)*X 2 0+(1979772103/5000000000 : ℝ)*X 2 1+(-428333341/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-383776317/2000000000 : ℝ)*X 0 0+(3898156507/10000000000 : ℝ)*X 0 1+(-1261404593/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4381870671/10000000000 : ℝ)*X 1 0+(-40677009/200000000 : ℝ)*X 1 1+(-5779008559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4527327481/10000000000 : ℝ)*X 2 0+(6144485193/10000000000 : ℝ)*X 2 1+(675043559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1717985653/2500000000 : ℝ)*X 0 0+(856102211/2000000000 : ℝ)*X 0 1+(-535553341/10000000000 : ℝ)*X 0 2+(1717985653/2500000000 : ℝ)*X 1 0+(856102211/2000000000 : ℝ)*X 1 1+(-535553341/10000000000 : ℝ)*X 1 2+(1717985653/2500000000 : ℝ)*X 2 0+(856102211/2000000000 : ℝ)*X 2 1+(-535553341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1614302919/10000000000 : ℝ)*X 0 0+(4137959621/10000000000 : ℝ)*X 0 1+(-6315029059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((867973433/2000000000 : ℝ)*X 1 0+(-1070498523/5000000000 : ℝ)*X 1 1+(-5734768521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((4985696219/10000000000 : ℝ)*X 2 0+(1419783483/2500000000 : ℝ)*X 2 1+(697163433/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3705617017/5000000000 : ℝ)*X 0 0+(73417779/200000000 : ℝ)*X 0 1+(-513503031/10000000000 : ℝ)*X 0 2+(3705617017/5000000000 : ℝ)*X 1 0+(73417779/200000000 : ℝ)*X 1 1+(-513503031/10000000000 : ℝ)*X 1 2+(3705617017/5000000000 : ℝ)*X 2 0+(73417779/200000000 : ℝ)*X 2 1+(-513503031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1504143319/10000000000 : ℝ)*X 0 0+(219738761/500000000 : ℝ)*X 0 1+(-6159446103/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1237599581/2500000000 : ℝ)*X 1 0+(-410808937/2000000000 : ℝ)*X 1 1+(-521717291/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4434762293/10000000000 : ℝ)*X 2 0+(5923516191/10000000000 : ℝ)*X 2 1+(889172361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((302020047/400000000 : ℝ)*X 0 0+(3465637983/10000000000 : ℝ)*X 0 1+(-574115423/10000000000 : ℝ)*X 0 2+(302020047/400000000 : ℝ)*X 1 0+(3465637983/10000000000 : ℝ)*X 1 1+(-574115423/10000000000 : ℝ)*X 1 2+(302020047/400000000 : ℝ)*X 2 0+(3465637983/10000000000 : ℝ)*X 2 1+(-574115423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((14879/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14879/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32853246046942743/2500000000000000000000 : ℝ) := by norm_num
    linear_combination (176183/125000000000 : ℝ)*(base5) + (1013630115893/1000000000000 : ℝ)*(base39) + (2084707/500000000000 : ℝ)*(base49) + (2251375540147/1000000000000 : ℝ)*(base59) + (6593611355801/500000000000 : ℝ)*(major_s1_0) + (6593611355801/500000000000 : ℝ)*(major_s1_1) + (6593611355801/500000000000 : ℝ)*(major_s1_2) + (9674749098093/500000000000 : ℝ)*(sp_s1_7) + (9674236809033/500000000000 : ℝ)*(sp_s1_8) + (19349206654761/1000000000000 : ℝ)*(sp_s1_9) + (7024941437117/1000000000000 : ℝ)*(sp_s1_13) + (1001227801/1000000000000 : ℝ)*(sp_s1_15) + (291879/12500000000 : ℝ)*(sp_s1_22) + (292950889/1000000000000 : ℝ)*(sp_s1_23) + (7024942846581/1000000000000 : ℝ)*(f.failure) + (9674749098093/500000000000 : ℝ)*(f.sum) + (757161823701695837/23282587140000000000000000000000 : ℝ)*base63 + (78151470115387/1591950000000000000000000000 : ℝ)*base64 + (133105022879381/3656300000000000000000000000 : ℝ)*base67 + (2119770721471549/3183900000000000000000000000 : ℝ)*base68 + (126593361387562939/311780223600000000000000000000 : ℝ)*base71 + (1611534358516193/3672150000000000000000000000 : ℝ)*base73 + (287431689555821/1828150000000000000000000000 : ℝ)*base74 + (174452445795977/1224050000000000000000000000 : ℝ)*base76 + (142673360360969585119/268529640900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (367/2500000000000000 : ℝ)*base86 + (367/2500000000000000 : ℝ)*base88 + (367/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8487/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8487/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5893629028437617313552457/716079042400000000000000000000 : ℝ) := by norm_num
    linear_combination (143916839341/125000000000 : ℝ)*(base39) + (1948936130539/1000000000000 : ℝ)*(base59) + (13620455482453/1000000000000 : ℝ)*(major_s1_0) + (13620455482453/1000000000000 : ℝ)*(major_s1_1) + (13620455482453/1000000000000 : ℝ)*(major_s1_2) + (13086831/250000000000 : ℝ)*(sp_s1_2) + (6166843/200000000000 : ℝ)*(sp_s1_6) + (83761853/1000000000000 : ℝ)*(sp_s1_7) + (60563833/1000000000000 : ℝ)*(sp_s1_8) + (499627373123/25000000000 : ℝ)*(sp_s1_14) + (19985118122941/1000000000000 : ℝ)*(sp_s1_15) + (19985126339449/1000000000000 : ℝ)*(sp_s1_16) + (7255550083039/1000000000000 : ℝ)*(sp_s1_20) + (743087/5000000000 : ℝ)*(sp_s1_27) + (3627864767327/500000000000 : ℝ)*(f.failure) + (19985178686773/1000000000000 : ℝ)*(f.sum) + (13228586905603857601/46565174280000000000000000000000 : ℝ)*base63 + (443273271398353/1591950000000000000000000000 : ℝ)*base64 + (1465953386239903/7312600000000000000000000000 : ℝ)*base67 + (2396659247463767/6367800000000000000000000000 : ℝ)*base68 + (1174919383267347253/7794505590000000000000000000000 : ℝ)*base71 + (9247221558021199/7344300000000000000000000000 : ℝ)*base73 + (244478738896107/3656300000000000000000000000 : ℝ)*base75 + (121290926991953/1224050000000000000000000000 : ℝ)*base76 + (236274432641378059183/537059281800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (639/1250000000000000 : ℝ)*base86 + (639/1250000000000000 : ℝ)*base88 + (639/1250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10103/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10103/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5479645708232363031181324275757/949968359623900000000000000000000000 : ℝ) := by norm_num
    linear_combination (2727199/500000000000 : ℝ)*(base11) + (709511343989/500000000000 : ℝ)*(base39) + (30497/100000000000 : ℝ)*(base40) + (1456309748497/1000000000000 : ℝ)*(base59) + (10309115662801/1000000000000 : ℝ)*(major_s1_0) + (10309115662801/1000000000000 : ℝ)*(major_s1_1) + (10309115662801/1000000000000 : ℝ)*(major_s1_2) + (19019099/500000000000 : ℝ)*(sp_s1_0) + (1820041/50000000000 : ℝ)*(sp_s1_2) + (26743729/500000000000 : ℝ)*(sp_s1_9) + (15126434545029/1000000000000 : ℝ)*(sp_s1_21) + (121011824301/8000000000 : ℝ)*(sp_s1_22) + (15126388149347/1000000000000 : ℝ)*(sp_s1_23) + (219670054609/40000000000 : ℝ)*(sp_s1_27) + (219670054609/40000000000 : ℝ)*(f.failure) + (121011824301/8000000000 : ℝ)*(f.sum) + (15232302753875270617/46565174280000000000000000000000 : ℝ)*base63 + (156122862441841/1591950000000000000000000000 : ℝ)*base64 + (1498292952235491/7312600000000000000000000000 : ℝ)*base67 + (1759458488859601/6367800000000000000000000000 : ℝ)*base69 + (3698535960081291137/7794505590000000000000000000000 : ℝ)*base70 + (1695053623146137/7344300000000000000000000000 : ℝ)*base72 + (964746447055089/3656300000000000000000000000 : ℝ)*base75 + (2112936925549/1224050000000000000000000000 : ℝ)*base77 + (123381347627287421549/537059281800000000000000000000000 : ℝ)*base78 + (63/100000000000000 : ℝ)*base86 + (63/100000000000000 : ℝ)*base88 + (63/100000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((73443/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(73443/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(36563/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(36563/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31839/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31839/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14879/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14879/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8487/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8487/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10103/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10103/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c320060_s1 p hpa hpb X hX hprev0

#print axioms solution
