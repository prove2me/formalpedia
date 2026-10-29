-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312051_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:18:36.893033+00:00
-- url     : https://prove2.me/submissions/a613beea-d58c-4beb-a9c5-e7989746ae92

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
theorem collision_support_c312051_s1_s1_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1834033579/5000000000 : ℝ)*x 0 + (3657797611/10000000000 : ℝ)*x 1 + (5298495709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1834033579/5000000000 : ℝ)^37 ≤ (27815190903537/100000000000000 : ℝ)^29 := by
    have hnat : (1834033579 : ℕ)^37*100000000000000^29 ≤ 27815190903537^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1834033579 5000000000 27815190903537 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3657797611/10000000000 : ℝ)^37 ≤ (27715871998469/100000000000000 : ℝ)^29 := by
    have hnat : (3657797611 : ℕ)^37*100000000000000^29 ≤ 27715871998469^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657797611 10000000000 27715871998469 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5298495709/10000000000 : ℝ)^37 ≤ (22234468542009/50000000000000 : ℝ)^29 := by
    have hnat : (5298495709 : ℕ)^37*50000000000000^29 ≤ 22234468542009^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5298495709 10000000000 22234468542009 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1834033579/5000000000 : ℝ), (3657797611/10000000000 : ℝ), (5298495709/10000000000 : ℝ)] ![(27815190903537/100000000000000 : ℝ), (27715871998469/100000000000000 : ℝ), (22234468542009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1834033579/5000000000 : ℝ)|^37 ≤ (27815190903537/100000000000000 : ℝ)^29
        have hw : |(-1834033579/5000000000 : ℝ)|=(1834033579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3657797611/10000000000 : ℝ)|^37 ≤ (27715871998469/100000000000000 : ℝ)^29
        have hw : |(3657797611/10000000000 : ℝ)|=(3657797611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5298495709/10000000000 : ℝ)|^37 ≤ (22234468542009/50000000000000 : ℝ)^29
        have hw : |(5298495709/10000000000 : ℝ)|=(5298495709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2821011353/10000000000 : ℝ)*x 0 + (-1406556661/5000000000 : ℝ)*x 1 + (6724874807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2821011353/10000000000 : ℝ)^37 ≤ (4974304684631/25000000000000 : ℝ)^29 := by
    have hnat : (2821011353 : ℕ)^37*25000000000000^29 ≤ 4974304684631^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821011353 10000000000 4974304684631 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1406556661/5000000000 : ℝ)^37 ≤ (9913086155559/50000000000000 : ℝ)^29 := by
    have hnat : (1406556661 : ℕ)^37*50000000000000^29 ≤ 9913086155559^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406556661 5000000000 9913086155559 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6724874807/10000000000 : ℝ)^37 ≤ (60276608942809/100000000000000 : ℝ)^29 := by
    have hnat : (6724874807 : ℕ)^37*100000000000000^29 ≤ 60276608942809^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6724874807 10000000000 60276608942809 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2821011353/10000000000 : ℝ), (-1406556661/5000000000 : ℝ), (6724874807/10000000000 : ℝ)] ![(4974304684631/25000000000000 : ℝ), (9913086155559/50000000000000 : ℝ), (60276608942809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2821011353/10000000000 : ℝ)|^37 ≤ (4974304684631/25000000000000 : ℝ)^29
        have hw : |(2821011353/10000000000 : ℝ)|=(2821011353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1406556661/5000000000 : ℝ)|^37 ≤ (9913086155559/50000000000000 : ℝ)^29
        have hw : |(-1406556661/5000000000 : ℝ)|=(1406556661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6724874807/10000000000 : ℝ)|^37 ≤ (60276608942809/100000000000000 : ℝ)^29
        have hw : |(6724874807/10000000000 : ℝ)|=(6724874807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (13668109/25000000 : ℝ)*x 0 + (5480183489/10000000000 : ℝ)*x 1 + (-128454253/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13668109/25000000 : ℝ)^37 ≤ (46283765016861/100000000000000 : ℝ)^29 := by
    have hnat : (13668109 : ℕ)^37*100000000000000^29 ≤ 46283765016861^29*25000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13668109 25000000 46283765016861 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5480183489/10000000000 : ℝ)^37 ≤ (46423574363467/100000000000000 : ℝ)^29 := by
    have hnat : (5480183489 : ℕ)^37*100000000000000^29 ≤ 46423574363467^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5480183489 10000000000 46423574363467 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128454253/1000000000 : ℝ)^37 ≤ (7292660597323/100000000000000 : ℝ)^29 := by
    have hnat : (128454253 : ℕ)^37*100000000000000^29 ≤ 7292660597323^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128454253 1000000000 7292660597323 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13668109/25000000 : ℝ), (5480183489/10000000000 : ℝ), (-128454253/1000000000 : ℝ)] ![(46283765016861/100000000000000 : ℝ), (46423574363467/100000000000000 : ℝ), (7292660597323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13668109/25000000 : ℝ)|^37 ≤ (46283765016861/100000000000000 : ℝ)^29
        have hw : |(13668109/25000000 : ℝ)|=(13668109/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5480183489/10000000000 : ℝ)|^37 ≤ (46423574363467/100000000000000 : ℝ)^29
        have hw : |(5480183489/10000000000 : ℝ)|=(5480183489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-128454253/1000000000 : ℝ)|^37 ≤ (7292660597323/100000000000000 : ℝ)^29
        have hw : |(-128454253/1000000000 : ℝ)|=(128454253/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5202941871/10000000000 : ℝ)*x 0 + (521525621/1000000000 : ℝ)*x 1 + (80696201/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5202941871/10000000000 : ℝ)^37 ≤ (21724152010863/50000000000000 : ℝ)^29 := by
    have hnat : (5202941871 : ℕ)^37*50000000000000^29 ≤ 21724152010863^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5202941871 10000000000 21724152010863 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521525621/1000000000 : ℝ)^37 ≤ (43579548294239/100000000000000 : ℝ)^29 := by
    have hnat : (521525621 : ℕ)^37*100000000000000^29 ≤ 43579548294239^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521525621 1000000000 43579548294239 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80696201/400000000 : ℝ)^37 ≤ (12972147672829/100000000000000 : ℝ)^29 := by
    have hnat : (80696201 : ℕ)^37*100000000000000^29 ≤ 12972147672829^29*400000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80696201 400000000 12972147672829 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5202941871/10000000000 : ℝ), (521525621/1000000000 : ℝ), (80696201/400000000 : ℝ)] ![(21724152010863/50000000000000 : ℝ), (43579548294239/100000000000000 : ℝ), (12972147672829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5202941871/10000000000 : ℝ)|^37 ≤ (21724152010863/50000000000000 : ℝ)^29
        have hw : |(5202941871/10000000000 : ℝ)|=(5202941871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521525621/1000000000 : ℝ)|^37 ≤ (43579548294239/100000000000000 : ℝ)^29
        have hw : |(521525621/1000000000 : ℝ)|=(521525621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(80696201/400000000 : ℝ)|^37 ≤ (12972147672829/100000000000000 : ℝ)^29
        have hw : |(80696201/400000000 : ℝ)|=(80696201/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-676784879/2000000000 : ℝ)*x 0 + (740673309/2500000000 : ℝ)*x 1 + (24578987/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (676784879/2000000000 : ℝ)^37 ≤ (25096066618711/100000000000000 : ℝ)^29 := by
    have hnat : (676784879 : ℕ)^37*100000000000000^29 ≤ 25096066618711^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676784879 2000000000 25096066618711 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740673309/2500000000 : ℝ)^37 ≤ (4236186557527/20000000000000 : ℝ)^29 := by
    have hnat : (740673309 : ℕ)^37*20000000000000^29 ≤ 4236186557527^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740673309 2500000000 4236186557527 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24578987/40000000 : ℝ)^37 ≤ (53723000582007/100000000000000 : ℝ)^29 := by
    have hnat : (24578987 : ℕ)^37*100000000000000^29 ≤ 53723000582007^29*40000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24578987 40000000 53723000582007 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-676784879/2000000000 : ℝ), (740673309/2500000000 : ℝ), (24578987/40000000 : ℝ)] ![(25096066618711/100000000000000 : ℝ), (4236186557527/20000000000000 : ℝ), (53723000582007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-676784879/2000000000 : ℝ)|^37 ≤ (25096066618711/100000000000000 : ℝ)^29
        have hw : |(-676784879/2000000000 : ℝ)|=(676784879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740673309/2500000000 : ℝ)|^37 ≤ (4236186557527/20000000000000 : ℝ)^29
        have hw : |(740673309/2500000000 : ℝ)|=(740673309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(24578987/40000000 : ℝ)|^37 ≤ (53723000582007/100000000000000 : ℝ)^29
        have hw : |(24578987/40000000 : ℝ)|=(24578987/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (646790091/2500000000 : ℝ)*x 0 + (-45302209/200000000 : ℝ)*x 1 + (3659194543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646790091/2500000000 : ℝ)^37 ≤ (4454342341847/25000000000000 : ℝ)^29 := by
    have hnat : (646790091 : ℕ)^37*25000000000000^29 ≤ 4454342341847^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646790091 2500000000 4454342341847 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45302209/200000000 : ℝ)^37 ≤ (15037755065253/100000000000000 : ℝ)^29 := by
    have hnat : (45302209 : ℕ)^37*100000000000000^29 ≤ 15037755065253^29*200000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45302209 200000000 15037755065253 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3659194543/5000000000 : ℝ)^37 ≤ (33572437778329/50000000000000 : ℝ)^29 := by
    have hnat : (3659194543 : ℕ)^37*50000000000000^29 ≤ 33572437778329^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3659194543 5000000000 33572437778329 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646790091/2500000000 : ℝ), (-45302209/200000000 : ℝ), (3659194543/5000000000 : ℝ)] ![(4454342341847/25000000000000 : ℝ), (15037755065253/100000000000000 : ℝ), (33572437778329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646790091/2500000000 : ℝ)|^37 ≤ (4454342341847/25000000000000 : ℝ)^29
        have hw : |(646790091/2500000000 : ℝ)|=(646790091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-45302209/200000000 : ℝ)|^37 ≤ (15037755065253/100000000000000 : ℝ)^29
        have hw : |(-45302209/200000000 : ℝ)|=(45302209/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3659194543/5000000000 : ℝ)|^37 ≤ (33572437778329/50000000000000 : ℝ)^29
        have hw : |(3659194543/5000000000 : ℝ)|=(3659194543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5038486071/10000000000 : ℝ)*x 0 + (6362143473/10000000000 : ℝ)*x 1 + (-49072341/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5038486071/10000000000 : ℝ)^37 ≤ (8340765999101/20000000000000 : ℝ)^29 := by
    have hnat : (5038486071 : ℕ)^37*20000000000000^29 ≤ 8340765999101^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038486071 10000000000 8340765999101 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6362143473/10000000000 : ℝ)^37 ≤ (28079870902333/50000000000000 : ℝ)^29 := by
    have hnat : (6362143473 : ℕ)^37*50000000000000^29 ≤ 28079870902333^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6362143473 10000000000 28079870902333 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49072341/1000000000 : ℝ)^37 ≤ (1068214098129/50000000000000 : ℝ)^29 := by
    have hnat : (49072341 : ℕ)^37*50000000000000^29 ≤ 1068214098129^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49072341 1000000000 1068214098129 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5038486071/10000000000 : ℝ), (6362143473/10000000000 : ℝ), (-49072341/1000000000 : ℝ)] ![(8340765999101/20000000000000 : ℝ), (28079870902333/50000000000000 : ℝ), (1068214098129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5038486071/10000000000 : ℝ)|^37 ≤ (8340765999101/20000000000000 : ℝ)^29
        have hw : |(5038486071/10000000000 : ℝ)|=(5038486071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6362143473/10000000000 : ℝ)|^37 ≤ (28079870902333/50000000000000 : ℝ)^29
        have hw : |(6362143473/10000000000 : ℝ)|=(6362143473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49072341/1000000000 : ℝ)|^37 ≤ (1068214098129/50000000000000 : ℝ)^29
        have hw : |(-49072341/1000000000 : ℝ)|=(49072341/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_12 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4975246263/10000000000 : ℝ)*x 0 + (6282289977/10000000000 : ℝ)*x 1 + (754849037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4975246263/10000000000 : ℝ)^37 ≤ (41037153194759/100000000000000 : ℝ)^29 := by
    have hnat : (4975246263 : ℕ)^37*100000000000000^29 ≤ 41037153194759^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975246263 10000000000 41037153194759 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6282289977/10000000000 : ℝ)^37 ≤ (27630986512173/50000000000000 : ℝ)^29 := by
    have hnat : (6282289977 : ℕ)^37*50000000000000^29 ≤ 27630986512173^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6282289977 10000000000 27630986512173 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (754849037/10000000000 : ℝ)^37 ≤ (3700873769663/100000000000000 : ℝ)^29 := by
    have hnat : (754849037 : ℕ)^37*100000000000000^29 ≤ 3700873769663^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754849037 10000000000 3700873769663 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4975246263/10000000000 : ℝ), (6282289977/10000000000 : ℝ), (754849037/10000000000 : ℝ)] ![(41037153194759/100000000000000 : ℝ), (27630986512173/50000000000000 : ℝ), (3700873769663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4975246263/10000000000 : ℝ)|^37 ≤ (41037153194759/100000000000000 : ℝ)^29
        have hw : |(4975246263/10000000000 : ℝ)|=(4975246263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6282289977/10000000000 : ℝ)|^37 ≤ (27630986512173/50000000000000 : ℝ)^29
        have hw : |(6282289977/10000000000 : ℝ)|=(6282289977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(754849037/10000000000 : ℝ)|^37 ≤ (3700873769663/100000000000000 : ℝ)^29
        have hw : |(754849037/10000000000 : ℝ)|=(754849037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-185806023/625000000 : ℝ)*x 0 + (674810827/2000000000 : ℝ)*x 1 + (6144768703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (185806023/625000000 : ℝ)^37 ≤ (21274043940621/100000000000000 : ℝ)^29 := by
    have hnat : (185806023 : ℕ)^37*100000000000000^29 ≤ 21274043940621^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      185806023 625000000 21274043940621 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674810827/2000000000 : ℝ)^37 ≤ (12501355287007/50000000000000 : ℝ)^29 := by
    have hnat : (674810827 : ℕ)^37*50000000000000^29 ≤ 12501355287007^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674810827 2000000000 12501355287007 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6144768703/10000000000 : ℝ)^37 ≤ (13430811365611/25000000000000 : ℝ)^29 := by
    have hnat : (6144768703 : ℕ)^37*25000000000000^29 ≤ 13430811365611^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6144768703 10000000000 13430811365611 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-185806023/625000000 : ℝ), (674810827/2000000000 : ℝ), (6144768703/10000000000 : ℝ)] ![(21274043940621/100000000000000 : ℝ), (12501355287007/50000000000000 : ℝ), (13430811365611/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-185806023/625000000 : ℝ)|^37 ≤ (21274043940621/100000000000000 : ℝ)^29
        have hw : |(-185806023/625000000 : ℝ)|=(185806023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674810827/2000000000 : ℝ)|^37 ≤ (12501355287007/50000000000000 : ℝ)^29
        have hw : |(674810827/2000000000 : ℝ)|=(674810827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6144768703/10000000000 : ℝ)|^37 ≤ (13430811365611/25000000000000 : ℝ)^29
        have hw : |(6144768703/10000000000 : ℝ)|=(6144768703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1136455879/5000000000 : ℝ)*x 0 + (-2579614749/10000000000 : ℝ)*x 1 + (1463680611/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136455879/5000000000 : ℝ)^37 ≤ (3020773125949/20000000000000 : ℝ)^29 := by
    have hnat : (1136455879 : ℕ)^37*20000000000000^29 ≤ 3020773125949^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136455879 5000000000 3020773125949 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2579614749/10000000000 : ℝ)^37 ≤ (1775109528329/10000000000000 : ℝ)^29 := by
    have hnat : (2579614749 : ℕ)^37*10000000000000^29 ≤ 1775109528329^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579614749 10000000000 1775109528329 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1463680611/2000000000 : ℝ)^37 ≤ (67145039075023/100000000000000 : ℝ)^29 := by
    have hnat : (1463680611 : ℕ)^37*100000000000000^29 ≤ 67145039075023^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1463680611 2000000000 67145039075023 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1136455879/5000000000 : ℝ), (-2579614749/10000000000 : ℝ), (1463680611/2000000000 : ℝ)] ![(3020773125949/20000000000000 : ℝ), (1775109528329/10000000000000 : ℝ), (67145039075023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1136455879/5000000000 : ℝ)|^37 ≤ (3020773125949/20000000000000 : ℝ)^29
        have hw : |(1136455879/5000000000 : ℝ)|=(1136455879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2579614749/10000000000 : ℝ)|^37 ≤ (1775109528329/10000000000000 : ℝ)^29
        have hw : |(-2579614749/10000000000 : ℝ)|=(2579614749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1463680611/2000000000 : ℝ)|^37 ≤ (67145039075023/100000000000000 : ℝ)^29
        have hw : |(1463680611/2000000000 : ℝ)|=(1463680611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6349483423/10000000000 : ℝ)*x 0 + (5051990283/10000000000 : ℝ)*x 1 + (-490701669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6349483423/10000000000 : ℝ)^37 ≤ (56017200241671/100000000000000 : ℝ)^29 := by
    have hnat : (6349483423 : ℕ)^37*100000000000000^29 ≤ 56017200241671^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6349483423 10000000000 56017200241671 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5051990283/10000000000 : ℝ)^37 ≤ (41846492311851/100000000000000 : ℝ)^29 := by
    have hnat : (5051990283 : ℕ)^37*100000000000000^29 ≤ 41846492311851^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5051990283 10000000000 41846492311851 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490701669/10000000000 : ℝ)^37 ≤ (2136307433753/100000000000000 : ℝ)^29 := by
    have hnat : (490701669 : ℕ)^37*100000000000000^29 ≤ 2136307433753^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490701669 10000000000 2136307433753 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6349483423/10000000000 : ℝ), (5051990283/10000000000 : ℝ), (-490701669/10000000000 : ℝ)] ![(56017200241671/100000000000000 : ℝ), (41846492311851/100000000000000 : ℝ), (2136307433753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6349483423/10000000000 : ℝ)|^37 ≤ (56017200241671/100000000000000 : ℝ)^29
        have hw : |(6349483423/10000000000 : ℝ)|=(6349483423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5051990283/10000000000 : ℝ)|^37 ≤ (41846492311851/100000000000000 : ℝ)^29
        have hw : |(5051990283/10000000000 : ℝ)|=(5051990283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490701669/10000000000 : ℝ)|^37 ≤ (2136307433753/100000000000000 : ℝ)^29
        have hw : |(-490701669/10000000000 : ℝ)|=(490701669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_18 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (391862107/625000000 : ℝ)*x 0 + (997716973/2000000000 : ℝ)*x 1 + (37740737/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391862107/625000000 : ℝ)^37 ≤ (13780441228763/25000000000000 : ℝ)^29 := by
    have hnat : (391862107 : ℕ)^37*25000000000000^29 ≤ 13780441228763^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391862107 625000000 13780441228763 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997716973/2000000000 : ℝ)^37 ≤ (2573598489981/6250000000000 : ℝ)^29 := by
    have hnat : (997716973 : ℕ)^37*6250000000000^29 ≤ 2573598489981^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997716973 2000000000 2573598489981 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (37740737/500000000 : ℝ)^37 ≤ (3700659233107/100000000000000 : ℝ)^29 := by
    have hnat : (37740737 : ℕ)^37*100000000000000^29 ≤ 3700659233107^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37740737 500000000 3700659233107 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(391862107/625000000 : ℝ), (997716973/2000000000 : ℝ), (37740737/500000000 : ℝ)] ![(13780441228763/25000000000000 : ℝ), (2573598489981/6250000000000 : ℝ), (3700659233107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(391862107/625000000 : ℝ)|^37 ≤ (13780441228763/25000000000000 : ℝ)^29
        have hw : |(391862107/625000000 : ℝ)|=(391862107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(997716973/2000000000 : ℝ)|^37 ≤ (2573598489981/6250000000000 : ℝ)^29
        have hw : |(997716973/2000000000 : ℝ)|=(997716973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(37740737/500000000 : ℝ)|^37 ≤ (3700659233107/100000000000000 : ℝ)^29
        have hw : |(37740737/500000000 : ℝ)|=(37740737/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_19 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-3950524149/10000000000 : ℝ)*x 0 + (49255869/125000000 : ℝ)*x 1 + (4775452523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3950524149/10000000000 : ℝ)^37 ≤ (15288224872119/50000000000000 : ℝ)^29 := by
    have hnat : (3950524149 : ℕ)^37*50000000000000^29 ≤ 15288224872119^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3950524149 10000000000 15288224872119 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49255869/125000000 : ℝ)^37 ≤ (30477195398201/100000000000000 : ℝ)^29 := by
    have hnat : (49255869 : ℕ)^37*100000000000000^29 ≤ 30477195398201^29*125000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49255869 125000000 30477195398201 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775452523/10000000000 : ℝ)^37 ≤ (19473177417353/50000000000000 : ℝ)^29 := by
    have hnat : (4775452523 : ℕ)^37*50000000000000^29 ≤ 19473177417353^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775452523 10000000000 19473177417353 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3950524149/10000000000 : ℝ), (49255869/125000000 : ℝ), (4775452523/10000000000 : ℝ)] ![(15288224872119/50000000000000 : ℝ), (30477195398201/100000000000000 : ℝ), (19473177417353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3950524149/10000000000 : ℝ)|^37 ≤ (15288224872119/50000000000000 : ℝ)^29
        have hw : |(-3950524149/10000000000 : ℝ)|=(3950524149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49255869/125000000 : ℝ)|^37 ≤ (30477195398201/100000000000000 : ℝ)^29
        have hw : |(49255869/125000000 : ℝ)|=(49255869/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4775452523/10000000000 : ℝ)|^37 ≤ (19473177417353/50000000000000 : ℝ)^29
        have hw : |(4775452523/10000000000 : ℝ)|=(4775452523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (129511877/500000000 : ℝ)*x 0 + (-1290991229/5000000000 : ℝ)*x 1 + (3540720897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129511877/500000000 : ℝ)^37 ≤ (1115275744361/6250000000000 : ℝ)^29 := by
    have hnat : (129511877 : ℕ)^37*6250000000000^29 ≤ 1115275744361^29*500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129511877 500000000 1115275744361 6250000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290991229/5000000000 : ℝ)^37 ≤ (8885942709427/50000000000000 : ℝ)^29 := by
    have hnat : (1290991229 : ℕ)^37*50000000000000^29 ≤ 8885942709427^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290991229 5000000000 8885942709427 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3540720897/5000000000 : ℝ)^37 ≤ (12876740533279/20000000000000 : ℝ)^29 := by
    have hnat : (3540720897 : ℕ)^37*20000000000000^29 ≤ 12876740533279^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3540720897 5000000000 12876740533279 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129511877/500000000 : ℝ), (-1290991229/5000000000 : ℝ), (3540720897/5000000000 : ℝ)] ![(1115275744361/6250000000000 : ℝ), (8885942709427/50000000000000 : ℝ), (12876740533279/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129511877/500000000 : ℝ)|^37 ≤ (1115275744361/6250000000000 : ℝ)^29
        have hw : |(129511877/500000000 : ℝ)|=(129511877/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1290991229/5000000000 : ℝ)|^37 ≤ (8885942709427/50000000000000 : ℝ)^29
        have hw : |(-1290991229/5000000000 : ℝ)|=(1290991229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3540720897/5000000000 : ℝ)|^37 ≤ (12876740533279/20000000000000 : ℝ)^29
        have hw : |(3540720897/5000000000 : ℝ)|=(3540720897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6178592631/10000000000 : ℝ)*x 0 + (939855877/2000000000 : ℝ)*x 1 + (-269280329/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6178592631/10000000000 : ℝ)^37 ≤ (10820165902589/20000000000000 : ℝ)^29 := by
    have hnat : (6178592631 : ℕ)^37*20000000000000^29 ≤ 10820165902589^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6178592631 10000000000 10820165902589 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (939855877/2000000000 : ℝ)^37 ≤ (3815549852113/10000000000000 : ℝ)^29 := by
    have hnat : (939855877 : ℕ)^37*10000000000000^29 ≤ 3815549852113^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      939855877 2000000000 3815549852113 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269280329/2000000000 : ℝ)^37 ≤ (774367194799/10000000000000 : ℝ)^29 := by
    have hnat : (269280329 : ℕ)^37*10000000000000^29 ≤ 774367194799^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269280329 2000000000 774367194799 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6178592631/10000000000 : ℝ), (939855877/2000000000 : ℝ), (-269280329/2000000000 : ℝ)] ![(10820165902589/20000000000000 : ℝ), (3815549852113/10000000000000 : ℝ), (774367194799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6178592631/10000000000 : ℝ)|^37 ≤ (10820165902589/20000000000000 : ℝ)^29
        have hw : |(6178592631/10000000000 : ℝ)|=(6178592631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(939855877/2000000000 : ℝ)|^37 ≤ (3815549852113/10000000000000 : ℝ)^29
        have hw : |(939855877/2000000000 : ℝ)|=(939855877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-269280329/2000000000 : ℝ)|^37 ≤ (774367194799/10000000000000 : ℝ)^29
        have hw : |(-269280329/2000000000 : ℝ)|=(269280329/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312051_s1_s1_25 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3641438763/10000000000 : ℝ)*x 0 + (714327507/1000000000 : ℝ)*x 1 + (645560751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3641438763/10000000000 : ℝ)^37 ≤ (27557821073579/100000000000000 : ℝ)^29 := by
    have hnat : (3641438763 : ℕ)^37*100000000000000^29 ≤ 27557821073579^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3641438763 10000000000 27557821073579 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (714327507/1000000000 : ℝ)^37 ≤ (32550915353349/50000000000000 : ℝ)^29 := by
    have hnat : (714327507 : ℕ)^37*50000000000000^29 ≤ 32550915353349^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714327507 1000000000 32550915353349 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (645560751/5000000000 : ℝ)^37 ≤ (1835087052789/25000000000000 : ℝ)^29 := by
    have hnat : (645560751 : ℕ)^37*25000000000000^29 ≤ 1835087052789^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645560751 5000000000 1835087052789 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3641438763/10000000000 : ℝ), (714327507/1000000000 : ℝ), (645560751/5000000000 : ℝ)] ![(27557821073579/100000000000000 : ℝ), (32550915353349/50000000000000 : ℝ), (1835087052789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3641438763/10000000000 : ℝ)|^37 ≤ (27557821073579/100000000000000 : ℝ)^29
        have hw : |(3641438763/10000000000 : ℝ)|=(3641438763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(714327507/1000000000 : ℝ)|^37 ≤ (32550915353349/50000000000000 : ℝ)^29
        have hw : |(714327507/1000000000 : ℝ)|=(714327507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(645560751/5000000000 : ℝ)|^37 ≤ (1835087052789/25000000000000 : ℝ)^29
        have hw : |(645560751/5000000000 : ℝ)|=(645560751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312051_s1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((78949/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78949/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(39683/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(39683/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10981/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10981/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4783/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4783/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (78949/100000 : ℝ) ^ (9/2 : ℝ) ≤ (34519130711833919491/100000000000000000000 : ℝ) := by
    have hpowers : (78949/100000 : ℝ)^9 ≤ (34519130711833919491/100000000000000000000 : ℝ)^2 := by
      have hnat : (78949 : ℕ)^9*100000000000000000000^2 ≤ 34519130711833919491^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78949 100000 34519130711833919491 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78949/100000 : ℝ)) (X := (34519130711833919491/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0a : (134519130711833919491/100000000000000000000 : ℝ) ≤ (667572895913699/625000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (134519130711833919491/100000000000000000000 : ℝ)^2 ≤ (667572895913699/625000000000000 : ℝ)^9 := by
      have hnat : (134519130711833919491 : ℕ)^2*625000000000000^9 ≤ 667572895913699^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        134519130711833919491 100000000000000000000 667572895913699 625000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (667572895913699/625000000000000 : ℝ)) (X := (134519130711833919491/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner0b : (84519130711833919491/50000000000000000000 : ℝ) ≤ (2247467047721511/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (84519130711833919491/50000000000000000000 : ℝ)^2 ≤ (2247467047721511/2000000000000000 : ℝ)^9 := by
      have hnat : (84519130711833919491 : ℕ)^2*2000000000000000^9 ≤ 2247467047721511^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84519130711833919491 50000000000000000000 2247467047721511 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2247467047721511/2000000000000000 : ℝ)) (X := (84519130711833919491/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(42572895913699/493431250000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(556168903988371/7894900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (78949/100000 : ℝ)) (alpha := (42572895913699/493431250000000 : ℝ)) (beta := (556168903988371/7894900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (78949/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(42572895913699/493431250000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(556168903988371/7894900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (78167/100000 : ℝ) ^ (9/2 : ℝ) ≤ (16503478959109677193/50000000000000000000 : ℝ) := by
    have hpowers : (78167/100000 : ℝ)^9 ≤ (16503478959109677193/50000000000000000000 : ℝ)^2 := by
      have hnat : (78167 : ℕ)^9*50000000000000000000^2 ≤ 16503478959109677193^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78167 100000 16503478959109677193 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78167/100000 : ℝ)) (X := (16503478959109677193/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1a : (66503478959109677193/50000000000000000000 : ℝ) ≤ (2130873317963383/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (66503478959109677193/50000000000000000000 : ℝ)^2 ≤ (2130873317963383/2000000000000000 : ℝ)^9 := by
      have hnat : (66503478959109677193 : ℕ)^2*2000000000000000^9 ≤ 2130873317963383^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66503478959109677193 50000000000000000000 2130873317963383 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2130873317963383/2000000000000000 : ℝ)) (X := (66503478959109677193/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner1b : (41503478959109677193/25000000000000000000 : ℝ) ≤ (11192342678255309/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (41503478959109677193/25000000000000000000 : ℝ)^2 ≤ (11192342678255309/10000000000000000 : ℝ)^9 := by
      have hnat : (41503478959109677193 : ℕ)^2*10000000000000000^9 ≤ 11192342678255309^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41503478959109677193 25000000000000000000 11192342678255309 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11192342678255309/10000000000000000 : ℝ)) (X := (41503478959109677193/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(130873317963383/1563340000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(268988044219197/3908350000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (78167/100000 : ℝ)) (alpha := (130873317963383/1563340000000000 : ℝ)) (beta := (268988044219197/3908350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (78167/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(130873317963383/1563340000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(268988044219197/3908350000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (39683/100000 : ℝ) ^ (9/2 : ℝ) ≤ (1562141019684215431/100000000000000000000 : ℝ) := by
    have hpowers : (39683/100000 : ℝ)^9 ≤ (1562141019684215431/100000000000000000000 : ℝ)^2 := by
      have hnat : (39683 : ℕ)^9*100000000000000000000^2 ≤ 1562141019684215431^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39683 100000 1562141019684215431 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39683/100000 : ℝ)) (X := (1562141019684215431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2a : (101562141019684215431/100000000000000000000 : ℝ) ≤ (5017252643693193/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (101562141019684215431/100000000000000000000 : ℝ)^2 ≤ (5017252643693193/5000000000000000 : ℝ)^9 := by
      have hnat : (101562141019684215431 : ℕ)^2*5000000000000000^9 ≤ 5017252643693193^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101562141019684215431 100000000000000000000 5017252643693193 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017252643693193/5000000000000000 : ℝ)) (X := (101562141019684215431/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s1_corner2b : (51562141019684215431/50000000000000000000 : ℝ) ≤ (2013720044272567/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (51562141019684215431/50000000000000000000 : ℝ)^2 ≤ (2013720044272567/2000000000000000 : ℝ)^9 := by
      have hnat : (51562141019684215431 : ℕ)^2*2000000000000000^9 ≤ 2013720044272567^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51562141019684215431 50000000000000000000 2013720044272567 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2013720044272567/2000000000000000 : ℝ)) (X := (51562141019684215431/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(17252643693193/1984150000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(34094933976449/3968300000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (39683/100000 : ℝ)) (alpha := (17252643693193/1984150000000000 : ℝ)) (beta := (34094933976449/3968300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (39683/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(17252643693193/1984150000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(34094933976449/3968300000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1834033579/5000000000 : ℝ)*X 0 0+(3657797611/10000000000 : ℝ)*X 0 1+(5298495709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2821011353/10000000000 : ℝ)*X 1 0+(-1406556661/5000000000 : ℝ)*X 1 1+(6724874807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((13668109/25000000 : ℝ)*X 2 0+(5480183489/10000000000 : ℝ)*X 2 1+(-128454253/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5202941871/10000000000 : ℝ)*X 0 0+(521525621/1000000000 : ℝ)*X 0 1+(80696201/400000000 : ℝ)*X 0 2+(5202941871/10000000000 : ℝ)*X 1 0+(521525621/1000000000 : ℝ)*X 1 1+(80696201/400000000 : ℝ)*X 1 2+(5202941871/10000000000 : ℝ)*X 2 0+(521525621/1000000000 : ℝ)*X 2 1+(80696201/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-676784879/2000000000 : ℝ)*X 0 0+(740673309/2500000000 : ℝ)*X 0 1+(24578987/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((646790091/2500000000 : ℝ)*X 1 0+(-45302209/200000000 : ℝ)*X 1 1+(3659194543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5038486071/10000000000 : ℝ)*X 2 0+(6362143473/10000000000 : ℝ)*X 2 1+(-49072341/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((4975246263/10000000000 : ℝ)*X 0 0+(6282289977/10000000000 : ℝ)*X 0 1+(754849037/10000000000 : ℝ)*X 0 2+(4975246263/10000000000 : ℝ)*X 1 0+(6282289977/10000000000 : ℝ)*X 1 1+(754849037/10000000000 : ℝ)*X 1 2+(4975246263/10000000000 : ℝ)*X 2 0+(6282289977/10000000000 : ℝ)*X 2 1+(754849037/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-185806023/625000000 : ℝ)*X 0 0+(674810827/2000000000 : ℝ)*X 0 1+(6144768703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((1136455879/5000000000 : ℝ)*X 1 0+(-2579614749/10000000000 : ℝ)*X 1 1+(1463680611/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6349483423/10000000000 : ℝ)*X 2 0+(5051990283/10000000000 : ℝ)*X 2 1+(-490701669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((391862107/625000000 : ℝ)*X 0 0+(997716973/2000000000 : ℝ)*X 0 1+(37740737/500000000 : ℝ)*X 0 2+(391862107/625000000 : ℝ)*X 1 0+(997716973/2000000000 : ℝ)*X 1 1+(37740737/500000000 : ℝ)*X 1 2+(391862107/625000000 : ℝ)*X 2 0+(997716973/2000000000 : ℝ)*X 2 1+(37740737/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-3950524149/10000000000 : ℝ)*X 0 0+(49255869/125000000 : ℝ)*X 0 1+(4775452523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((129511877/500000000 : ℝ)*X 1 0+(-1290991229/5000000000 : ℝ)*X 1 1+(3540720897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6178592631/10000000000 : ℝ)*X 2 0+(939855877/2000000000 : ℝ)*X 2 1+(-269280329/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((3641438763/10000000000 : ℝ)*X 0 0+(714327507/1000000000 : ℝ)*X 0 1+(645560751/5000000000 : ℝ)*X 0 2+(3641438763/10000000000 : ℝ)*X 1 0+(714327507/1000000000 : ℝ)*X 1 1+(645560751/5000000000 : ℝ)*X 1 2+(3641438763/10000000000 : ℝ)*X 2 0+(714327507/1000000000 : ℝ)*X 2 1+(645560751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312051_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((44003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72852669111070775563734728119863/12244599343244450000000000000000000000 : ℝ) := by norm_num
    linear_combination (138633436383/1000000000000 : ℝ)*(base49) + (186490307331/1000000000000 : ℝ)*(base59) + (1383915425757/1000000000000 : ℝ)*(base60) + (5513740415089/1000000000000 : ℝ)*(major_s1_0) + (5513740415089/1000000000000 : ℝ)*(major_s1_1) + (5513740415089/1000000000000 : ℝ)*(major_s1_2) + (17081671/1000000000000 : ℝ)*(sp_s1_2) + (348013/200000000000 : ℝ)*(sp_s1_6) + (3862058483359/500000000000 : ℝ)*(sp_s1_7) + (1544809948629/200000000000 : ℝ)*(sp_s1_8) + (7724099885047/1000000000000 : ℝ)*(sp_s1_9) + (825834414381/250000000000 : ℝ)*(sp_s1_12) + (67223573/1000000000000 : ℝ)*(sp_s1_14) + (4496521/200000000000 : ℝ)*(sp_s1_25) + (660672376039/200000000000 : ℝ)*(f.failure) + (3862058483359/500000000000 : ℝ)*(f.sum) + (145474727467289311467/310190106100000000000000000000000 : ℝ)*base63 + (2060849054484281/3968300000000000000000000000 : ℝ)*base65 + (516406371815131/1954175000000000000000000000 : ℝ)*base67 + (1018310571238083/1984150000000000000000000000 : ℝ)*base69 + (153371005377662133727/313293316700000000000000000000000 : ℝ)*base71 + (1060487477311099/7894900000000000000000000000 : ℝ)*base73 + (343719318937101/1563340000000000000000000000 : ℝ)*base75 + (792189262864839/1973725000000000000000000000 : ℝ)*base77 + (120360462465377556449/617120648300000000000000000000000 : ℝ)*base79 + (17607/20000000000000000 : ℝ)*base87 + (17607/20000000000000000 : ℝ)*base89 + (17607/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10981/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10981/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (27735635634194516272356483/1721391850000000000000000000000 : ℝ) := by norm_num
    linear_combination (138602452383/1000000000000 : ℝ)*(base49) + (192788418197/250000000000 : ℝ)*(base59) + (1638661894977/1000000000000 : ℝ)*(base60) + (5512474151821/1000000000000 : ℝ)*(major_s1_0) + (5512474151821/1000000000000 : ℝ)*(major_s1_1) + (5512474151821/1000000000000 : ℝ)*(major_s1_2) + (21910507/250000000000 : ℝ)*(sp_s1_0) + (8799747/250000000000 : ℝ)*(sp_s1_6) + (146358251/1000000000000 : ℝ)*(sp_s1_7) + (1544421137817/200000000000 : ℝ)*(sp_s1_13) + (7722339689363/1000000000000 : ℝ)*(sp_s1_14) + (7722212807771/1000000000000 : ℝ)*(sp_s1_15) + (3302568044511/1000000000000 : ℝ)*(sp_s1_18) + (15860199/125000000000 : ℝ)*(sp_s1_21) + (3302603243499/1000000000000 : ℝ)*(f.failure) + (7722339689363/1000000000000 : ℝ)*(f.sum) + (59090427814874481/44312872300000000000000000000000 : ℝ)*base62 + (223618856118713/566900000000000000000000000 : ℝ)*base64 + (158090504198683/977087500000000000000000000 : ℝ)*base66 + (58422828739009/283450000000000000000000000 : ℝ)*base68 + (765794207722647997/3442783700000000000000000000000 : ℝ)*base70 + (123546468771857/607300000000000000000000000 : ℝ)*base73 + (11147489428733/1563340000000000000000000000 : ℝ)*base75 + (39802685777/2372265625000000000000000 : ℝ)*base76 + (10904891359536766157/47470819100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (48587/100000000000000000 : ℝ)*base87 + (48587/100000000000000000 : ℝ)*base89 + (48587/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4783/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4783/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7750356205073226827675997181437/1224459934324445000000000000000000000 : ℝ) := by norm_num
    linear_combination (46433069459/500000000000 : ℝ)*(base39) + (48579188679/125000000000 : ℝ)*(base49) + (74970746679/1000000000000 : ℝ)*(base60) + (131005323457/50000000000 : ℝ)*(major_s1_0) + (131005323457/50000000000 : ℝ)*(major_s1_1) + (131005323457/50000000000 : ℝ)*(major_s1_2) + (9042483/100000000000 : ℝ)*(sp_s1_1) + (16236517/500000000000 : ℝ)*(sp_s1_8) + (3542179/1000000000000 : ℝ)*(sp_s1_12) + (42813261/1000000000000 : ℝ)*(sp_s1_15) + (1835233514127/500000000000 : ℝ)*(sp_s1_19) + (367034413039/100000000000 : ℝ)*(sp_s1_20) + (3670424214993/1000000000000 : ℝ)*(sp_s1_21) + (1569740257969/1000000000000 : ℝ)*(sp_s1_25) + (392435950037/250000000000 : ℝ)*(f.failure) + (1835233514127/500000000000 : ℝ)*(f.sum) + (3266730707259391199/7754752652500000000000000000000 : ℝ)*base62 + (435380510510233/396830000000000000000000000 : ℝ)*base64 + (698809938755917/781670000000000000000000000 : ℝ)*base66 + (187463838413087/198415000000000000000000000 : ℝ)*base68 + (17893939244551674489/31329331670000000000000000000000 : ℝ)*base70 + (422414454169701/789490000000000000000000000 : ℝ)*base72 + (7092501730677/9770875000000000000000000 : ℝ)*base74 + (658682690721893/789490000000000000000000000 : ℝ)*base76 + (18677077501620256447/61712064830000000000000000000000 : ℝ)*base78 + (25781/25000000000000000 : ℝ)*base87 + (25781/25000000000000000 : ℝ)*base89 + (25781/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((78949/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78949/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(39683/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(39683/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44003/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44003/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10981/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10981/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4783/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4783/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312051_s1 p hpa hpb X hX hprev0

#print axioms solution
