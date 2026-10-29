-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:27:03.563959+00:00
-- url     : https://prove2.me/submissions/e898906c-1fa9-4e6a-b428-69761f2f9cc1

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
theorem collision_support_c310055_s1_s1_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-22702403/200000000 : ℝ)*x 0 + (2981520851/5000000000 : ℝ)*x 1 + (1033937563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22702403/200000000 : ℝ)^71 ≤ (3013803383707/50000000000000 : ℝ)^55 := by
    have hnat : (22702403 : ℕ)^71*50000000000000^55 ≤ 3013803383707^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22702403 200000000 3013803383707 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2981520851/5000000000 : ℝ)^71 ≤ (51303784410893/100000000000000 : ℝ)^55 := by
    have hnat : (2981520851 : ℕ)^71*100000000000000^55 ≤ 51303784410893^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2981520851 5000000000 51303784410893 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033937563/2000000000 : ℝ)^71 ≤ (42668608806987/100000000000000 : ℝ)^55 := by
    have hnat : (1033937563 : ℕ)^71*100000000000000^55 ≤ 42668608806987^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033937563 2000000000 42668608806987 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22702403/200000000 : ℝ), (2981520851/5000000000 : ℝ), (1033937563/2000000000 : ℝ)] ![(3013803383707/50000000000000 : ℝ), (51303784410893/100000000000000 : ℝ), (42668608806987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22702403/200000000 : ℝ)|^71 ≤ (3013803383707/50000000000000 : ℝ)^55
        have hw : |(-22702403/200000000 : ℝ)|=(22702403/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2981520851/5000000000 : ℝ)|^71 ≤ (51303784410893/100000000000000 : ℝ)^55
        have hw : |(2981520851/5000000000 : ℝ)|=(2981520851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033937563/2000000000 : ℝ)|^71 ≤ (42668608806987/100000000000000 : ℝ)^55
        have hw : |(1033937563/2000000000 : ℝ)|=(1033937563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-615790709/2500000000 : ℝ)*x 0 + (880425301/2500000000 : ℝ)*x 1 + (3262042729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (615790709/2500000000 : ℝ)^71 ≤ (8192999821193/50000000000000 : ℝ)^55 := by
    have hnat : (615790709 : ℕ)^71*50000000000000^55 ≤ 8192999821193^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615790709 2500000000 8192999821193 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (880425301/2500000000 : ℝ)^71 ≤ (25995530779273/100000000000000 : ℝ)^55 := by
    have hnat : (880425301 : ℕ)^71*100000000000000^55 ≤ 25995530779273^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880425301 2500000000 25995530779273 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3262042729/5000000000 : ℝ)^71 ≤ (1440461739199/2500000000000 : ℝ)^55 := by
    have hnat : (3262042729 : ℕ)^71*2500000000000^55 ≤ 1440461739199^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3262042729 5000000000 1440461739199 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-615790709/2500000000 : ℝ), (880425301/2500000000 : ℝ), (3262042729/5000000000 : ℝ)] ![(8192999821193/50000000000000 : ℝ), (25995530779273/100000000000000 : ℝ), (1440461739199/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-615790709/2500000000 : ℝ)|^71 ≤ (8192999821193/50000000000000 : ℝ)^55
        have hw : |(-615790709/2500000000 : ℝ)|=(615790709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(880425301/2500000000 : ℝ)|^71 ≤ (25995530779273/100000000000000 : ℝ)^55
        have hw : |(880425301/2500000000 : ℝ)|=(880425301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3262042729/5000000000 : ℝ)|^71 ≤ (1440461739199/2500000000000 : ℝ)^55
        have hw : |(3262042729/5000000000 : ℝ)|=(3262042729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (127778531/500000000 : ℝ)*x 0 + (265319/5000000000 : ℝ)*x 1 + (864105393/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127778531/500000000 : ℝ)^71 ≤ (8591930012547/50000000000000 : ℝ)^55 := by
    have hnat : (127778531 : ℕ)^71*50000000000000^55 ≤ 8591930012547^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127778531 500000000 8591930012547 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265319/5000000000 : ℝ)^71 ≤ (75690841/25000000000000 : ℝ)^55 := by
    have hnat : (265319 : ℕ)^71*25000000000000^55 ≤ 75690841^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265319 5000000000 75690841 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (864105393/1000000000 : ℝ)^71 ≤ (82815837194087/100000000000000 : ℝ)^55 := by
    have hnat : (864105393 : ℕ)^71*100000000000000^55 ≤ 82815837194087^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864105393 1000000000 82815837194087 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127778531/500000000 : ℝ), (265319/5000000000 : ℝ), (864105393/1000000000 : ℝ)] ![(8591930012547/50000000000000 : ℝ), (75690841/25000000000000 : ℝ), (82815837194087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127778531/500000000 : ℝ)|^71 ≤ (8591930012547/50000000000000 : ℝ)^55
        have hw : |(127778531/500000000 : ℝ)|=(127778531/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265319/5000000000 : ℝ)|^71 ≤ (75690841/25000000000000 : ℝ)^55
        have hw : |(265319/5000000000 : ℝ)|=(265319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(864105393/1000000000 : ℝ)|^71 ≤ (82815837194087/100000000000000 : ℝ)^55
        have hw : |(864105393/1000000000 : ℝ)|=(864105393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2288300887/10000000000 : ℝ)*x 0 + (8415662381/10000000000 : ℝ)*x 1 + (-991523981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2288300887/10000000000 : ℝ)^71 ≤ (7450058446939/50000000000000 : ℝ)^55 := by
    have hnat : (2288300887 : ℕ)^71*50000000000000^55 ≤ 7450058446939^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2288300887 10000000000 7450058446939 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8415662381/10000000000 : ℝ)^71 ≤ (10004740392137/12500000000000 : ℝ)^55 := by
    have hnat : (8415662381 : ℕ)^71*12500000000000^55 ≤ 10004740392137^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8415662381 10000000000 10004740392137 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991523981/10000000000 : ℝ)^71 ≤ (506195995829/10000000000000 : ℝ)^55 := by
    have hnat : (991523981 : ℕ)^71*10000000000000^55 ≤ 506195995829^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991523981 10000000000 506195995829 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2288300887/10000000000 : ℝ), (8415662381/10000000000 : ℝ), (-991523981/10000000000 : ℝ)] ![(7450058446939/50000000000000 : ℝ), (10004740392137/12500000000000 : ℝ), (506195995829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2288300887/10000000000 : ℝ)|^71 ≤ (7450058446939/50000000000000 : ℝ)^55
        have hw : |(2288300887/10000000000 : ℝ)|=(2288300887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8415662381/10000000000 : ℝ)|^71 ≤ (10004740392137/12500000000000 : ℝ)^55
        have hw : |(8415662381/10000000000 : ℝ)|=(8415662381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-991523981/10000000000 : ℝ)|^71 ≤ (506195995829/10000000000000 : ℝ)^55
        have hw : |(-991523981/10000000000 : ℝ)|=(991523981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4038698857/10000000000 : ℝ)*x 0 + (704595681/1000000000 : ℝ)*x 1 + (1033470759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4038698857/10000000000 : ℝ)^71 ≤ (3877961998201/12500000000000 : ℝ)^55 := by
    have hnat : (4038698857 : ℕ)^71*12500000000000^55 ≤ 3877961998201^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038698857 10000000000 3877961998201 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (704595681/1000000000 : ℝ)^71 ≤ (31818106997041/50000000000000 : ℝ)^55 := by
    have hnat : (704595681 : ℕ)^71*50000000000000^55 ≤ 31818106997041^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704595681 1000000000 31818106997041 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033470759/10000000000 : ℝ)^71 ≤ (1068018000401/20000000000000 : ℝ)^55 := by
    have hnat : (1033470759 : ℕ)^71*20000000000000^55 ≤ 1068018000401^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033470759 10000000000 1068018000401 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4038698857/10000000000 : ℝ), (704595681/1000000000 : ℝ), (1033470759/10000000000 : ℝ)] ![(3877961998201/12500000000000 : ℝ), (31818106997041/50000000000000 : ℝ), (1068018000401/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4038698857/10000000000 : ℝ)|^71 ≤ (3877961998201/12500000000000 : ℝ)^55
        have hw : |(4038698857/10000000000 : ℝ)|=(4038698857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(704595681/1000000000 : ℝ)|^71 ≤ (31818106997041/50000000000000 : ℝ)^55
        have hw : |(704595681/1000000000 : ℝ)|=(704595681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1033470759/10000000000 : ℝ)|^71 ≤ (1068018000401/20000000000000 : ℝ)^55
        have hw : |(1033470759/10000000000 : ℝ)|=(1033470759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-366380931/5000000000 : ℝ)*x 0 + (737073697/2000000000 : ℝ)*x 1 + (7502513129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366380931/5000000000 : ℝ)^71 ≤ (3425864914713/100000000000000 : ℝ)^55 := by
    have hnat : (366380931 : ℕ)^71*100000000000000^55 ≤ 3425864914713^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366380931 5000000000 3425864914713 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (737073697/2000000000 : ℝ)^71 ≤ (13782762732301/50000000000000 : ℝ)^55 := by
    have hnat : (737073697 : ℕ)^71*50000000000000^55 ≤ 13782762732301^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737073697 2000000000 13782762732301 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7502513129/10000000000 : ℝ)^71 ≤ (34504304803351/50000000000000 : ℝ)^55 := by
    have hnat : (7502513129 : ℕ)^71*50000000000000^55 ≤ 34504304803351^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7502513129 10000000000 34504304803351 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366380931/5000000000 : ℝ), (737073697/2000000000 : ℝ), (7502513129/10000000000 : ℝ)] ![(3425864914713/100000000000000 : ℝ), (13782762732301/50000000000000 : ℝ), (34504304803351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366380931/5000000000 : ℝ)|^71 ≤ (3425864914713/100000000000000 : ℝ)^55
        have hw : |(-366380931/5000000000 : ℝ)|=(366380931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(737073697/2000000000 : ℝ)|^71 ≤ (13782762732301/50000000000000 : ℝ)^55
        have hw : |(737073697/2000000000 : ℝ)|=(737073697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7502513129/10000000000 : ℝ)|^71 ≤ (34504304803351/50000000000000 : ℝ)^55
        have hw : |(7502513129/10000000000 : ℝ)|=(7502513129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (419155981/2500000000 : ℝ)*x 0 + (-11074153/1250000000 : ℝ)*x 1 + (575039357/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419155981/2500000000 : ℝ)^71 ≤ (39891184561/400000000000 : ℝ)^55 := by
    have hnat : (419155981 : ℕ)^71*400000000000^55 ≤ 39891184561^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419155981 2500000000 39891184561 400000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11074153/1250000000 : ℝ)^71 ≤ (224016833281/100000000000000 : ℝ)^55 := by
    have hnat : (11074153 : ℕ)^71*100000000000000^55 ≤ 224016833281^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11074153 1250000000 224016833281 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (575039357/625000000 : ℝ)^71 ≤ (44901593505053/50000000000000 : ℝ)^55 := by
    have hnat : (575039357 : ℕ)^71*50000000000000^55 ≤ 44901593505053^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575039357 625000000 44901593505053 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419155981/2500000000 : ℝ), (-11074153/1250000000 : ℝ), (575039357/625000000 : ℝ)] ![(39891184561/400000000000 : ℝ), (224016833281/100000000000000 : ℝ), (44901593505053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419155981/2500000000 : ℝ)|^71 ≤ (39891184561/400000000000 : ℝ)^55
        have hw : |(419155981/2500000000 : ℝ)|=(419155981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11074153/1250000000 : ℝ)|^71 ≤ (224016833281/100000000000000 : ℝ)^55
        have hw : |(-11074153/1250000000 : ℝ)|=(11074153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(575039357/625000000 : ℝ)|^71 ≤ (44901593505053/50000000000000 : ℝ)^55
        have hw : |(575039357/625000000 : ℝ)|=(575039357/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3619388731/5000000000 : ℝ)*x 0 + (2002776883/5000000000 : ℝ)*x 1 + (-365181299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3619388731/5000000000 : ℝ)^71 ≤ (65893194688353/100000000000000 : ℝ)^55 := by
    have hnat : (3619388731 : ℕ)^71*100000000000000^55 ≤ 65893194688353^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3619388731 5000000000 65893194688353 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002776883/5000000000 : ℝ)^71 ≤ (3069541389521/10000000000000 : ℝ)^55 := by
    have hnat : (2002776883 : ℕ)^71*10000000000000^55 ≤ 3069541389521^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002776883 5000000000 3069541389521 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365181299/5000000000 : ℝ)^71 ≤ (341139139931/10000000000000 : ℝ)^55 := by
    have hnat : (365181299 : ℕ)^71*10000000000000^55 ≤ 341139139931^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365181299 5000000000 341139139931 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3619388731/5000000000 : ℝ), (2002776883/5000000000 : ℝ), (-365181299/5000000000 : ℝ)] ![(65893194688353/100000000000000 : ℝ), (3069541389521/10000000000000 : ℝ), (341139139931/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3619388731/5000000000 : ℝ)|^71 ≤ (65893194688353/100000000000000 : ℝ)^55
        have hw : |(3619388731/5000000000 : ℝ)|=(3619388731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002776883/5000000000 : ℝ)|^71 ≤ (3069541389521/10000000000000 : ℝ)^55
        have hw : |(2002776883/5000000000 : ℝ)|=(2002776883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365181299/5000000000 : ℝ)|^71 ≤ (341139139931/10000000000000 : ℝ)^55
        have hw : |(-365181299/5000000000 : ℝ)|=(365181299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1081279351/1250000000 : ℝ)*x 0 + (2116296471/10000000000 : ℝ)*x 1 + (190369499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081279351/1250000000 : ℝ)^71 ≤ (4146472060067/5000000000000 : ℝ)^55 := by
    have hnat : (1081279351 : ℕ)^71*5000000000000^55 ≤ 4146472060067^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081279351 1250000000 4146472060067 5000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2116296471/10000000000 : ℝ)^71 ≤ (2694080561669/20000000000000 : ℝ)^55 := by
    have hnat : (2116296471 : ℕ)^71*20000000000000^55 ≤ 2694080561669^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116296471 10000000000 2694080561669 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190369499/2500000000 : ℝ)^71 ≤ (1800077988723/50000000000000 : ℝ)^55 := by
    have hnat : (190369499 : ℕ)^71*50000000000000^55 ≤ 1800077988723^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190369499 2500000000 1800077988723 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081279351/1250000000 : ℝ), (2116296471/10000000000 : ℝ), (190369499/2500000000 : ℝ)] ![(4146472060067/5000000000000 : ℝ), (2694080561669/20000000000000 : ℝ), (1800077988723/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081279351/1250000000 : ℝ)|^71 ≤ (4146472060067/5000000000000 : ℝ)^55
        have hw : |(1081279351/1250000000 : ℝ)|=(1081279351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2116296471/10000000000 : ℝ)|^71 ≤ (2694080561669/20000000000000 : ℝ)^55
        have hw : |(2116296471/10000000000 : ℝ)|=(2116296471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(190369499/2500000000 : ℝ)|^71 ≤ (1800077988723/50000000000000 : ℝ)^55
        have hw : |(190369499/2500000000 : ℝ)|=(190369499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3249229/31250000 : ℝ)*x 0 + (4058171243/5000000000 : ℝ)*x 1 + (1337966881/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3249229/31250000 : ℝ)^71 ≤ (5382033368609/100000000000000 : ℝ)^55 := by
    have hnat : (3249229 : ℕ)^71*100000000000000^55 ≤ 5382033368609^55*31250000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3249229 31250000 5382033368609 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4058171243/5000000000 : ℝ)^71 ≤ (38191127068543/50000000000000 : ℝ)^55 := by
    have hnat : (4058171243 : ℕ)^71*50000000000000^55 ≤ 38191127068543^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4058171243 5000000000 38191127068543 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1337966881/5000000000 : ℝ)^71 ≤ (1823571248383/10000000000000 : ℝ)^55 := by
    have hnat : (1337966881 : ℕ)^71*10000000000000^55 ≤ 1823571248383^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337966881 5000000000 1823571248383 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3249229/31250000 : ℝ), (4058171243/5000000000 : ℝ), (1337966881/5000000000 : ℝ)] ![(5382033368609/100000000000000 : ℝ), (38191127068543/50000000000000 : ℝ), (1823571248383/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3249229/31250000 : ℝ)|^71 ≤ (5382033368609/100000000000000 : ℝ)^55
        have hw : |(-3249229/31250000 : ℝ)|=(3249229/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4058171243/5000000000 : ℝ)|^71 ≤ (38191127068543/50000000000000 : ℝ)^55
        have hw : |(4058171243/5000000000 : ℝ)|=(4058171243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1337966881/5000000000 : ℝ)|^71 ≤ (1823571248383/10000000000000 : ℝ)^55
        have hw : |(1337966881/5000000000 : ℝ)|=(1337966881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7277575919/10000000000 : ℝ)*x 0 + (-10060641/10000000000 : ℝ)*x 1 + (4299819461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7277575919/10000000000 : ℝ)^71 ≤ (33174733162211/50000000000000 : ℝ)^55 := by
    have hnat : (7277575919 : ℕ)^71*50000000000000^55 ≤ 33174733162211^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7277575919 10000000000 33174733162211 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10060641/10000000000 : ℝ)^71 ≤ (1351021329/10000000000000 : ℝ)^55 := by
    have hnat : (10060641 : ℕ)^71*10000000000000^55 ≤ 1351021329^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10060641 10000000000 1351021329 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4299819461/10000000000 : ℝ)^71 ≤ (33637023451829/100000000000000 : ℝ)^55 := by
    have hnat : (4299819461 : ℕ)^71*100000000000000^55 ≤ 33637023451829^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299819461 10000000000 33637023451829 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7277575919/10000000000 : ℝ), (-10060641/10000000000 : ℝ), (4299819461/10000000000 : ℝ)] ![(33174733162211/50000000000000 : ℝ), (1351021329/10000000000000 : ℝ), (33637023451829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7277575919/10000000000 : ℝ)|^71 ≤ (33174733162211/50000000000000 : ℝ)^55
        have hw : |(7277575919/10000000000 : ℝ)|=(7277575919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10060641/10000000000 : ℝ)|^71 ≤ (1351021329/10000000000000 : ℝ)^55
        have hw : |(-10060641/10000000000 : ℝ)|=(10060641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4299819461/10000000000 : ℝ)|^71 ≤ (33637023451829/100000000000000 : ℝ)^55
        have hw : |(4299819461/10000000000 : ℝ)|=(4299819461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1432780581/10000000000 : ℝ)*x 0 + (537349323/625000000 : ℝ)*x 1 + (-1625239627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1432780581/10000000000 : ℝ)^71 ≤ (8141504860823/100000000000000 : ℝ)^55 := by
    have hnat : (1432780581 : ℕ)^71*100000000000000^55 ≤ 8141504860823^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1432780581 10000000000 8141504860823 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537349323/625000000 : ℝ)^71 ≤ (41139241029571/50000000000000 : ℝ)^55 := by
    have hnat : (537349323 : ℕ)^71*50000000000000^55 ≤ 41139241029571^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537349323 625000000 41139241029571 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625239627/10000000000 : ℝ)^71 ≤ (74843852159/781250000000 : ℝ)^55 := by
    have hnat : (1625239627 : ℕ)^71*781250000000^55 ≤ 74843852159^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625239627 10000000000 74843852159 781250000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1432780581/10000000000 : ℝ), (537349323/625000000 : ℝ), (-1625239627/10000000000 : ℝ)] ![(8141504860823/100000000000000 : ℝ), (41139241029571/50000000000000 : ℝ), (74843852159/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1432780581/10000000000 : ℝ)|^71 ≤ (8141504860823/100000000000000 : ℝ)^55
        have hw : |(1432780581/10000000000 : ℝ)|=(1432780581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537349323/625000000 : ℝ)|^71 ≤ (41139241029571/50000000000000 : ℝ)^55
        have hw : |(537349323/625000000 : ℝ)|=(537349323/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1625239627/10000000000 : ℝ)|^71 ≤ (74843852159/781250000000 : ℝ)^55
        have hw : |(-1625239627/10000000000 : ℝ)|=(1625239627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s1_s1_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1674930561/2000000000 : ℝ)*x 0 + (2038276549/10000000000 : ℝ)*x 1 + (1362875063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1674930561/2000000000 : ℝ)^71 ≤ (79534793208547/100000000000000 : ℝ)^55 := by
    have hnat : (1674930561 : ℕ)^71*100000000000000^55 ≤ 79534793208547^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674930561 2000000000 79534793208547 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2038276549/10000000000 : ℝ)^71 ≤ (6416400600411/50000000000000 : ℝ)^55 := by
    have hnat : (2038276549 : ℕ)^71*50000000000000^55 ≤ 6416400600411^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038276549 10000000000 6416400600411 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362875063/10000000000 : ℝ)^71 ≤ (3816202787831/50000000000000 : ℝ)^55 := by
    have hnat : (1362875063 : ℕ)^71*50000000000000^55 ≤ 3816202787831^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362875063 10000000000 3816202787831 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1674930561/2000000000 : ℝ), (2038276549/10000000000 : ℝ), (1362875063/10000000000 : ℝ)] ![(79534793208547/100000000000000 : ℝ), (6416400600411/50000000000000 : ℝ), (3816202787831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1674930561/2000000000 : ℝ)|^71 ≤ (79534793208547/100000000000000 : ℝ)^55
        have hw : |(1674930561/2000000000 : ℝ)|=(1674930561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2038276549/10000000000 : ℝ)|^71 ≤ (6416400600411/50000000000000 : ℝ)^55
        have hw : |(2038276549/10000000000 : ℝ)|=(2038276549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362875063/10000000000 : ℝ)|^71 ≤ (3816202787831/50000000000000 : ℝ)^55
        have hw : |(1362875063/10000000000 : ℝ)|=(1362875063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310055_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((89013/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89013/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2744/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2744/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(87887/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(87887/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38651/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38651/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9341/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9341/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37943/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37943/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (89013/100000 : ℝ) ^ (35/8 : ℝ) ≤ (30048915112524893467/50000000000000000000 : ℝ) := by
    have hpowers : (89013/100000 : ℝ)^35 ≤ (30048915112524893467/50000000000000000000 : ℝ)^8 := by
      have hnat : (89013 : ℕ)^35*50000000000000000000^8 ≤ 30048915112524893467^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89013 100000 30048915112524893467 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89013/100000 : ℝ)) (X := (30048915112524893467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (80048915112524893467/50000000000000000000 : ℝ) ≤ (1391959778918749/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (80048915112524893467/50000000000000000000 : ℝ)^8 ≤ (1391959778918749/1250000000000000 : ℝ)^35 := by
      have hnat : (80048915112524893467 : ℕ)^8*1250000000000000^35 ≤ 1391959778918749^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        80048915112524893467 50000000000000000000 1391959778918749 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1391959778918749/1250000000000000 : ℝ)) (X := (80048915112524893467/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55048915112524893467/25000000000000000000 : ℝ) ≤ (5988613587927951/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (55048915112524893467/25000000000000000000 : ℝ)^8 ≤ (5988613587927951/5000000000000000 : ℝ)^35 := by
      have hnat : (55048915112524893467 : ℕ)^8*5000000000000000^35 ≤ 5988613587927951^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55048915112524893467 25000000000000000000 5988613587927951 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5988613587927951/5000000000000000 : ℝ)) (X := (55048915112524893467/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(141959778918749/1112662500000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(84154894450591/890130000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (89013/100000 : ℝ)) (alpha := (141959778918749/1112662500000000 : ℝ)) (beta := (84154894450591/890130000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (89013/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(141959778918749/1112662500000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(84154894450591/890130000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (2744/3125 : ℝ) ^ (35/8 : ℝ) ≤ (56618925532945519361/100000000000000000000 : ℝ) := by
    have hpowers : (2744/3125 : ℝ)^35 ≤ (56618925532945519361/100000000000000000000 : ℝ)^8 := by
      have hnat : (2744 : ℕ)^35*100000000000000000000^8 ≤ 56618925532945519361^8*3125^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2744 3125 56618925532945519361 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2744/3125 : ℝ)) (X := (56618925532945519361/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (156618925532945519361/100000000000000000000 : ℝ) ≤ (11079899632230363/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (156618925532945519361/100000000000000000000 : ℝ)^8 ≤ (11079899632230363/10000000000000000 : ℝ)^35 := by
      have hnat : (156618925532945519361 : ℕ)^8*10000000000000000^35 ≤ 11079899632230363^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156618925532945519361 100000000000000000000 11079899632230363 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11079899632230363/10000000000000000 : ℝ)) (X := (156618925532945519361/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (106618925532945519361/50000000000000000000 : ℝ) ≤ (11889647588076317/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (106618925532945519361/50000000000000000000 : ℝ)^8 ≤ (11889647588076317/10000000000000000 : ℝ)^35 := by
      have hnat : (106618925532945519361 : ℕ)^8*10000000000000000^35 ≤ 11889647588076317^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106618925532945519361 50000000000000000000 11889647588076317 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11889647588076317/10000000000000000 : ℝ)) (X := (106618925532945519361/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(154271376032909/1254400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(404873977922977/4390400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (2744/3125 : ℝ)) (alpha := (154271376032909/1254400000000000 : ℝ)) (beta := (404873977922977/4390400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2744/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(154271376032909/1254400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(404873977922977/4390400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (87887/100000 : ℝ) ^ (35/8 : ℝ) ≤ (28421062207110850473/50000000000000000000 : ℝ) := by
    have hpowers : (87887/100000 : ℝ)^35 ≤ (28421062207110850473/50000000000000000000 : ℝ)^8 := by
      have hnat : (87887 : ℕ)^35*50000000000000000000^8 ≤ 28421062207110850473^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87887 100000 28421062207110850473 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (87887/100000 : ℝ)) (X := (28421062207110850473/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (78421062207110850473/50000000000000000000 : ℝ) ≤ (5541753402535801/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (78421062207110850473/50000000000000000000 : ℝ)^8 ≤ (5541753402535801/5000000000000000 : ℝ)^35 := by
      have hnat : (78421062207110850473 : ℕ)^8*5000000000000000^35 ≤ 5541753402535801^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78421062207110850473 50000000000000000000 5541753402535801 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5541753402535801/5000000000000000 : ℝ)) (X := (78421062207110850473/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (53421062207110850473/25000000000000000000 : ℝ) ≤ (11895332166351321/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (53421062207110850473/25000000000000000000 : ℝ)^8 ≤ (11895332166351321/10000000000000000 : ℝ)^35 := by
      have hnat : (53421062207110850473 : ℕ)^8*10000000000000000^35 ≤ 11895332166351321^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53421062207110850473 25000000000000000000 11895332166351321 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11895332166351321/10000000000000000 : ℝ)) (X := (53421062207110850473/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(541753402535801/4394350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(811825361279719/8788700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (87887/100000 : ℝ)) (alpha := (541753402535801/4394350000000000 : ℝ)) (beta := (811825361279719/8788700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (87887/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(541753402535801/4394350000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(811825361279719/8788700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-22702403/200000000 : ℝ)*X 0 0+(2981520851/5000000000 : ℝ)*X 0 1+(1033937563/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-615790709/2500000000 : ℝ)*X 0 0+(880425301/2500000000 : ℝ)*X 0 1+(3262042729/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((127778531/500000000 : ℝ)*X 1 0+(265319/5000000000 : ℝ)*X 1 1+(864105393/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2288300887/10000000000 : ℝ)*X 2 0+(8415662381/10000000000 : ℝ)*X 2 1+(-991523981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4038698857/10000000000 : ℝ)*X 0 0+(704595681/1000000000 : ℝ)*X 0 1+(1033470759/10000000000 : ℝ)*X 0 2+(4038698857/10000000000 : ℝ)*X 1 0+(704595681/1000000000 : ℝ)*X 1 1+(1033470759/10000000000 : ℝ)*X 1 2+(4038698857/10000000000 : ℝ)*X 2 0+(704595681/1000000000 : ℝ)*X 2 1+(1033470759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-366380931/5000000000 : ℝ)*X 0 0+(737073697/2000000000 : ℝ)*X 0 1+(7502513129/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((419155981/2500000000 : ℝ)*X 1 0+(-11074153/1250000000 : ℝ)*X 1 1+(575039357/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((3619388731/5000000000 : ℝ)*X 2 0+(2002776883/5000000000 : ℝ)*X 2 1+(-365181299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1081279351/1250000000 : ℝ)*X 0 0+(2116296471/10000000000 : ℝ)*X 0 1+(190369499/2500000000 : ℝ)*X 0 2+(1081279351/1250000000 : ℝ)*X 1 0+(2116296471/10000000000 : ℝ)*X 1 1+(190369499/2500000000 : ℝ)*X 1 2+(1081279351/1250000000 : ℝ)*X 2 0+(2116296471/10000000000 : ℝ)*X 2 1+(190369499/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-3249229/31250000 : ℝ)*X 0 0+(4058171243/5000000000 : ℝ)*X 0 1+(1337966881/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7277575919/10000000000 : ℝ)*X 1 0+(-10060641/10000000000 : ℝ)*X 1 1+(4299819461/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1432780581/10000000000 : ℝ)*X 2 0+(537349323/625000000 : ℝ)*X 2 1+(-1625239627/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1674930561/2000000000 : ℝ)*X 0 0+(2038276549/10000000000 : ℝ)*X 0 1+(1362875063/10000000000 : ℝ)*X 0 2+(1674930561/2000000000 : ℝ)*X 1 0+(2038276549/10000000000 : ℝ)*X 1 1+(1362875063/10000000000 : ℝ)*X 1 2+(1674930561/2000000000 : ℝ)*X 2 0+(2038276549/10000000000 : ℝ)*X 2 1+(1362875063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((38651/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38651/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72452108899955768982230598145041/11448824905100800000000000000000000000 : ℝ) := by norm_num
    linear_combination (205784924093/250000000000 : ℝ)*(base7) + (1220499/1000000000000 : ℝ)*(base49) + (766814793/1953125000 : ℝ)*(base53) + (140797/200000000000 : ℝ)*(base60) + (1780080027003/1000000000000 : ℝ)*(major_s1_0) + (1780080027003/1000000000000 : ℝ)*(major_s1_1) + (1387470852987/1000000000000 : ℝ)*(major_s1_2) + (100547/8000000000 : ℝ)*(sp_s1_0) + (785189441801/500000000000 : ℝ)*(sp_s1_7) + (314079733367/200000000000 : ℝ)*(sp_s1_8) + (392599579869/200000000000 : ℝ)*(sp_s1_9) + (1923360365377/1000000000000 : ℝ)*(sp_s1_13) + (3607429/500000000000 : ℝ)*(sp_s1_14) + (4970753/500000000000 : ℝ)*(sp_s1_23) + (220044133801/200000000000 : ℝ)*(f.failure) + (1963007840851/1000000000000 : ℝ)*(f.sum) + (252024749613845627/881963622400000000000000000000 : ℝ)*base62 + (1009336585498807/8788700000000000000000000000 : ℝ)*base64 + (1507264638708571/4390400000000000000000000000 : ℝ)*base66 + (198160736990407/1098587500000000000000000000 : ℝ)*base68 + (59526365263178008933/260769517700000000000000000000000 : ℝ)*base70 + (688142636397/74177500000000000000000000 : ℝ)*base73 + (263042257367873/1254400000000000000000000000 : ℝ)*base74 + (215333816427169/1483550000000000000000000000 : ℝ)*base76 + (33594279671077974301/130267558400000000000000000000000 : ℝ)*base78 + (5193/20000000000000000 : ℝ)*base87 + (5193/20000000000000000 : ℝ)*base89 + (5193/20000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9341/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9341/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (141011845786662634354704967487303/11448824905100800000000000000000000000 : ℝ) := by norm_num
    linear_combination (381771201211/500000000000 : ℝ)*(base7) + (1737169/1000000000000 : ℝ)*(base40) + (50902447/1000000000000 : ℝ)*(base53) + (1364119/1000000000000 : ℝ)*(base59) + (65356966571/40000000000 : ℝ)*(major_s1_0) + (65356966571/40000000000 : ℝ)*(major_s1_1) + (408468315457/250000000000 : ℝ)*(major_s1_2) + (31225799/500000000000 : ℝ)*(sp_s1_0) + (15847381/1000000000000 : ℝ)*(sp_s1_7) + (179138691/1000000000000 : ℝ)*(sp_s1_8) + (1796878900731/1000000000000 : ℝ)*(sp_s1_14) + (1796778061019/1000000000000 : ℝ)*(sp_s1_15) + (1797008102157/1000000000000 : ℝ)*(sp_s1_16) + (1773427974897/1000000000000 : ℝ)*(sp_s1_20) + (40395422899/40000000000 : ℝ)*(f.failure) + (1797008102157/1000000000000 : ℝ)*(f.sum) + (18591228788132324249/110245452800000000000000000000000 : ℝ)*base63 + (917291618591099/1098587500000000000000000000 : ℝ)*base65 + (169867382133833/878080000000000000000000000 : ℝ)*base67 + (371234587916027/1098587500000000000000000000 : ℝ)*base69 + (30544015837489231163/391154276550000000000000000000000 : ℝ)*base71 + (143807268563023/178026000000000000000000000 : ℝ)*base73 + (20335926849583/50176000000000000000000000 : ℝ)*base75 + (182049295770157/890130000000000000000000000 : ℝ)*base76 + (38672001414316739741/78160535040000000000000000000000 : ℝ)*base79 + (2093/4000000000000000 : ℝ)*base86 + (2093/4000000000000000 : ℝ)*base88 + (2093/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37943/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37943/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (135098522099324118213808054518139/11448824905100800000000000000000000000 : ℝ) := by norm_num
    linear_combination (220152403237/250000000000 : ℝ)*(base7) + (455293/1000000000000 : ℝ)*(base11) + (25210678123/1000000000000 : ℝ)*(base40) + (647407/200000000000 : ℝ)*(base43) + (1321/1000000000000 : ℝ)*(base50) + (324676445911/200000000000 : ℝ)*(major_s1_0) + (1623378992521/1000000000000 : ℝ)*(major_s1_1) + (324676445911/200000000000 : ℝ)*(major_s1_2) + (33879303/500000000000 : ℝ)*(sp_s1_9) + (6145541/200000000000 : ℝ)*(sp_s1_20) + (42794073257/25000000000 : ℝ)*(sp_s1_21) + (106985413913/62500000000 : ℝ)*(sp_s1_22) + (1711695626967/1000000000000 : ℝ)*(sp_s1_23) + (1883948765001/1000000000000 : ℝ)*(sp_s1_27) + (1003369879757/1000000000000 : ℝ)*(f.failure) + (106985413913/62500000000 : ℝ)*(f.sum) + (33640416781824473317/110245452800000000000000000000000 : ℝ)*base62 + (262263834465593/1757740000000000000000000000 : ℝ)*base65 + (1259316250276137/4390400000000000000000000000 : ℝ)*base66 + (266212446756007/219717500000000000000000000 : ℝ)*base68 + (6629093189188528651/156461710620000000000000000000000 : ℝ)*base70 + (326425878223949/445065000000000000000000000 : ℝ)*base72 + (795167522085771/1254400000000000000000000000 : ℝ)*base74 + (96491338371529/445065000000000000000000000 : ℝ)*base77 + (35019576989229641981/390802675200000000000000000000000 : ℝ)*base78 + (24301/100000000000000000 : ℝ)*base87 + (75699/100000000000000000 : ℝ)*base88 + (24301/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((89013/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(89013/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2744/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2744/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(87887/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(87887/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((38651/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38651/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9341/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9341/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37943/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(37943/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310055_s1 p hpa hpb X hX hprev0

#print axioms solution
