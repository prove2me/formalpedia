-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308048_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:34:55.985614+00:00
-- url     : https://prove2.me/submissions/2dd3859c-10af-48e2-9f01-6d49ce4958b6

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
theorem collision_support_c308048_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-270769891/1000000000 : ℝ)*x 0 + (2705514859/10000000000 : ℝ)*x 1 + (-3511478973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270769891/1000000000 : ℝ)^35 ≤ (18385775857081/100000000000000 : ℝ)^27 := by
    have hnat : (270769891 : ℕ)^35*100000000000000^27 ≤ 18385775857081^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270769891 1000000000 18385775857081 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705514859/10000000000 : ℝ)^35 ≤ (18366553938351/100000000000000 : ℝ)^27 := by
    have hnat : (2705514859 : ℕ)^35*100000000000000^27 ≤ 18366553938351^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705514859 10000000000 18366553938351 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3511478973/5000000000 : ℝ)^35 ≤ (15811917548897/25000000000000 : ℝ)^27 := by
    have hnat : (3511478973 : ℕ)^35*25000000000000^27 ≤ 15811917548897^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3511478973 5000000000 15811917548897 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-270769891/1000000000 : ℝ), (2705514859/10000000000 : ℝ), (-3511478973/5000000000 : ℝ)] ![(18385775857081/100000000000000 : ℝ), (18366553938351/100000000000000 : ℝ), (15811917548897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-270769891/1000000000 : ℝ)|^35 ≤ (18385775857081/100000000000000 : ℝ)^27
        have hw : |(-270769891/1000000000 : ℝ)|=(270769891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705514859/10000000000 : ℝ)|^35 ≤ (18366553938351/100000000000000 : ℝ)^27
        have hw : |(2705514859/10000000000 : ℝ)|=(2705514859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3511478973/5000000000 : ℝ)|^35 ≤ (15811917548897/25000000000000 : ℝ)^27
        have hw : |(-3511478973/5000000000 : ℝ)|=(3511478973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (534997899/1000000000 : ℝ)*x 0 + (267669481/500000000 : ℝ)*x 1 + (-915047419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534997899/1000000000 : ℝ)^35 ≤ (44449185052739/100000000000000 : ℝ)^27 := by
    have hnat : (534997899 : ℕ)^35*100000000000000^27 ≤ 44449185052739^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534997899 1000000000 44449185052739 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (267669481/500000000 : ℝ)^35 ≤ (44485921032171/100000000000000 : ℝ)^27 := by
    have hnat : (267669481 : ℕ)^35*100000000000000^27 ≤ 44485921032171^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267669481 500000000 44485921032171 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (915047419/5000000000 : ℝ)^35 ≤ (11064893906299/100000000000000 : ℝ)^27 := by
    have hnat : (915047419 : ℕ)^35*100000000000000^27 ≤ 11064893906299^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      915047419 5000000000 11064893906299 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534997899/1000000000 : ℝ), (267669481/500000000 : ℝ), (-915047419/5000000000 : ℝ)] ![(44449185052739/100000000000000 : ℝ), (44485921032171/100000000000000 : ℝ), (11064893906299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534997899/1000000000 : ℝ)|^35 ≤ (44449185052739/100000000000000 : ℝ)^27
        have hw : |(534997899/1000000000 : ℝ)|=(534997899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(267669481/500000000 : ℝ)|^35 ≤ (44485921032171/100000000000000 : ℝ)^27
        have hw : |(267669481/500000000 : ℝ)|=(267669481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-915047419/5000000000 : ℝ)|^35 ≤ (11064893906299/100000000000000 : ℝ)^27
        have hw : |(-915047419/5000000000 : ℝ)|=(915047419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2256686141/10000000000 : ℝ)*x 0 + (199394991/1000000000 : ℝ)*x 1 + (-3927047773/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256686141/10000000000 : ℝ)^35 ≤ (2903601801781/20000000000000 : ℝ)^27 := by
    have hnat : (2256686141 : ℕ)^35*20000000000000^27 ≤ 2903601801781^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256686141 10000000000 2903601801781 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199394991/1000000000 : ℝ)^35 ≤ (12365798585337/100000000000000 : ℝ)^27 := by
    have hnat : (199394991 : ℕ)^35*100000000000000^27 ≤ 12365798585337^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199394991 1000000000 12365798585337 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3927047773/5000000000 : ℝ)^35 ≤ (73116192391729/100000000000000 : ℝ)^27 := by
    have hnat : (3927047773 : ℕ)^35*100000000000000^27 ≤ 73116192391729^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3927047773 5000000000 73116192391729 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2256686141/10000000000 : ℝ), (199394991/1000000000 : ℝ), (-3927047773/5000000000 : ℝ)] ![(2903601801781/20000000000000 : ℝ), (12365798585337/100000000000000 : ℝ), (73116192391729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2256686141/10000000000 : ℝ)|^35 ≤ (2903601801781/20000000000000 : ℝ)^27
        have hw : |(-2256686141/10000000000 : ℝ)|=(2256686141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199394991/1000000000 : ℝ)|^35 ≤ (12365798585337/100000000000000 : ℝ)^27
        have hw : |(199394991/1000000000 : ℝ)|=(199394991/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3927047773/5000000000 : ℝ)|^35 ≤ (73116192391729/100000000000000 : ℝ)^27
        have hw : |(-3927047773/5000000000 : ℝ)|=(3927047773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (161752627/500000000 : ℝ)*x 0 + (-285840933/1000000000 : ℝ)*x 1 + (-6492101431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161752627/500000000 : ℝ)^35 ≤ (5788966053343/25000000000000 : ℝ)^27 := by
    have hnat : (161752627 : ℕ)^35*25000000000000^27 ≤ 5788966053343^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161752627 500000000 5788966053343 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285840933/1000000000 : ℝ)^35 ≤ (3944628395233/20000000000000 : ℝ)^27 := by
    have hnat : (285840933 : ℕ)^35*20000000000000^27 ≤ 3944628395233^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285840933 1000000000 3944628395233 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6492101431/10000000000 : ℝ)^35 ≤ (11424198759679/20000000000000 : ℝ)^27 := by
    have hnat : (6492101431 : ℕ)^35*20000000000000^27 ≤ 11424198759679^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6492101431 10000000000 11424198759679 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161752627/500000000 : ℝ), (-285840933/1000000000 : ℝ), (-6492101431/10000000000 : ℝ)] ![(5788966053343/25000000000000 : ℝ), (3944628395233/20000000000000 : ℝ), (11424198759679/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161752627/500000000 : ℝ)|^35 ≤ (5788966053343/25000000000000 : ℝ)^27
        have hw : |(161752627/500000000 : ℝ)|=(161752627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285840933/1000000000 : ℝ)|^35 ≤ (3944628395233/20000000000000 : ℝ)^27
        have hw : |(-285840933/1000000000 : ℝ)|=(285840933/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6492101431/10000000000 : ℝ)|^35 ≤ (11424198759679/20000000000000 : ℝ)^27
        have hw : |(-6492101431/10000000000 : ℝ)|=(6492101431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4917986591/10000000000 : ℝ)*x 0 + (6705704927/10000000000 : ℝ)*x 1 + (7504313/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4917986591/10000000000 : ℝ)^35 ≤ (39853371792323/100000000000000 : ℝ)^27 := by
    have hnat : (4917986591 : ℕ)^35*100000000000000^27 ≤ 39853371792323^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4917986591 10000000000 39853371792323 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6705704927/10000000000 : ℝ)^35 ≤ (59569035620861/100000000000000 : ℝ)^27 := by
    have hnat : (6705704927 : ℕ)^35*100000000000000^27 ≤ 59569035620861^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6705704927 10000000000 59569035620861 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7504313/400000000 : ℝ)^35 ≤ (72199071589/12500000000000 : ℝ)^27 := by
    have hnat : (7504313 : ℕ)^35*12500000000000^27 ≤ 72199071589^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7504313 400000000 72199071589 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4917986591/10000000000 : ℝ), (6705704927/10000000000 : ℝ), (7504313/400000000 : ℝ)] ![(39853371792323/100000000000000 : ℝ), (59569035620861/100000000000000 : ℝ), (72199071589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4917986591/10000000000 : ℝ)|^35 ≤ (39853371792323/100000000000000 : ℝ)^27
        have hw : |(4917986591/10000000000 : ℝ)|=(4917986591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6705704927/10000000000 : ℝ)|^35 ≤ (59569035620861/100000000000000 : ℝ)^27
        have hw : |(6705704927/10000000000 : ℝ)|=(6705704927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7504313/400000000 : ℝ)|^35 ≤ (72199071589/12500000000000 : ℝ)^27
        have hw : |(7504313/400000000 : ℝ)|=(7504313/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_12 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4895282703/10000000000 : ℝ)*x 0 + (6674748037/10000000000 : ℝ)*x 1 + (-323863829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4895282703/10000000000 : ℝ)^35 ≤ (19807519226787/50000000000000 : ℝ)^27 := by
    have hnat : (4895282703 : ℕ)^35*50000000000000^27 ≤ 19807519226787^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4895282703 10000000000 19807519226787 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6674748037/10000000000 : ℝ)^35 ≤ (59212797587243/100000000000000 : ℝ)^27 := by
    have hnat : (6674748037 : ℕ)^35*100000000000000^27 ≤ 59212797587243^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6674748037 10000000000 59212797587243 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323863829/10000000000 : ℝ)^35 ≤ (293040984579/25000000000000 : ℝ)^27 := by
    have hnat : (323863829 : ℕ)^35*25000000000000^27 ≤ 293040984579^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323863829 10000000000 293040984579 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4895282703/10000000000 : ℝ), (6674748037/10000000000 : ℝ), (-323863829/10000000000 : ℝ)] ![(19807519226787/50000000000000 : ℝ), (59212797587243/100000000000000 : ℝ), (293040984579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4895282703/10000000000 : ℝ)|^35 ≤ (19807519226787/50000000000000 : ℝ)^27
        have hw : |(4895282703/10000000000 : ℝ)|=(4895282703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6674748037/10000000000 : ℝ)|^35 ≤ (59212797587243/100000000000000 : ℝ)^27
        have hw : |(6674748037/10000000000 : ℝ)|=(6674748037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323863829/10000000000 : ℝ)|^35 ≤ (293040984579/25000000000000 : ℝ)^27
        have hw : |(-323863829/10000000000 : ℝ)|=(323863829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1996031903/10000000000 : ℝ)*x 0 + (56366803/250000000 : ℝ)*x 1 + (-7854099987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1996031903/10000000000 : ℝ)^35 ≤ (6191269353859/50000000000000 : ℝ)^27 := by
    have hnat : (1996031903 : ℕ)^35*50000000000000^27 ≤ 6191269353859^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996031903 10000000000 6191269353859 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56366803/250000000 : ℝ)^35 ≤ (14501215295501/100000000000000 : ℝ)^27 := by
    have hnat : (56366803 : ℕ)^35*100000000000000^27 ≤ 14501215295501^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56366803 250000000 14501215295501 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7854099987/10000000000 : ℝ)^35 ≤ (73116245984039/100000000000000 : ℝ)^27 := by
    have hnat : (7854099987 : ℕ)^35*100000000000000^27 ≤ 73116245984039^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7854099987 10000000000 73116245984039 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1996031903/10000000000 : ℝ), (56366803/250000000 : ℝ), (-7854099987/10000000000 : ℝ)] ![(6191269353859/50000000000000 : ℝ), (14501215295501/100000000000000 : ℝ), (73116245984039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1996031903/10000000000 : ℝ)|^35 ≤ (6191269353859/50000000000000 : ℝ)^27
        have hw : |(-1996031903/10000000000 : ℝ)|=(1996031903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56366803/250000000 : ℝ)|^35 ≤ (14501215295501/100000000000000 : ℝ)^27
        have hw : |(56366803/250000000 : ℝ)|=(56366803/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7854099987/10000000000 : ℝ)|^35 ≤ (73116245984039/100000000000000 : ℝ)^27
        have hw : |(-7854099987/10000000000 : ℝ)|=(7854099987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (572279027/2000000000 : ℝ)*x 0 + (-3232166693/10000000000 : ℝ)*x 1 + (-6492106911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (572279027/2000000000 : ℝ)^35 ≤ (9874926317097/50000000000000 : ℝ)^27 := by
    have hnat : (572279027 : ℕ)^35*50000000000000^27 ≤ 9874926317097^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      572279027 2000000000 9874926317097 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3232166693/10000000000 : ℝ)^35 ≤ (23129091041399/100000000000000 : ℝ)^27 := by
    have hnat : (3232166693 : ℕ)^35*100000000000000^27 ≤ 23129091041399^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3232166693 10000000000 23129091041399 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6492106911/10000000000 : ℝ)^35 ≤ (28560528150301/50000000000000 : ℝ)^27 := by
    have hnat : (6492106911 : ℕ)^35*50000000000000^27 ≤ 28560528150301^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6492106911 10000000000 28560528150301 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(572279027/2000000000 : ℝ), (-3232166693/10000000000 : ℝ), (-6492106911/10000000000 : ℝ)] ![(9874926317097/50000000000000 : ℝ), (23129091041399/100000000000000 : ℝ), (28560528150301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(572279027/2000000000 : ℝ)|^35 ≤ (9874926317097/50000000000000 : ℝ)^27
        have hw : |(572279027/2000000000 : ℝ)|=(572279027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3232166693/10000000000 : ℝ)|^35 ≤ (23129091041399/100000000000000 : ℝ)^27
        have hw : |(-3232166693/10000000000 : ℝ)|=(3232166693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6492106911/10000000000 : ℝ)|^35 ≤ (28560528150301/50000000000000 : ℝ)^27
        have hw : |(-6492106911/10000000000 : ℝ)|=(6492106911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1675562169/2500000000 : ℝ)*x 0 + (1230444213/2500000000 : ℝ)*x 1 + (93801063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1675562169/2500000000 : ℝ)^35 ≤ (14882309605223/25000000000000 : ℝ)^27 := by
    have hnat : (1675562169 : ℕ)^35*25000000000000^27 ≤ 14882309605223^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675562169 2500000000 14882309605223 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1230444213/2500000000 : ℝ)^35 ≤ (997329793539/2500000000000 : ℝ)^27 := by
    have hnat : (1230444213 : ℕ)^35*2500000000000^27 ≤ 997329793539^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230444213 2500000000 997329793539 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (93801063/5000000000 : ℝ)^35 ≤ (577569828461/100000000000000 : ℝ)^27 := by
    have hnat : (93801063 : ℕ)^35*100000000000000^27 ≤ 577569828461^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93801063 5000000000 577569828461 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1675562169/2500000000 : ℝ), (1230444213/2500000000 : ℝ), (93801063/5000000000 : ℝ)] ![(14882309605223/25000000000000 : ℝ), (997329793539/2500000000000 : ℝ), (577569828461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1675562169/2500000000 : ℝ)|^35 ≤ (14882309605223/25000000000000 : ℝ)^27
        have hw : |(1675562169/2500000000 : ℝ)|=(1675562169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1230444213/2500000000 : ℝ)|^35 ≤ (997329793539/2500000000000 : ℝ)^27
        have hw : |(1230444213/2500000000 : ℝ)|=(1230444213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(93801063/5000000000 : ℝ)|^35 ≤ (577569828461/100000000000000 : ℝ)^27
        have hw : |(93801063/5000000000 : ℝ)|=(93801063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_18 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6671308943/10000000000 : ℝ)*x 0 + (4899056349/10000000000 : ℝ)*x 1 + (-323854093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6671308943/10000000000 : ℝ)^35 ≤ (29586626098073/50000000000000 : ℝ)^27 := by
    have hnat : (6671308943 : ℕ)^35*50000000000000^27 ≤ 29586626098073^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6671308943 10000000000 29586626098073 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4899056349/10000000000 : ℝ)^35 ≤ (2478414345729/6250000000000 : ℝ)^27 := by
    have hnat : (4899056349 : ℕ)^35*6250000000000^27 ≤ 2478414345729^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899056349 10000000000 2478414345729 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323854093/10000000000 : ℝ)^35 ≤ (1172118260133/100000000000000 : ℝ)^27 := by
    have hnat : (323854093 : ℕ)^35*100000000000000^27 ≤ 1172118260133^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323854093 10000000000 1172118260133 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6671308943/10000000000 : ℝ), (4899056349/10000000000 : ℝ), (-323854093/10000000000 : ℝ)] ![(29586626098073/50000000000000 : ℝ), (2478414345729/6250000000000 : ℝ), (1172118260133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6671308943/10000000000 : ℝ)|^35 ≤ (29586626098073/50000000000000 : ℝ)^27
        have hw : |(6671308943/10000000000 : ℝ)|=(6671308943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4899056349/10000000000 : ℝ)|^35 ≤ (2478414345729/6250000000000 : ℝ)^27
        have hw : |(4899056349/10000000000 : ℝ)|=(4899056349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323854093/10000000000 : ℝ)|^35 ≤ (1172118260133/100000000000000 : ℝ)^27
        have hw : |(-323854093/10000000000 : ℝ)|=(323854093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_19 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-399880881/1250000000 : ℝ)*x 0 + (1739448497/10000000000 : ℝ)*x 1 + (-3663426753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399880881/1250000000 : ℝ)^35 ≤ (4564466962603/20000000000000 : ℝ)^27 := by
    have hnat : (399880881 : ℕ)^35*20000000000000^27 ≤ 4564466962603^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399880881 1250000000 4564466962603 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1739448497/10000000000 : ℝ)^35 ≤ (10359727622213/100000000000000 : ℝ)^27 := by
    have hnat : (1739448497 : ℕ)^35*100000000000000^27 ≤ 10359727622213^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739448497 10000000000 10359727622213 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3663426753/5000000000 : ℝ)^35 ≤ (66817937555261/100000000000000 : ℝ)^27 := by
    have hnat : (3663426753 : ℕ)^35*100000000000000^27 ≤ 66817937555261^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663426753 5000000000 66817937555261 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399880881/1250000000 : ℝ), (1739448497/10000000000 : ℝ), (-3663426753/5000000000 : ℝ)] ![(4564466962603/20000000000000 : ℝ), (10359727622213/100000000000000 : ℝ), (66817937555261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399880881/1250000000 : ℝ)|^35 ≤ (4564466962603/20000000000000 : ℝ)^27
        have hw : |(-399880881/1250000000 : ℝ)|=(399880881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1739448497/10000000000 : ℝ)|^35 ≤ (10359727622213/100000000000000 : ℝ)^27
        have hw : |(1739448497/10000000000 : ℝ)|=(1739448497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3663426753/5000000000 : ℝ)|^35 ≤ (66817937555261/100000000000000 : ℝ)^27
        have hw : |(-3663426753/5000000000 : ℝ)|=(3663426753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3122278061/10000000000 : ℝ)*x 0 + (-1184530929/2500000000 : ℝ)*x 1 + (-4923450721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3122278061/10000000000 : ℝ)^35 ≤ (22114920280873/100000000000000 : ℝ)^27 := by
    have hnat : (3122278061 : ℕ)^35*100000000000000^27 ≤ 22114920280873^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122278061 10000000000 22114920280873 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1184530929/2500000000 : ℝ)^35 ≤ (7594859928987/20000000000000 : ℝ)^27 := by
    have hnat : (1184530929 : ℕ)^35*20000000000000^27 ≤ 7594859928987^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184530929 2500000000 7594859928987 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4923450721/10000000000 : ℝ)^35 ≤ (39910780066919/100000000000000 : ℝ)^27 := by
    have hnat : (4923450721 : ℕ)^35*100000000000000^27 ≤ 39910780066919^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4923450721 10000000000 39910780066919 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3122278061/10000000000 : ℝ), (-1184530929/2500000000 : ℝ), (-4923450721/10000000000 : ℝ)] ![(22114920280873/100000000000000 : ℝ), (7594859928987/20000000000000 : ℝ), (39910780066919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3122278061/10000000000 : ℝ)|^35 ≤ (22114920280873/100000000000000 : ℝ)^27
        have hw : |(3122278061/10000000000 : ℝ)|=(3122278061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1184530929/2500000000 : ℝ)|^35 ≤ (7594859928987/20000000000000 : ℝ)^27
        have hw : |(-1184530929/2500000000 : ℝ)|=(1184530929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4923450721/10000000000 : ℝ)|^35 ≤ (39910780066919/100000000000000 : ℝ)^27
        have hw : |(-4923450721/10000000000 : ℝ)|=(4923450721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1139109623/2000000000 : ℝ)*x 0 + (139728859/250000000 : ℝ)*x 1 + (953457519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1139109623/2000000000 : ℝ)^35 ≤ (48206056623103/100000000000000 : ℝ)^27 := by
    have hnat : (1139109623 : ℕ)^35*100000000000000^27 ≤ 48206056623103^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139109623 2000000000 48206056623103 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139728859/250000000 : ℝ)^35 ≤ (470419905579/1000000000000 : ℝ)^27 := by
    have hnat : (139728859 : ℕ)^35*1000000000000^27 ≤ 470419905579^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139728859 250000000 470419905579 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953457519/10000000000 : ℝ)^35 ≤ (2375976397113/50000000000000 : ℝ)^27 := by
    have hnat : (953457519 : ℕ)^35*50000000000000^27 ≤ 2375976397113^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953457519 10000000000 2375976397113 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1139109623/2000000000 : ℝ), (139728859/250000000 : ℝ), (953457519/10000000000 : ℝ)] ![(48206056623103/100000000000000 : ℝ), (470419905579/1000000000000 : ℝ), (2375976397113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1139109623/2000000000 : ℝ)|^35 ≤ (48206056623103/100000000000000 : ℝ)^27
        have hw : |(1139109623/2000000000 : ℝ)|=(1139109623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(139728859/250000000 : ℝ)|^35 ≤ (470419905579/1000000000000 : ℝ)^27
        have hw : |(139728859/250000000 : ℝ)|=(139728859/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(953457519/10000000000 : ℝ)|^35 ≤ (2375976397113/50000000000000 : ℝ)^27
        have hw : |(953457519/10000000000 : ℝ)|=(953457519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308048_s1_s1_25 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (742495867/2500000000 : ℝ)*x 0 + (720253223/1250000000 : ℝ)*x 1 + (-3984493991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (742495867/2500000000 : ℝ)^35 ≤ (2590854459489/12500000000000 : ℝ)^27 := by
    have hnat : (742495867 : ℕ)^35*12500000000000^27 ≤ 2590854459489^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742495867 2500000000 2590854459489 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (720253223/1250000000 : ℝ)^35 ≤ (48936681441373/100000000000000 : ℝ)^27 := by
    have hnat : (720253223 : ℕ)^35*100000000000000^27 ≤ 48936681441373^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      720253223 1250000000 48936681441373 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3984493991/10000000000 : ℝ)^35 ≤ (30336482868191/100000000000000 : ℝ)^27 := by
    have hnat : (3984493991 : ℕ)^35*100000000000000^27 ≤ 30336482868191^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3984493991 10000000000 30336482868191 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(742495867/2500000000 : ℝ), (720253223/1250000000 : ℝ), (-3984493991/10000000000 : ℝ)] ![(2590854459489/12500000000000 : ℝ), (48936681441373/100000000000000 : ℝ), (30336482868191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(742495867/2500000000 : ℝ)|^35 ≤ (2590854459489/12500000000000 : ℝ)^27
        have hw : |(742495867/2500000000 : ℝ)|=(742495867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(720253223/1250000000 : ℝ)|^35 ≤ (48936681441373/100000000000000 : ℝ)^27
        have hw : |(720253223/1250000000 : ℝ)|=(720253223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3984493991/10000000000 : ℝ)|^35 ≤ (30336482868191/100000000000000 : ℝ)^27
        have hw : |(-3984493991/10000000000 : ℝ)|=(3984493991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308048_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((1699/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1699/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84757/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84757/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14537/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14537/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60981/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60981/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12191/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12191/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6177/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6177/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (1699/2000 : ℝ) ^ (17/4 : ℝ) ≤ (49997049817629502639/100000000000000000000 : ℝ) := by
    have hpowers : (1699/2000 : ℝ)^17 ≤ (49997049817629502639/100000000000000000000 : ℝ)^4 := by
      have hnat : (1699 : ℕ)^17*100000000000000000000^4 ≤ 49997049817629502639^4*2000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1699 2000 49997049817629502639 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1699/2000 : ℝ)) (X := (49997049817629502639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (149997049817629502639/100000000000000000000 : ℝ) ≤ (5500488131601367/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (149997049817629502639/100000000000000000000 : ℝ)^4 ≤ (5500488131601367/5000000000000000 : ℝ)^17 := by
      have hnat : (149997049817629502639 : ℕ)^4*5000000000000000^17 ≤ 5500488131601367^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        149997049817629502639 100000000000000000000 5500488131601367 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5500488131601367/5000000000000000 : ℝ)) (X := (149997049817629502639/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (99997049817629502639/50000000000000000000 : ℝ) ≤ (1177138522528687/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (99997049817629502639/50000000000000000000 : ℝ)^4 ≤ (1177138522528687/1000000000000000 : ℝ)^17 := by
      have hnat : (99997049817629502639 : ℕ)^4*1000000000000000^17 ≤ 1177138522528687^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        99997049817629502639 50000000000000000000 1177138522528687 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1177138522528687/1000000000000000 : ℝ)) (X := (99997049817629502639/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(500488131601367/4247500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(96301120260517/1061875000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (1699/2000 : ℝ)) (alpha := (500488131601367/4247500000000000 : ℝ)) (beta := (96301120260517/1061875000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1699/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(500488131601367/4247500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(96301120260517/1061875000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (84757/100000 : ℝ) ^ (17/4 : ℝ) ≤ (386844324629265707/781250000000000000 : ℝ) := by
    have hpowers : (84757/100000 : ℝ)^17 ≤ (386844324629265707/781250000000000000 : ℝ)^4 := by
      have hnat : (84757 : ℕ)^17*781250000000000000^4 ≤ 386844324629265707^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        84757 100000 386844324629265707 781250000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (84757/100000 : ℝ)) (X := (386844324629265707/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (1168094324629265707/781250000000000000 : ℝ) ≤ (439706638783501/400000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (1168094324629265707/781250000000000000 : ℝ)^4 ≤ (439706638783501/400000000000000 : ℝ)^17 := by
      have hnat : (1168094324629265707 : ℕ)^4*400000000000000^17 ≤ 439706638783501^17*781250000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1168094324629265707 781250000000000000 439706638783501 400000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (439706638783501/400000000000000 : ℝ)) (X := (1168094324629265707/781250000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (777469324629265707/390625000000000000 : ℝ) ≤ (1469754810150613/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (777469324629265707/390625000000000000 : ℝ)^4 ≤ (1469754810150613/1250000000000000 : ℝ)^17 := by
      have hnat : (777469324629265707 : ℕ)^4*1250000000000000^17 ≤ 1469754810150613^17*390625000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        777469324629265707 390625000000000000 1469754810150613 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1469754810150613/1250000000000000 : ℝ)) (X := (777469324629265707/390625000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(39706638783501/339028000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(765372511617379/8475700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (84757/100000 : ℝ)) (alpha := (39706638783501/339028000000000 : ℝ)) (beta := (765372511617379/8475700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (84757/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(39706638783501/339028000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(765372511617379/8475700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (14537/50000 : ℝ) ^ (17/4 : ℝ) ≤ (20987240160965137/4000000000000000000 : ℝ) := by
    have hpowers : (14537/50000 : ℝ)^17 ≤ (20987240160965137/4000000000000000000 : ℝ)^4 := by
      have hnat : (14537 : ℕ)^17*4000000000000000000^4 ≤ 20987240160965137^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14537 50000 20987240160965137 4000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14537/50000 : ℝ)) (X := (20987240160965137/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (4020987240160965137/4000000000000000000 : ℝ) ≤ (10012320744962843/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (4020987240160965137/4000000000000000000 : ℝ)^4 ≤ (10012320744962843/10000000000000000 : ℝ)^17 := by
      have hnat : (4020987240160965137 : ℕ)^4*10000000000000000^17 ≤ 10012320744962843^17*4000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4020987240160965137 4000000000000000000 10012320744962843 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012320744962843/10000000000000000 : ℝ)) (X := (4020987240160965137/4000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (2020987240160965137/2000000000000000000 : ℝ) ≤ (10024592411532047/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (2020987240160965137/2000000000000000000 : ℝ)^4 ≤ (10024592411532047/10000000000000000 : ℝ)^17 := by
      have hnat : (2020987240160965137 : ℕ)^4*10000000000000000^17 ≤ 10024592411532047^17*2000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2020987240160965137 2000000000000000000 10024592411532047 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024592411532047/10000000000000000 : ℝ)) (X := (2020987240160965137/2000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(12320744962843/2907400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3067916642301/726850000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (14537/50000 : ℝ)) (alpha := (12320744962843/2907400000000000 : ℝ)) (beta := (3067916642301/726850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (14537/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(12320744962843/2907400000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3067916642301/726850000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-270769891/1000000000 : ℝ)*X 0 0+(2705514859/10000000000 : ℝ)*X 0 1+(-3511478973/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((534997899/1000000000 : ℝ)*X 0 0+(267669481/500000000 : ℝ)*X 0 1+(-915047419/5000000000 : ℝ)*X 0 2+(534997899/1000000000 : ℝ)*X 1 0+(267669481/500000000 : ℝ)*X 1 1+(-915047419/5000000000 : ℝ)*X 1 2+(534997899/1000000000 : ℝ)*X 2 0+(267669481/500000000 : ℝ)*X 2 1+(-915047419/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2256686141/10000000000 : ℝ)*X 0 0+(199394991/1000000000 : ℝ)*X 0 1+(-3927047773/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((161752627/500000000 : ℝ)*X 1 0+(-285840933/1000000000 : ℝ)*X 1 1+(-6492101431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4917986591/10000000000 : ℝ)*X 2 0+(6705704927/10000000000 : ℝ)*X 2 1+(7504313/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((4895282703/10000000000 : ℝ)*X 0 0+(6674748037/10000000000 : ℝ)*X 0 1+(-323863829/10000000000 : ℝ)*X 0 2+(4895282703/10000000000 : ℝ)*X 1 0+(6674748037/10000000000 : ℝ)*X 1 1+(-323863829/10000000000 : ℝ)*X 1 2+(4895282703/10000000000 : ℝ)*X 2 0+(6674748037/10000000000 : ℝ)*X 2 1+(-323863829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-1996031903/10000000000 : ℝ)*X 0 0+(56366803/250000000 : ℝ)*X 0 1+(-7854099987/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((572279027/2000000000 : ℝ)*X 1 0+(-3232166693/10000000000 : ℝ)*X 1 1+(-6492106911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1675562169/2500000000 : ℝ)*X 2 0+(1230444213/2500000000 : ℝ)*X 2 1+(93801063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((6671308943/10000000000 : ℝ)*X 0 0+(4899056349/10000000000 : ℝ)*X 0 1+(-323854093/10000000000 : ℝ)*X 0 2+(6671308943/10000000000 : ℝ)*X 1 0+(4899056349/10000000000 : ℝ)*X 1 1+(-323854093/10000000000 : ℝ)*X 1 2+(6671308943/10000000000 : ℝ)*X 2 0+(4899056349/10000000000 : ℝ)*X 2 1+(-323854093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-399880881/1250000000 : ℝ)*X 0 0+(1739448497/10000000000 : ℝ)*X 0 1+(-3663426753/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3122278061/10000000000 : ℝ)*X 1 0+(-1184530929/2500000000 : ℝ)*X 1 1+(-4923450721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((1139109623/2000000000 : ℝ)*X 2 0+(139728859/250000000 : ℝ)*X 2 1+(953457519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((742495867/2500000000 : ℝ)*X 0 0+(720253223/1250000000 : ℝ)*X 0 1+(-3984493991/10000000000 : ℝ)*X 0 2+(742495867/2500000000 : ℝ)*X 1 0+(720253223/1250000000 : ℝ)*X 1 1+(-3984493991/10000000000 : ℝ)*X 1 2+(742495867/2500000000 : ℝ)*X 2 0+(720253223/1250000000 : ℝ)*X 2 1+(-3984493991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308048_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((60981/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60981/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (45195936113038604378925711922461/5233397881977500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3223487/1000000000000 : ℝ)*(base23) + (20310712491/1000000000000 : ℝ)*(base39) + (460971/250000000000 : ℝ)*(base49) + (917480401627/500000000000 : ℝ)*(base59) + (3806443931/7812500000 : ℝ)*(base60) + (4518060072637/1000000000000 : ℝ)*(major_s1_0) + (4518060072637/1000000000000 : ℝ)*(major_s1_1) + (4518060072637/1000000000000 : ℝ)*(major_s1_2) + (6153064977567/1000000000000 : ℝ)*(sp_s1_7) + (769121931109/125000000000 : ℝ)*(sp_s1_8) + (6153061754081/1000000000000 : ℝ)*(sp_s1_9) + (288304125663/100000000000 : ℝ)*(sp_s1_12) + (11191087/125000000000 : ℝ)*(sp_s1_14) + (172381/15625000000 : ℝ)*(sp_s1_25) + (1441526144507/500000000000 : ℝ)*(f.failure) + (6153064977567/1000000000000 : ℝ)*(f.sum) + (63521578840603914363/246422501800000000000000000000000 : ℝ)*base63 + (347296063555103/726850000000000000000000000 : ℝ)*base65 + (7064934676430703/8475700000000000000000000000 : ℝ)*base66 + (1626985017485929/2907400000000000000000000000 : ℝ)*base69 + (11830617531356115673/61745907500000000000000000000000 : ℝ)*base71 + (106130322795977/530937500000000000000000000 : ℝ)*base73 + (553070413466563/1695140000000000000000000000 : ℝ)*base75 + (455429773666971/4247500000000000000000000000 : ℝ)*base76 + (55682401328950224037/360005357500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (13523/50000000000000000 : ℝ)*base86 + (13523/50000000000000000 : ℝ)*base88 + (13523/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12191/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12191/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6419718253854149587355665748979/523339788197750000000000000000000000 : ℝ) := by norm_num
    linear_combination (8685467/1000000000000 : ℝ)*(base18) + (1706159/100000000000 : ℝ)*(base21) + (10153322993/500000000000 : ℝ)*(base39) + (7617413071/4000000000 : ℝ)*(base59) + (10185302027/12500000000 : ℝ)*(base60) + (225880097887/50000000000 : ℝ)*(major_s1_0) + (225880097887/50000000000 : ℝ)*(major_s1_1) + (225880097887/50000000000 : ℝ)*(major_s1_2) + (2671861/125000000000 : ℝ)*(sp_s1_6) + (58833523/500000000000 : ℝ)*(sp_s1_8) + (76905498357/12500000000 : ℝ)*(sp_s1_13) + (6152313516047/1000000000000 : ℝ)*(sp_s1_14) + (615242280697/100000000000 : ℝ)*(sp_s1_15) + (1441369291543/500000000000 : ℝ)*(sp_s1_18) + (1441379978987/500000000000 : ℝ)*(f.failure) + (76905498357/12500000000 : ℝ)*(f.sum) + (3674430245312966829/12321125090000000000000000000000 : ℝ)*base62 + (36937799318793/72685000000000000000000000 : ℝ)*base64 + (31866108150797/211892500000000000000000000 : ℝ)*base67 + (5208765328019/18171250000000000000000000 : ℝ)*base68 + (2982982985300590879/6174590750000000000000000000000 : ℝ)*base70 + (235697539613507/424750000000000000000000000 : ℝ)*base73 + (85800432116679/211892500000000000000000000 : ℝ)*base74 + (7913642340199/53093750000000000000000000 : ℝ)*base76 + (1000387341674806639/2250033484375000000000000000000 : ℝ)*base79 + (31757/50000000000000000 : ℝ)*base87 + (31757/50000000000000000 : ℝ)*base89 + (31757/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6177/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6177/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (120447209429028552606181143/12349181500000000000000000000000 : ℝ) := by norm_num
    linear_combination (559217118459/500000000000 : ℝ)*(base5) + (6641779/1000000000000 : ℝ)*(base8) + (294998226533/1000000000000 : ℝ)*(base39) + (38541837357/1000000000000 : ℝ)*(base50) + (266021470287/200000000000 : ℝ)*(base59) + (1752709477017/1000000000000 : ℝ)*(major_s1_0) + (1752709477017/1000000000000 : ℝ)*(major_s1_1) + (1752709477017/1000000000000 : ℝ)*(major_s1_2) + (2323321/100000000000 : ℝ)*(sp_s1_0) + (1182199/25000000000 : ℝ)*(sp_s1_9) + (8519023/200000000000 : ℝ)*(sp_s1_15) + (2386951590969/1000000000000 : ℝ)*(sp_s1_19) + (2386981465957/1000000000000 : ℝ)*(sp_s1_20) + (3505325819801/1000000000000 : ℝ)*(sp_s1_21) + (559217118459/500000000000 : ℝ)*(f.failure) + (2386981465957/1000000000000 : ℝ)*(f.sum) + (82995343021742634043/246422501800000000000000000000000 : ℝ)*base63 + (13111133599717/45428125000000000000000000 : ℝ)*base64 + (2803972876864737/8475700000000000000000000000 : ℝ)*base67 + (558504245851689/2907400000000000000000000000 : ℝ)*base69 + (28032328442282991807/61745907500000000000000000000000 : ℝ)*base70 + (1247427285686547/2123750000000000000000000000 : ℝ)*base72 + (758962979237/67805600000000000000000000 : ℝ)*base74 + (566526758402761/4247500000000000000000000000 : ℝ)*base76 + (73018663643736559083/360005357500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (21651/50000000000000000 : ℝ)*base86 + (21651/50000000000000000 : ℝ)*base88 + (21651/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((1699/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1699/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84757/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84757/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-14537/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-14537/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60981/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60981/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12191/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12191/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6177/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6177/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308048_s1 p hpa hpb X hX hprev0

#print axioms solution
