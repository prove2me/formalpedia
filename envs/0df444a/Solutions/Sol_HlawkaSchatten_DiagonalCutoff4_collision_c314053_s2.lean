-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:46:50.008648+00:00
-- url     : https://prove2.me/submissions/1b669a8a-704d-4c32-a316-81346129afaf

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
theorem collision_support_c314053_s2_s2_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-141118459/625000000 : ℝ)*x 0 + (1270554127/2500000000 : ℝ)*x 1 + (5112349731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141118459/625000000 : ℝ)^75 ≤ (1885154968767/12500000000000 : ℝ)^59 := by
    have hnat : (141118459 : ℕ)^75*12500000000000^59 ≤ 1885154968767^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141118459 625000000 1885154968767 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270554127/2500000000 : ℝ)^75 ≤ (42299844020377/100000000000000 : ℝ)^59 := by
    have hnat : (1270554127 : ℕ)^75*100000000000000^59 ≤ 42299844020377^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270554127 2500000000 42299844020377 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5112349731/10000000000 : ℝ)^75 ≤ (5327364526129/12500000000000 : ℝ)^59 := by
    have hnat : (5112349731 : ℕ)^75*12500000000000^59 ≤ 5327364526129^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112349731 10000000000 5327364526129 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-141118459/625000000 : ℝ), (1270554127/2500000000 : ℝ), (5112349731/10000000000 : ℝ)] ![(1885154968767/12500000000000 : ℝ), (42299844020377/100000000000000 : ℝ), (5327364526129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-141118459/625000000 : ℝ)|^75 ≤ (1885154968767/12500000000000 : ℝ)^59
        have hw : |(-141118459/625000000 : ℝ)|=(141118459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270554127/2500000000 : ℝ)|^75 ≤ (42299844020377/100000000000000 : ℝ)^59
        have hw : |(1270554127/2500000000 : ℝ)|=(1270554127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5112349731/10000000000 : ℝ)|^75 ≤ (5327364526129/12500000000000 : ℝ)^59
        have hw : |(5112349731/10000000000 : ℝ)|=(5112349731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4490774659/10000000000 : ℝ)*x 0 + (-865089429/5000000000 : ℝ)*x 1 + (6078129491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4490774659/10000000000 : ℝ)^75 ≤ (18071970481/50000000000 : ℝ)^59 := by
    have hnat : (4490774659 : ℕ)^75*50000000000^59 ≤ 18071970481^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490774659 10000000000 18071970481 50000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (865089429/5000000000 : ℝ)^75 ≤ (1343945397183/12500000000000 : ℝ)^59 := by
    have hnat : (865089429 : ℕ)^75*12500000000000^59 ≤ 1343945397183^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865089429 5000000000 1343945397183 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6078129491/10000000000 : ℝ)^75 ≤ (10620899168203/20000000000000 : ℝ)^59 := by
    have hnat : (6078129491 : ℕ)^75*20000000000000^59 ≤ 10620899168203^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6078129491 10000000000 10620899168203 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4490774659/10000000000 : ℝ), (-865089429/5000000000 : ℝ), (6078129491/10000000000 : ℝ)] ![(18071970481/50000000000 : ℝ), (1343945397183/12500000000000 : ℝ), (10620899168203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4490774659/10000000000 : ℝ)|^75 ≤ (18071970481/50000000000 : ℝ)^59
        have hw : |(4490774659/10000000000 : ℝ)|=(4490774659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-865089429/5000000000 : ℝ)|^75 ≤ (1343945397183/12500000000000 : ℝ)^59
        have hw : |(-865089429/5000000000 : ℝ)|=(865089429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6078129491/10000000000 : ℝ)|^75 ≤ (10620899168203/20000000000000 : ℝ)^59
        have hw : |(6078129491/10000000000 : ℝ)|=(6078129491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4513431843/10000000000 : ℝ)*x 0 + (3035477853/5000000000 : ℝ)*x 1 + (-1710868757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4513431843/10000000000 : ℝ)^75 ≤ (9093976971357/25000000000000 : ℝ)^59 := by
    have hnat : (4513431843 : ℕ)^75*25000000000000^59 ≤ 9093976971357^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513431843 10000000000 9093976971357 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3035477853/5000000000 : ℝ)^75 ≤ (3314052135509/6250000000000 : ℝ)^59 := by
    have hnat : (3035477853 : ℕ)^75*6250000000000^59 ≤ 3314052135509^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3035477853 5000000000 3314052135509 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1710868757/10000000000 : ℝ)^75 ≤ (1324907240283/12500000000000 : ℝ)^59 := by
    have hnat : (1710868757 : ℕ)^75*12500000000000^59 ≤ 1324907240283^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710868757 10000000000 1324907240283 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4513431843/10000000000 : ℝ), (3035477853/5000000000 : ℝ), (-1710868757/10000000000 : ℝ)] ![(9093976971357/25000000000000 : ℝ), (3314052135509/6250000000000 : ℝ), (1324907240283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4513431843/10000000000 : ℝ)|^75 ≤ (9093976971357/25000000000000 : ℝ)^59
        have hw : |(4513431843/10000000000 : ℝ)|=(4513431843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3035477853/5000000000 : ℝ)|^75 ≤ (3314052135509/6250000000000 : ℝ)^59
        have hw : |(3035477853/5000000000 : ℝ)|=(3035477853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1710868757/10000000000 : ℝ)|^75 ≤ (1324907240283/12500000000000 : ℝ)^59
        have hw : |(-1710868757/10000000000 : ℝ)|=(1710868757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1354070189/2000000000 : ℝ)*x 0 + (2790902257/10000000000 : ℝ)*x 1 + (686682249/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354070189/2000000000 : ℝ)^75 ≤ (60908124992467/100000000000000 : ℝ)^59 := by
    have hnat : (1354070189 : ℕ)^75*100000000000000^59 ≤ 60908124992467^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354070189 2000000000 60908124992467 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2790902257/10000000000 : ℝ)^75 ≤ (19744133781139/100000000000000 : ℝ)^59 := by
    have hnat : (2790902257 : ℕ)^75*100000000000000^59 ≤ 19744133781139^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2790902257 10000000000 19744133781139 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686682249/2500000000 : ℝ)^75 ≤ (604616912781/3125000000000 : ℝ)^59 := by
    have hnat : (686682249 : ℕ)^75*3125000000000^59 ≤ 604616912781^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686682249 2500000000 604616912781 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354070189/2000000000 : ℝ), (2790902257/10000000000 : ℝ), (686682249/2500000000 : ℝ)] ![(60908124992467/100000000000000 : ℝ), (19744133781139/100000000000000 : ℝ), (604616912781/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354070189/2000000000 : ℝ)|^75 ≤ (60908124992467/100000000000000 : ℝ)^59
        have hw : |(1354070189/2000000000 : ℝ)|=(1354070189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2790902257/10000000000 : ℝ)|^75 ≤ (19744133781139/100000000000000 : ℝ)^59
        have hw : |(2790902257/10000000000 : ℝ)|=(2790902257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686682249/2500000000 : ℝ)|^75 ≤ (604616912781/3125000000000 : ℝ)^59
        have hw : |(686682249/2500000000 : ℝ)|=(686682249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095199619/5000000000 : ℝ)*x 0 + (2115857067/5000000000 : ℝ)*x 1 + (2988100013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095199619/5000000000 : ℝ)^75 ≤ (2902098380803/20000000000000 : ℝ)^59 := by
    have hnat : (1095199619 : ℕ)^75*20000000000000^59 ≤ 2902098380803^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095199619 5000000000 2902098380803 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115857067/5000000000 : ℝ)^75 ≤ (2094655614121/6250000000000 : ℝ)^59 := by
    have hnat : (2115857067 : ℕ)^75*6250000000000^59 ≤ 2094655614121^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115857067 5000000000 2094655614121 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2988100013/5000000000 : ℝ)^75 ≤ (25987509126277/50000000000000 : ℝ)^59 := by
    have hnat : (2988100013 : ℕ)^75*50000000000000^59 ≤ 25987509126277^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988100013 5000000000 25987509126277 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095199619/5000000000 : ℝ), (2115857067/5000000000 : ℝ), (2988100013/5000000000 : ℝ)] ![(2902098380803/20000000000000 : ℝ), (2094655614121/6250000000000 : ℝ), (25987509126277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095199619/5000000000 : ℝ)|^75 ≤ (2902098380803/20000000000000 : ℝ)^59
        have hw : |(-1095199619/5000000000 : ℝ)|=(1095199619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115857067/5000000000 : ℝ)|^75 ≤ (2094655614121/6250000000000 : ℝ)^59
        have hw : |(2115857067/5000000000 : ℝ)|=(2115857067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2988100013/5000000000 : ℝ)|^75 ≤ (25987509126277/50000000000000 : ℝ)^59
        have hw : |(2988100013/5000000000 : ℝ)|=(2988100013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4228025677/10000000000 : ℝ)*x 0 + (-279999883/2000000000 : ℝ)*x 1 + (6541965807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4228025677/10000000000 : ℝ)^75 ≤ (4184670042613/12500000000000 : ℝ)^59 := by
    have hnat : (4228025677 : ℕ)^75*12500000000000^59 ≤ 4184670042613^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228025677 10000000000 4184670042613 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279999883/2000000000 : ℝ)^75 ≤ (164285525719/2000000000000 : ℝ)^59 := by
    have hnat : (279999883 : ℕ)^75*2000000000000^59 ≤ 164285525719^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279999883 2000000000 164285525719 2000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6541965807/10000000000 : ℝ)^75 ≤ (7288545420129/12500000000000 : ℝ)^59 := by
    have hnat : (6541965807 : ℕ)^75*12500000000000^59 ≤ 7288545420129^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6541965807 10000000000 7288545420129 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4228025677/10000000000 : ℝ), (-279999883/2000000000 : ℝ), (6541965807/10000000000 : ℝ)] ![(4184670042613/12500000000000 : ℝ), (164285525719/2000000000000 : ℝ), (7288545420129/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4228025677/10000000000 : ℝ)|^75 ≤ (4184670042613/12500000000000 : ℝ)^59
        have hw : |(4228025677/10000000000 : ℝ)|=(4228025677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-279999883/2000000000 : ℝ)|^75 ≤ (164285525719/2000000000000 : ℝ)^59
        have hw : |(-279999883/2000000000 : ℝ)|=(279999883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6541965807/10000000000 : ℝ)|^75 ≤ (7288545420129/12500000000000 : ℝ)^59
        have hw : |(6541965807/10000000000 : ℝ)|=(6541965807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (425080191/1000000000 : ℝ)*x 0 + (342042729/500000000 : ℝ)*x 1 + (-883842479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425080191/1000000000 : ℝ)^75 ≤ (3370677514227/10000000000000 : ℝ)^59 := by
    have hnat : (425080191 : ℕ)^75*10000000000000^59 ≤ 3370677514227^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425080191 1000000000 3370677514227 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342042729/500000000 : ℝ)^75 ≤ (61715538598773/100000000000000 : ℝ)^59 := by
    have hnat : (342042729 : ℕ)^75*100000000000000^59 ≤ 61715538598773^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342042729 500000000 61715538598773 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883842479/10000000000 : ℝ)^75 ≤ (915537247447/20000000000000 : ℝ)^59 := by
    have hnat : (883842479 : ℕ)^75*20000000000000^59 ≤ 915537247447^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883842479 10000000000 915537247447 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(425080191/1000000000 : ℝ), (342042729/500000000 : ℝ), (-883842479/10000000000 : ℝ)] ![(3370677514227/10000000000000 : ℝ), (61715538598773/100000000000000 : ℝ), (915537247447/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(425080191/1000000000 : ℝ)|^75 ≤ (3370677514227/10000000000000 : ℝ)^59
        have hw : |(425080191/1000000000 : ℝ)|=(425080191/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342042729/500000000 : ℝ)|^75 ≤ (61715538598773/100000000000000 : ℝ)^59
        have hw : |(342042729/500000000 : ℝ)|=(342042729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883842479/10000000000 : ℝ)|^75 ≤ (915537247447/20000000000000 : ℝ)^59
        have hw : |(-883842479/10000000000 : ℝ)|=(883842479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1315163861/2000000000 : ℝ)*x 0 + (1981761721/5000000000 : ℝ)*x 1 + (338881259/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1315163861/2000000000 : ℝ)^75 ≤ (11738438797733/20000000000000 : ℝ)^59 := by
    have hnat : (1315163861 : ℕ)^75*20000000000000^59 ≤ 11738438797733^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315163861 2000000000 11738438797733 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981761721/5000000000 : ℝ)^75 ≤ (15419012813607/50000000000000 : ℝ)^59 := by
    have hnat : (1981761721 : ℕ)^75*50000000000000^59 ≤ 15419012813607^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981761721 5000000000 15419012813607 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338881259/2000000000 : ℝ)^75 ≤ (10469780373379/100000000000000 : ℝ)^59 := by
    have hnat : (338881259 : ℕ)^75*100000000000000^59 ≤ 10469780373379^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338881259 2000000000 10469780373379 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1315163861/2000000000 : ℝ), (1981761721/5000000000 : ℝ), (338881259/2000000000 : ℝ)] ![(11738438797733/20000000000000 : ℝ), (15419012813607/50000000000000 : ℝ), (10469780373379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1315163861/2000000000 : ℝ)|^75 ≤ (11738438797733/20000000000000 : ℝ)^59
        have hw : |(1315163861/2000000000 : ℝ)|=(1315163861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1981761721/5000000000 : ℝ)|^75 ≤ (15419012813607/50000000000000 : ℝ)^59
        have hw : |(1981761721/5000000000 : ℝ)|=(1981761721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338881259/2000000000 : ℝ)|^75 ≤ (10469780373379/100000000000000 : ℝ)^59
        have hw : |(338881259/2000000000 : ℝ)|=(338881259/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-352312727/2500000000 : ℝ)*x 0 + (4918399349/10000000000 : ℝ)*x 1 + (2950379107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352312727/2500000000 : ℝ)^75 ≤ (4141670074921/50000000000000 : ℝ)^59 := by
    have hnat : (352312727 : ℕ)^75*50000000000000^59 ≤ 4141670074921^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352312727 2500000000 4141670074921 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4918399349/10000000000 : ℝ)^75 ≤ (20287128624639/50000000000000 : ℝ)^59 := by
    have hnat : (4918399349 : ℕ)^75*50000000000000^59 ≤ 20287128624639^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918399349 10000000000 20287128624639 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2950379107/5000000000 : ℝ)^75 ≤ (25571201293599/50000000000000 : ℝ)^59 := by
    have hnat : (2950379107 : ℕ)^75*50000000000000^59 ≤ 25571201293599^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2950379107 5000000000 25571201293599 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352312727/2500000000 : ℝ), (4918399349/10000000000 : ℝ), (2950379107/5000000000 : ℝ)] ![(4141670074921/50000000000000 : ℝ), (20287128624639/50000000000000 : ℝ), (25571201293599/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352312727/2500000000 : ℝ)|^75 ≤ (4141670074921/50000000000000 : ℝ)^59
        have hw : |(-352312727/2500000000 : ℝ)|=(352312727/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4918399349/10000000000 : ℝ)|^75 ≤ (20287128624639/50000000000000 : ℝ)^59
        have hw : |(4918399349/10000000000 : ℝ)|=(4918399349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2950379107/5000000000 : ℝ)|^75 ≤ (25571201293599/50000000000000 : ℝ)^59
        have hw : |(2950379107/5000000000 : ℝ)|=(2950379107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2064537677/5000000000 : ℝ)*x 0 + (-46425839/312500000 : ℝ)*x 1 + (821592621/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2064537677/5000000000 : ℝ)^75 ≤ (32484583222267/100000000000000 : ℝ)^59 := by
    have hnat : (2064537677 : ℕ)^75*100000000000000^59 ≤ 32484583222267^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2064537677 5000000000 32484583222267 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46425839/312500000 : ℝ)^75 ≤ (4429073559779/50000000000000 : ℝ)^59 := by
    have hnat : (46425839 : ℕ)^75*50000000000000^59 ≤ 4429073559779^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46425839 312500000 4429073559779 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (821592621/1250000000 : ℝ)^75 ≤ (58657269639897/100000000000000 : ℝ)^59 := by
    have hnat : (821592621 : ℕ)^75*100000000000000^59 ≤ 58657269639897^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821592621 1250000000 58657269639897 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2064537677/5000000000 : ℝ), (-46425839/312500000 : ℝ), (821592621/1250000000 : ℝ)] ![(32484583222267/100000000000000 : ℝ), (4429073559779/50000000000000 : ℝ), (58657269639897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2064537677/5000000000 : ℝ)|^75 ≤ (32484583222267/100000000000000 : ℝ)^59
        have hw : |(2064537677/5000000000 : ℝ)|=(2064537677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-46425839/312500000 : ℝ)|^75 ≤ (4429073559779/50000000000000 : ℝ)^59
        have hw : |(-46425839/312500000 : ℝ)|=(46425839/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(821592621/1250000000 : ℝ)|^75 ≤ (58657269639897/100000000000000 : ℝ)^59
        have hw : |(821592621/1250000000 : ℝ)|=(821592621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2699308877/5000000000 : ℝ)*x 0 + (5727822407/10000000000 : ℝ)*x 1 + (-959282601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699308877/5000000000 : ℝ)^75 ≤ (5709410336723/12500000000000 : ℝ)^59 := by
    have hnat : (2699308877 : ℕ)^75*12500000000000^59 ≤ 5709410336723^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699308877 5000000000 5709410336723 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5727822407/10000000000 : ℝ)^75 ≤ (49244710642283/100000000000000 : ℝ)^59 := by
    have hnat : (5727822407 : ℕ)^75*100000000000000^59 ≤ 49244710642283^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5727822407 10000000000 49244710642283 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (959282601/10000000000 : ℝ)^75 ≤ (5080006649377/100000000000000 : ℝ)^59 := by
    have hnat : (959282601 : ℕ)^75*100000000000000^59 ≤ 5080006649377^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959282601 10000000000 5080006649377 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699308877/5000000000 : ℝ), (5727822407/10000000000 : ℝ), (-959282601/10000000000 : ℝ)] ![(5709410336723/12500000000000 : ℝ), (49244710642283/100000000000000 : ℝ), (5080006649377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699308877/5000000000 : ℝ)|^75 ≤ (5709410336723/12500000000000 : ℝ)^59
        have hw : |(2699308877/5000000000 : ℝ)|=(2699308877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5727822407/10000000000 : ℝ)|^75 ≤ (49244710642283/100000000000000 : ℝ)^59
        have hw : |(5727822407/10000000000 : ℝ)|=(5727822407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-959282601/10000000000 : ℝ)|^75 ≤ (5080006649377/100000000000000 : ℝ)^59
        have hw : |(-959282601/10000000000 : ℝ)|=(959282601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (771256381/1000000000 : ℝ)*x 0 + (524373449/2000000000 : ℝ)*x 1 + (809637233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (771256381/1000000000 : ℝ)^75 ≤ (2875203560093/4000000000000 : ℝ)^59 := by
    have hnat : (771256381 : ℕ)^75*4000000000000^59 ≤ 2875203560093^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771256381 1000000000 2875203560093 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524373449/2000000000 : ℝ)^75 ≤ (284948141333/1562500000000 : ℝ)^59 := by
    have hnat : (524373449 : ℕ)^75*1562500000000^59 ≤ 284948141333^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524373449 2000000000 284948141333 1562500000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809637233/5000000000 : ℝ)^75 ≤ (2470807484419/25000000000000 : ℝ)^59 := by
    have hnat : (809637233 : ℕ)^75*25000000000000^59 ≤ 2470807484419^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809637233 5000000000 2470807484419 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(771256381/1000000000 : ℝ), (524373449/2000000000 : ℝ), (809637233/5000000000 : ℝ)] ![(2875203560093/4000000000000 : ℝ), (284948141333/1562500000000 : ℝ), (2470807484419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(771256381/1000000000 : ℝ)|^75 ≤ (2875203560093/4000000000000 : ℝ)^59
        have hw : |(771256381/1000000000 : ℝ)|=(771256381/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524373449/2000000000 : ℝ)|^75 ≤ (284948141333/1562500000000 : ℝ)^59
        have hw : |(524373449/2000000000 : ℝ)|=(524373449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(809637233/5000000000 : ℝ)|^75 ≤ (2470807484419/25000000000000 : ℝ)^59
        have hw : |(809637233/5000000000 : ℝ)|=(809637233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1313083567/10000000000 : ℝ)*x 0 + (5457890337/10000000000 : ℝ)*x 1 + (2719718507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313083567/10000000000 : ℝ)^75 ≤ (7571557264899/100000000000000 : ℝ)^59 := by
    have hnat : (1313083567 : ℕ)^75*100000000000000^59 ≤ 7571557264899^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313083567 10000000000 7571557264899 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5457890337/10000000000 : ℝ)^75 ≤ (5789212768633/12500000000000 : ℝ)^59 := by
    have hnat : (5457890337 : ℕ)^75*12500000000000^59 ≤ 5789212768633^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457890337 10000000000 5789212768633 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719718507/5000000000 : ℝ)^75 ≤ (5764342571289/12500000000000 : ℝ)^59 := by
    have hnat : (2719718507 : ℕ)^75*12500000000000^59 ≤ 5764342571289^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719718507 5000000000 5764342571289 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1313083567/10000000000 : ℝ), (5457890337/10000000000 : ℝ), (2719718507/5000000000 : ℝ)] ![(7571557264899/100000000000000 : ℝ), (5789212768633/12500000000000 : ℝ), (5764342571289/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1313083567/10000000000 : ℝ)|^75 ≤ (7571557264899/100000000000000 : ℝ)^59
        have hw : |(-1313083567/10000000000 : ℝ)|=(1313083567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5457890337/10000000000 : ℝ)|^75 ≤ (5789212768633/12500000000000 : ℝ)^59
        have hw : |(5457890337/10000000000 : ℝ)|=(5457890337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719718507/5000000000 : ℝ)|^75 ≤ (5764342571289/12500000000000 : ℝ)^59
        have hw : |(2719718507/5000000000 : ℝ)|=(2719718507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5472005651/10000000000 : ℝ)*x 0 + (-1063442957/10000000000 : ℝ)*x 1 + (1117987813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5472005651/10000000000 : ℝ)^75 ≤ (46466015040251/100000000000000 : ℝ)^59 := by
    have hnat : (5472005651 : ℕ)^75*100000000000000^59 ≤ 46466015040251^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472005651 10000000000 46466015040251 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1063442957/10000000000 : ℝ)^75 ≤ (2895624827219/50000000000000 : ℝ)^59 := by
    have hnat : (1063442957 : ℕ)^75*50000000000000^59 ≤ 2895624827219^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063442957 10000000000 2895624827219 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117987813/2000000000 : ℝ)^75 ≤ (11935683823159/25000000000000 : ℝ)^59 := by
    have hnat : (1117987813 : ℕ)^75*25000000000000^59 ≤ 11935683823159^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117987813 2000000000 11935683823159 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5472005651/10000000000 : ℝ), (-1063442957/10000000000 : ℝ), (1117987813/2000000000 : ℝ)] ![(46466015040251/100000000000000 : ℝ), (2895624827219/50000000000000 : ℝ), (11935683823159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5472005651/10000000000 : ℝ)|^75 ≤ (46466015040251/100000000000000 : ℝ)^59
        have hw : |(5472005651/10000000000 : ℝ)|=(5472005651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1063442957/10000000000 : ℝ)|^75 ≤ (2895624827219/50000000000000 : ℝ)^59
        have hw : |(-1063442957/10000000000 : ℝ)|=(1063442957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1117987813/2000000000 : ℝ)|^75 ≤ (11935683823159/25000000000000 : ℝ)^59
        have hw : |(1117987813/2000000000 : ℝ)|=(1117987813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4108001171/10000000000 : ℝ)*x 0 + (3364929/5000000 : ℝ)*x 1 + (-63661233/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4108001171/10000000000 : ℝ)^75 ≤ (806849276353/2500000000000 : ℝ)^59 := by
    have hnat : (4108001171 : ℕ)^75*2500000000000^59 ≤ 806849276353^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4108001171 10000000000 806849276353 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3364929/5000000 : ℝ)^75 ≤ (7555678083081/12500000000000 : ℝ)^59 := by
    have hnat : (3364929 : ℕ)^75*12500000000000^59 ≤ 7555678083081^59*5000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3364929 5000000 7555678083081 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63661233/500000000 : ℝ)^75 ≤ (3640302131633/50000000000000 : ℝ)^59 := by
    have hnat : (63661233 : ℕ)^75*50000000000000^59 ≤ 3640302131633^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63661233 500000000 3640302131633 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4108001171/10000000000 : ℝ), (3364929/5000000 : ℝ), (-63661233/500000000 : ℝ)] ![(806849276353/2500000000000 : ℝ), (7555678083081/12500000000000 : ℝ), (3640302131633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4108001171/10000000000 : ℝ)|^75 ≤ (806849276353/2500000000000 : ℝ)^59
        have hw : |(4108001171/10000000000 : ℝ)|=(4108001171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3364929/5000000 : ℝ)|^75 ≤ (7555678083081/12500000000000 : ℝ)^59
        have hw : |(3364929/5000000 : ℝ)|=(3364929/5000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63661233/500000000 : ℝ)|^75 ≤ (3640302131633/50000000000000 : ℝ)^59
        have hw : |(-63661233/500000000 : ℝ)|=(63661233/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314053_s2_s2_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7819626981/10000000000 : ℝ)*x 0 + (2062606247/10000000000 : ℝ)*x 1 + (20581603/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7819626981/10000000000 : ℝ)^75 ≤ (36575438553463/50000000000000 : ℝ)^59 := by
    have hnat : (7819626981 : ℕ)^75*50000000000000^59 ≤ 36575438553463^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7819626981 10000000000 36575438553463 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062606247/10000000000 : ℝ)^75 ≤ (420092912837/3125000000000 : ℝ)^59 := by
    have hnat : (2062606247 : ℕ)^75*3125000000000^59 ≤ 420092912837^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062606247 10000000000 420092912837 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20581603/100000000 : ℝ)^75 ≤ (6703074836079/50000000000000 : ℝ)^59 := by
    have hnat : (20581603 : ℕ)^75*50000000000000^59 ≤ 6703074836079^59*100000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20581603 100000000 6703074836079 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7819626981/10000000000 : ℝ), (2062606247/10000000000 : ℝ), (20581603/100000000 : ℝ)] ![(36575438553463/50000000000000 : ℝ), (420092912837/3125000000000 : ℝ), (6703074836079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7819626981/10000000000 : ℝ)|^75 ≤ (36575438553463/50000000000000 : ℝ)^59
        have hw : |(7819626981/10000000000 : ℝ)|=(7819626981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062606247/10000000000 : ℝ)|^75 ≤ (420092912837/3125000000000 : ℝ)^59
        have hw : |(2062606247/10000000000 : ℝ)|=(2062606247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20581603/100000000 : ℝ)|^75 ≤ (6703074836079/50000000000000 : ℝ)^59
        have hw : |(20581603/100000000 : ℝ)|=(20581603/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314053_s2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((14371/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14371/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31153/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6069/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6069/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15059/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15059/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4463/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4463/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34267/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34267/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (14371/25000 : ℝ) ^ (37/8 : ℝ) ≤ (7725112020958886921/100000000000000000000 : ℝ) := by
    have hpowers : (14371/25000 : ℝ)^37 ≤ (7725112020958886921/100000000000000000000 : ℝ)^8 := by
      have hnat : (14371 : ℕ)^37*100000000000000000000^8 ≤ 7725112020958886921^8*25000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14371 25000 7725112020958886921 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14371/25000 : ℝ)) (X := (7725112020958886921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (107725112020958886921/100000000000000000000 : ℝ) ≤ (5081096626786079/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (107725112020958886921/100000000000000000000 : ℝ)^8 ≤ (5081096626786079/5000000000000000 : ℝ)^37 := by
      have hnat : (107725112020958886921 : ℕ)^8*5000000000000000^37 ≤ 5081096626786079^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107725112020958886921 100000000000000000000 5081096626786079 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5081096626786079/5000000000000000 : ℝ)) (X := (107725112020958886921/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (57725112020958886921/50000000000000000000 : ℝ) ≤ (10315511397669877/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (57725112020958886921/50000000000000000000 : ℝ)^8 ≤ (10315511397669877/10000000000000000 : ℝ)^37 := by
      have hnat : (57725112020958886921 : ℕ)^8*10000000000000000^37 ≤ 10315511397669877^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57725112020958886921 50000000000000000000 10315511397669877 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10315511397669877/10000000000000000 : ℝ)) (X := (57725112020958886921/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(81096626786079/2874200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(153318144097719/5748400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (14371/25000 : ℝ)) (alpha := (81096626786079/2874200000000000 : ℝ)) (beta := (153318144097719/5748400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14371/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(81096626786079/2874200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(153318144097719/5748400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (31153/50000 : ℝ) ^ (37/8 : ℝ) ≤ (11212453430281326921/100000000000000000000 : ℝ) := by
    have hpowers : (31153/50000 : ℝ)^37 ≤ (11212453430281326921/100000000000000000000 : ℝ)^8 := by
      have hnat : (31153 : ℕ)^37*100000000000000000000^8 ≤ 11212453430281326921^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31153 50000 11212453430281326921 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31153/50000 : ℝ)) (X := (11212453430281326921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (111212453430281326921/100000000000000000000 : ℝ) ≤ (2046487582774741/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (111212453430281326921/100000000000000000000 : ℝ)^8 ≤ (2046487582774741/2000000000000000 : ℝ)^37 := by
      have hnat : (111212453430281326921 : ℕ)^8*2000000000000000^37 ≤ 2046487582774741^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        111212453430281326921 100000000000000000000 2046487582774741 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2046487582774741/2000000000000000 : ℝ)) (X := (111212453430281326921/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (61212453430281326921/50000000000000000000 : ℝ) ≤ (10447175053835073/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (61212453430281326921/50000000000000000000 : ℝ)^8 ≤ (10447175053835073/10000000000000000 : ℝ)^37 := by
      have hnat : (61212453430281326921 : ℕ)^8*10000000000000000^37 ≤ 10447175053835073^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61212453430281326921 50000000000000000000 10447175053835073 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10447175053835073/10000000000000000 : ℝ)) (X := (61212453430281326921/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(46487582774741/1246120000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(26842142495171/778825000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (31153/50000 : ℝ)) (alpha := (46487582774741/1246120000000000 : ℝ)) (beta := (26842142495171/778825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (31153/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(46487582774741/1246120000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(26842142495171/778825000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (6069/10000 : ℝ) ^ (37/8 : ℝ) ≤ (1985851441897090733/20000000000000000000 : ℝ) := by
    have hpowers : (6069/10000 : ℝ)^37 ≤ (1985851441897090733/20000000000000000000 : ℝ)^8 := by
      have hnat : (6069 : ℕ)^37*20000000000000000000^8 ≤ 1985851441897090733^8*10000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6069 10000 1985851441897090733 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6069/10000 : ℝ)) (X := (1985851441897090733/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (21985851441897090733/20000000000000000000 : ℝ) ≤ (10206794260760989/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (21985851441897090733/20000000000000000000 : ℝ)^8 ≤ (10206794260760989/10000000000000000 : ℝ)^37 := by
      have hnat : (21985851441897090733 : ℕ)^8*10000000000000000^37 ≤ 10206794260760989^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21985851441897090733 20000000000000000000 10206794260760989 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10206794260760989/10000000000000000 : ℝ)) (X := (21985851441897090733/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (11985851441897090733/10000000000000000000 : ℝ) ≤ (5199714447821709/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (11985851441897090733/10000000000000000000 : ℝ)^8 ≤ (5199714447821709/5000000000000000 : ℝ)^37 := by
      have hnat : (11985851441897090733 : ℕ)^8*5000000000000000^37 ≤ 5199714447821709^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11985851441897090733 10000000000000000000 5199714447821709 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5199714447821709/5000000000000000 : ℝ)) (X := (11985851441897090733/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(68931420253663/2023000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(192634634882429/6069000000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (6069/10000 : ℝ)) (alpha := (68931420253663/2023000000000000 : ℝ)) (beta := (192634634882429/6069000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (6069/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(68931420253663/2023000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(192634634882429/6069000000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-141118459/625000000 : ℝ)*X 0 0+(1270554127/2500000000 : ℝ)*X 0 1+(5112349731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4490774659/10000000000 : ℝ)*X 1 0+(-865089429/5000000000 : ℝ)*X 1 1+(6078129491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((4513431843/10000000000 : ℝ)*X 2 0+(3035477853/5000000000 : ℝ)*X 2 1+(-1710868757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1354070189/2000000000 : ℝ)*X 0 0+(2790902257/10000000000 : ℝ)*X 0 1+(686682249/2500000000 : ℝ)*X 0 2+(1354070189/2000000000 : ℝ)*X 1 0+(2790902257/10000000000 : ℝ)*X 1 1+(686682249/2500000000 : ℝ)*X 1 2+(1354070189/2000000000 : ℝ)*X 2 0+(2790902257/10000000000 : ℝ)*X 2 1+(686682249/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1095199619/5000000000 : ℝ)*X 0 0+(2115857067/5000000000 : ℝ)*X 0 1+(2988100013/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4228025677/10000000000 : ℝ)*X 1 0+(-279999883/2000000000 : ℝ)*X 1 1+(6541965807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((425080191/1000000000 : ℝ)*X 2 0+(342042729/500000000 : ℝ)*X 2 1+(-883842479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1315163861/2000000000 : ℝ)*X 0 0+(1981761721/5000000000 : ℝ)*X 0 1+(338881259/2000000000 : ℝ)*X 0 2+(1315163861/2000000000 : ℝ)*X 1 0+(1981761721/5000000000 : ℝ)*X 1 1+(338881259/2000000000 : ℝ)*X 1 2+(1315163861/2000000000 : ℝ)*X 2 0+(1981761721/5000000000 : ℝ)*X 2 1+(338881259/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-352312727/2500000000 : ℝ)*X 0 0+(4918399349/10000000000 : ℝ)*X 0 1+(2950379107/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2064537677/5000000000 : ℝ)*X 1 0+(-46425839/312500000 : ℝ)*X 1 1+(821592621/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2699308877/5000000000 : ℝ)*X 2 0+(5727822407/10000000000 : ℝ)*X 2 1+(-959282601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((771256381/1000000000 : ℝ)*X 0 0+(524373449/2000000000 : ℝ)*X 0 1+(809637233/5000000000 : ℝ)*X 0 2+(771256381/1000000000 : ℝ)*X 1 0+(524373449/2000000000 : ℝ)*X 1 1+(809637233/5000000000 : ℝ)*X 1 2+(771256381/1000000000 : ℝ)*X 2 0+(524373449/2000000000 : ℝ)*X 2 1+(809637233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1313083567/10000000000 : ℝ)*X 0 0+(5457890337/10000000000 : ℝ)*X 0 1+(2719718507/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5472005651/10000000000 : ℝ)*X 1 0+(-1063442957/10000000000 : ℝ)*X 1 1+(1117987813/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4108001171/10000000000 : ℝ)*X 2 0+(3364929/5000000 : ℝ)*X 2 1+(-63661233/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7819626981/10000000000 : ℝ)*X 0 0+(2062606247/10000000000 : ℝ)*X 0 1+(20581603/100000000 : ℝ)*X 0 2+(7819626981/10000000000 : ℝ)*X 1 0+(2062606247/10000000000 : ℝ)*X 1 1+(20581603/100000000 : ℝ)*X 1 2+(7819626981/10000000000 : ℝ)*X 2 0+(2062606247/10000000000 : ℝ)*X 2 1+(20581603/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((15059/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15059/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6770365453948507966237359/1125402125000000000000000000000 : ℝ) := by norm_num
    linear_combination (6757/50000000000 : ℝ)*(base8) + (110787642973/1000000000000 : ℝ)*(base49) + (199007895171/250000000000 : ℝ)*(base59) + (5789200806851/1000000000000 : ℝ)*(major_s2_0) + (5789200806851/1000000000000 : ℝ)*(major_s2_1) + (5789200806851/1000000000000 : ℝ)*(major_s2_2) + (5959473/500000000000 : ℝ)*(sp_s2_0) + (10598907/1000000000000 : ℝ)*(sp_s2_6) + (4106961414881/500000000000 : ℝ)*(sp_s2_7) + (2053409295307/250000000000 : ℝ)*(sp_s2_8) + (8213901165327/1000000000000 : ℝ)*(sp_s2_9) + (3364454125623/1000000000000 : ℝ)*(sp_s2_13) + (148851311/500000000000 : ℝ)*(sp_s2_15) + (16859261/500000000000 : ℝ)*(sp_s2_23) + (336446472453/100000000000 : ℝ)*(f.failure) + (8213934883849/1000000000000 : ℝ)*(f.sum) + (3820906388088778899/4501608500000000000000000000000 : ℝ)*base62 + (243318249158003/867000000000000000000000000 : ℝ)*base65 + (961018719498283/1557650000000000000000000000 : ℝ)*base67 + (141285635072141/289000000000000000000000000 : ℝ)*base68 + (11661904296964099/444987750000000000000000000000 : ℝ)*base70 + (428534838654613/821200000000000000000000000 : ℝ)*base72 + (88961021310153/1246120000000000000000000000 : ℝ)*base74 + (35002984154247/410600000000000000000000000 : ℝ)*base77 + (2950523751932347603/25582843600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base83 + (5257/10000000000000000 : ℝ)*base87 + (5257/10000000000000000 : ℝ)*base89 + (5257/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4463/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4463/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1082252407673694293573/80920000000000000000000000 : ℝ) := by norm_num
    linear_combination (101963/250000000000 : ℝ)*(base39) + (193373118103/1000000000000 : ℝ)*(base49) + (155145615809/500000000000 : ℝ)*(base59) + (45224627521/8000000000 : ℝ)*(major_s2_0) + (45224627521/8000000000 : ℝ)*(major_s2_1) + (45224627521/8000000000 : ℝ)*(major_s2_2) + (19174181/1000000000000 : ℝ)*(sp_s2_1) + (30635243/1000000000000 : ℝ)*(sp_s2_2) + (36977459/500000000000 : ℝ)*(sp_s2_7) + (8020722917913/1000000000000 : ℝ)*(sp_s2_14) + (160415553973/20000000000 : ℝ)*(sp_s2_15) + (2005191559397/250000000000 : ℝ)*(sp_s2_16) + (821314273449/250000000000 : ℝ)*(sp_s2_20) + (6153469/62500000000 : ℝ)*(sp_s2_27) + (32853555493/10000000000 : ℝ)*(f.failure) + (8020796872831/1000000000000 : ℝ)*(f.sum) + (156049426572463463/1260450380000000000000000000000 : ℝ)*base62 + (126154590326123/242760000000000000000000000 : ℝ)*base65 + (13059836125837/19470625000000000000000000 : ℝ)*base67 + (11818450457319/80920000000000000000000000 : ℝ)*base69 + (1713938460743/6069000000000000000000000 : ℝ)*base71 + (73265038517/560000000000000000000000 : ℝ)*base72 + (32961601887001/249224000000000000000000000 : ℝ)*base75 + (65371911379/280000000000000000000000 : ℝ)*base77 + (937276874670021/17445680000000000000000000000 : ℝ)*base78 + (17/1000000000000000 : ℝ)*base87 + (17/1000000000000000 : ℝ)*base89 + (17/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34267/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34267/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32912333561585198215053015999/9241802250500000000000000000000000 : ℝ) := by norm_num
    linear_combination (14774659187/62500000000 : ℝ)*(base40) + (17104271767/500000000000 : ℝ)*(base49) + (23506166443/62500000000 : ℝ)*(base59) + (2541142212319/500000000000 : ℝ)*(major_s2_0) + (2541142212319/500000000000 : ℝ)*(major_s2_1) + (2541142212319/500000000000 : ℝ)*(major_s2_2) + (5231967/500000000000 : ℝ)*(sp_s2_0) + (2403481/500000000000 : ℝ)*(sp_s2_2) + (5169257/1000000000000 : ℝ)*(sp_s2_16) + (5193847/100000000000 : ℝ)*(sp_s2_20) + (7210925559409/1000000000000 : ℝ)*(sp_s2_21) + (450683501459/62500000000 : ℝ)*(sp_s2_22) + (1802731511781/250000000000 : ℝ)*(sp_s2_23) + (738394925093/250000000000 : ℝ)*(sp_s2_27) + (1476815819421/500000000000 : ℝ)*(f.failure) + (450683501459/62500000000 : ℝ)*(f.sum) + (1497911440150276673/3938907437500000000000000000000 : ℝ)*base62 + (1196070605712401/3034500000000000000000000000 : ℝ)*base64 + (37778959827981/97353125000000000000000000 : ℝ)*base66 + (972637842387903/1011500000000000000000000000 : ℝ)*base68 + (295522024599552283/1557457125000000000000000000000 : ℝ)*base71 + (3347728130891239/2874200000000000000000000000 : ℝ)*base72 + (295617370417101/623060000000000000000000000 : ℝ)*base74 + (295165898950651/1437100000000000000000000000 : ℝ)*base77 + (64372275096653282771/89539952600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (52049/50000000000000000 : ℝ)*base87 + (52049/50000000000000000 : ℝ)*base89 + (52049/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((14371/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14371/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31153/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31153/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6069/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6069/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15059/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15059/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4463/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4463/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34267/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(34267/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314053_s2 p hpa hpb X hX hprev1

#print axioms solution
