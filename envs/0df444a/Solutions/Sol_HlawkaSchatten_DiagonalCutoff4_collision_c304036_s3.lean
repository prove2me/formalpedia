-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304036_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:38:57.610354+00:00
-- url     : https://prove2.me/submissions/08be4ec5-e5a2-4e2e-9ce0-4503d7e0c927

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
theorem collision_support_c304036_s3_s3_0 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-177712619/1000000000 : ℝ)*x 0 + (-540988961/1000000000 : ℝ)*x 1 + (-270468467/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (177712619/1000000000 : ℝ)^17 ≤ (10443891454603/100000000000000 : ℝ)^13 := by
    have hnat : (177712619 : ℕ)^17*100000000000000^13 ≤ 10443891454603^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177712619 1000000000 10443891454603 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540988961/1000000000 : ℝ)^17 ≤ (44780870066911/100000000000000 : ℝ)^13 := by
    have hnat : (540988961 : ℕ)^17*100000000000000^13 ≤ 44780870066911^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540988961 1000000000 44780870066911 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270468467/500000000 : ℝ)^17 ≤ (11193809615913/25000000000000 : ℝ)^13 := by
    have hnat : (270468467 : ℕ)^17*25000000000000^13 ≤ 11193809615913^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270468467 500000000 11193809615913 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-177712619/1000000000 : ℝ), (-540988961/1000000000 : ℝ), (-270468467/500000000 : ℝ)] ![(10443891454603/100000000000000 : ℝ), (44780870066911/100000000000000 : ℝ), (11193809615913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-177712619/1000000000 : ℝ)|^17 ≤ (10443891454603/100000000000000 : ℝ)^13
        have hw : |(-177712619/1000000000 : ℝ)|=(177712619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-540988961/1000000000 : ℝ)|^17 ≤ (44780870066911/100000000000000 : ℝ)^13
        have hw : |(-540988961/1000000000 : ℝ)|=(540988961/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270468467/500000000 : ℝ)|^17 ≤ (11193809615913/25000000000000 : ℝ)^13
        have hw : |(-270468467/500000000 : ℝ)|=(270468467/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5308122911/10000000000 : ℝ)*x 0 + (1896994223/5000000000 : ℝ)*x 1 + (-948585089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5308122911/10000000000 : ℝ)^17 ≤ (43682493703061/100000000000000 : ℝ)^13 := by
    have hnat : (5308122911 : ℕ)^17*100000000000000^13 ≤ 43682493703061^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5308122911 10000000000 43682493703061 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896994223/5000000000 : ℝ)^17 ≤ (28157045467281/100000000000000 : ℝ)^13 := by
    have hnat : (1896994223 : ℕ)^17*100000000000000^13 ≤ 28157045467281^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896994223 5000000000 28157045467281 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948585089/2500000000 : ℝ)^17 ≤ (1126418432451/4000000000000 : ℝ)^13 := by
    have hnat : (948585089 : ℕ)^17*4000000000000^13 ≤ 1126418432451^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948585089 2500000000 1126418432451 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5308122911/10000000000 : ℝ), (1896994223/5000000000 : ℝ), (-948585089/2500000000 : ℝ)] ![(43682493703061/100000000000000 : ℝ), (28157045467281/100000000000000 : ℝ), (1126418432451/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5308122911/10000000000 : ℝ)|^17 ≤ (43682493703061/100000000000000 : ℝ)^13
        have hw : |(5308122911/10000000000 : ℝ)|=(5308122911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1896994223/5000000000 : ℝ)|^17 ≤ (28157045467281/100000000000000 : ℝ)^13
        have hw : |(1896994223/5000000000 : ℝ)|=(1896994223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948585089/2500000000 : ℝ)|^17 ≤ (1126418432451/4000000000000 : ℝ)^13
        have hw : |(-948585089/2500000000 : ℝ)|=(948585089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5307553083/10000000000 : ℝ)*x 0 + (-3794304347/10000000000 : ℝ)*x 1 + (1897328143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5307553083/10000000000 : ℝ)^17 ≤ (43676361611451/100000000000000 : ℝ)^13 := by
    have hnat : (5307553083 : ℕ)^17*100000000000000^13 ≤ 43676361611451^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5307553083 10000000000 43676361611451 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3794304347/10000000000 : ℝ)^17 ≤ (3520013916697/12500000000000 : ℝ)^13 := by
    have hnat : (3794304347 : ℕ)^17*12500000000000^13 ≤ 3520013916697^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3794304347 10000000000 3520013916697 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1897328143/5000000000 : ℝ)^17 ≤ (7040881761631/25000000000000 : ℝ)^13 := by
    have hnat : (1897328143 : ℕ)^17*25000000000000^13 ≤ 7040881761631^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897328143 5000000000 7040881761631 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5307553083/10000000000 : ℝ), (-3794304347/10000000000 : ℝ), (1897328143/5000000000 : ℝ)] ![(43676361611451/100000000000000 : ℝ), (3520013916697/12500000000000 : ℝ), (7040881761631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5307553083/10000000000 : ℝ)|^17 ≤ (43676361611451/100000000000000 : ℝ)^13
        have hw : |(5307553083/10000000000 : ℝ)|=(5307553083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3794304347/10000000000 : ℝ)|^17 ≤ (3520013916697/12500000000000 : ℝ)^13
        have hw : |(-3794304347/10000000000 : ℝ)|=(3794304347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1897328143/5000000000 : ℝ)|^17 ≤ (7040881761631/25000000000000 : ℝ)^13
        have hw : |(1897328143/5000000000 : ℝ)|=(1897328143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-221877213/1250000000 : ℝ)*x 0 + (-5436744757/10000000000 : ℝ)*x 1 + (-2691985639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221877213/1250000000 : ℝ)^17 ≤ (2606922620651/25000000000000 : ℝ)^13 := by
    have hnat : (221877213 : ℕ)^17*25000000000000^13 ≤ 2606922620651^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221877213 1250000000 2606922620651 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436744757/10000000000 : ℝ)^17 ≤ (45071786594173/100000000000000 : ℝ)^13 := by
    have hnat : (5436744757 : ℕ)^17*100000000000000^13 ≤ 45071786594173^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436744757 10000000000 45071786594173 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2691985639/5000000000 : ℝ)^17 ≤ (11125130725907/25000000000000 : ℝ)^13 := by
    have hnat : (2691985639 : ℕ)^17*25000000000000^13 ≤ 11125130725907^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691985639 5000000000 11125130725907 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221877213/1250000000 : ℝ), (-5436744757/10000000000 : ℝ), (-2691985639/5000000000 : ℝ)] ![(2606922620651/25000000000000 : ℝ), (45071786594173/100000000000000 : ℝ), (11125130725907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221877213/1250000000 : ℝ)|^17 ≤ (2606922620651/25000000000000 : ℝ)^13
        have hw : |(-221877213/1250000000 : ℝ)|=(221877213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5436744757/10000000000 : ℝ)|^17 ≤ (45071786594173/100000000000000 : ℝ)^13
        have hw : |(-5436744757/10000000000 : ℝ)|=(5436744757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2691985639/5000000000 : ℝ)|^17 ≤ (11125130725907/25000000000000 : ℝ)^13
        have hw : |(-2691985639/5000000000 : ℝ)|=(2691985639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (528675239/1000000000 : ℝ)*x 0 + (477844857/1250000000 : ℝ)*x 1 + (-3789217673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528675239/1000000000 : ℝ)^17 ≤ (21726328918329/50000000000000 : ℝ)^13 := by
    have hnat : (528675239 : ℕ)^17*50000000000000^13 ≤ 21726328918329^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528675239 1000000000 21726328918329 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (477844857/1250000000 : ℝ)^17 ≤ (7109147046591/25000000000000 : ℝ)^13 := by
    have hnat : (477844857 : ℕ)^17*25000000000000^13 ≤ 7109147046591^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      477844857 1250000000 7109147046591 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3789217673/10000000000 : ℝ)^17 ≤ (28110753956891/100000000000000 : ℝ)^13 := by
    have hnat : (3789217673 : ℕ)^17*100000000000000^13 ≤ 28110753956891^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789217673 10000000000 28110753956891 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528675239/1000000000 : ℝ), (477844857/1250000000 : ℝ), (-3789217673/10000000000 : ℝ)] ![(21726328918329/50000000000000 : ℝ), (7109147046591/25000000000000 : ℝ), (28110753956891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528675239/1000000000 : ℝ)|^17 ≤ (21726328918329/50000000000000 : ℝ)^13
        have hw : |(528675239/1000000000 : ℝ)|=(528675239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(477844857/1250000000 : ℝ)|^17 ≤ (7109147046591/25000000000000 : ℝ)^13
        have hw : |(477844857/1250000000 : ℝ)|=(477844857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3789217673/10000000000 : ℝ)|^17 ≤ (28110753956891/100000000000000 : ℝ)^13
        have hw : |(-3789217673/10000000000 : ℝ)|=(3789217673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (212668759/400000000 : ℝ)*x 0 + (-3756962683/10000000000 : ℝ)*x 1 + (955436261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212668759/400000000 : ℝ)^17 ≤ (5471877889547/12500000000000 : ℝ)^13 := by
    have hnat : (212668759 : ℕ)^17*12500000000000^13 ≤ 5471877889547^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212668759 400000000 5471877889547 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3756962683/10000000000 : ℝ)^17 ≤ (2779825024589/10000000000000 : ℝ)^13 := by
    have hnat : (3756962683 : ℕ)^17*10000000000000^13 ≤ 2779825024589^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3756962683 10000000000 2779825024589 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (955436261/2500000000 : ℝ)^17 ≤ (710668165523/2500000000000 : ℝ)^13 := by
    have hnat : (955436261 : ℕ)^17*2500000000000^13 ≤ 710668165523^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955436261 2500000000 710668165523 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212668759/400000000 : ℝ), (-3756962683/10000000000 : ℝ), (955436261/2500000000 : ℝ)] ![(5471877889547/12500000000000 : ℝ), (2779825024589/10000000000000 : ℝ), (710668165523/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212668759/400000000 : ℝ)|^17 ≤ (5471877889547/12500000000000 : ℝ)^13
        have hw : |(212668759/400000000 : ℝ)|=(212668759/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3756962683/10000000000 : ℝ)|^17 ≤ (2779825024589/10000000000000 : ℝ)^13
        have hw : |(-3756962683/10000000000 : ℝ)|=(3756962683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(955436261/2500000000 : ℝ)|^17 ≤ (710668165523/2500000000000 : ℝ)^13
        have hw : |(955436261/2500000000 : ℝ)|=(955436261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5137183471/10000000000 : ℝ)*x 0 + (-1933098309/5000000000 : ℝ)*x 1 + (-3909981071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5137183471/10000000000 : ℝ)^17 ≤ (20926057393149/50000000000000 : ℝ)^13 := by
    have hnat : (5137183471 : ℕ)^17*50000000000000^13 ≤ 20926057393149^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137183471 10000000000 20926057393149 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933098309/5000000000 : ℝ)^17 ≤ (1154394821649/4000000000000 : ℝ)^13 := by
    have hnat : (1933098309 : ℕ)^17*4000000000000^13 ≤ 1154394821649^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933098309 5000000000 1154394821649 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3909981071/10000000000 : ℝ)^17 ≤ (29288014664433/100000000000000 : ℝ)^13 := by
    have hnat : (3909981071 : ℕ)^17*100000000000000^13 ≤ 29288014664433^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3909981071 10000000000 29288014664433 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5137183471/10000000000 : ℝ), (-1933098309/5000000000 : ℝ), (-3909981071/10000000000 : ℝ)] ![(20926057393149/50000000000000 : ℝ), (1154394821649/4000000000000 : ℝ), (29288014664433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5137183471/10000000000 : ℝ)|^17 ≤ (20926057393149/50000000000000 : ℝ)^13
        have hw : |(5137183471/10000000000 : ℝ)|=(5137183471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933098309/5000000000 : ℝ)|^17 ≤ (1154394821649/4000000000000 : ℝ)^13
        have hw : |(-1933098309/5000000000 : ℝ)|=(1933098309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3909981071/10000000000 : ℝ)|^17 ≤ (29288014664433/100000000000000 : ℝ)^13
        have hw : |(-3909981071/10000000000 : ℝ)|=(3909981071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-74548739/500000000 : ℝ)*x 0 + (-215047859/400000000 : ℝ)*x 1 + (-1127894183/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74548739/500000000 : ℝ)^17 ≤ (1660288124183/20000000000000 : ℝ)^13 := by
    have hnat : (74548739 : ℕ)^17*20000000000000^13 ≤ 1660288124183^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74548739 500000000 1660288124183 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215047859/400000000 : ℝ)^17 ≤ (8883301426609/20000000000000 : ℝ)^13 := by
    have hnat : (215047859 : ℕ)^17*20000000000000^13 ≤ 8883301426609^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215047859 400000000 8883301426609 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127894183/2000000000 : ℝ)^17 ≤ (47282052235797/100000000000000 : ℝ)^13 := by
    have hnat : (1127894183 : ℕ)^17*100000000000000^13 ≤ 47282052235797^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127894183 2000000000 47282052235797 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-74548739/500000000 : ℝ), (-215047859/400000000 : ℝ), (-1127894183/2000000000 : ℝ)] ![(1660288124183/20000000000000 : ℝ), (8883301426609/20000000000000 : ℝ), (47282052235797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-74548739/500000000 : ℝ)|^17 ≤ (1660288124183/20000000000000 : ℝ)^13
        have hw : |(-74548739/500000000 : ℝ)|=(74548739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215047859/400000000 : ℝ)|^17 ≤ (8883301426609/20000000000000 : ℝ)^13
        have hw : |(-215047859/400000000 : ℝ)|=(215047859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127894183/2000000000 : ℝ)|^17 ≤ (47282052235797/100000000000000 : ℝ)^13
        have hw : |(-1127894183/2000000000 : ℝ)|=(1127894183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5302989397/10000000000 : ℝ)*x 0 + (1925914829/5000000000 : ℝ)*x 1 + (-233871579/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302989397/10000000000 : ℝ)^17 ≤ (21813628856909/50000000000000 : ℝ)^13 := by
    have hnat : (5302989397 : ℕ)^17*50000000000000^13 ≤ 21813628856909^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302989397 10000000000 21813628856909 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1925914829/5000000000 : ℝ)^17 ≤ (28719707883611/100000000000000 : ℝ)^13 := by
    have hnat : (1925914829 : ℕ)^17*100000000000000^13 ≤ 28719707883611^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1925914829 5000000000 28719707883611 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233871579/625000000 : ℝ)^17 ≤ (6913258597039/25000000000000 : ℝ)^13 := by
    have hnat : (233871579 : ℕ)^17*25000000000000^13 ≤ 6913258597039^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233871579 625000000 6913258597039 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302989397/10000000000 : ℝ), (1925914829/5000000000 : ℝ), (-233871579/625000000 : ℝ)] ![(21813628856909/50000000000000 : ℝ), (28719707883611/100000000000000 : ℝ), (6913258597039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302989397/10000000000 : ℝ)|^17 ≤ (21813628856909/50000000000000 : ℝ)^13
        have hw : |(5302989397/10000000000 : ℝ)|=(5302989397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1925914829/5000000000 : ℝ)|^17 ≤ (28719707883611/100000000000000 : ℝ)^13
        have hw : |(1925914829/5000000000 : ℝ)|=(1925914829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233871579/625000000 : ℝ)|^17 ≤ (6913258597039/25000000000000 : ℝ)^13
        have hw : |(-233871579/625000000 : ℝ)|=(233871579/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5561455807/10000000000 : ℝ)*x 0 + (-926146839/2500000000 : ℝ)*x 1 + (3598903467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5561455807/10000000000 : ℝ)^17 ≤ (23214265840461/50000000000000 : ℝ)^13 := by
    have hnat : (5561455807 : ℕ)^17*50000000000000^13 ≤ 23214265840461^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5561455807 10000000000 23214265840461 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (926146839/2500000000 : ℝ)^17 ≤ (27292568331477/100000000000000 : ℝ)^13 := by
    have hnat : (926146839 : ℕ)^17*100000000000000^13 ≤ 27292568331477^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926146839 2500000000 27292568331477 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3598903467/10000000000 : ℝ)^17 ≤ (13139449982763/50000000000000 : ℝ)^13 := by
    have hnat : (3598903467 : ℕ)^17*50000000000000^13 ≤ 13139449982763^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3598903467 10000000000 13139449982763 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5561455807/10000000000 : ℝ), (-926146839/2500000000 : ℝ), (3598903467/10000000000 : ℝ)] ![(23214265840461/50000000000000 : ℝ), (27292568331477/100000000000000 : ℝ), (13139449982763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5561455807/10000000000 : ℝ)|^17 ≤ (23214265840461/50000000000000 : ℝ)^13
        have hw : |(5561455807/10000000000 : ℝ)|=(5561455807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-926146839/2500000000 : ℝ)|^17 ≤ (27292568331477/100000000000000 : ℝ)^13
        have hw : |(-926146839/2500000000 : ℝ)|=(926146839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3598903467/10000000000 : ℝ)|^17 ≤ (13139449982763/50000000000000 : ℝ)^13
        have hw : |(3598903467/10000000000 : ℝ)|=(3598903467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_19 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5210394567/10000000000 : ℝ)*x 0 + (-3755776331/10000000000 : ℝ)*x 1 + (-3939698163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5210394567/10000000000 : ℝ)^17 ≤ (42633783714223/100000000000000 : ℝ)^13 := by
    have hnat : (5210394567 : ℕ)^17*100000000000000^13 ≤ 42633783714223^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5210394567 10000000000 42633783714223 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3755776331/10000000000 : ℝ)^17 ≤ (13893385959163/50000000000000 : ℝ)^13 := by
    have hnat : (3755776331 : ℕ)^17*50000000000000^13 ≤ 13893385959163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3755776331 10000000000 13893385959163 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3939698163/10000000000 : ℝ)^17 ≤ (29579444347799/100000000000000 : ℝ)^13 := by
    have hnat : (3939698163 : ℕ)^17*100000000000000^13 ≤ 29579444347799^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3939698163 10000000000 29579444347799 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5210394567/10000000000 : ℝ), (-3755776331/10000000000 : ℝ), (-3939698163/10000000000 : ℝ)] ![(42633783714223/100000000000000 : ℝ), (13893385959163/50000000000000 : ℝ), (29579444347799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5210394567/10000000000 : ℝ)|^17 ≤ (42633783714223/100000000000000 : ℝ)^13
        have hw : |(5210394567/10000000000 : ℝ)|=(5210394567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3755776331/10000000000 : ℝ)|^17 ≤ (13893385959163/50000000000000 : ℝ)^13
        have hw : |(-3755776331/10000000000 : ℝ)|=(3755776331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3939698163/10000000000 : ℝ)|^17 ≤ (29579444347799/100000000000000 : ℝ)^13
        have hw : |(-3939698163/10000000000 : ℝ)|=(3939698163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-149101547/1000000000 : ℝ)*x 0 + (-9023901/16000000 : ℝ)*x 1 + (-1075138981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (149101547/1000000000 : ℝ)^17 ≤ (1660347376897/20000000000000 : ℝ)^13 := by
    have hnat : (149101547 : ℕ)^17*20000000000000^13 ≤ 1660347376897^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149101547 1000000000 1660347376897 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9023901/16000000 : ℝ)^17 ≤ (23643587363323/50000000000000 : ℝ)^13 := by
    have hnat : (9023901 : ℕ)^17*50000000000000^13 ≤ 23643587363323^13*16000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9023901 16000000 23643587363323 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075138981/2000000000 : ℝ)^17 ≤ (22205544185007/50000000000000 : ℝ)^13 := by
    have hnat : (1075138981 : ℕ)^17*50000000000000^13 ≤ 22205544185007^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075138981 2000000000 22205544185007 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-149101547/1000000000 : ℝ), (-9023901/16000000 : ℝ), (-1075138981/2000000000 : ℝ)] ![(1660347376897/20000000000000 : ℝ), (23643587363323/50000000000000 : ℝ), (22205544185007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-149101547/1000000000 : ℝ)|^17 ≤ (1660347376897/20000000000000 : ℝ)^13
        have hw : |(-149101547/1000000000 : ℝ)|=(149101547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-9023901/16000000 : ℝ)|^17 ≤ (23643587363323/50000000000000 : ℝ)^13
        have hw : |(-9023901/16000000 : ℝ)|=(9023901/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1075138981/2000000000 : ℝ)|^17 ≤ (22205544185007/50000000000000 : ℝ)^13
        have hw : |(-1075138981/2000000000 : ℝ)|=(1075138981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5562017091/10000000000 : ℝ)*x 0 + (359827193/1000000000 : ℝ)*x 1 + (-3704577243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5562017091/10000000000 : ℝ)^17 ≤ (1451083102981/3125000000000 : ℝ)^13 := by
    have hnat : (5562017091 : ℕ)^17*3125000000000^13 ≤ 1451083102981^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5562017091 10000000000 1451083102981 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (359827193/1000000000 : ℝ)^17 ≤ (2627286979453/10000000000000 : ℝ)^13 := by
    have hnat : (359827193 : ℕ)^17*10000000000000^13 ≤ 2627286979453^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359827193 1000000000 2627286979453 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3704577243/10000000000 : ℝ)^17 ≤ (6823117725523/25000000000000 : ℝ)^13 := by
    have hnat : (3704577243 : ℕ)^17*25000000000000^13 ≤ 6823117725523^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3704577243 10000000000 6823117725523 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5562017091/10000000000 : ℝ), (359827193/1000000000 : ℝ), (-3704577243/10000000000 : ℝ)] ![(1451083102981/3125000000000 : ℝ), (2627286979453/10000000000000 : ℝ), (6823117725523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5562017091/10000000000 : ℝ)|^17 ≤ (1451083102981/3125000000000 : ℝ)^13
        have hw : |(5562017091/10000000000 : ℝ)|=(5562017091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(359827193/1000000000 : ℝ)|^17 ≤ (2627286979453/10000000000000 : ℝ)^13
        have hw : |(359827193/1000000000 : ℝ)|=(359827193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3704577243/10000000000 : ℝ)|^17 ≤ (6823117725523/25000000000000 : ℝ)^13
        have hw : |(-3704577243/10000000000 : ℝ)|=(3704577243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2651184123/5000000000 : ℝ)*x 0 + (-935488767/2500000000 : ℝ)*x 1 + (1926252637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651184123/5000000000 : ℝ)^17 ≤ (5452571914959/12500000000000 : ℝ)^13 := by
    have hnat : (2651184123 : ℕ)^17*12500000000000^13 ≤ 5452571914959^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651184123 5000000000 5452571914959 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935488767/2500000000 : ℝ)^17 ≤ (27653129132743/100000000000000 : ℝ)^13 := by
    have hnat : (935488767 : ℕ)^17*100000000000000^13 ≤ 27653129132743^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935488767 2500000000 27653129132743 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926252637/5000000000 : ℝ)^17 ≤ (14363147764091/50000000000000 : ℝ)^13 := by
    have hnat : (1926252637 : ℕ)^17*50000000000000^13 ≤ 14363147764091^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926252637 5000000000 14363147764091 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651184123/5000000000 : ℝ), (-935488767/2500000000 : ℝ), (1926252637/5000000000 : ℝ)] ![(5452571914959/12500000000000 : ℝ), (27653129132743/100000000000000 : ℝ), (14363147764091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651184123/5000000000 : ℝ)|^17 ≤ (5452571914959/12500000000000 : ℝ)^13
        have hw : |(2651184123/5000000000 : ℝ)|=(2651184123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935488767/2500000000 : ℝ)|^17 ≤ (27653129132743/100000000000000 : ℝ)^13
        have hw : |(-935488767/2500000000 : ℝ)|=(935488767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1926252637/5000000000 : ℝ)|^17 ≤ (14363147764091/50000000000000 : ℝ)^13
        have hw : |(1926252637/5000000000 : ℝ)|=(1926252637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304036_s3_s3_25 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1042086713/2000000000 : ℝ)*x 0 + (-985003093/2500000000 : ℝ)*x 1 + (-1877707163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042086713/2000000000 : ℝ)^17 ≤ (21317100499081/50000000000000 : ℝ)^13 := by
    have hnat : (1042086713 : ℕ)^17*50000000000000^13 ≤ 21317100499081^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042086713 2000000000 21317100499081 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985003093/2500000000 : ℝ)^17 ≤ (1183301174313/4000000000000 : ℝ)^13 := by
    have hnat : (985003093 : ℕ)^17*4000000000000^13 ≤ 1183301174313^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985003093 2500000000 1183301174313 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1877707163/5000000000 : ℝ)^17 ≤ (27783269628573/100000000000000 : ℝ)^13 := by
    have hnat : (1877707163 : ℕ)^17*100000000000000^13 ≤ 27783269628573^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1877707163 5000000000 27783269628573 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042086713/2000000000 : ℝ), (-985003093/2500000000 : ℝ), (-1877707163/5000000000 : ℝ)] ![(21317100499081/50000000000000 : ℝ), (1183301174313/4000000000000 : ℝ), (27783269628573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042086713/2000000000 : ℝ)|^17 ≤ (21317100499081/50000000000000 : ℝ)^13
        have hw : |(1042086713/2000000000 : ℝ)|=(1042086713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985003093/2500000000 : ℝ)|^17 ≤ (1183301174313/4000000000000 : ℝ)^13
        have hw : |(-985003093/2500000000 : ℝ)|=(985003093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1877707163/5000000000 : ℝ)|^17 ≤ (27783269628573/100000000000000 : ℝ)^13
        have hw : |(-1877707163/5000000000 : ℝ)|=(1877707163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304036_s3 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((10373/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42181/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-42181/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8451/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8451/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1269/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1269/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12693/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12693/100000 : ℝ)*X 1 2) := by
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
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (10373/100000 : ℝ) ^ (33/8 : ℝ) ≤ (2180447164298673/25000000000000000000 : ℝ) := by
    have hpowers : (10373/100000 : ℝ)^33 ≤ (2180447164298673/25000000000000000000 : ℝ)^8 := by
      have hnat : (10373 : ℕ)^33*25000000000000000000^8 ≤ 2180447164298673^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10373 100000 2180447164298673 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10373/100000 : ℝ)) (X := (2180447164298673/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (25002180447164298673/25000000000000000000 : ℝ) ≤ (10000211430315867/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (25002180447164298673/25000000000000000000 : ℝ)^8 ≤ (10000211430315867/10000000000000000 : ℝ)^33 := by
      have hnat : (25002180447164298673 : ℕ)^8*10000000000000000^33 ≤ 10000211430315867^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002180447164298673 25000000000000000000 10000211430315867 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000211430315867/10000000000000000 : ℝ)) (X := (25002180447164298673/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (12502180447164298673/12500000000000000000 : ℝ) ≤ (5000211423331667/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (12502180447164298673/12500000000000000000 : ℝ)^8 ≤ (5000211423331667/5000000000000000 : ℝ)^33 := by
      have hnat : (12502180447164298673 : ℕ)^8*5000000000000000^33 ≤ 5000211423331667^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502180447164298673 12500000000000000000 5000211423331667 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000211423331667/5000000000000000 : ℝ)) (X := (12502180447164298673/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(9192622429/45100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(211416347467/1037300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (10373/100000 : ℝ)) (alpha := (9192622429/45100000000000 : ℝ)) (beta := (211416347467/1037300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10373/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(9192622429/45100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(211416347467/1037300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (42181/100000 : ℝ) ^ (33/8 : ℝ) ≤ (2841888894751629341/100000000000000000000 : ℝ) := by
    have hpowers : (42181/100000 : ℝ)^33 ≤ (2841888894751629341/100000000000000000000 : ℝ)^8 := by
      have hnat : (42181 : ℕ)^33*100000000000000000000^8 ≤ 2841888894751629341^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42181 100000 2841888894751629341 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42181/100000 : ℝ)) (X := (2841888894751629341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (102841888894751629341/100000000000000000000 : ℝ) ≤ (629260297421961/625000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (102841888894751629341/100000000000000000000 : ℝ)^8 ≤ (629260297421961/625000000000000 : ℝ)^33 := by
      have hnat : (102841888894751629341 : ℕ)^8*625000000000000^33 ≤ 629260297421961^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102841888894751629341 100000000000000000000 629260297421961 625000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (629260297421961/625000000000000 : ℝ)) (X := (102841888894751629341/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (52841888894751629341/50000000000000000000 : ℝ) ≤ (5067458554191471/5000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (52841888894751629341/50000000000000000000 : ℝ)^8 ≤ (5067458554191471/5000000000000000 : ℝ)^33 := by
      have hnat : (52841888894751629341 : ℕ)^8*5000000000000000^33 ≤ 5067458554191471^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52841888894751629341 50000000000000000000 5067458554191471 5000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5067458554191471/5000000000000000 : ℝ)) (X := (52841888894751629341/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(4260297421961/263631250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(33376174815783/2109050000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (42181/100000 : ℝ)) (alpha := (4260297421961/263631250000000 : ℝ)) (beta := (33376174815783/2109050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (42181/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(4260297421961/263631250000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(33376174815783/2109050000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (8451/20000 : ℝ) ^ (33/8 : ℝ) ≤ (35781389409109479/1250000000000000000 : ℝ) := by
    have hpowers : (8451/20000 : ℝ)^33 ≤ (35781389409109479/1250000000000000000 : ℝ)^8 := by
      have hnat : (8451 : ℕ)^33*1250000000000000000^8 ≤ 35781389409109479^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8451 20000 35781389409109479 1250000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8451/20000 : ℝ)) (X := (35781389409109479/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (1285781389409109479/1250000000000000000 : ℝ) ≤ (2517163538443209/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (1285781389409109479/1250000000000000000 : ℝ)^8 ≤ (2517163538443209/2500000000000000 : ℝ)^33 := by
      have hnat : (1285781389409109479 : ℕ)^8*2500000000000000^33 ≤ 2517163538443209^33*1250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1285781389409109479 1250000000000000000 2517163538443209 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517163538443209/2500000000000000 : ℝ)) (X := (1285781389409109479/1250000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (660781389409109479/625000000000000000 : ℝ) ≤ (1013587582430363/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (660781389409109479/625000000000000000 : ℝ)^8 ≤ (1013587582430363/1000000000000000 : ℝ)^33 := by
      have hnat : (660781389409109479 : ℕ)^8*1000000000000000^33 ≤ 1013587582430363^33*625000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        660781389409109479 625000000000000000 1013587582430363 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1013587582430363/1000000000000000 : ℝ)) (X := (660781389409109479/625000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(17163538443209/1056375000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(33610835265397/2112750000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (8451/20000 : ℝ)) (alpha := (17163538443209/1056375000000000 : ℝ)) (beta := (33610835265397/2112750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8451/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(17163538443209/1056375000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(33610835265397/2112750000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-177712619/1000000000 : ℝ)*X 0 0+(-540988961/1000000000 : ℝ)*X 0 1+(-270468467/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((5308122911/10000000000 : ℝ)*X 1 0+(1896994223/5000000000 : ℝ)*X 1 1+(-948585089/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((5307553083/10000000000 : ℝ)*X 2 0+(-3794304347/10000000000 : ℝ)*X 2 1+(1897328143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-221877213/1250000000 : ℝ)*X 0 0+(-5436744757/10000000000 : ℝ)*X 0 1+(-2691985639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((528675239/1000000000 : ℝ)*X 1 0+(477844857/1250000000 : ℝ)*X 1 1+(-3789217673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((212668759/400000000 : ℝ)*X 2 0+(-3756962683/10000000000 : ℝ)*X 2 1+(955436261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5137183471/10000000000 : ℝ)*X 0 0+(-1933098309/5000000000 : ℝ)*X 0 1+(-3909981071/10000000000 : ℝ)*X 0 2+(5137183471/10000000000 : ℝ)*X 1 0+(-1933098309/5000000000 : ℝ)*X 1 1+(-3909981071/10000000000 : ℝ)*X 1 2+(5137183471/10000000000 : ℝ)*X 2 0+(-1933098309/5000000000 : ℝ)*X 2 1+(-3909981071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-74548739/500000000 : ℝ)*X 0 0+(-215047859/400000000 : ℝ)*X 0 1+(-1127894183/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((5302989397/10000000000 : ℝ)*X 1 0+(1925914829/5000000000 : ℝ)*X 1 1+(-233871579/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5561455807/10000000000 : ℝ)*X 2 0+(-926146839/2500000000 : ℝ)*X 2 1+(3598903467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_19 : ((5210394567/10000000000 : ℝ)*X 0 0+(-3755776331/10000000000 : ℝ)*X 0 1+(-3939698163/10000000000 : ℝ)*X 0 2+(5210394567/10000000000 : ℝ)*X 1 0+(-3755776331/10000000000 : ℝ)*X 1 1+(-3939698163/10000000000 : ℝ)*X 1 2+(5210394567/10000000000 : ℝ)*X 2 0+(-3755776331/10000000000 : ℝ)*X 2 1+(-3939698163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((-149101547/1000000000 : ℝ)*X 0 0+(-9023901/16000000 : ℝ)*X 0 1+(-1075138981/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((5562017091/10000000000 : ℝ)*X 1 0+(359827193/1000000000 : ℝ)*X 1 1+(-3704577243/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((2651184123/5000000000 : ℝ)*X 2 0+(-935488767/2500000000 : ℝ)*X 2 1+(1926252637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_25 : ((1042086713/2000000000 : ℝ)*X 0 0+(-985003093/2500000000 : ℝ)*X 0 1+(-1877707163/5000000000 : ℝ)*X 0 2+(1042086713/2000000000 : ℝ)*X 1 0+(-985003093/2500000000 : ℝ)*X 1 1+(-1877707163/5000000000 : ℝ)*X 1 2+(1042086713/2000000000 : ℝ)*X 2 0+(-985003093/2500000000 : ℝ)*X 2 1+(-1877707163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304036_s3_s3_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((9/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (504352478631307444208963360329/61628003806050000000000000000000000 : ℝ) := by norm_num
    linear_combination (242527269553/250000000000 : ℝ)*(base39) + (150137588863/1000000000000 : ℝ)*(base50) + (33280958667/250000000000 : ℝ)*(base60) + (829185804823/200000000000 : ℝ)*(major_s3_0) + (829185804823/200000000000 : ℝ)*(major_s3_1) + (829185804823/200000000000 : ℝ)*(major_s3_2) + (18756461/25000000000 : ℝ)*(sp_s3_0) + (2524274861/1000000000000 : ℝ)*(sp_s3_2) + (5557564715189/1000000000000 : ℝ)*(sp_s3_7) + (138959296661/25000000000 : ℝ)*(sp_s3_8) + (277676671579/50000000000 : ℝ)*(sp_s3_9) + (546696690769/200000000000 : ℝ)*(sp_s3_13) + (5689281/100000000000 : ℝ)*(sp_s3_14) + (2314159999/1000000000000 : ℝ)*(sp_s3_22) + (546696690769/200000000000 : ℝ)*(f.failure) + (138959296661/25000000000 : ℝ)*(f.sum) + (9879492674408180891/17823581550000000000000000000000 : ℝ)*base62 + (36496138437079/105637500000000000000000000 : ℝ)*base64 + (64205911327731/210905000000000000000000000 : ℝ)*base66 + (188513419232711/422550000000000000000000000 : ℝ)*base68 + (21874683239494423/381140100000000000000000000000 : ℝ)*base71 + (109886093271131/207460000000000000000000000 : ℝ)*base73 + (10670588548353/26363125000000000000000000 : ℝ)*base74 + (497093172253/1804000000000000000000000 : ℝ)*base77 + (622996620159044337/1750174052000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1971/2500000000000000 : ℝ)*base87 + (1971/2500000000000000 : ℝ)*base89 + (1971/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1269/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1269/10000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (316888699598559469388364561/21877175650000000000000000000000 : ℝ) := by norm_num
    linear_combination (663995279783/100000000000 : ℝ)*(base39) + (134956857507/40000000000 : ℝ)*(base40) + (291253/25000000000 : ℝ)*(base50) + (131004242819/250000000000 : ℝ)*(base60) + (13701638521251/1000000000000 : ℝ)*(major_s3_0) + (13701638521251/1000000000000 : ℝ)*(major_s3_1) + (13701638521251/1000000000000 : ℝ)*(major_s3_2) + (374723283/1000000000000 : ℝ)*(sp_s3_0) + (41075573/125000000000 : ℝ)*(sp_s3_1) + (1455463339/500000000000 : ℝ)*(sp_s3_8) + (4592291945971/250000000000 : ℝ)*(sp_s3_14) + (3673260595181/200000000000 : ℝ)*(sp_s3_15) + (18369542507167/1000000000000 : ℝ)*(sp_s3_16) + (9033729707033/1000000000000 : ℝ)*(sp_s3_19) + (9033729707033/1000000000000 : ℝ)*(f.failure) + (18369542507167/1000000000000 : ℝ)*(f.sum) + (2287515705231798853/9901989750000000000000000000000 : ℝ)*base62 + (736920908251/29343750000000000000000000 : ℝ)*base64 + (544937067907069/1054525000000000000000000000 : ℝ)*base66 + (44925795874051/117375000000000000000000000 : ℝ)*base69 + (74133157275277289/211744500000000000000000000000 : ℝ)*base71 + (87625068244973/1037300000000000000000000000 : ℝ)*base72 + (30927925434839/263631250000000000000000000 : ℝ)*base74 + (7473058410071/45100000000000000000000000 : ℝ)*base76 + (2847490701569926641/43754351300000000000000000000000 : ℝ)*base78 + (1147/12500000000000000 : ℝ)*base87 + (1147/12500000000000000 : ℝ)*base89 + (1147/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12693/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12693/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1115187829127486910429893/79404187500000000000000000000 : ℝ) := by norm_num
    linear_combination (6641137262943/1000000000000 : ℝ)*(base39) + (3266302052591/1000000000000 : ℝ)*(base40) + (104841085797/200000000000 : ℝ)*(base50) + (3149597/125000000000 : ℝ)*(base60) + (3425998330703/250000000000 : ℝ)*(major_s3_0) + (3425998330703/250000000000 : ℝ)*(major_s3_1) + (3425998330703/250000000000 : ℝ)*(major_s3_2) + (755066567/1000000000000 : ℝ)*(sp_s3_2) + (219007321/200000000000 : ℝ)*(sp_s3_7) + (246205603/250000000000 : ℝ)*(sp_s3_15) + (18371604658681/1000000000000 : ℝ)*(sp_s3_20) + (9185857436437/500000000000 : ℝ)*(sp_s3_21) + (18371944628719/1000000000000 : ℝ)*(sp_s3_22) + (9035282268851/1000000000000 : ℝ)*(sp_s3_25) + (9035282268851/1000000000000 : ℝ)*(f.failure) + (9186349847643/500000000000 : ℝ)*(f.sum) + (18170410408353300799/89117907750000000000000000000000 : ℝ)*base62 + (311315981160907/1056375000000000000000000000 : ℝ)*base64 + (689358761748291/2109050000000000000000000000 : ℝ)*base66 + (180299746023341/2112750000000000000000000000 : ℝ)*base69 + (276614049884348197/476425125000000000000000000000 : ℝ)*base70 + (7570676579627/11275000000000000000000000 : ℝ)*base73 + (39952921217953/1054525000000000000000000000 : ℝ)*base75 + (13141369549511/22550000000000000000000000 : ℝ)*base76 + (18920980735716709/29724423437500000000000000000 : ℝ)*base79 + (3891/12500000000000000 : ℝ)*base86 + (3891/12500000000000000 : ℝ)*base88 + (3891/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev2 : (0 : ℝ) ≤ ((10373/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10373/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-42181/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-42181/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8451/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8451/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1269/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-1269/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-12693/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-12693/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304036_s3 p hpa hpb X hX hprev2

#print axioms solution
