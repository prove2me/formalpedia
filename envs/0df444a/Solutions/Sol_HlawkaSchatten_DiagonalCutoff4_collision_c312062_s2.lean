-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:54.886993+00:00
-- url     : https://prove2.me/submissions/04c74255-d53d-479e-8990-0dbbd6e3f0af

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
theorem collision_support_c312062_s2_s2_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-913447517/5000000000 : ℝ)*x 0 + (614303351/1250000000 : ℝ)*x 1 + (-2837388481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (913447517/5000000000 : ℝ)^73 ≤ (708525236253/6250000000000 : ℝ)^57 := by
    have hnat : (913447517 : ℕ)^73*6250000000000^57 ≤ 708525236253^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      913447517 5000000000 708525236253 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (614303351/1250000000 : ℝ)^73 ≤ (10064883996629/25000000000000 : ℝ)^57 := by
    have hnat : (614303351 : ℕ)^73*25000000000000^57 ≤ 10064883996629^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      614303351 1250000000 10064883996629 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2837388481/5000000000 : ℝ)^73 ≤ (3025253763827/6250000000000 : ℝ)^57 := by
    have hnat : (2837388481 : ℕ)^73*6250000000000^57 ≤ 3025253763827^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2837388481 5000000000 3025253763827 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-913447517/5000000000 : ℝ), (614303351/1250000000 : ℝ), (-2837388481/5000000000 : ℝ)] ![(708525236253/6250000000000 : ℝ), (10064883996629/25000000000000 : ℝ), (3025253763827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-913447517/5000000000 : ℝ)|^73 ≤ (708525236253/6250000000000 : ℝ)^57
        have hw : |(-913447517/5000000000 : ℝ)|=(913447517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(614303351/1250000000 : ℝ)|^73 ≤ (10064883996629/25000000000000 : ℝ)^57
        have hw : |(614303351/1250000000 : ℝ)|=(614303351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2837388481/5000000000 : ℝ)|^73 ≤ (3025253763827/6250000000000 : ℝ)^57
        have hw : |(-2837388481/5000000000 : ℝ)|=(2837388481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5121503919/10000000000 : ℝ)*x 0 + (1024837557/2000000000 : ℝ)*x 1 + (2283068983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5121503919/10000000000 : ℝ)^73 ≤ (10611209502187/25000000000000 : ℝ)^57 := by
    have hnat : (5121503919 : ℕ)^73*25000000000000^57 ≤ 10611209502187^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121503919 10000000000 10611209502187 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1024837557/2000000000 : ℝ)^73 ≤ (42473326414153/100000000000000 : ℝ)^57 := by
    have hnat : (1024837557 : ℕ)^73*100000000000000^57 ≤ 42473326414153^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024837557 2000000000 42473326414153 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2283068983/10000000000 : ℝ)^73 ≤ (15081835561277/100000000000000 : ℝ)^57 := by
    have hnat : (2283068983 : ℕ)^73*100000000000000^57 ≤ 15081835561277^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2283068983 10000000000 15081835561277 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5121503919/10000000000 : ℝ), (1024837557/2000000000 : ℝ), (2283068983/10000000000 : ℝ)] ![(10611209502187/25000000000000 : ℝ), (42473326414153/100000000000000 : ℝ), (15081835561277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5121503919/10000000000 : ℝ)|^73 ≤ (10611209502187/25000000000000 : ℝ)^57
        have hw : |(5121503919/10000000000 : ℝ)|=(5121503919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1024837557/2000000000 : ℝ)|^73 ≤ (42473326414153/100000000000000 : ℝ)^57
        have hw : |(1024837557/2000000000 : ℝ)|=(1024837557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2283068983/10000000000 : ℝ)|^73 ≤ (15081835561277/100000000000000 : ℝ)^57
        have hw : |(2283068983/10000000000 : ℝ)|=(2283068983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1369489119/2500000000 : ℝ)*x 0 + (1094108279/2000000000 : ℝ)*x 1 + (-33255629/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369489119/2500000000 : ℝ)^73 ≤ (1445767224587/3125000000000 : ℝ)^57 := by
    have hnat : (1369489119 : ℕ)^73*3125000000000^57 ≤ 1445767224587^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369489119 2500000000 1445767224587 3125000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094108279/2000000000 : ℝ)^73 ≤ (23092181431319/50000000000000 : ℝ)^57 := by
    have hnat : (1094108279 : ℕ)^73*50000000000000^57 ≤ 23092181431319^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094108279 2000000000 23092181431319 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33255629/250000000 : ℝ)^73 ≤ (943885741707/12500000000000 : ℝ)^57 := by
    have hnat : (33255629 : ℕ)^73*12500000000000^57 ≤ 943885741707^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33255629 250000000 943885741707 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1369489119/2500000000 : ℝ), (1094108279/2000000000 : ℝ), (-33255629/250000000 : ℝ)] ![(1445767224587/3125000000000 : ℝ), (23092181431319/50000000000000 : ℝ), (943885741707/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1369489119/2500000000 : ℝ)|^73 ≤ (1445767224587/3125000000000 : ℝ)^57
        have hw : |(1369489119/2500000000 : ℝ)|=(1369489119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094108279/2000000000 : ℝ)|^73 ≤ (23092181431319/50000000000000 : ℝ)^57
        have hw : |(1094108279/2000000000 : ℝ)|=(1094108279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-33255629/250000000 : ℝ)|^73 ≤ (943885741707/12500000000000 : ℝ)^57
        have hw : |(-33255629/250000000 : ℝ)|=(33255629/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-22333449/156250000 : ℝ)*x 0 + (4384525269/10000000000 : ℝ)*x 1 + (-3220787207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (22333449/156250000 : ℝ)^73 ≤ (8279057520921/100000000000000 : ℝ)^57 := by
    have hnat : (22333449 : ℕ)^73*100000000000000^57 ≤ 8279057520921^57*156250000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22333449 156250000 8279057520921 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4384525269/10000000000 : ℝ)^73 ≤ (34786410422553/100000000000000 : ℝ)^57 := by
    have hnat : (4384525269 : ℕ)^73*100000000000000^57 ≤ 34786410422553^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384525269 10000000000 34786410422553 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3220787207/5000000000 : ℝ)^73 ≤ (14233633009403/25000000000000 : ℝ)^57 := by
    have hnat : (3220787207 : ℕ)^73*25000000000000^57 ≤ 14233633009403^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220787207 5000000000 14233633009403 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-22333449/156250000 : ℝ), (4384525269/10000000000 : ℝ), (-3220787207/5000000000 : ℝ)] ![(8279057520921/100000000000000 : ℝ), (34786410422553/100000000000000 : ℝ), (14233633009403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-22333449/156250000 : ℝ)|^73 ≤ (8279057520921/100000000000000 : ℝ)^57
        have hw : |(-22333449/156250000 : ℝ)|=(22333449/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4384525269/10000000000 : ℝ)|^73 ≤ (34786410422553/100000000000000 : ℝ)^57
        have hw : |(4384525269/10000000000 : ℝ)|=(4384525269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3220787207/5000000000 : ℝ)|^73 ≤ (14233633009403/25000000000000 : ℝ)^57
        have hw : |(-3220787207/5000000000 : ℝ)|=(3220787207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2429778389/5000000000 : ℝ)*x 0 + (-561928069/5000000000 : ℝ)*x 1 + (-1550356017/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2429778389/5000000000 : ℝ)^73 ≤ (39684763228881/100000000000000 : ℝ)^57 := by
    have hnat : (2429778389 : ℕ)^73*100000000000000^57 ≤ 39684763228881^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429778389 5000000000 39684763228881 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561928069/5000000000 : ℝ)^73 ≤ (608476144221/10000000000000 : ℝ)^57 := by
    have hnat : (561928069 : ℕ)^73*10000000000000^57 ≤ 608476144221^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561928069 5000000000 608476144221 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1550356017/2500000000 : ℝ)^73 ≤ (27115237657259/50000000000000 : ℝ)^57 := by
    have hnat : (1550356017 : ℕ)^73*50000000000000^57 ≤ 27115237657259^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550356017 2500000000 27115237657259 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2429778389/5000000000 : ℝ), (-561928069/5000000000 : ℝ), (-1550356017/2500000000 : ℝ)] ![(39684763228881/100000000000000 : ℝ), (608476144221/10000000000000 : ℝ), (27115237657259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2429778389/5000000000 : ℝ)|^73 ≤ (39684763228881/100000000000000 : ℝ)^57
        have hw : |(2429778389/5000000000 : ℝ)|=(2429778389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561928069/5000000000 : ℝ)|^73 ≤ (608476144221/10000000000000 : ℝ)^57
        have hw : |(-561928069/5000000000 : ℝ)|=(561928069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1550356017/2500000000 : ℝ)|^73 ≤ (27115237657259/50000000000000 : ℝ)^57
        have hw : |(-1550356017/2500000000 : ℝ)|=(1550356017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2411980477/5000000000 : ℝ)*x 0 + (9779129/16000000 : ℝ)*x 1 + (329303687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2411980477/5000000000 : ℝ)^73 ≤ (9828215697441/25000000000000 : ℝ)^57 := by
    have hnat : (2411980477 : ℕ)^73*25000000000000^57 ≤ 9828215697441^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411980477 5000000000 9828215697441 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (9779129/16000000 : ℝ)^73 ≤ (13307626586431/25000000000000 : ℝ)^57 := by
    have hnat : (9779129 : ℕ)^73*25000000000000^57 ≤ 13307626586431^57*16000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9779129 16000000 13307626586431 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329303687/2500000000 : ℝ)^73 ≤ (932078856441/12500000000000 : ℝ)^57 := by
    have hnat : (329303687 : ℕ)^73*12500000000000^57 ≤ 932078856441^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329303687 2500000000 932078856441 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2411980477/5000000000 : ℝ), (9779129/16000000 : ℝ), (329303687/2500000000 : ℝ)] ![(9828215697441/25000000000000 : ℝ), (13307626586431/25000000000000 : ℝ), (932078856441/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2411980477/5000000000 : ℝ)|^73 ≤ (9828215697441/25000000000000 : ℝ)^57
        have hw : |(2411980477/5000000000 : ℝ)|=(2411980477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(9779129/16000000 : ℝ)|^73 ≤ (13307626586431/25000000000000 : ℝ)^57
        have hw : |(9779129/16000000 : ℝ)|=(9779129/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329303687/2500000000 : ℝ)|^73 ≤ (932078856441/12500000000000 : ℝ)^57
        have hw : |(329303687/2500000000 : ℝ)|=(329303687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (508867581/1000000000 : ℝ)*x 0 + (6211228973/10000000000 : ℝ)*x 1 + (-147997179/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (508867581/1000000000 : ℝ)^73 ≤ (10524179344889/25000000000000 : ℝ)^57 := by
    have hnat : (508867581 : ℕ)^73*25000000000000^57 ≤ 10524179344889^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508867581 1000000000 10524179344889 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6211228973/10000000000 : ℝ)^73 ≤ (2717015502393/5000000000000 : ℝ)^57 := by
    have hnat : (6211228973 : ℕ)^73*5000000000000^57 ≤ 2717015502393^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6211228973 10000000000 2717015502393 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147997179/2000000000 : ℝ)^73 ≤ (3562972561851/100000000000000 : ℝ)^57 := by
    have hnat : (147997179 : ℕ)^73*100000000000000^57 ≤ 3562972561851^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147997179 2000000000 3562972561851 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(508867581/1000000000 : ℝ), (6211228973/10000000000 : ℝ), (-147997179/2000000000 : ℝ)] ![(10524179344889/25000000000000 : ℝ), (2717015502393/5000000000000 : ℝ), (3562972561851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(508867581/1000000000 : ℝ)|^73 ≤ (10524179344889/25000000000000 : ℝ)^57
        have hw : |(508867581/1000000000 : ℝ)|=(508867581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6211228973/10000000000 : ℝ)|^73 ≤ (2717015502393/5000000000000 : ℝ)^57
        have hw : |(6211228973/10000000000 : ℝ)|=(6211228973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147997179/2000000000 : ℝ)|^73 ≤ (3562972561851/100000000000000 : ℝ)^57
        have hw : |(-147997179/2000000000 : ℝ)|=(147997179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1018000311/10000000000 : ℝ)*x 0 + (474445083/1000000000 : ℝ)*x 1 + (-637254903/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1018000311/10000000000 : ℝ)^73 ≤ (2680346944129/50000000000000 : ℝ)^57 := by
    have hnat : (1018000311 : ℕ)^73*50000000000000^57 ≤ 2680346944129^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018000311 10000000000 2680346944129 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474445083/1000000000 : ℝ)^73 ≤ (3848493684473/10000000000000 : ℝ)^57 := by
    have hnat : (474445083 : ℕ)^73*10000000000000^57 ≤ 3848493684473^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474445083 1000000000 3848493684473 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (637254903/1000000000 : ℝ)^73 ≤ (28077184628071/50000000000000 : ℝ)^57 := by
    have hnat : (637254903 : ℕ)^73*50000000000000^57 ≤ 28077184628071^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      637254903 1000000000 28077184628071 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1018000311/10000000000 : ℝ), (474445083/1000000000 : ℝ), (-637254903/1000000000 : ℝ)] ![(2680346944129/50000000000000 : ℝ), (3848493684473/10000000000000 : ℝ), (28077184628071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1018000311/10000000000 : ℝ)|^73 ≤ (2680346944129/50000000000000 : ℝ)^57
        have hw : |(-1018000311/10000000000 : ℝ)|=(1018000311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(474445083/1000000000 : ℝ)|^73 ≤ (3848493684473/10000000000000 : ℝ)^57
        have hw : |(474445083/1000000000 : ℝ)|=(474445083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-637254903/1000000000 : ℝ)|^73 ≤ (28077184628071/50000000000000 : ℝ)^57
        have hw : |(-637254903/1000000000 : ℝ)|=(637254903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2257769599/5000000000 : ℝ)*x 0 + (-1551122129/10000000000 : ℝ)*x 1 + (-6241862707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257769599/5000000000 : ℝ)^73 ≤ (144492728327/400000000000 : ℝ)^57 := by
    have hnat : (2257769599 : ℕ)^73*400000000000^57 ≤ 144492728327^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257769599 5000000000 144492728327 400000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551122129/10000000000 : ℝ)^73 ≤ (9193034802479/100000000000000 : ℝ)^57 := by
    have hnat : (1551122129 : ℕ)^73*100000000000000^57 ≤ 9193034802479^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551122129 10000000000 9193034802479 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6241862707/10000000000 : ℝ)^73 ≤ (27341891553503/50000000000000 : ℝ)^57 := by
    have hnat : (6241862707 : ℕ)^73*50000000000000^57 ≤ 27341891553503^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6241862707 10000000000 27341891553503 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257769599/5000000000 : ℝ), (-1551122129/10000000000 : ℝ), (-6241862707/10000000000 : ℝ)] ![(144492728327/400000000000 : ℝ), (9193034802479/100000000000000 : ℝ), (27341891553503/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257769599/5000000000 : ℝ)|^73 ≤ (144492728327/400000000000 : ℝ)^57
        have hw : |(2257769599/5000000000 : ℝ)|=(2257769599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1551122129/10000000000 : ℝ)|^73 ≤ (9193034802479/100000000000000 : ℝ)^57
        have hw : |(-1551122129/10000000000 : ℝ)|=(1551122129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6241862707/10000000000 : ℝ)|^73 ≤ (27341891553503/50000000000000 : ℝ)^57
        have hw : |(-6241862707/10000000000 : ℝ)|=(6241862707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2985383883/5000000000 : ℝ)*x 0 + (619428887/1250000000 : ℝ)*x 1 + (1343663329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2985383883/5000000000 : ℝ)^73 ≤ (413286714811/800000000000 : ℝ)^57 := by
    have hnat : (2985383883 : ℕ)^73*800000000000^57 ≤ 413286714811^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2985383883 5000000000 413286714811 800000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (619428887/1250000000 : ℝ)^73 ≤ (40690241507899/100000000000000 : ℝ)^57 := by
    have hnat : (619428887 : ℕ)^73*100000000000000^57 ≤ 40690241507899^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619428887 1250000000 40690241507899 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343663329/10000000000 : ℝ)^73 ≤ (7648919121019/100000000000000 : ℝ)^57 := by
    have hnat : (1343663329 : ℕ)^73*100000000000000^57 ≤ 7648919121019^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343663329 10000000000 7648919121019 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2985383883/5000000000 : ℝ), (619428887/1250000000 : ℝ), (1343663329/10000000000 : ℝ)] ![(413286714811/800000000000 : ℝ), (40690241507899/100000000000000 : ℝ), (7648919121019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2985383883/5000000000 : ℝ)|^73 ≤ (413286714811/800000000000 : ℝ)^57
        have hw : |(2985383883/5000000000 : ℝ)|=(2985383883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(619428887/1250000000 : ℝ)|^73 ≤ (40690241507899/100000000000000 : ℝ)^57
        have hw : |(619428887/1250000000 : ℝ)|=(619428887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343663329/10000000000 : ℝ)|^73 ≤ (7648919121019/100000000000000 : ℝ)^57
        have hw : |(1343663329/10000000000 : ℝ)|=(1343663329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3241269603/5000000000 : ℝ)*x 0 + (4794676491/10000000000 : ℝ)*x 1 + (-186247907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3241269603/5000000000 : ℝ)^73 ≤ (57398651044861/100000000000000 : ℝ)^57 := by
    have hnat : (3241269603 : ℕ)^73*100000000000000^57 ≤ 57398651044861^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3241269603 5000000000 57398651044861 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4794676491/10000000000 : ℝ)^73 ≤ (39007479386259/100000000000000 : ℝ)^57 := by
    have hnat : (4794676491 : ℕ)^73*100000000000000^57 ≤ 39007479386259^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794676491 10000000000 39007479386259 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186247907/2500000000 : ℝ)^73 ≤ (3593869553027/100000000000000 : ℝ)^57 := by
    have hnat : (186247907 : ℕ)^73*100000000000000^57 ≤ 3593869553027^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186247907 2500000000 3593869553027 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3241269603/5000000000 : ℝ), (4794676491/10000000000 : ℝ), (-186247907/2500000000 : ℝ)] ![(57398651044861/100000000000000 : ℝ), (39007479386259/100000000000000 : ℝ), (3593869553027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3241269603/5000000000 : ℝ)|^73 ≤ (57398651044861/100000000000000 : ℝ)^57
        have hw : |(3241269603/5000000000 : ℝ)|=(3241269603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4794676491/10000000000 : ℝ)|^73 ≤ (39007479386259/100000000000000 : ℝ)^57
        have hw : |(4794676491/10000000000 : ℝ)|=(4794676491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-186247907/2500000000 : ℝ)|^73 ≤ (3593869553027/100000000000000 : ℝ)^57
        have hw : |(-186247907/2500000000 : ℝ)|=(186247907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-188768937/2500000000 : ℝ)*x 0 + (5359365181/10000000000 : ℝ)*x 1 + (-297170841/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (188768937/2500000000 : ℝ)^73 ≤ (914072200817/25000000000000 : ℝ)^57 := by
    have hnat : (188768937 : ℕ)^73*25000000000000^57 ≤ 914072200817^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188768937 2500000000 914072200817 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5359365181/10000000000 : ℝ)^73 ≤ (44985752815627/100000000000000 : ℝ)^57 := by
    have hnat : (5359365181 : ℕ)^73*100000000000000^57 ≤ 44985752815627^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359365181 10000000000 44985752815627 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (297170841/500000000 : ℝ)^73 ≤ (51357958358083/100000000000000 : ℝ)^57 := by
    have hnat : (297170841 : ℕ)^73*100000000000000^57 ≤ 51357958358083^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297170841 500000000 51357958358083 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-188768937/2500000000 : ℝ), (5359365181/10000000000 : ℝ), (-297170841/500000000 : ℝ)] ![(914072200817/25000000000000 : ℝ), (44985752815627/100000000000000 : ℝ), (51357958358083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-188768937/2500000000 : ℝ)|^73 ≤ (914072200817/25000000000000 : ℝ)^57
        have hw : |(-188768937/2500000000 : ℝ)|=(188768937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5359365181/10000000000 : ℝ)|^73 ≤ (44985752815627/100000000000000 : ℝ)^57
        have hw : |(5359365181/10000000000 : ℝ)|=(5359365181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-297170841/500000000 : ℝ)|^73 ≤ (51357958358083/100000000000000 : ℝ)^57
        have hw : |(-297170841/500000000 : ℝ)|=(297170841/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6027600273/10000000000 : ℝ)*x 0 + (-284756433/2000000000 : ℝ)*x 1 + (-4839078371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6027600273/10000000000 : ℝ)^73 ≤ (26145720119203/50000000000000 : ℝ)^57 := by
    have hnat : (6027600273 : ℕ)^73*50000000000000^57 ≤ 26145720119203^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6027600273 10000000000 26145720119203 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284756433/2000000000 : ℝ)^73 ≤ (8237845969739/100000000000000 : ℝ)^57 := by
    have hnat : (284756433 : ℕ)^73*100000000000000^57 ≤ 8237845969739^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284756433 2000000000 8237845969739 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4839078371/10000000000 : ℝ)^73 ≤ (39470713782041/100000000000000 : ℝ)^57 := by
    have hnat : (4839078371 : ℕ)^73*100000000000000^57 ≤ 39470713782041^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839078371 10000000000 39470713782041 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6027600273/10000000000 : ℝ), (-284756433/2000000000 : ℝ), (-4839078371/10000000000 : ℝ)] ![(26145720119203/50000000000000 : ℝ), (8237845969739/100000000000000 : ℝ), (39470713782041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6027600273/10000000000 : ℝ)|^73 ≤ (26145720119203/50000000000000 : ℝ)^57
        have hw : |(6027600273/10000000000 : ℝ)|=(6027600273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-284756433/2000000000 : ℝ)|^73 ≤ (8237845969739/100000000000000 : ℝ)^57
        have hw : |(-284756433/2000000000 : ℝ)|=(284756433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4839078371/10000000000 : ℝ)|^73 ≤ (39470713782041/100000000000000 : ℝ)^57
        have hw : |(-4839078371/10000000000 : ℝ)|=(4839078371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4656505131/10000000000 : ℝ)*x 0 + (5570345167/10000000000 : ℝ)*x 1 + (1146156739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4656505131/10000000000 : ℝ)^73 ≤ (37573700525729/100000000000000 : ℝ)^57 := by
    have hnat : (4656505131 : ℕ)^73*100000000000000^57 ≤ 37573700525729^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656505131 10000000000 37573700525729 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5570345167/10000000000 : ℝ)^73 ≤ (47266208757153/100000000000000 : ℝ)^57 := by
    have hnat : (5570345167 : ℕ)^73*100000000000000^57 ≤ 47266208757153^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5570345167 10000000000 47266208757153 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1146156739/5000000000 : ℝ)^73 ≤ (3032018139979/20000000000000 : ℝ)^57 := by
    have hnat : (1146156739 : ℕ)^73*20000000000000^57 ≤ 3032018139979^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1146156739 5000000000 3032018139979 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4656505131/10000000000 : ℝ), (5570345167/10000000000 : ℝ), (1146156739/5000000000 : ℝ)] ![(37573700525729/100000000000000 : ℝ), (47266208757153/100000000000000 : ℝ), (3032018139979/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4656505131/10000000000 : ℝ)|^73 ≤ (37573700525729/100000000000000 : ℝ)^57
        have hw : |(4656505131/10000000000 : ℝ)|=(4656505131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5570345167/10000000000 : ℝ)|^73 ≤ (47266208757153/100000000000000 : ℝ)^57
        have hw : |(5570345167/10000000000 : ℝ)|=(5570345167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1146156739/5000000000 : ℝ)|^73 ≤ (3032018139979/20000000000000 : ℝ)^57
        have hw : |(1146156739/5000000000 : ℝ)|=(1146156739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312062_s2_s2_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (414676311/625000000 : ℝ)*x 0 + (2248460881/5000000000 : ℝ)*x 1 + (-190901307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414676311/625000000 : ℝ)^73 ≤ (29565577044531/50000000000000 : ℝ)^57 := by
    have hnat : (414676311 : ℕ)^73*50000000000000^57 ≤ 29565577044531^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414676311 625000000 29565577044531 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248460881/5000000000 : ℝ)^73 ≤ (35932551476869/100000000000000 : ℝ)^57 := by
    have hnat : (2248460881 : ℕ)^73*100000000000000^57 ≤ 35932551476869^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248460881 5000000000 35932551476869 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (190901307/2000000000 : ℝ)^73 ≤ (2468147212181/50000000000000 : ℝ)^57 := by
    have hnat : (190901307 : ℕ)^73*50000000000000^57 ≤ 2468147212181^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190901307 2000000000 2468147212181 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(414676311/625000000 : ℝ), (2248460881/5000000000 : ℝ), (-190901307/2000000000 : ℝ)] ![(29565577044531/50000000000000 : ℝ), (35932551476869/100000000000000 : ℝ), (2468147212181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(414676311/625000000 : ℝ)|^73 ≤ (29565577044531/50000000000000 : ℝ)^57
        have hw : |(414676311/625000000 : ℝ)|=(414676311/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248460881/5000000000 : ℝ)|^73 ≤ (35932551476869/100000000000000 : ℝ)^57
        have hw : |(2248460881/5000000000 : ℝ)|=(2248460881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-190901307/2000000000 : ℝ)|^73 ≤ (2468147212181/50000000000000 : ℝ)^57
        have hw : |(-190901307/2000000000 : ℝ)|=(190901307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312062_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((16573/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16573/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66319/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66319/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25603/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25603/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2421/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2421/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19517/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19517/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25161/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25161/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (16573/25000 : ℝ) ^ (9/2 : ℝ) ≤ (628977397059033277/4000000000000000000 : ℝ) := by
    have hpowers : (16573/25000 : ℝ)^9 ≤ (628977397059033277/4000000000000000000 : ℝ)^2 := by
      have hnat : (16573 : ℕ)^9*4000000000000000000^2 ≤ 628977397059033277^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16573 25000 628977397059033277 4000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16573/25000 : ℝ)) (X := (628977397059033277/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0a : (4628977397059033277/4000000000000000000 : ℝ) ≤ (10329860574404081/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (4628977397059033277/4000000000000000000 : ℝ)^2 ≤ (10329860574404081/10000000000000000 : ℝ)^9 := by
      have hnat : (4628977397059033277 : ℕ)^2*10000000000000000^9 ≤ 10329860574404081^9*4000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4628977397059033277 4000000000000000000 10329860574404081 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10329860574404081/10000000000000000 : ℝ)) (X := (4628977397059033277/4000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0b : (2628977397059033277/2000000000000000000 : ℝ) ≤ (10626504062053953/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2628977397059033277/2000000000000000000 : ℝ)^2 ≤ (10626504062053953/10000000000000000 : ℝ)^9 := by
      have hnat : (2628977397059033277 : ℕ)^2*10000000000000000^9 ≤ 10626504062053953^9*2000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2628977397059033277 2000000000000000000 10626504062053953 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10626504062053953/10000000000000000 : ℝ)) (X := (2628977397059033277/2000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(329860574404081/6629200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(18540217978117/414325000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (16573/25000 : ℝ)) (alpha := (329860574404081/6629200000000000 : ℝ)) (beta := (18540217978117/414325000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16573/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(329860574404081/6629200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(18540217978117/414325000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (66319/100000 : ℝ) ^ (9/2 : ℝ) ≤ (3938318806133947027/25000000000000000000 : ℝ) := by
    have hpowers : (66319/100000 : ℝ)^9 ≤ (3938318806133947027/25000000000000000000 : ℝ)^2 := by
      have hnat : (66319 : ℕ)^9*25000000000000000000^2 ≤ 3938318806133947027^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66319 100000 3938318806133947027 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66319/100000 : ℝ)) (X := (3938318806133947027/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1a : (28938318806133947027/25000000000000000000 : ℝ) ≤ (2582608149694749/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (28938318806133947027/25000000000000000000 : ℝ)^2 ≤ (2582608149694749/2500000000000000 : ℝ)^9 := by
      have hnat : (28938318806133947027 : ℕ)^2*2500000000000000^9 ≤ 2582608149694749^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28938318806133947027 25000000000000000000 2582608149694749 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2582608149694749/2500000000000000 : ℝ)) (X := (28938318806133947027/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1b : (16438318806133947027/12500000000000000000 : ℝ) ≤ (10627540102438163/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (16438318806133947027/12500000000000000000 : ℝ)^2 ≤ (10627540102438163/10000000000000000 : ℝ)^9 := by
      have hnat : (16438318806133947027 : ℕ)^2*10000000000000000^9 ≤ 10627540102438163^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16438318806133947027 12500000000000000000 10627540102438163 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10627540102438163/10000000000000000 : ℝ)) (X := (16438318806133947027/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(82608149694749/1657975000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(297107503659167/6631900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (66319/100000 : ℝ)) (alpha := (82608149694749/1657975000000000 : ℝ)) (beta := (297107503659167/6631900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (66319/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(82608149694749/1657975000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(297107503659167/6631900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (25603/50000 : ℝ) ^ (9/2 : ℝ) ≤ (4919759051829606261/100000000000000000000 : ℝ) := by
    have hpowers : (25603/50000 : ℝ)^9 ≤ (4919759051829606261/100000000000000000000 : ℝ)^2 := by
      have hnat : (25603 : ℕ)^9*100000000000000000000^2 ≤ 4919759051829606261^2*50000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25603 50000 4919759051829606261 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25603/50000 : ℝ)) (X := (4919759051829606261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2a : (104919759051829606261/100000000000000000000 : ℝ) ≤ (631705952853927/625000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (104919759051829606261/100000000000000000000 : ℝ)^2 ≤ (631705952853927/625000000000000 : ℝ)^9 := by
      have hnat : (104919759051829606261 : ℕ)^2*625000000000000^9 ≤ 631705952853927^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104919759051829606261 100000000000000000000 631705952853927 625000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631705952853927/625000000000000 : ℝ)) (X := (104919759051829606261/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2b : (54919759051829606261/50000000000000000000 : ℝ) ≤ (10210745951432783/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (54919759051829606261/50000000000000000000 : ℝ)^2 ≤ (10210745951432783/10000000000000000 : ℝ)^9 := by
      have hnat : (54919759051829606261 : ℕ)^2*10000000000000000^9 ≤ 10210745951432783^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54919759051829606261 50000000000000000000 10210745951432783 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10210745951432783/10000000000000000 : ℝ)) (X := (54919759051829606261/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(6705952853927/320037500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(103450705769951/5120600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (25603/50000 : ℝ)) (alpha := (6705952853927/320037500000000 : ℝ)) (beta := (103450705769951/5120600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (25603/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(6705952853927/320037500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(103450705769951/5120600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-913447517/5000000000 : ℝ)*X 0 0+(614303351/1250000000 : ℝ)*X 0 1+(-2837388481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5121503919/10000000000 : ℝ)*X 2 0+(1024837557/2000000000 : ℝ)*X 2 1+(2283068983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((1369489119/2500000000 : ℝ)*X 0 0+(1094108279/2000000000 : ℝ)*X 0 1+(-33255629/250000000 : ℝ)*X 0 2+(1369489119/2500000000 : ℝ)*X 1 0+(1094108279/2000000000 : ℝ)*X 1 1+(-33255629/250000000 : ℝ)*X 1 2+(1369489119/2500000000 : ℝ)*X 2 0+(1094108279/2000000000 : ℝ)*X 2 1+(-33255629/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-22333449/156250000 : ℝ)*X 0 0+(4384525269/10000000000 : ℝ)*X 0 1+(-3220787207/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2429778389/5000000000 : ℝ)*X 1 0+(-561928069/5000000000 : ℝ)*X 1 1+(-1550356017/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2411980477/5000000000 : ℝ)*X 2 0+(9779129/16000000 : ℝ)*X 2 1+(329303687/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((508867581/1000000000 : ℝ)*X 0 0+(6211228973/10000000000 : ℝ)*X 0 1+(-147997179/2000000000 : ℝ)*X 0 2+(508867581/1000000000 : ℝ)*X 1 0+(6211228973/10000000000 : ℝ)*X 1 1+(-147997179/2000000000 : ℝ)*X 1 2+(508867581/1000000000 : ℝ)*X 2 0+(6211228973/10000000000 : ℝ)*X 2 1+(-147997179/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1018000311/10000000000 : ℝ)*X 0 0+(474445083/1000000000 : ℝ)*X 0 1+(-637254903/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2257769599/5000000000 : ℝ)*X 1 0+(-1551122129/10000000000 : ℝ)*X 1 1+(-6241862707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2985383883/5000000000 : ℝ)*X 2 0+(619428887/1250000000 : ℝ)*X 2 1+(1343663329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3241269603/5000000000 : ℝ)*X 0 0+(4794676491/10000000000 : ℝ)*X 0 1+(-186247907/2500000000 : ℝ)*X 0 2+(3241269603/5000000000 : ℝ)*X 1 0+(4794676491/10000000000 : ℝ)*X 1 1+(-186247907/2500000000 : ℝ)*X 1 2+(3241269603/5000000000 : ℝ)*X 2 0+(4794676491/10000000000 : ℝ)*X 2 1+(-186247907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-188768937/2500000000 : ℝ)*X 0 0+(5359365181/10000000000 : ℝ)*X 0 1+(-297170841/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6027600273/10000000000 : ℝ)*X 1 0+(-284756433/2000000000 : ℝ)*X 1 1+(-4839078371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4656505131/10000000000 : ℝ)*X 2 0+(5570345167/10000000000 : ℝ)*X 2 1+(1146156739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((414676311/625000000 : ℝ)*X 0 0+(2248460881/5000000000 : ℝ)*X 0 1+(-190901307/2000000000 : ℝ)*X 0 2+(414676311/625000000 : ℝ)*X 1 0+(2248460881/5000000000 : ℝ)*X 1 1+(-190901307/2000000000 : ℝ)*X 1 2+(414676311/625000000 : ℝ)*X 2 0+(2248460881/5000000000 : ℝ)*X 2 1+(-190901307/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((2421/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2421/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20194375017915788128973938288527/1407018993078050000000000000000000000 : ℝ) := by norm_num
    linear_combination (236144667463/1000000000000 : ℝ)*(base39) + (23736643177/500000000000 : ℝ)*(base49) + (189590927953/1000000000000 : ℝ)*(base60) + (699974351159/125000000000 : ℝ)*(major_s2_0) + (699974351159/125000000000 : ℝ)*(major_s2_1) + (699974351159/125000000000 : ℝ)*(major_s2_2) + (96968511/1000000000000 : ℝ)*(sp_s2_0) + (3922283295643/500000000000 : ℝ)*(sp_s2_7) + (7844447310821/1000000000000 : ℝ)*(sp_s2_8) + (3922255145269/500000000000 : ℝ)*(sp_s2_9) + (838729579073/250000000000 : ℝ)*(sp_s2_13) + (2958253/1000000000000 : ℝ)*(sp_s2_14) + (219207229/1000000000000 : ℝ)*(sp_s2_15) + (156227511/1000000000000 : ℝ)*(sp_s2_23) + (838729579073/250000000000 : ℝ)*(f.failure) + (156893330361/20000000000 : ℝ)*(f.sum) + (30165831116255645383/84898267850000000000000000000000 : ℝ)*base62 + (17788706004249/640075000000000000000000000 : ℝ)*base65 + (32703311535721/414493750000000000000000000 : ℝ)*base66 + (7131853152491/20002343750000000000000000 : ℝ)*base68 + (10675774956401171/1325995371875000000000000000000 : ℝ)*base71 + (151688879464937/828650000000000000000000000 : ℝ)*base72 + (1122797739638221/3315950000000000000000000000 : ℝ)*base75 + (18243833342549/51790625000000000000000000 : ℝ)*base77 + (5587273571611417291/27477619675000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (11649/25000000000000000 : ℝ)*base87 + (11649/25000000000000000 : ℝ)*base89 + (11649/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19517/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19517/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (53185712646711550919110678312977/2814037986156100000000000000000000000 : ℝ) := by norm_num
    linear_combination (8275880843/40000000000 : ℝ)*(base39) + (101978954723/1000000000000 : ℝ)*(base49) + (1805799/500000000000 : ℝ)*(base60) + (5714633918513/1000000000000 : ℝ)*(major_s2_0) + (5714633918513/1000000000000 : ℝ)*(major_s2_1) + (5714633918513/1000000000000 : ℝ)*(major_s2_2) + (2038049/62500000000 : ℝ)*(sp_s2_2) + (10347453/125000000000 : ℝ)*(sp_s2_7) + (71461849/1000000000000 : ℝ)*(sp_s2_8) + (4002729332269/500000000000 : ℝ)*(sp_s2_14) + (4002734991157/500000000000 : ℝ)*(sp_s2_15) + (8005508835379/1000000000000 : ℝ)*(sp_s2_16) + (85586596337/25000000000 : ℝ)*(sp_s2_20) + (256239331/1000000000000 : ℝ)*(sp_s2_27) + (3423720092811/1000000000000 : ℝ)*(f.failure) + (8005541444163/1000000000000 : ℝ)*(f.sum) + (4312344007671701999/10612283481250000000000000000000 : ℝ)*base62 + (409048020708983/5120600000000000000000000000 : ℝ)*base65 + (100795377798139/6631900000000000000000000000 : ℝ)*base66 + (511907955098623/640075000000000000000000000 : ℝ)*base68 + (21381478103854230617/169727407600000000000000000000000 : ℝ)*base71 + (631430148725617/828650000000000000000000000 : ℝ)*base73 + (523639786297099/828987500000000000000000000 : ℝ)*base74 + (3993015151988367/6629200000000000000000000000 : ℝ)*base76 + (21731052959702660219/109910478700000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (62443/100000000000000000 : ℝ)*base87 + (62443/100000000000000000 : ℝ)*base89 + (62443/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25161/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25161/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10387747790951269824812498380497/2814037986156100000000000000000000000 : ℝ) := by norm_num
    linear_combination (1430441/500000000000 : ℝ)*(base11) + (186216153269/250000000000 : ℝ)*(base39) + (444371291/10000000000 : ℝ)*(base49) + (2262999345111/500000000000 : ℝ)*(major_s2_0) + (2262999345111/500000000000 : ℝ)*(major_s2_1) + (2262999345111/500000000000 : ℝ)*(major_s2_2) + (11122787/1000000000000 : ℝ)*(sp_s2_0) + (569/40000000000 : ℝ)*(sp_s2_6) + (7995857/500000000000 : ℝ)*(sp_s2_9) + (1548673/1000000000000 : ℝ)*(sp_s2_20) + (6340390684379/1000000000000 : ℝ)*(sp_s2_21) + (396275291753/62500000000 : ℝ)*(sp_s2_22) + (3170194338167/500000000000 : ℝ)*(sp_s2_23) + (1355794959513/500000000000 : ℝ)*(sp_s2_27) + (2711591481923/1000000000000 : ℝ)*(f.failure) + (396275291753/62500000000 : ℝ)*(f.sum) + (11020073882486635707/21224566962500000000000000000000 : ℝ)*base62 + (1416414565909189/2560300000000000000000000000 : ℝ)*base64 + (1647639721840197/3315950000000000000000000000 : ℝ)*base67 + (443244960382547/640075000000000000000000000 : ℝ)*base68 + (43119489586537207321/84863703800000000000000000000000 : ℝ)*base70 + (9212748491961/414325000000000000000000000 : ℝ)*base72 + (631359922393681/828987500000000000000000000 : ℝ)*base74 + (2153182708952689/3314600000000000000000000000 : ℝ)*base76 + (2695416771520365837/54955239350000000000000000000000 : ℝ)*base78 + (13699/100000000000000000 : ℝ)*base87 + (13699/100000000000000000 : ℝ)*base89 + (13699/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((16573/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16573/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66319/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66319/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25603/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25603/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2421/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2421/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19517/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(19517/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-25161/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-25161/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312062_s2 p hpa hpb X hX hprev1

#print axioms solution
