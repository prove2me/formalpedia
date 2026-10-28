-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302061_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:24:23.577554+00:00
-- url     : https://prove2.me/submissions/35d7caa1-efe5-430b-96a5-b87756f35bca

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
theorem collision_support_c302061_s7_s7_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-134496937/500000000 : ℝ)*x 0 + (2286557623/5000000000 : ℝ)*x 1 + (5642044291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134496937/500000000 : ℝ)^131 ≤ (3519222235769/20000000000000 : ℝ)^99 := by
    have hnat : (134496937 : ℕ)^131*20000000000000^99 ≤ 3519222235769^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134496937 500000000 3519222235769 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2286557623/5000000000 : ℝ)^131 ≤ (8878134851499/25000000000000 : ℝ)^99 := by
    have hnat : (2286557623 : ℕ)^131*25000000000000^99 ≤ 8878134851499^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286557623 5000000000 8878134851499 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5642044291/10000000000 : ℝ)^131 ≤ (46891349398833/100000000000000 : ℝ)^99 := by
    have hnat : (5642044291 : ℕ)^131*100000000000000^99 ≤ 46891349398833^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5642044291 10000000000 46891349398833 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-134496937/500000000 : ℝ), (2286557623/5000000000 : ℝ), (5642044291/10000000000 : ℝ)] ![(3519222235769/20000000000000 : ℝ), (8878134851499/25000000000000 : ℝ), (46891349398833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-134496937/500000000 : ℝ)|^131 ≤ (3519222235769/20000000000000 : ℝ)^99
        have hw : |(-134496937/500000000 : ℝ)|=(134496937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2286557623/5000000000 : ℝ)|^131 ≤ (8878134851499/25000000000000 : ℝ)^99
        have hw : |(2286557623/5000000000 : ℝ)|=(2286557623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5642044291/10000000000 : ℝ)|^131 ≤ (46891349398833/100000000000000 : ℝ)^99
        have hw : |(5642044291/10000000000 : ℝ)|=(5642044291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_1 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2359975213/5000000000 : ℝ)*x 0 + (-1367535101/5000000000 : ℝ)*x 1 + (1093529089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2359975213/5000000000 : ℝ)^131 ≤ (18514563684103/50000000000000 : ℝ)^99 := by
    have hnat : (2359975213 : ℕ)^131*50000000000000^99 ≤ 18514563684103^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2359975213 5000000000 18514563684103 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367535101/5000000000 : ℝ)^131 ≤ (17987818262877/100000000000000 : ℝ)^99 := by
    have hnat : (1367535101 : ℕ)^131*100000000000000^99 ≤ 17987818262877^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367535101 5000000000 17987818262877 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093529089/2000000000 : ℝ)^131 ≤ (4498305435601/10000000000000 : ℝ)^99 := by
    have hnat : (1093529089 : ℕ)^131*10000000000000^99 ≤ 4498305435601^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093529089 2000000000 4498305435601 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2359975213/5000000000 : ℝ), (-1367535101/5000000000 : ℝ), (1093529089/2000000000 : ℝ)] ![(18514563684103/50000000000000 : ℝ), (17987818262877/100000000000000 : ℝ), (4498305435601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2359975213/5000000000 : ℝ)|^131 ≤ (18514563684103/50000000000000 : ℝ)^99
        have hw : |(2359975213/5000000000 : ℝ)|=(2359975213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1367535101/5000000000 : ℝ)|^131 ≤ (17987818262877/100000000000000 : ℝ)^99
        have hw : |(-1367535101/5000000000 : ℝ)|=(1367535101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093529089/2000000000 : ℝ)|^131 ≤ (4498305435601/10000000000000 : ℝ)^99
        have hw : |(1093529089/2000000000 : ℝ)|=(1093529089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2371895693/5000000000 : ℝ)*x 0 + (6036209893/10000000000 : ℝ)*x 1 + (-242991773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2371895693/5000000000 : ℝ)^131 ≤ (298214590923/800000000000 : ℝ)^99 := by
    have hnat : (2371895693 : ℕ)^131*800000000000^99 ≤ 298214590923^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2371895693 5000000000 298214590923 800000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6036209893/10000000000 : ℝ)^131 ≤ (25637181799163/50000000000000 : ℝ)^99 := by
    have hnat : (6036209893 : ℕ)^131*50000000000000^99 ≤ 25637181799163^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6036209893 10000000000 25637181799163 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (242991773/1250000000 : ℝ)^131 ≤ (286220313207/2500000000000 : ℝ)^99 := by
    have hnat : (242991773 : ℕ)^131*2500000000000^99 ≤ 286220313207^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242991773 1250000000 286220313207 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2371895693/5000000000 : ℝ), (6036209893/10000000000 : ℝ), (-242991773/1250000000 : ℝ)] ![(298214590923/800000000000 : ℝ), (25637181799163/50000000000000 : ℝ), (286220313207/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2371895693/5000000000 : ℝ)|^131 ≤ (298214590923/800000000000 : ℝ)^99
        have hw : |(2371895693/5000000000 : ℝ)|=(2371895693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6036209893/10000000000 : ℝ)|^131 ≤ (25637181799163/50000000000000 : ℝ)^99
        have hw : |(6036209893/10000000000 : ℝ)|=(6036209893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-242991773/1250000000 : ℝ)|^131 ≤ (286220313207/2500000000000 : ℝ)^99
        have hw : |(-242991773/1250000000 : ℝ)|=(242991773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (356618319/625000000 : ℝ)*x 0 + (3342025043/10000000000 : ℝ)*x 1 + (3919278927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356618319/625000000 : ℝ)^131 ≤ (1487337658173/3125000000000 : ℝ)^99 := by
    have hnat : (356618319 : ℕ)^131*3125000000000^99 ≤ 1487337658173^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356618319 625000000 1487337658173 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3342025043/10000000000 : ℝ)^131 ≤ (11725307841301/50000000000000 : ℝ)^99 := by
    have hnat : (3342025043 : ℕ)^131*50000000000000^99 ≤ 11725307841301^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3342025043 10000000000 11725307841301 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3919278927/10000000000 : ℝ)^131 ≤ (5790915850517/20000000000000 : ℝ)^99 := by
    have hnat : (3919278927 : ℕ)^131*20000000000000^99 ≤ 5790915850517^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3919278927 10000000000 5790915850517 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(356618319/625000000 : ℝ), (3342025043/10000000000 : ℝ), (3919278927/10000000000 : ℝ)] ![(1487337658173/3125000000000 : ℝ), (11725307841301/50000000000000 : ℝ), (5790915850517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(356618319/625000000 : ℝ)|^131 ≤ (1487337658173/3125000000000 : ℝ)^99
        have hw : |(356618319/625000000 : ℝ)|=(356618319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3342025043/10000000000 : ℝ)|^131 ≤ (11725307841301/50000000000000 : ℝ)^99
        have hw : |(3342025043/10000000000 : ℝ)|=(3342025043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3919278927/10000000000 : ℝ)|^131 ≤ (5790915850517/20000000000000 : ℝ)^99
        have hw : |(3919278927/10000000000 : ℝ)|=(3919278927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1348282301/5000000000 : ℝ)*x 0 + (2194525771/5000000000 : ℝ)*x 1 + (5806906013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348282301/5000000000 : ℝ)^131 ≤ (3530697311231/20000000000000 : ℝ)^99 := by
    have hnat : (1348282301 : ℕ)^131*20000000000000^99 ≤ 3530697311231^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348282301 5000000000 3530697311231 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194525771/5000000000 : ℝ)^131 ≤ (33633597707831/100000000000000 : ℝ)^99 := by
    have hnat : (2194525771 : ℕ)^131*100000000000000^99 ≤ 33633597707831^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194525771 5000000000 33633597707831 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5806906013/10000000000 : ℝ)^131 ≤ (48712915723007/100000000000000 : ℝ)^99 := by
    have hnat : (5806906013 : ℕ)^131*100000000000000^99 ≤ 48712915723007^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5806906013 10000000000 48712915723007 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1348282301/5000000000 : ℝ), (2194525771/5000000000 : ℝ), (5806906013/10000000000 : ℝ)] ![(3530697311231/20000000000000 : ℝ), (33633597707831/100000000000000 : ℝ), (48712915723007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1348282301/5000000000 : ℝ)|^131 ≤ (3530697311231/20000000000000 : ℝ)^99
        have hw : |(-1348282301/5000000000 : ℝ)|=(1348282301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194525771/5000000000 : ℝ)|^131 ≤ (33633597707831/100000000000000 : ℝ)^99
        have hw : |(2194525771/5000000000 : ℝ)|=(2194525771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5806906013/10000000000 : ℝ)|^131 ≤ (48712915723007/100000000000000 : ℝ)^99
        have hw : |(5806906013/10000000000 : ℝ)|=(5806906013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1153094449/2500000000 : ℝ)*x 0 + (-99037563/400000000 : ℝ)*x 1 + (5771062507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1153094449/2500000000 : ℝ)^131 ≤ (17958271494069/50000000000000 : ℝ)^99 := by
    have hnat : (1153094449 : ℕ)^131*50000000000000^99 ≤ 17958271494069^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153094449 2500000000 17958271494069 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99037563/400000000 : ℝ)^131 ≤ (985501133253/6250000000000 : ℝ)^99 := by
    have hnat : (99037563 : ℕ)^131*6250000000000^99 ≤ 985501133253^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99037563 400000000 985501133253 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5771062507/10000000000 : ℝ)^131 ≤ (188732183079/390625000000 : ℝ)^99 := by
    have hnat : (5771062507 : ℕ)^131*390625000000^99 ≤ 188732183079^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5771062507 10000000000 188732183079 390625000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1153094449/2500000000 : ℝ), (-99037563/400000000 : ℝ), (5771062507/10000000000 : ℝ)] ![(17958271494069/50000000000000 : ℝ), (985501133253/6250000000000 : ℝ), (188732183079/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1153094449/2500000000 : ℝ)|^131 ≤ (17958271494069/50000000000000 : ℝ)^99
        have hw : |(1153094449/2500000000 : ℝ)|=(1153094449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99037563/400000000 : ℝ)|^131 ≤ (985501133253/6250000000000 : ℝ)^99
        have hw : |(-99037563/400000000 : ℝ)|=(99037563/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5771062507/10000000000 : ℝ)|^131 ≤ (188732183079/390625000000 : ℝ)^99
        have hw : |(5771062507/10000000000 : ℝ)|=(5771062507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4636241087/10000000000 : ℝ)*x 0 + (6333317551/10000000000 : ℝ)*x 1 + (-164743427/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4636241087/10000000000 : ℝ)^131 ≤ (36162635647969/100000000000000 : ℝ)^99 := by
    have hnat : (4636241087 : ℕ)^131*100000000000000^99 ≤ 36162635647969^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4636241087 10000000000 36162635647969 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6333317551/10000000000 : ℝ)^131 ≤ (54640174367767/100000000000000 : ℝ)^99 := by
    have hnat : (6333317551 : ℕ)^131*100000000000000^99 ≤ 54640174367767^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6333317551 10000000000 54640174367767 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164743427/1000000000 : ℝ)^131 ≤ (4598594987613/50000000000000 : ℝ)^99 := by
    have hnat : (164743427 : ℕ)^131*50000000000000^99 ≤ 4598594987613^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164743427 1000000000 4598594987613 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4636241087/10000000000 : ℝ), (6333317551/10000000000 : ℝ), (-164743427/1000000000 : ℝ)] ![(36162635647969/100000000000000 : ℝ), (54640174367767/100000000000000 : ℝ), (4598594987613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4636241087/10000000000 : ℝ)|^131 ≤ (36162635647969/100000000000000 : ℝ)^99
        have hw : |(4636241087/10000000000 : ℝ)|=(4636241087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6333317551/10000000000 : ℝ)|^131 ≤ (54640174367767/100000000000000 : ℝ)^99
        have hw : |(6333317551/10000000000 : ℝ)|=(6333317551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-164743427/1000000000 : ℝ)|^131 ≤ (4598594987613/50000000000000 : ℝ)^99
        have hw : |(-164743427/1000000000 : ℝ)|=(164743427/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (714256953/1250000000 : ℝ)*x 0 + (3656475397/10000000000 : ℝ)*x 1 + (450342021/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (714256953/1250000000 : ℝ)^131 ≤ (23842459984907/50000000000000 : ℝ)^99 := by
    have hnat : (714256953 : ℕ)^131*50000000000000^99 ≤ 23842459984907^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714256953 1250000000 23842459984907 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3656475397/10000000000 : ℝ)^131 ≤ (26413769437867/100000000000000 : ℝ)^99 := by
    have hnat : (3656475397 : ℕ)^131*100000000000000^99 ≤ 26413769437867^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3656475397 10000000000 26413769437867 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450342021/1250000000 : ℝ)^131 ≤ (25901310567751/100000000000000 : ℝ)^99 := by
    have hnat : (450342021 : ℕ)^131*100000000000000^99 ≤ 25901310567751^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450342021 1250000000 25901310567751 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(714256953/1250000000 : ℝ), (3656475397/10000000000 : ℝ), (450342021/1250000000 : ℝ)] ![(23842459984907/50000000000000 : ℝ), (26413769437867/100000000000000 : ℝ), (25901310567751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(714256953/1250000000 : ℝ)|^131 ≤ (23842459984907/50000000000000 : ℝ)^99
        have hw : |(714256953/1250000000 : ℝ)|=(714256953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3656475397/10000000000 : ℝ)|^131 ≤ (26413769437867/100000000000000 : ℝ)^99
        have hw : |(3656475397/10000000000 : ℝ)|=(3656475397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450342021/1250000000 : ℝ)|^131 ≤ (25901310567751/100000000000000 : ℝ)^99
        have hw : |(450342021/1250000000 : ℝ)|=(450342021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-577161187/2500000000 : ℝ)*x 0 + (4705262779/10000000000 : ℝ)*x 1 + (5810192923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (577161187/2500000000 : ℝ)^131 ≤ (7186932284441/50000000000000 : ℝ)^99 := by
    have hnat : (577161187 : ℕ)^131*50000000000000^99 ≤ 7186932284441^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      577161187 2500000000 7186932284441 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4705262779/10000000000 : ℝ)^131 ≤ (18438365302441/50000000000000 : ℝ)^99 := by
    have hnat : (4705262779 : ℕ)^131*50000000000000^99 ≤ 18438365302441^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705262779 10000000000 18438365302441 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5810192923/10000000000 : ℝ)^131 ≤ (9749880961457/20000000000000 : ℝ)^99 := by
    have hnat : (5810192923 : ℕ)^131*20000000000000^99 ≤ 9749880961457^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5810192923 10000000000 9749880961457 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-577161187/2500000000 : ℝ), (4705262779/10000000000 : ℝ), (5810192923/10000000000 : ℝ)] ![(7186932284441/50000000000000 : ℝ), (18438365302441/50000000000000 : ℝ), (9749880961457/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-577161187/2500000000 : ℝ)|^131 ≤ (7186932284441/50000000000000 : ℝ)^99
        have hw : |(-577161187/2500000000 : ℝ)|=(577161187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4705262779/10000000000 : ℝ)|^131 ≤ (18438365302441/50000000000000 : ℝ)^99
        have hw : |(4705262779/10000000000 : ℝ)|=(4705262779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5810192923/10000000000 : ℝ)|^131 ≤ (9749880961457/20000000000000 : ℝ)^99
        have hw : |(5810192923/10000000000 : ℝ)|=(5810192923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (224788853/500000000 : ℝ)*x 0 + (-1306200429/5000000000 : ℝ)*x 1 + (2887175503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224788853/500000000 : ℝ)^131 ≤ (34720026276539/100000000000000 : ℝ)^99 := by
    have hnat : (224788853 : ℕ)^131*100000000000000^99 ≤ 34720026276539^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224788853 500000000 34720026276539 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306200429/5000000000 : ℝ)^131 ≤ (3385620216489/20000000000000 : ℝ)^99 := by
    have hnat : (1306200429 : ℕ)^131*20000000000000^99 ≤ 3385620216489^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306200429 5000000000 3385620216489 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2887175503/5000000000 : ℝ)^131 ≤ (48351872624957/100000000000000 : ℝ)^99 := by
    have hnat : (2887175503 : ℕ)^131*100000000000000^99 ≤ 48351872624957^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2887175503 5000000000 48351872624957 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224788853/500000000 : ℝ), (-1306200429/5000000000 : ℝ), (2887175503/5000000000 : ℝ)] ![(34720026276539/100000000000000 : ℝ), (3385620216489/20000000000000 : ℝ), (48351872624957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224788853/500000000 : ℝ)|^131 ≤ (34720026276539/100000000000000 : ℝ)^99
        have hw : |(224788853/500000000 : ℝ)|=(224788853/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1306200429/5000000000 : ℝ)|^131 ≤ (3385620216489/20000000000000 : ℝ)^99
        have hw : |(-1306200429/5000000000 : ℝ)|=(1306200429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2887175503/5000000000 : ℝ)|^131 ≤ (48351872624957/100000000000000 : ℝ)^99
        have hw : |(2887175503/5000000000 : ℝ)|=(2887175503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1283006159/2500000000 : ℝ)*x 0 + (5874170567/10000000000 : ℝ)*x 1 + (-51379627/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1283006159/2500000000 : ℝ)^131 ≤ (646345474661/1562500000000 : ℝ)^99 := by
    have hnat : (1283006159 : ℕ)^131*1562500000000^99 ≤ 646345474661^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283006159 2500000000 646345474661 1562500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5874170567/10000000000 : ℝ)^131 ≤ (49460967852003/100000000000000 : ℝ)^99 := by
    have hnat : (5874170567 : ℕ)^131*100000000000000^99 ≤ 49460967852003^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5874170567 10000000000 49460967852003 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51379627/312500000 : ℝ)^131 ≤ (9172921759209/100000000000000 : ℝ)^99 := by
    have hnat : (51379627 : ℕ)^131*100000000000000^99 ≤ 9172921759209^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51379627 312500000 9172921759209 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1283006159/2500000000 : ℝ), (5874170567/10000000000 : ℝ), (-51379627/312500000 : ℝ)] ![(646345474661/1562500000000 : ℝ), (49460967852003/100000000000000 : ℝ), (9172921759209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1283006159/2500000000 : ℝ)|^131 ≤ (646345474661/1562500000000 : ℝ)^99
        have hw : |(1283006159/2500000000 : ℝ)|=(1283006159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5874170567/10000000000 : ℝ)|^131 ≤ (49460967852003/100000000000000 : ℝ)^99
        have hw : |(5874170567/10000000000 : ℝ)|=(5874170567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51379627/312500000 : ℝ)|^131 ≤ (9172921759209/100000000000000 : ℝ)^99
        have hw : |(-51379627/312500000 : ℝ)|=(51379627/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1539814023/2500000000 : ℝ)*x 0 + (1564795993/5000000000 : ℝ)*x 1 + (1798108003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1539814023/2500000000 : ℝ)^131 ≤ (26330978419581/50000000000000 : ℝ)^99 := by
    have hnat : (1539814023 : ℕ)^131*50000000000000^99 ≤ 26330978419581^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1539814023 2500000000 26330978419581 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564795993/5000000000 : ℝ)^131 ≤ (5374685463731/25000000000000 : ℝ)^99 := by
    have hnat : (1564795993 : ℕ)^131*25000000000000^99 ≤ 5374685463731^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564795993 5000000000 5374685463731 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1798108003/5000000000 : ℝ)^131 ≤ (12919650645209/50000000000000 : ℝ)^99 := by
    have hnat : (1798108003 : ℕ)^131*50000000000000^99 ≤ 12919650645209^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1798108003 5000000000 12919650645209 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1539814023/2500000000 : ℝ), (1564795993/5000000000 : ℝ), (1798108003/5000000000 : ℝ)] ![(26330978419581/50000000000000 : ℝ), (5374685463731/25000000000000 : ℝ), (12919650645209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1539814023/2500000000 : ℝ)|^131 ≤ (26330978419581/50000000000000 : ℝ)^99
        have hw : |(1539814023/2500000000 : ℝ)|=(1539814023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1564795993/5000000000 : ℝ)|^131 ≤ (5374685463731/25000000000000 : ℝ)^99
        have hw : |(1564795993/5000000000 : ℝ)|=(1564795993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1798108003/5000000000 : ℝ)|^131 ≤ (12919650645209/50000000000000 : ℝ)^99
        have hw : |(1798108003/5000000000 : ℝ)|=(1798108003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-116383893/500000000 : ℝ)*x 0 + (2397860159/5000000000 : ℝ)*x 1 + (5711018741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (116383893/500000000 : ℝ)^131 ≤ (14530878991007/100000000000000 : ℝ)^99 := by
    have hnat : (116383893 : ℕ)^131*100000000000000^99 ≤ 14530878991007^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116383893 500000000 14530878991007 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397860159/5000000000 : ℝ)^131 ≤ (3781773333679/10000000000000 : ℝ)^99 := by
    have hnat : (2397860159 : ℕ)^131*10000000000000^99 ≤ 3781773333679^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397860159 5000000000 3781773333679 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5711018741/10000000000 : ℝ)^131 ≤ (47651387661857/100000000000000 : ℝ)^99 := by
    have hnat : (5711018741 : ℕ)^131*100000000000000^99 ≤ 47651387661857^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5711018741 10000000000 47651387661857 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-116383893/500000000 : ℝ), (2397860159/5000000000 : ℝ), (5711018741/10000000000 : ℝ)] ![(14530878991007/100000000000000 : ℝ), (3781773333679/10000000000000 : ℝ), (47651387661857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-116383893/500000000 : ℝ)|^131 ≤ (14530878991007/100000000000000 : ℝ)^99
        have hw : |(-116383893/500000000 : ℝ)|=(116383893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2397860159/5000000000 : ℝ)|^131 ≤ (3781773333679/10000000000000 : ℝ)^99
        have hw : |(2397860159/5000000000 : ℝ)|=(2397860159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5711018741/10000000000 : ℝ)|^131 ≤ (47651387661857/100000000000000 : ℝ)^99
        have hw : |(5711018741/10000000000 : ℝ)|=(5711018741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2544564229/5000000000 : ℝ)*x 0 + (-2375233969/10000000000 : ℝ)*x 1 + (5392405121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2544564229/5000000000 : ℝ)^131 ≤ (40909208999487/100000000000000 : ℝ)^99 := by
    have hnat : (2544564229 : ℕ)^131*100000000000000^99 ≤ 40909208999487^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2544564229 5000000000 40909208999487 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2375233969/10000000000 : ℝ)^131 ≤ (3731251578229/25000000000000 : ℝ)^99 := by
    have hnat : (2375233969 : ℕ)^131*25000000000000^99 ≤ 3731251578229^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375233969 10000000000 3731251578229 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392405121/10000000000 : ℝ)^131 ≤ (11041446170309/25000000000000 : ℝ)^99 := by
    have hnat : (5392405121 : ℕ)^131*25000000000000^99 ≤ 11041446170309^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392405121 10000000000 11041446170309 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2544564229/5000000000 : ℝ), (-2375233969/10000000000 : ℝ), (5392405121/10000000000 : ℝ)] ![(40909208999487/100000000000000 : ℝ), (3731251578229/25000000000000 : ℝ), (11041446170309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2544564229/5000000000 : ℝ)|^131 ≤ (40909208999487/100000000000000 : ℝ)^99
        have hw : |(2544564229/5000000000 : ℝ)|=(2544564229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2375233969/10000000000 : ℝ)|^131 ≤ (3731251578229/25000000000000 : ℝ)^99
        have hw : |(-2375233969/10000000000 : ℝ)|=(2375233969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392405121/10000000000 : ℝ)|^131 ≤ (11041446170309/25000000000000 : ℝ)^99
        have hw : |(5392405121/10000000000 : ℝ)|=(5392405121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (897373541/2000000000 : ℝ)*x 0 + (6302450797/10000000000 : ℝ)*x 1 + (-237099683/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (897373541/2000000000 : ℝ)^131 ≤ (34629010125851/100000000000000 : ℝ)^99 := by
    have hnat : (897373541 : ℕ)^131*100000000000000^99 ≤ 34629010125851^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897373541 2000000000 34629010125851 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6302450797/10000000000 : ℝ)^131 ≤ (27144037485279/50000000000000 : ℝ)^99 := by
    have hnat : (6302450797 : ℕ)^131*50000000000000^99 ≤ 27144037485279^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6302450797 10000000000 27144037485279 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (237099683/1250000000 : ℝ)^131 ≤ (1385364360839/12500000000000 : ℝ)^99 := by
    have hnat : (237099683 : ℕ)^131*12500000000000^99 ≤ 1385364360839^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237099683 1250000000 1385364360839 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(897373541/2000000000 : ℝ), (6302450797/10000000000 : ℝ), (-237099683/1250000000 : ℝ)] ![(34629010125851/100000000000000 : ℝ), (27144037485279/50000000000000 : ℝ), (1385364360839/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(897373541/2000000000 : ℝ)|^131 ≤ (34629010125851/100000000000000 : ℝ)^99
        have hw : |(897373541/2000000000 : ℝ)|=(897373541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6302450797/10000000000 : ℝ)|^131 ≤ (27144037485279/50000000000000 : ℝ)^99
        have hw : |(6302450797/10000000000 : ℝ)|=(6302450797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-237099683/1250000000 : ℝ)|^131 ≤ (1385364360839/12500000000000 : ℝ)^99
        have hw : |(-237099683/1250000000 : ℝ)|=(237099683/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302061_s7_s7_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3112128427/5000000000 : ℝ)*x 0 + (1555424009/5000000000 : ℝ)*x 1 + (3536478063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3112128427/5000000000 : ℝ)^131 ≤ (26699303785971/50000000000000 : ℝ)^99 := by
    have hnat : (3112128427 : ℕ)^131*50000000000000^99 ≤ 26699303785971^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3112128427 5000000000 26699303785971 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1555424009/5000000000 : ℝ)^131 ≤ (21328525296723/100000000000000 : ℝ)^99 := by
    have hnat : (1555424009 : ℕ)^131*100000000000000^99 ≤ 21328525296723^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555424009 5000000000 21328525296723 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3536478063/10000000000 : ℝ)^131 ≤ (25272867114287/100000000000000 : ℝ)^99 := by
    have hnat : (3536478063 : ℕ)^131*100000000000000^99 ≤ 25272867114287^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3536478063 10000000000 25272867114287 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3112128427/5000000000 : ℝ), (1555424009/5000000000 : ℝ), (3536478063/10000000000 : ℝ)] ![(26699303785971/50000000000000 : ℝ), (21328525296723/100000000000000 : ℝ), (25272867114287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3112128427/5000000000 : ℝ)|^131 ≤ (26699303785971/50000000000000 : ℝ)^99
        have hw : |(3112128427/5000000000 : ℝ)|=(3112128427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1555424009/5000000000 : ℝ)|^131 ≤ (21328525296723/100000000000000 : ℝ)^99
        have hw : |(1555424009/5000000000 : ℝ)|=(1555424009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3536478063/10000000000 : ℝ)|^131 ≤ (25272867114287/100000000000000 : ℝ)^99
        have hw : |(3536478063/10000000000 : ℝ)|=(3536478063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302061_s7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev6 : (0 : ℝ) ≤ ((33917/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33917/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39177/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8989/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8989/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9161/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9161/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22219/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22219/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(413/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(413/2000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (33917/100000 : ℝ) ^ (65/16 : ℝ) ≤ (247372154023223917/20000000000000000000 : ℝ) := by
    have hpowers : (33917/100000 : ℝ)^65 ≤ (247372154023223917/20000000000000000000 : ℝ)^16 := by
      have hnat : (33917 : ℕ)^65*20000000000000000000^16 ≤ 247372154023223917^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33917 100000 247372154023223917 20000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33917/100000 : ℝ)) (X := (247372154023223917/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner0a : (20247372154023223917/20000000000000000000 : ℝ) ≤ (10030304882502183/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (20247372154023223917/20000000000000000000 : ℝ)^16 ≤ (10030304882502183/10000000000000000 : ℝ)^65 := by
      have hnat : (20247372154023223917 : ℕ)^16*10000000000000000^65 ≤ 10030304882502183^65*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20247372154023223917 20000000000000000000 10030304882502183 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030304882502183/10000000000000000 : ℝ)) (X := (20247372154023223917/20000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner0b : (10247372154023223917/10000000000000000000 : ℝ) ≤ (10060331925582153/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (10247372154023223917/10000000000000000000 : ℝ)^16 ≤ (10060331925582153/10000000000000000 : ℝ)^65 := by
      have hnat : (10247372154023223917 : ℕ)^16*10000000000000000^65 ≤ 10060331925582153^65*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10247372154023223917 10000000000000000000 10060331925582153 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10060331925582153/10000000000000000 : ℝ)) (X := (10247372154023223917/10000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(30304882502183/3391700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3002704307997/339170000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (33917/100000 : ℝ)) (alpha := (30304882502183/3391700000000000 : ℝ)) (beta := (3002704307997/339170000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (33917/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(30304882502183/3391700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3002704307997/339170000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (39177/100000 : ℝ) ^ (65/16 : ℝ) ≤ (1110859566048419083/50000000000000000000 : ℝ) := by
    have hpowers : (39177/100000 : ℝ)^65 ≤ (1110859566048419083/50000000000000000000 : ℝ)^16 := by
      have hnat : (39177 : ℕ)^65*50000000000000000000^16 ≤ 1110859566048419083^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39177 100000 1110859566048419083 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39177/100000 : ℝ)) (X := (1110859566048419083/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner1a : (51110859566048419083/50000000000000000000 : ℝ) ≤ (5027118179570137/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (51110859566048419083/50000000000000000000 : ℝ)^16 ≤ (5027118179570137/5000000000000000 : ℝ)^65 := by
      have hnat : (51110859566048419083 : ℕ)^16*5000000000000000^65 ≤ 5027118179570137^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51110859566048419083 50000000000000000000 5027118179570137 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027118179570137/5000000000000000 : ℝ)) (X := (51110859566048419083/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner1b : (26110859566048419083/25000000000000000000 : ℝ) ≤ (2021518247448299/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (26110859566048419083/25000000000000000000 : ℝ)^16 ≤ (2021518247448299/2000000000000000 : ℝ)^65 := by
      have hnat : (26110859566048419083 : ℕ)^16*2000000000000000^65 ≤ 2021518247448299^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26110859566048419083 25000000000000000000 2021518247448299 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2021518247448299/2000000000000000 : ℝ)) (X := (26110859566048419083/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27118179570137/1958850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(36771108271/2700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (39177/100000 : ℝ)) (alpha := (27118179570137/1958850000000000 : ℝ)) (beta := (36771108271/2700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39177/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27118179570137/1958850000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(36771108271/2700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (8989/25000 : ℝ) ^ (65/16 : ℝ) ≤ (1567910244560774073/100000000000000000000 : ℝ) := by
    have hpowers : (8989/25000 : ℝ)^65 ≤ (1567910244560774073/100000000000000000000 : ℝ)^16 := by
      have hnat : (8989 : ℕ)^65*100000000000000000000^16 ≤ 1567910244560774073^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8989 25000 1567910244560774073 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8989/25000 : ℝ)) (X := (1567910244560774073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner2a : (101567910244560774073/100000000000000000000 : ℝ) ≤ (10038368694474929/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (101567910244560774073/100000000000000000000 : ℝ)^16 ≤ (10038368694474929/10000000000000000 : ℝ)^65 := by
      have hnat : (101567910244560774073 : ℕ)^16*10000000000000000^65 ≤ 10038368694474929^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101567910244560774073 100000000000000000000 10038368694474929 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10038368694474929/10000000000000000 : ℝ)) (X := (101567910244560774073/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s7_corner2b : (51567910244560774073/50000000000000000000 : ℝ) ≤ (2015258689946471/2000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (51567910244560774073/50000000000000000000 : ℝ)^16 ≤ (2015258689946471/2000000000000000 : ℝ)^65 := by
      have hnat : (51567910244560774073 : ℕ)^16*2000000000000000^65 ≤ 2015258689946471^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51567910244560774073 50000000000000000000 2015258689946471 2000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2015258689946471/2000000000000000 : ℝ)) (X := (51567910244560774073/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(38368694474929/3595600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(18962377628713/1797800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (8989/25000 : ℝ)) (alpha := (38368694474929/3595600000000000 : ℝ)) (beta := (18962377628713/1797800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8989/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(38368694474929/3595600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(18962377628713/1797800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-134496937/500000000 : ℝ)*X 0 0+(2286557623/5000000000 : ℝ)*X 0 1+(5642044291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((2359975213/5000000000 : ℝ)*X 1 0+(-1367535101/5000000000 : ℝ)*X 1 1+(1093529089/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((2371895693/5000000000 : ℝ)*X 2 0+(6036209893/10000000000 : ℝ)*X 2 1+(-242991773/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((356618319/625000000 : ℝ)*X 0 0+(3342025043/10000000000 : ℝ)*X 0 1+(3919278927/10000000000 : ℝ)*X 0 2+(356618319/625000000 : ℝ)*X 1 0+(3342025043/10000000000 : ℝ)*X 1 1+(3919278927/10000000000 : ℝ)*X 1 2+(356618319/625000000 : ℝ)*X 2 0+(3342025043/10000000000 : ℝ)*X 2 1+(3919278927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-1348282301/5000000000 : ℝ)*X 0 0+(2194525771/5000000000 : ℝ)*X 0 1+(5806906013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((1153094449/2500000000 : ℝ)*X 1 0+(-99037563/400000000 : ℝ)*X 1 1+(5771062507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((4636241087/10000000000 : ℝ)*X 2 0+(6333317551/10000000000 : ℝ)*X 2 1+(-164743427/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((714256953/1250000000 : ℝ)*X 0 0+(3656475397/10000000000 : ℝ)*X 0 1+(450342021/1250000000 : ℝ)*X 0 2+(714256953/1250000000 : ℝ)*X 1 0+(3656475397/10000000000 : ℝ)*X 1 1+(450342021/1250000000 : ℝ)*X 1 2+(714256953/1250000000 : ℝ)*X 2 0+(3656475397/10000000000 : ℝ)*X 2 1+(450342021/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-577161187/2500000000 : ℝ)*X 0 0+(4705262779/10000000000 : ℝ)*X 0 1+(5810192923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((224788853/500000000 : ℝ)*X 1 0+(-1306200429/5000000000 : ℝ)*X 1 1+(2887175503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((1283006159/2500000000 : ℝ)*X 2 0+(5874170567/10000000000 : ℝ)*X 2 1+(-51379627/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((1539814023/2500000000 : ℝ)*X 0 0+(1564795993/5000000000 : ℝ)*X 0 1+(1798108003/5000000000 : ℝ)*X 0 2+(1539814023/2500000000 : ℝ)*X 1 0+(1564795993/5000000000 : ℝ)*X 1 1+(1798108003/5000000000 : ℝ)*X 1 2+(1539814023/2500000000 : ℝ)*X 2 0+(1564795993/5000000000 : ℝ)*X 2 1+(1798108003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-116383893/500000000 : ℝ)*X 0 0+(2397860159/5000000000 : ℝ)*X 0 1+(5711018741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((2544564229/5000000000 : ℝ)*X 1 0+(-2375233969/10000000000 : ℝ)*X 1 1+(5392405121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((897373541/2000000000 : ℝ)*X 2 0+(6302450797/10000000000 : ℝ)*X 2 1+(-237099683/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((3112128427/5000000000 : ℝ)*X 0 0+(1555424009/5000000000 : ℝ)*X 0 1+(3536478063/10000000000 : ℝ)*X 0 2+(3112128427/5000000000 : ℝ)*X 1 0+(1555424009/5000000000 : ℝ)*X 1 1+(3536478063/10000000000 : ℝ)*X 1 2+(3112128427/5000000000 : ℝ)*X 2 0+(1555424009/5000000000 : ℝ)*X 2 1+(3536478063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302061_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((9161/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9161/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8919955207228945232951/587025000000000000000000000 : ℝ) := by norm_num
    linear_combination (137813/100000000000 : ℝ)*(base50) + (2053592314463/1000000000000 : ℝ)*(base59) + (12774865088557/1000000000000 : ℝ)*(major_s7_0) + (12774865088557/1000000000000 : ℝ)*(major_s7_1) + (12774865088557/1000000000000 : ℝ)*(major_s7_2) + (194467501/1000000000000 : ℝ)*(sp_s7_0) + (32319667/500000000000 : ℝ)*(sp_s7_1) + (75460723/500000000000 : ℝ)*(sp_s7_6) + (16985566651411/1000000000000 : ℝ)*(sp_s7_7) + (8492585082541/500000000000 : ℝ)*(sp_s7_8) + (530796434517/31250000000 : ℝ)*(sp_s7_9) + (8563813071687/1000000000000 : ℝ)*(sp_s7_13) + (526314497/1000000000000 : ℝ)*(sp_s7_15) + (8600449/31250000000 : ℝ)*(sp_s7_23) + (8563963993133/1000000000000 : ℝ)*(f.failure) + (265402517483/15625000000 : ℝ)*(f.sum) + (41708531927784658211/140864821200000000000000000000000 : ℝ)*base62 + (83412727206359/1797800000000000000000000000 : ℝ)*base65 + (2366563607107/2700000000000000000000000 : ℝ)*base67 + (409122041804573/3595600000000000000000000000 : ℝ)*base69 + (1337283206551919443/4690460200000000000000000000000 : ℝ)*base70 + (859037679537/26090000000000000000000000 : ℝ)*base73 + (598781513228909/1958850000000000000000000000 : ℝ)*base75 + (158494389169557/260900000000000000000000000 : ℝ)*base77 + (1873930723145453/7044300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (5039/10000000000000000 : ℝ)*base86 + (5039/10000000000000000 : ℝ)*base88 + (5039/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22219/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22219/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13592403625973667001502953415923/796285356773400000000000000000000000 : ℝ) := by norm_num
    linear_combination (1481153/1000000000000 : ℝ)*(base39) + (9424421/1000000000000 : ℝ)*(base40) + (1669555084549/1000000000000 : ℝ)*(base59) + (12281654353313/1000000000000 : ℝ)*(major_s7_0) + (12281654353313/1000000000000 : ℝ)*(major_s7_1) + (12281654353313/1000000000000 : ℝ)*(major_s7_2) + (6936967/20000000000 : ℝ)*(sp_s7_1) + (184397947/500000000000 : ℝ)*(sp_s7_2) + (16226927/125000000000 : ℝ)*(sp_s7_6) + (205606077/500000000000 : ℝ)*(sp_s7_7) + (16329564491203/1000000000000 : ℝ)*(sp_s7_14) + (16329628855007/1000000000000 : ℝ)*(sp_s7_15) + (16329606907463/1000000000000 : ℝ)*(sp_s7_16) + (8233197497927/1000000000000 : ℝ)*(sp_s7_20) + (8233327313343/1000000000000 : ℝ)*(f.failure) + (16329975703357/1000000000000 : ℝ)*(f.sum) + (24294369969405127519/140864821200000000000000000000000 : ℝ)*base62 + (1120313499062869/1797800000000000000000000000 : ℝ)*base64 + (1090646520727/2700000000000000000000000 : ℝ)*base66 + (1643037416300303/3595600000000000000000000000 : ℝ)*base68 + (29522036651398837151/60975982600000000000000000000000 : ℝ)*base70 + (54062123531899/339170000000000000000000000 : ℝ)*base73 + (888432838174619/1958850000000000000000000000 : ℝ)*base74 + (1710108106716131/3391700000000000000000000000 : ℝ)*base76 + (40529785500236221/91575900000000000000000000000 : ℝ)*base79 + (7531/10000000000000000 : ℝ)*base87 + (7531/10000000000000000 : ℝ)*base89 + (7531/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(413/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(413/2000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (59870084511527272366076112187/17695230150520000000000000000000000 : ℝ) := by norm_num
    linear_combination (112905046061/250000000000 : ℝ)*(base40) + (344161404607/200000000000 : ℝ)*(base59) + (2402383568673/200000000000 : ℝ)*(major_s7_0) + (2402383568673/200000000000 : ℝ)*(major_s7_1) + (2402383568673/200000000000 : ℝ)*(major_s7_2) + (34189839/1000000000000 : ℝ)*(sp_s7_0) + (64602813/1000000000000 : ℝ)*(sp_s7_1) + (4525869/250000000000 : ℝ)*(sp_s7_8) + (3445993/250000000000 : ℝ)*(sp_s7_9) + (16577/250000000000 : ℝ)*(sp_s7_13) + (998206122511/62500000000 : ℝ)*(sp_s7_21) + (7985624721863/500000000000 : ℝ)*(sp_s7_22) + (7985659183021/500000000000 : ℝ)*(sp_s7_23) + (8052502342599/1000000000000 : ℝ)*(sp_s7_27) + (4026251204453/500000000000 : ℝ)*(f.failure) + (3194266430003/200000000000 : ℝ)*(f.sum) + (4028801886280801637/9390988080000000000000000000000 : ℝ)*base62 + (397139155913369/359560000000000000000000000 : ℝ)*base64 + (140578987367/180000000000000000000000 : ℝ)*base66 + (700671278450543/719120000000000000000000000 : ℝ)*base68 + (2921650435537252007/12195196520000000000000000000000 : ℝ)*base70 + (376830343774243/339170000000000000000000000 : ℝ)*base72 + (65063556433741/130590000000000000000000000 : ℝ)*base74 + (131066158044423/678340000000000000000000000 : ℝ)*base77 + (4775738484098791/6105060000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (401/5000000000000000 : ℝ)*base87 + (401/5000000000000000 : ℝ)*base89 + (401/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev6 : (0 : ℝ) ≤ ((33917/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(33917/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39177/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39177/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8989/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8989/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((9161/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9161/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22219/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22219/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(413/2000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(413/2000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302061_s7 p hpa hpb X hX hprev6

#print axioms solution
