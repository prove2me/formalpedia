-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c328053_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:22:10.746143+00:00
-- url     : https://prove2.me/submissions/741dd912-5da3-4d1d-af64-99330155a7de

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
theorem collision_support_c328053_s1_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1941333853/10000000000 : ℝ)*x 0 + (994396043/2000000000 : ℝ)*x 1 + (249509287/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941333853/10000000000 : ℝ)^93 ≤ (1726167817727/12500000000000 : ℝ)^77 := by
    have hnat : (1941333853 : ℕ)^93*12500000000000^77 ≤ 1726167817727^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941333853 10000000000 1726167817727 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994396043/2000000000 : ℝ)^93 ≤ (1075005219199/2500000000000 : ℝ)^77 := by
    have hnat : (994396043 : ℕ)^93*2500000000000^77 ≤ 1075005219199^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994396043 2000000000 1075005219199 2500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249509287/500000000 : ℝ)^93 ≤ (10797612169317/25000000000000 : ℝ)^77 := by
    have hnat : (249509287 : ℕ)^93*25000000000000^77 ≤ 10797612169317^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249509287 500000000 10797612169317 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1941333853/10000000000 : ℝ), (994396043/2000000000 : ℝ), (249509287/500000000 : ℝ)] ![(1726167817727/12500000000000 : ℝ), (1075005219199/2500000000000 : ℝ), (10797612169317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1941333853/10000000000 : ℝ)|^93 ≤ (1726167817727/12500000000000 : ℝ)^77
        have hw : |(-1941333853/10000000000 : ℝ)|=(1941333853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994396043/2000000000 : ℝ)|^93 ≤ (1075005219199/2500000000000 : ℝ)^77
        have hw : |(994396043/2000000000 : ℝ)|=(994396043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249509287/500000000 : ℝ)|^93 ≤ (10797612169317/25000000000000 : ℝ)^77
        have hw : |(249509287/500000000 : ℝ)|=(249509287/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2224607249/5000000000 : ℝ)*x 0 + (5925310641/10000000000 : ℝ)*x 1 + (-1393384469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2224607249/5000000000 : ℝ)^93 ≤ (9400249308211/25000000000000 : ℝ)^77 := by
    have hnat : (2224607249 : ℕ)^93*25000000000000^77 ≤ 9400249308211^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224607249 5000000000 9400249308211 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5925310641/10000000000 : ℝ)^93 ≤ (53147429709633/100000000000000 : ℝ)^77 := by
    have hnat : (5925310641 : ℕ)^93*100000000000000^77 ≤ 53147429709633^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5925310641 10000000000 53147429709633 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1393384469/10000000000 : ℝ)^93 ≤ (9251573035773/100000000000000 : ℝ)^77 := by
    have hnat : (1393384469 : ℕ)^93*100000000000000^77 ≤ 9251573035773^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393384469 10000000000 9251573035773 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2224607249/5000000000 : ℝ), (5925310641/10000000000 : ℝ), (-1393384469/10000000000 : ℝ)] ![(9400249308211/25000000000000 : ℝ), (53147429709633/100000000000000 : ℝ), (9251573035773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2224607249/5000000000 : ℝ)|^93 ≤ (9400249308211/25000000000000 : ℝ)^77
        have hw : |(2224607249/5000000000 : ℝ)|=(2224607249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5925310641/10000000000 : ℝ)|^93 ≤ (53147429709633/100000000000000 : ℝ)^77
        have hw : |(5925310641/10000000000 : ℝ)|=(5925310641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1393384469/10000000000 : ℝ)|^93 ≤ (9251573035773/100000000000000 : ℝ)^77
        have hw : |(-1393384469/10000000000 : ℝ)|=(1393384469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3597353943/5000000000 : ℝ)*x 0 + (450578007/2000000000 : ℝ)*x 1 + (2224938439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3597353943/5000000000 : ℝ)^93 ≤ (33594765975669/50000000000000 : ℝ)^77 := by
    have hnat : (3597353943 : ℕ)^93*50000000000000^77 ≤ 33594765975669^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3597353943 5000000000 33594765975669 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450578007/2000000000 : ℝ)^93 ≤ (413222934073/2500000000000 : ℝ)^77 := by
    have hnat : (450578007 : ℕ)^93*2500000000000^77 ≤ 413222934073^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450578007 2000000000 413222934073 2500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2224938439/10000000000 : ℝ)^93 ≤ (8140775336387/50000000000000 : ℝ)^77 := by
    have hnat : (2224938439 : ℕ)^93*50000000000000^77 ≤ 8140775336387^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2224938439 10000000000 8140775336387 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3597353943/5000000000 : ℝ), (450578007/2000000000 : ℝ), (2224938439/10000000000 : ℝ)] ![(33594765975669/50000000000000 : ℝ), (413222934073/2500000000000 : ℝ), (8140775336387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3597353943/5000000000 : ℝ)|^93 ≤ (33594765975669/50000000000000 : ℝ)^77
        have hw : |(3597353943/5000000000 : ℝ)|=(3597353943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450578007/2000000000 : ℝ)|^93 ≤ (413222934073/2500000000000 : ℝ)^77
        have hw : |(450578007/2000000000 : ℝ)|=(450578007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2224938439/10000000000 : ℝ)|^93 ≤ (8140775336387/50000000000000 : ℝ)^77
        have hw : |(2224938439/10000000000 : ℝ)|=(2224938439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-38709663/200000000 : ℝ)*x 0 + (280197657/625000000 : ℝ)*x 1 + (5473569039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38709663/200000000 : ℝ)^93 ≤ (6879546220599/50000000000000 : ℝ)^77 := by
    have hnat : (38709663 : ℕ)^93*50000000000000^77 ≤ 6879546220599^77*200000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38709663 200000000 6879546220599 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280197657/625000000 : ℝ)^93 ≤ (2371736677339/6250000000000 : ℝ)^77 := by
    have hnat : (280197657 : ℕ)^93*6250000000000^77 ≤ 2371736677339^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280197657 625000000 2371736677339 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5473569039/10000000000 : ℝ)^93 ≤ (24146560353627/50000000000000 : ℝ)^77 := by
    have hnat : (5473569039 : ℕ)^93*50000000000000^77 ≤ 24146560353627^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473569039 10000000000 24146560353627 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38709663/200000000 : ℝ), (280197657/625000000 : ℝ), (5473569039/10000000000 : ℝ)] ![(6879546220599/50000000000000 : ℝ), (2371736677339/6250000000000 : ℝ), (24146560353627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38709663/200000000 : ℝ)|^93 ≤ (6879546220599/50000000000000 : ℝ)^77
        have hw : |(-38709663/200000000 : ℝ)|=(38709663/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280197657/625000000 : ℝ)|^93 ≤ (2371736677339/6250000000000 : ℝ)^77
        have hw : |(280197657/625000000 : ℝ)|=(280197657/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5473569039/10000000000 : ℝ)|^93 ≤ (24146560353627/50000000000000 : ℝ)^77
        have hw : |(5473569039/10000000000 : ℝ)|=(5473569039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2161654279/5000000000 : ℝ)*x 0 + (-1287760007/10000000000 : ℝ)*x 1 + (306024257/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161654279/5000000000 : ℝ)^93 ≤ (36319652407669/100000000000000 : ℝ)^77 := by
    have hnat : (2161654279 : ℕ)^93*100000000000000^77 ≤ 36319652407669^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161654279 5000000000 36319652407669 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287760007/10000000000 : ℝ)^93 ≤ (4205673686687/50000000000000 : ℝ)^77 := by
    have hnat : (1287760007 : ℕ)^93*50000000000000^77 ≤ 4205673686687^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287760007 10000000000 4205673686687 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (306024257/500000000 : ℝ)^93 ≤ (13817250051333/25000000000000 : ℝ)^77 := by
    have hnat : (306024257 : ℕ)^93*25000000000000^77 ≤ 13817250051333^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306024257 500000000 13817250051333 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161654279/5000000000 : ℝ), (-1287760007/10000000000 : ℝ), (306024257/500000000 : ℝ)] ![(36319652407669/100000000000000 : ℝ), (4205673686687/50000000000000 : ℝ), (13817250051333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161654279/5000000000 : ℝ)|^93 ≤ (36319652407669/100000000000000 : ℝ)^77
        have hw : |(2161654279/5000000000 : ℝ)|=(2161654279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1287760007/10000000000 : ℝ)|^93 ≤ (4205673686687/50000000000000 : ℝ)^77
        have hw : |(-1287760007/10000000000 : ℝ)|=(1287760007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(306024257/500000000 : ℝ)|^93 ≤ (13817250051333/25000000000000 : ℝ)^77
        have hw : |(306024257/500000000 : ℝ)|=(306024257/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2168578983/5000000000 : ℝ)*x 0 + (6365158081/10000000000 : ℝ)*x 1 + (-459158231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2168578983/5000000000 : ℝ)^93 ≤ (7292044522739/20000000000000 : ℝ)^77 := by
    have hnat : (2168578983 : ℕ)^93*20000000000000^77 ≤ 7292044522739^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2168578983 5000000000 7292044522739 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6365158081/10000000000 : ℝ)^93 ≤ (115897019893/200000000000 : ℝ)^77 := by
    have hnat : (6365158081 : ℕ)^93*200000000000^77 ≤ 115897019893^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6365158081 10000000000 115897019893 200000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459158231/5000000000 : ℝ)^93 ≤ (5591267425281/100000000000000 : ℝ)^77 := by
    have hnat : (459158231 : ℕ)^93*100000000000000^77 ≤ 5591267425281^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459158231 5000000000 5591267425281 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2168578983/5000000000 : ℝ), (6365158081/10000000000 : ℝ), (-459158231/5000000000 : ℝ)] ![(7292044522739/20000000000000 : ℝ), (115897019893/200000000000 : ℝ), (5591267425281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2168578983/5000000000 : ℝ)|^93 ≤ (7292044522739/20000000000000 : ℝ)^77
        have hw : |(2168578983/5000000000 : ℝ)|=(2168578983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6365158081/10000000000 : ℝ)|^93 ≤ (115897019893/200000000000 : ℝ)^77
        have hw : |(6365158081/10000000000 : ℝ)|=(6365158081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-459158231/5000000000 : ℝ)|^93 ≤ (5591267425281/100000000000000 : ℝ)^77
        have hw : |(-459158231/5000000000 : ℝ)|=(459158231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3583362729/5000000000 : ℝ)*x 0 + (143327991/500000000 : ℝ)*x 1 + (201242171/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3583362729/5000000000 : ℝ)^93 ≤ (13374807698281/20000000000000 : ℝ)^77 := by
    have hnat : (3583362729 : ℕ)^93*20000000000000^77 ≤ 13374807698281^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3583362729 5000000000 13374807698281 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (143327991/500000000 : ℝ)^93 ≤ (22110820312137/100000000000000 : ℝ)^77 := by
    have hnat : (143327991 : ℕ)^93*100000000000000^77 ≤ 22110820312137^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143327991 500000000 22110820312137 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201242171/1250000000 : ℝ)^93 ≤ (2753785294577/25000000000000 : ℝ)^77 := by
    have hnat : (201242171 : ℕ)^93*25000000000000^77 ≤ 2753785294577^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201242171 1250000000 2753785294577 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3583362729/5000000000 : ℝ), (143327991/500000000 : ℝ), (201242171/1250000000 : ℝ)] ![(13374807698281/20000000000000 : ℝ), (22110820312137/100000000000000 : ℝ), (2753785294577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3583362729/5000000000 : ℝ)|^93 ≤ (13374807698281/20000000000000 : ℝ)^77
        have hw : |(3583362729/5000000000 : ℝ)|=(3583362729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(143327991/500000000 : ℝ)|^93 ≤ (22110820312137/100000000000000 : ℝ)^77
        have hw : |(143327991/500000000 : ℝ)|=(143327991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(201242171/1250000000 : ℝ)|^93 ≤ (2753785294577/25000000000000 : ℝ)^77
        have hw : |(201242171/1250000000 : ℝ)|=(201242171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-742992011/5000000000 : ℝ)*x 0 + (4898698777/10000000000 : ℝ)*x 1 + (84749251/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (742992011/5000000000 : ℝ)^93 ≤ (9999197115761/100000000000000 : ℝ)^77 := by
    have hnat : (742992011 : ℕ)^93*100000000000000^77 ≤ 9999197115761^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742992011 5000000000 9999197115761 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4898698777/10000000000 : ℝ)^93 ≤ (42235916935357/100000000000000 : ℝ)^77 := by
    have hnat : (4898698777 : ℕ)^93*100000000000000^77 ≤ 42235916935357^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4898698777 10000000000 42235916935357 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84749251/156250000 : ℝ)^93 ≤ (9552977188239/20000000000000 : ℝ)^77 := by
    have hnat : (84749251 : ℕ)^93*20000000000000^77 ≤ 9552977188239^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84749251 156250000 9552977188239 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-742992011/5000000000 : ℝ), (4898698777/10000000000 : ℝ), (84749251/156250000 : ℝ)] ![(9999197115761/100000000000000 : ℝ), (42235916935357/100000000000000 : ℝ), (9552977188239/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-742992011/5000000000 : ℝ)|^93 ≤ (9999197115761/100000000000000 : ℝ)^77
        have hw : |(-742992011/5000000000 : ℝ)|=(742992011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4898698777/10000000000 : ℝ)|^93 ≤ (42235916935357/100000000000000 : ℝ)^77
        have hw : |(4898698777/10000000000 : ℝ)|=(4898698777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84749251/156250000 : ℝ)|^93 ≤ (9552977188239/20000000000000 : ℝ)^77
        have hw : |(84749251/156250000 : ℝ)|=(84749251/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4271239177/10000000000 : ℝ)*x 0 + (-264675611/2000000000 : ℝ)*x 1 + (6143019599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271239177/10000000000 : ℝ)^93 ≤ (35791991923993/100000000000000 : ℝ)^77 := by
    have hnat : (4271239177 : ℕ)^93*100000000000000^77 ≤ 35791991923993^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271239177 10000000000 35791991923993 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264675611/2000000000 : ℝ)^93 ≤ (1086642548049/12500000000000 : ℝ)^77 := by
    have hnat : (264675611 : ℕ)^93*12500000000000^77 ≤ 1086642548049^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264675611 2000000000 1086642548049 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6143019599/10000000000 : ℝ)^93 ≤ (55514867666049/100000000000000 : ℝ)^77 := by
    have hnat : (6143019599 : ℕ)^93*100000000000000^77 ≤ 55514867666049^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6143019599 10000000000 55514867666049 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271239177/10000000000 : ℝ), (-264675611/2000000000 : ℝ), (6143019599/10000000000 : ℝ)] ![(35791991923993/100000000000000 : ℝ), (1086642548049/12500000000000 : ℝ), (55514867666049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271239177/10000000000 : ℝ)|^93 ≤ (35791991923993/100000000000000 : ℝ)^77
        have hw : |(4271239177/10000000000 : ℝ)|=(4271239177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264675611/2000000000 : ℝ)|^93 ≤ (1086642548049/12500000000000 : ℝ)^77
        have hw : |(-264675611/2000000000 : ℝ)|=(264675611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6143019599/10000000000 : ℝ)|^93 ≤ (55514867666049/100000000000000 : ℝ)^77
        have hw : |(6143019599/10000000000 : ℝ)|=(6143019599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (196515591/400000000 : ℝ)*x 0 + (180859337/312500000 : ℝ)*x 1 + (-967934667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196515591/400000000 : ℝ)^93 ≤ (42383738211279/100000000000000 : ℝ)^77 := by
    have hnat : (196515591 : ℕ)^93*100000000000000^77 ≤ 42383738211279^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196515591 400000000 42383738211279 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180859337/312500000 : ℝ)^93 ≤ (25829046819313/50000000000000 : ℝ)^77 := by
    have hnat : (180859337 : ℕ)^93*50000000000000^77 ≤ 25829046819313^77*312500000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180859337 312500000 25829046819313 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967934667/10000000000 : ℝ)^93 ≤ (744771017957/12500000000000 : ℝ)^77 := by
    have hnat : (967934667 : ℕ)^93*12500000000000^77 ≤ 744771017957^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967934667 10000000000 744771017957 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(196515591/400000000 : ℝ), (180859337/312500000 : ℝ), (-967934667/10000000000 : ℝ)] ![(42383738211279/100000000000000 : ℝ), (25829046819313/50000000000000 : ℝ), (744771017957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(196515591/400000000 : ℝ)|^93 ≤ (42383738211279/100000000000000 : ℝ)^77
        have hw : |(196515591/400000000 : ℝ)|=(196515591/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180859337/312500000 : ℝ)|^93 ≤ (25829046819313/50000000000000 : ℝ)^77
        have hw : |(180859337/312500000 : ℝ)|=(180859337/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-967934667/10000000000 : ℝ)|^93 ≤ (744771017957/12500000000000 : ℝ)^77
        have hw : |(-967934667/10000000000 : ℝ)|=(967934667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1552436409/2000000000 : ℝ)*x 0 + (21887461/100000000 : ℝ)*x 1 + (1534664269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1552436409/2000000000 : ℝ)^93 ≤ (2945664705739/4000000000000 : ℝ)^77 := by
    have hnat : (1552436409 : ℕ)^93*4000000000000^77 ≤ 2945664705739^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552436409 2000000000 2945664705739 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21887461/100000000 : ℝ)^93 ≤ (15962213951727/100000000000000 : ℝ)^77 := by
    have hnat : (21887461 : ℕ)^93*100000000000000^77 ≤ 15962213951727^77*100000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21887461 100000000 15962213951727 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1534664269/10000000000 : ℝ)^93 ≤ (2599042096951/25000000000000 : ℝ)^77 := by
    have hnat : (1534664269 : ℕ)^93*25000000000000^77 ≤ 2599042096951^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534664269 10000000000 2599042096951 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1552436409/2000000000 : ℝ), (21887461/100000000 : ℝ), (1534664269/10000000000 : ℝ)] ![(2945664705739/4000000000000 : ℝ), (15962213951727/100000000000000 : ℝ), (2599042096951/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1552436409/2000000000 : ℝ)|^93 ≤ (2945664705739/4000000000000 : ℝ)^77
        have hw : |(1552436409/2000000000 : ℝ)|=(1552436409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21887461/100000000 : ℝ)|^93 ≤ (15962213951727/100000000000000 : ℝ)^77
        have hw : |(21887461/100000000 : ℝ)|=(21887461/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1534664269/10000000000 : ℝ)|^93 ≤ (2599042096951/25000000000000 : ℝ)^77
        have hw : |(1534664269/10000000000 : ℝ)|=(1534664269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426075503/10000000000 : ℝ)*x 0 + (5150574309/10000000000 : ℝ)*x 1 + (2610418213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426075503/10000000000 : ℝ)^93 ≤ (9514367587221/100000000000000 : ℝ)^77 := by
    have hnat : (1426075503 : ℕ)^93*100000000000000^77 ≤ 9514367587221^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426075503 10000000000 9514367587221 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150574309/10000000000 : ℝ)^93 ≤ (11218157078781/25000000000000 : ℝ)^77 := by
    have hnat : (5150574309 : ℕ)^93*25000000000000^77 ≤ 11218157078781^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150574309 10000000000 11218157078781 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610418213/5000000000 : ℝ)^93 ≤ (2280650204359/5000000000000 : ℝ)^77 := by
    have hnat : (2610418213 : ℕ)^93*5000000000000^77 ≤ 2280650204359^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610418213 5000000000 2280650204359 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426075503/10000000000 : ℝ), (5150574309/10000000000 : ℝ), (2610418213/5000000000 : ℝ)] ![(9514367587221/100000000000000 : ℝ), (11218157078781/25000000000000 : ℝ), (2280650204359/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426075503/10000000000 : ℝ)|^93 ≤ (9514367587221/100000000000000 : ℝ)^77
        have hw : |(-1426075503/10000000000 : ℝ)|=(1426075503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150574309/10000000000 : ℝ)|^93 ≤ (11218157078781/25000000000000 : ℝ)^77
        have hw : |(5150574309/10000000000 : ℝ)|=(5150574309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610418213/5000000000 : ℝ)|^93 ≤ (2280650204359/5000000000000 : ℝ)^77
        have hw : |(2610418213/5000000000 : ℝ)|=(2610418213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4958946613/10000000000 : ℝ)*x 0 + (-523673197/5000000000 : ℝ)*x 1 + (2843768959/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4958946613/10000000000 : ℝ)^93 ≤ (42864102078521/100000000000000 : ℝ)^77 := by
    have hnat : (4958946613 : ℕ)^93*100000000000000^77 ≤ 42864102078521^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4958946613 10000000000 42864102078521 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523673197/5000000000 : ℝ)^93 ≤ (6553491650601/100000000000000 : ℝ)^77 := by
    have hnat : (523673197 : ℕ)^93*100000000000000^77 ≤ 6553491650601^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523673197 5000000000 6553491650601 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2843768959/5000000000 : ℝ)^93 ≤ (25291203127953/50000000000000 : ℝ)^77 := by
    have hnat : (2843768959 : ℕ)^93*50000000000000^77 ≤ 25291203127953^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843768959 5000000000 25291203127953 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4958946613/10000000000 : ℝ), (-523673197/5000000000 : ℝ), (2843768959/5000000000 : ℝ)] ![(42864102078521/100000000000000 : ℝ), (6553491650601/100000000000000 : ℝ), (25291203127953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4958946613/10000000000 : ℝ)|^93 ≤ (42864102078521/100000000000000 : ℝ)^77
        have hw : |(4958946613/10000000000 : ℝ)|=(4958946613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523673197/5000000000 : ℝ)|^93 ≤ (6553491650601/100000000000000 : ℝ)^77
        have hw : |(-523673197/5000000000 : ℝ)|=(523673197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2843768959/5000000000 : ℝ)|^93 ≤ (25291203127953/50000000000000 : ℝ)^77
        have hw : |(2843768959/5000000000 : ℝ)|=(2843768959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (852094809/2000000000 : ℝ)*x 0 + (6256471811/10000000000 : ℝ)*x 1 + (-117904401/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852094809/2000000000 : ℝ)^93 ≤ (35683066377793/100000000000000 : ℝ)^77 := by
    have hnat : (852094809 : ℕ)^93*100000000000000^77 ≤ 35683066377793^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852094809 2000000000 35683066377793 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6256471811/10000000000 : ℝ)^93 ≤ (11351110288359/20000000000000 : ℝ)^77 := by
    have hnat : (6256471811 : ℕ)^93*20000000000000^77 ≤ 11351110288359^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6256471811 10000000000 11351110288359 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (117904401/1000000000 : ℝ)^93 ≤ (1890345540629/25000000000000 : ℝ)^77 := by
    have hnat : (117904401 : ℕ)^93*25000000000000^77 ≤ 1890345540629^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117904401 1000000000 1890345540629 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852094809/2000000000 : ℝ), (6256471811/10000000000 : ℝ), (-117904401/1000000000 : ℝ)] ![(35683066377793/100000000000000 : ℝ), (11351110288359/20000000000000 : ℝ), (1890345540629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852094809/2000000000 : ℝ)|^93 ≤ (35683066377793/100000000000000 : ℝ)^77
        have hw : |(852094809/2000000000 : ℝ)|=(852094809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6256471811/10000000000 : ℝ)|^93 ≤ (11351110288359/20000000000000 : ℝ)^77
        have hw : |(6256471811/10000000000 : ℝ)|=(6256471811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-117904401/1000000000 : ℝ)|^93 ≤ (1890345540629/25000000000000 : ℝ)^77
        have hw : |(-117904401/1000000000 : ℝ)|=(117904401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328053_s1_s1_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1961089673/2500000000 : ℝ)*x 0 + (901777687/5000000000 : ℝ)*x 1 + (1820872509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1961089673/2500000000 : ℝ)^93 ≤ (74584280159823/100000000000000 : ℝ)^77 := by
    have hnat : (1961089673 : ℕ)^93*100000000000000^77 ≤ 74584280159823^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961089673 2500000000 74584280159823 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901777687/5000000000 : ℝ)^93 ≤ (3158631717631/25000000000000 : ℝ)^77 := by
    have hnat : (901777687 : ℕ)^93*25000000000000^77 ≤ 3158631717631^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901777687 5000000000 3158631717631 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1820872509/10000000000 : ℝ)^93 ≤ (6390596478109/50000000000000 : ℝ)^77 := by
    have hnat : (1820872509 : ℕ)^93*50000000000000^77 ≤ 6390596478109^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1820872509 10000000000 6390596478109 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1961089673/2500000000 : ℝ), (901777687/5000000000 : ℝ), (1820872509/10000000000 : ℝ)] ![(74584280159823/100000000000000 : ℝ), (3158631717631/25000000000000 : ℝ), (6390596478109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1961089673/2500000000 : ℝ)|^93 ≤ (74584280159823/100000000000000 : ℝ)^77
        have hw : |(1961089673/2500000000 : ℝ)|=(1961089673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(901777687/5000000000 : ℝ)|^93 ≤ (3158631717631/25000000000000 : ℝ)^77
        have hw : |(901777687/5000000000 : ℝ)|=(901777687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1820872509/10000000000 : ℝ)|^93 ≤ (6390596478109/50000000000000 : ℝ)^77
        have hw : |(1820872509/10000000000 : ℝ)|=(1820872509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328053_s1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((30531/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30531/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30639/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30639/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59533/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59533/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1281/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1281/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26241/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26241/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6349/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6349/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
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
  have s1_pow0 : (30531/50000 : ℝ) ^ (91/16 : ℝ) ≤ (6047455817770729339/100000000000000000000 : ℝ) := by
    have hpowers : (30531/50000 : ℝ)^91 ≤ (6047455817770729339/100000000000000000000 : ℝ)^16 := by
      have hnat : (30531 : ℕ)^91*100000000000000000000^16 ≤ 6047455817770729339^16*50000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30531 50000 6047455817770729339 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30531/50000 : ℝ)) (X := (6047455817770729339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (106047455817770729339/100000000000000000000 : ℝ) ≤ (1262971568835177/1250000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (106047455817770729339/100000000000000000000 : ℝ)^16 ≤ (1262971568835177/1250000000000000 : ℝ)^91 := by
      have hnat : (106047455817770729339 : ℕ)^16*1250000000000000^91 ≤ 1262971568835177^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106047455817770729339 100000000000000000000 1262971568835177 1250000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262971568835177/1250000000000000 : ℝ)) (X := (106047455817770729339/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (56047455817770729339/50000000000000000000 : ℝ) ≤ (5101388562794009/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (56047455817770729339/50000000000000000000 : ℝ)^16 ≤ (5101388562794009/5000000000000000 : ℝ)^91 := by
      have hnat : (56047455817770729339 : ℕ)^16*5000000000000000^91 ≤ 5101388562794009^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56047455817770729339 50000000000000000000 5101388562794009 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5101388562794009/5000000000000000 : ℝ)) (X := (56047455817770729339/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(12971568835177/763275000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(49502287453301/3053100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (30531/50000 : ℝ)) (alpha := (12971568835177/763275000000000 : ℝ)) (beta := (49502287453301/3053100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (30531/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(12971568835177/763275000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(49502287453301/3053100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (30639/50000 : ℝ) ^ (91/16 : ℝ) ≤ (6170137066607819383/100000000000000000000 : ℝ) := by
    have hpowers : (30639/50000 : ℝ)^91 ≤ (6170137066607819383/100000000000000000000 : ℝ)^16 := by
      have hnat : (30639 : ℕ)^91*100000000000000000000^16 ≤ 6170137066607819383^16*50000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30639 50000 6170137066607819383 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (30639/50000 : ℝ)) (X := (6170137066607819383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (106170137066607819383/100000000000000000000 : ℝ) ≤ (10105826705360397/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (106170137066607819383/100000000000000000000 : ℝ)^16 ≤ (10105826705360397/10000000000000000 : ℝ)^91 := by
      have hnat : (106170137066607819383 : ℕ)^16*10000000000000000^91 ≤ 10105826705360397^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        106170137066607819383 100000000000000000000 10105826705360397 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10105826705360397/10000000000000000 : ℝ)) (X := (106170137066607819383/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (56170137066607819383/50000000000000000000 : ℝ) ≤ (2551675053014561/2500000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (56170137066607819383/50000000000000000000 : ℝ)^16 ≤ (2551675053014561/2500000000000000 : ℝ)^91 := by
      have hnat : (56170137066607819383 : ℕ)^16*2500000000000000^91 ≤ 2551675053014561^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56170137066607819383 50000000000000000000 2551675053014561 2500000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2551675053014561/2500000000000000 : ℝ)) (X := (56170137066607819383/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(15118100765771/875400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(100873506697847/6127800000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (30639/50000 : ℝ)) (alpha := (15118100765771/875400000000000 : ℝ)) (beta := (100873506697847/6127800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (30639/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(15118100765771/875400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(100873506697847/6127800000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (59533/100000 : ℝ) ^ (91/16 : ℝ) ≤ (1047043685762024697/20000000000000000000 : ℝ) := by
    have hpowers : (59533/100000 : ℝ)^91 ≤ (1047043685762024697/20000000000000000000 : ℝ)^16 := by
      have hnat : (59533 : ℕ)^91*20000000000000000000^16 ≤ 1047043685762024697^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59533 100000 1047043685762024697 20000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (59533/100000 : ℝ)) (X := (1047043685762024697/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (21047043685762024697/20000000000000000000 : ℝ) ≤ (40360491810829/40000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (21047043685762024697/20000000000000000000 : ℝ)^16 ≤ (40360491810829/40000000000000 : ℝ)^91 := by
      have hnat : (21047043685762024697 : ℕ)^16*40000000000000^91 ≤ 40360491810829^91*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21047043685762024697 20000000000000000000 40360491810829 40000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40360491810829/40000000000000 : ℝ)) (X := (21047043685762024697/20000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (11047043685762024697/10000000000000000000 : ℝ) ≤ (10176623440314587/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (11047043685762024697/10000000000000000000 : ℝ)^16 ≤ (10176623440314587/10000000000000000 : ℝ)^91 := by
      have hnat : (11047043685762024697 : ℕ)^16*10000000000000000^91 ≤ 10176623440314587^91*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11047043685762024697 10000000000000000000 10176623440314587 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10176623440314587/10000000000000000 : ℝ)) (X := (11047043685762024697/10000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(360491810829/23813200000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(86500487607337/5953300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (59533/100000 : ℝ)) (alpha := (360491810829/23813200000000 : ℝ)) (beta := (86500487607337/5953300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (59533/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(360491810829/23813200000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(86500487607337/5953300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1941333853/10000000000 : ℝ)*X 0 0+(994396043/2000000000 : ℝ)*X 0 1+(249509287/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2224607249/5000000000 : ℝ)*X 2 0+(5925310641/10000000000 : ℝ)*X 2 1+(-1393384469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((3597353943/5000000000 : ℝ)*X 0 0+(450578007/2000000000 : ℝ)*X 0 1+(2224938439/10000000000 : ℝ)*X 0 2+(3597353943/5000000000 : ℝ)*X 1 0+(450578007/2000000000 : ℝ)*X 1 1+(2224938439/10000000000 : ℝ)*X 1 2+(3597353943/5000000000 : ℝ)*X 2 0+(450578007/2000000000 : ℝ)*X 2 1+(2224938439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-38709663/200000000 : ℝ)*X 0 0+(280197657/625000000 : ℝ)*X 0 1+(5473569039/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2161654279/5000000000 : ℝ)*X 1 0+(-1287760007/10000000000 : ℝ)*X 1 1+(306024257/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2168578983/5000000000 : ℝ)*X 2 0+(6365158081/10000000000 : ℝ)*X 2 1+(-459158231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3583362729/5000000000 : ℝ)*X 0 0+(143327991/500000000 : ℝ)*X 0 1+(201242171/1250000000 : ℝ)*X 0 2+(3583362729/5000000000 : ℝ)*X 1 0+(143327991/500000000 : ℝ)*X 1 1+(201242171/1250000000 : ℝ)*X 1 2+(3583362729/5000000000 : ℝ)*X 2 0+(143327991/500000000 : ℝ)*X 2 1+(201242171/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-742992011/5000000000 : ℝ)*X 0 0+(4898698777/10000000000 : ℝ)*X 0 1+(84749251/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4271239177/10000000000 : ℝ)*X 1 0+(-264675611/2000000000 : ℝ)*X 1 1+(6143019599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((196515591/400000000 : ℝ)*X 2 0+(180859337/312500000 : ℝ)*X 2 1+(-967934667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1552436409/2000000000 : ℝ)*X 0 0+(21887461/100000000 : ℝ)*X 0 1+(1534664269/10000000000 : ℝ)*X 0 2+(1552436409/2000000000 : ℝ)*X 1 0+(21887461/100000000 : ℝ)*X 1 1+(1534664269/10000000000 : ℝ)*X 1 2+(1552436409/2000000000 : ℝ)*X 2 0+(21887461/100000000 : ℝ)*X 2 1+(1534664269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1426075503/10000000000 : ℝ)*X 0 0+(5150574309/10000000000 : ℝ)*X 0 1+(2610418213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((4958946613/10000000000 : ℝ)*X 1 0+(-523673197/5000000000 : ℝ)*X 1 1+(2843768959/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((852094809/2000000000 : ℝ)*X 2 0+(6256471811/10000000000 : ℝ)*X 2 1+(-117904401/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1961089673/2500000000 : ℝ)*X 0 0+(901777687/5000000000 : ℝ)*X 0 1+(1820872509/10000000000 : ℝ)*X 0 2+(1961089673/2500000000 : ℝ)*X 1 0+(901777687/5000000000 : ℝ)*X 1 1+(1820872509/10000000000 : ℝ)*X 1 2+(1961089673/2500000000 : ℝ)*X 2 0+(901777687/5000000000 : ℝ)*X 2 1+(1820872509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328053_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((1281/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1281/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8241484145445925757680386549/2389082298700000000000000000000000 : ℝ) := by norm_num
    linear_combination (222801/200000000000 : ℝ)*(base8) + (70567813987/100000000000 : ℝ)*(base49) + (1723175408127/1000000000000 : ℝ)*(base59) + (10549366773411/1000000000000 : ℝ)*(major_s1_0) + (10549366773411/1000000000000 : ℝ)*(major_s1_1) + (10549366773411/1000000000000 : ℝ)*(major_s1_2) + (52824163/1000000000000 : ℝ)*(sp_s1_0) + (8926879/1000000000000 : ℝ)*(sp_s1_6) + (16236658975689/1000000000000 : ℝ)*(sp_s1_7) + (16236435326413/1000000000000 : ℝ)*(sp_s1_8) + (4059141278639/250000000000 : ℝ)*(sp_s1_9) + (24310052781/5000000000 : ℝ)*(sp_s1_13) + (69396861/250000000000 : ℝ)*(sp_s1_15) + (147799301/1000000000000 : ℝ)*(sp_s1_23) + (4862019483079/1000000000000 : ℝ)*(f.failure) + (16236712913857/1000000000000 : ℝ)*(f.sum) + (186368715238471243/469506200000000000000000000000 : ℝ)*base63 + (124750741934669/160900000000000000000000000 : ℝ)*base65 + (49914868417241/2042600000000000000000000000 : ℝ)*base67 + (4038756876151/16090000000000000000000000 : ℝ)*base69 + (579424149539968297/1637479300000000000000000000000 : ℝ)*base71 + (217032143068347/1017700000000000000000000000 : ℝ)*base73 + (72760012010327/291800000000000000000000000 : ℝ)*base75 + (54065968310189/254425000000000000000000000 : ℝ)*base77 + (8099383262254909921/20787540200000000000000000000000 : ℝ)*base78 + (1359/4000000000000000 : ℝ)*base86 + (1359/4000000000000000 : ℝ)*base88 + (1359/4000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26241/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26241/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5477556179599861708645177915131/309386157681650000000000000000000000 : ℝ) := by norm_num
    linear_combination (20180310329/25000000000 : ℝ)*(base49) + (1089490167899/1000000000000 : ℝ)*(base59) + (2587306077141/250000000000 : ℝ)*(major_s1_0) + (2587306077141/250000000000 : ℝ)*(major_s1_1) + (2587306077141/250000000000 : ℝ)*(major_s1_2) + (15685861/500000000000 : ℝ)*(sp_s1_2) + (11066623/62500000000 : ℝ)*(sp_s1_6) + (43781353/500000000000 : ℝ)*(sp_s1_7) + (334676393/1000000000000 : ℝ)*(sp_s1_8) + (15928577847403/1000000000000 : ℝ)*(sp_s1_14) + (15928330733717/1000000000000 : ℝ)*(sp_s1_15) + (15928634038387/1000000000000 : ℝ)*(sp_s1_16) + (4769536936507/1000000000000 : ℝ)*(sp_s1_20) + (15825751/250000000000 : ℝ)*(sp_s1_27) + (119244432637/25000000000 : ℝ)*(f.failure) + (1592866541011/100000000000 : ℝ)*(f.sum) + (631137308455400273/2171466175000000000000000000000 : ℝ)*base63 + (315120664798431/2976650000000000000000000000 : ℝ)*base65 + (140716364482943/255325000000000000000000000 : ℝ)*base67 + (8784110548711/297665000000000000000000000 : ℝ)*base68 + (1057896437069238687/7573341762500000000000000000000 : ℝ)*base71 + (51784753056299/127212500000000000000000000 : ℝ)*base72 + (30832557731197/72950000000000000000000000 : ℝ)*base75 + (54804867108721/254425000000000000000000000 : ℝ)*base77 + (2163142201866634309/5196885050000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (123/100000000000000 : ℝ)*base87 + (123/100000000000000 : ℝ)*base89 + (123/100000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6349/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6349/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4201703659924993276909963191/309386157681650000000000000000000 : ℝ) := by norm_num
    linear_combination (265183289409/1000000000000 : ℝ)*(base40) + (155583032237/250000000000 : ℝ)*(base49) + (499900395809/500000000000 : ℝ)*(base59) + (9121259833431/1000000000000 : ℝ)*(major_s1_0) + (9121259833431/1000000000000 : ℝ)*(major_s1_1) + (9121259833431/1000000000000 : ℝ)*(major_s1_2) + (90667321/1000000000000 : ℝ)*(sp_s1_0) + (47630929/200000000000 : ℝ)*(sp_s1_2) + (33472379/1000000000000 : ℝ)*(sp_s1_16) + (110729759/250000000000 : ℝ)*(sp_s1_20) + (14038594615053/1000000000000 : ℝ)*(sp_s1_21) + (7019342641187/500000000000 : ℝ)*(sp_s1_22) + (14038413655349/1000000000000 : ℝ)*(sp_s1_23) + (4203386938519/1000000000000 : ℝ)*(sp_s1_27) + (1050957464389/250000000000 : ℝ)*(f.failure) + (7019342641187/500000000000 : ℝ)*(f.sum) + (6373925339998820071/17371729400000000000000000000000 : ℝ)*base63 + (1741528686634413/5953300000000000000000000000 : ℝ)*base65 + (1173915902354001/2042600000000000000000000000 : ℝ)*base67 + (47898823235297/119066000000000000000000000 : ℝ)*base69 + (3857970931718194409/60586734100000000000000000000000 : ℝ)*base71 + (312275654217587/1017700000000000000000000000 : ℝ)*base73 + (247876593191327/291800000000000000000000000 : ℝ)*base75 + (64425786794087/127212500000000000000000000 : ℝ)*base77 + (13559234477412424099/20787540200000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1131/1000000000000000 : ℝ)*base87 + (1131/1000000000000000 : ℝ)*base89 + (1131/1000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((30531/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30531/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(30639/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(30639/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59533/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(59533/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1281/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1281/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(26241/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(26241/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6349/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6349/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c328053_s1 p hpa hpb X hX hprev0

#print axioms solution
