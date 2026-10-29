-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306055_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:14.669792+00:00
-- url     : https://prove2.me/submissions/2ead5984-43ae-46f8-91e6-59c9cef52010

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
theorem collision_support_c306055_s6_s6_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2555800693/10000000000 : ℝ)*x 0 + (1374594109/2500000000 : ℝ)*x 1 + (474231123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2555800693/10000000000 : ℝ)^135 ≤ (10455329261/62500000000 : ℝ)^103 := by
    have hnat : (2555800693 : ℕ)^135*62500000000^103 ≤ 10455329261^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555800693 10000000000 10455329261 62500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374594109/2500000000 : ℝ)^135 ≤ (4565944367037/10000000000000 : ℝ)^103 := by
    have hnat : (1374594109 : ℕ)^135*10000000000000^103 ≤ 4565944367037^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374594109 2500000000 4565944367037 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474231123/1000000000 : ℝ)^135 ≤ (37612029492177/100000000000000 : ℝ)^103 := by
    have hnat : (474231123 : ℕ)^135*100000000000000^103 ≤ 37612029492177^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474231123 1000000000 37612029492177 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2555800693/10000000000 : ℝ), (1374594109/2500000000 : ℝ), (474231123/1000000000 : ℝ)] ![(10455329261/62500000000 : ℝ), (4565944367037/10000000000000 : ℝ), (37612029492177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2555800693/10000000000 : ℝ)|^135 ≤ (10455329261/62500000000 : ℝ)^103
        have hw : |(-2555800693/10000000000 : ℝ)|=(2555800693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1374594109/2500000000 : ℝ)|^135 ≤ (4565944367037/10000000000000 : ℝ)^103
        have hw : |(1374594109/2500000000 : ℝ)|=(1374594109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(474231123/1000000000 : ℝ)|^135 ≤ (37612029492177/100000000000000 : ℝ)^103
        have hw : |(474231123/1000000000 : ℝ)|=(474231123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4741422773/10000000000 : ℝ)*x 0 + (-902852921/5000000000 : ℝ)*x 1 + (48423297/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4741422773/10000000000 : ℝ)^135 ≤ (752055881281/2000000000000 : ℝ)^103 := by
    have hnat : (4741422773 : ℕ)^135*2000000000000^103 ≤ 752055881281^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4741422773 10000000000 752055881281 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902852921/5000000000 : ℝ)^135 ≤ (10609682380567/100000000000000 : ℝ)^103 := by
    have hnat : (902852921 : ℕ)^135*100000000000000^103 ≤ 10609682380567^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902852921 5000000000 10609682380567 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (48423297/80000000 : ℝ)^135 ≤ (6473440443423/12500000000000 : ℝ)^103 := by
    have hnat : (48423297 : ℕ)^135*12500000000000^103 ≤ 6473440443423^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48423297 80000000 6473440443423 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4741422773/10000000000 : ℝ), (-902852921/5000000000 : ℝ), (48423297/80000000 : ℝ)] ![(752055881281/2000000000000 : ℝ), (10609682380567/100000000000000 : ℝ), (6473440443423/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4741422773/10000000000 : ℝ)|^135 ≤ (752055881281/2000000000000 : ℝ)^103
        have hw : |(4741422773/10000000000 : ℝ)|=(4741422773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-902852921/5000000000 : ℝ)|^135 ≤ (10609682380567/100000000000000 : ℝ)^103
        have hw : |(-902852921/5000000000 : ℝ)|=(902852921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(48423297/80000000 : ℝ)|^135 ≤ (6473440443423/12500000000000 : ℝ)^103
        have hw : |(48423297/80000000 : ℝ)|=(48423297/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (148177809/312500000 : ℝ)*x 0 + (5493270007/10000000000 : ℝ)*x 1 + (-2563028093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (148177809/312500000 : ℝ)^135 ≤ (37605570643187/100000000000000 : ℝ)^103 := by
    have hnat : (148177809 : ℕ)^135*100000000000000^103 ≤ 37605570643187^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148177809 312500000 37605570643187 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5493270007/10000000000 : ℝ)^135 ≤ (22801936392541/50000000000000 : ℝ)^103 := by
    have hnat : (5493270007 : ℕ)^135*50000000000000^103 ≤ 22801936392541^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493270007 10000000000 22801936392541 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2563028093/10000000000 : ℝ)^135 ≤ (671622262289/4000000000000 : ℝ)^103 := by
    have hnat : (2563028093 : ℕ)^135*4000000000000^103 ≤ 671622262289^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563028093 10000000000 671622262289 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(148177809/312500000 : ℝ), (5493270007/10000000000 : ℝ), (-2563028093/10000000000 : ℝ)] ![(37605570643187/100000000000000 : ℝ), (22801936392541/50000000000000 : ℝ), (671622262289/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(148177809/312500000 : ℝ)|^135 ≤ (37605570643187/100000000000000 : ℝ)^103
        have hw : |(148177809/312500000 : ℝ)|=(148177809/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5493270007/10000000000 : ℝ)|^135 ≤ (22801936392541/50000000000000 : ℝ)^103
        have hw : |(5493270007/10000000000 : ℝ)|=(5493270007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2563028093/10000000000 : ℝ)|^135 ≤ (671622262289/4000000000000 : ℝ)^103
        have hw : |(-2563028093/10000000000 : ℝ)|=(2563028093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5723599109/10000000000 : ℝ)*x 0 + (2070734277/5000000000 : ℝ)*x 1 + (2971412977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5723599109/10000000000 : ℝ)^135 ≤ (962524885013/2000000000000 : ℝ)^103 := by
    have hnat : (5723599109 : ℕ)^135*2000000000000^103 ≤ 962524885013^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5723599109 10000000000 962524885013 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070734277/5000000000 : ℝ)^135 ≤ (31492855166607/100000000000000 : ℝ)^103 := by
    have hnat : (2070734277 : ℕ)^135*100000000000000^103 ≤ 31492855166607^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070734277 5000000000 31492855166607 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2971412977/10000000000 : ℝ)^135 ≤ (10190450281713/50000000000000 : ℝ)^103 := by
    have hnat : (2971412977 : ℕ)^135*50000000000000^103 ≤ 10190450281713^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2971412977 10000000000 10190450281713 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5723599109/10000000000 : ℝ), (2070734277/5000000000 : ℝ), (2971412977/10000000000 : ℝ)] ![(962524885013/2000000000000 : ℝ), (31492855166607/100000000000000 : ℝ), (10190450281713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5723599109/10000000000 : ℝ)|^135 ≤ (962524885013/2000000000000 : ℝ)^103
        have hw : |(5723599109/10000000000 : ℝ)|=(5723599109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070734277/5000000000 : ℝ)|^135 ≤ (31492855166607/100000000000000 : ℝ)^103
        have hw : |(2070734277/5000000000 : ℝ)|=(2070734277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2971412977/10000000000 : ℝ)|^135 ≤ (10190450281713/50000000000000 : ℝ)^103
        have hw : |(2971412977/10000000000 : ℝ)|=(2971412977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2470259007/10000000000 : ℝ)*x 0 + (5208563573/10000000000 : ℝ)*x 1 + (1021826391/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2470259007/10000000000 : ℝ)^135 ≤ (15998525747013/100000000000000 : ℝ)^103 := by
    have hnat : (2470259007 : ℕ)^135*100000000000000^103 ≤ 15998525747013^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2470259007 10000000000 15998525747013 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5208563573/10000000000 : ℝ)^135 ≤ (531640467247/1250000000000 : ℝ)^103 := by
    have hnat : (5208563573 : ℕ)^135*1250000000000^103 ≤ 531640467247^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208563573 10000000000 531640467247 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021826391/2000000000 : ℝ)^135 ≤ (41470236854511/100000000000000 : ℝ)^103 := by
    have hnat : (1021826391 : ℕ)^135*100000000000000^103 ≤ 41470236854511^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021826391 2000000000 41470236854511 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2470259007/10000000000 : ℝ), (5208563573/10000000000 : ℝ), (1021826391/2000000000 : ℝ)] ![(15998525747013/100000000000000 : ℝ), (531640467247/1250000000000 : ℝ), (41470236854511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2470259007/10000000000 : ℝ)|^135 ≤ (15998525747013/100000000000000 : ℝ)^103
        have hw : |(-2470259007/10000000000 : ℝ)|=(2470259007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5208563573/10000000000 : ℝ)|^135 ≤ (531640467247/1250000000000 : ℝ)^103
        have hw : |(5208563573/10000000000 : ℝ)|=(5208563573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1021826391/2000000000 : ℝ)|^135 ≤ (41470236854511/100000000000000 : ℝ)^103
        have hw : |(1021826391/2000000000 : ℝ)|=(1021826391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1175047827/2500000000 : ℝ)*x 0 + (-1500527793/10000000000 : ℝ)*x 1 + (1258690843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1175047827/2500000000 : ℝ)^135 ≤ (37174789392589/100000000000000 : ℝ)^103 := by
    have hnat : (1175047827 : ℕ)^135*100000000000000^103 ≤ 37174789392589^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175047827 2500000000 37174789392589 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1500527793/10000000000 : ℝ)^135 ≤ (1664753202539/20000000000000 : ℝ)^103 := by
    have hnat : (1500527793 : ℕ)^135*20000000000000^103 ≤ 1664753202539^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500527793 10000000000 1664753202539 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1258690843/2000000000 : ℝ)^135 ≤ (54501444585461/100000000000000 : ℝ)^103 := by
    have hnat : (1258690843 : ℕ)^135*100000000000000^103 ≤ 54501444585461^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1258690843 2000000000 54501444585461 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1175047827/2500000000 : ℝ), (-1500527793/10000000000 : ℝ), (1258690843/2000000000 : ℝ)] ![(37174789392589/100000000000000 : ℝ), (1664753202539/20000000000000 : ℝ), (54501444585461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1175047827/2500000000 : ℝ)|^135 ≤ (37174789392589/100000000000000 : ℝ)^103
        have hw : |(1175047827/2500000000 : ℝ)|=(1175047827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1500527793/10000000000 : ℝ)|^135 ≤ (1664753202539/20000000000000 : ℝ)^103
        have hw : |(-1500527793/10000000000 : ℝ)|=(1500527793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1258690843/2000000000 : ℝ)|^135 ≤ (54501444585461/100000000000000 : ℝ)^103
        have hw : |(1258690843/2000000000 : ℝ)|=(1258690843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4700458023/10000000000 : ℝ)*x 0 + (5806559373/10000000000 : ℝ)*x 1 + (-220432633/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4700458023/10000000000 : ℝ)^135 ≤ (37177554301287/100000000000000 : ℝ)^103 := by
    have hnat : (4700458023 : ℕ)^135*100000000000000^103 ≤ 37177554301287^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4700458023 10000000000 37177554301287 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5806559373/10000000000 : ℝ)^135 ≤ (24521288221459/50000000000000 : ℝ)^103 := by
    have hnat : (5806559373 : ℕ)^135*50000000000000^103 ≤ 24521288221459^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5806559373 10000000000 24521288221459 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220432633/1000000000 : ℝ)^135 ≤ (13779869230387/100000000000000 : ℝ)^103 := by
    have hnat : (220432633 : ℕ)^135*100000000000000^103 ≤ 13779869230387^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220432633 1000000000 13779869230387 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4700458023/10000000000 : ℝ), (5806559373/10000000000 : ℝ), (-220432633/1000000000 : ℝ)] ![(37177554301287/100000000000000 : ℝ), (24521288221459/50000000000000 : ℝ), (13779869230387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4700458023/10000000000 : ℝ)|^135 ≤ (37177554301287/100000000000000 : ℝ)^103
        have hw : |(4700458023/10000000000 : ℝ)|=(4700458023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5806559373/10000000000 : ℝ)|^135 ≤ (24521288221459/50000000000000 : ℝ)^103
        have hw : |(5806559373/10000000000 : ℝ)|=(5806559373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220432633/1000000000 : ℝ)|^135 ≤ (13779869230387/100000000000000 : ℝ)^103
        have hw : |(-220432633/1000000000 : ℝ)|=(220432633/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1384859381/2500000000 : ℝ)*x 0 + (237904371/500000000 : ℝ)*x 1 + (1242102723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1384859381/2500000000 : ℝ)^135 ≤ (23053437193371/50000000000000 : ℝ)^103 := by
    have hnat : (1384859381 : ℕ)^135*50000000000000^103 ≤ 23053437193371^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1384859381 2500000000 23053437193371 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (237904371/500000000 : ℝ)^135 ≤ (37776110980649/100000000000000 : ℝ)^103 := by
    have hnat : (237904371 : ℕ)^135*100000000000000^103 ≤ 37776110980649^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237904371 500000000 37776110980649 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1242102723/5000000000 : ℝ)^135 ≤ (1007313413753/6250000000000 : ℝ)^103 := by
    have hnat : (1242102723 : ℕ)^135*6250000000000^103 ≤ 1007313413753^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242102723 5000000000 1007313413753 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1384859381/2500000000 : ℝ), (237904371/500000000 : ℝ), (1242102723/5000000000 : ℝ)] ![(23053437193371/50000000000000 : ℝ), (37776110980649/100000000000000 : ℝ), (1007313413753/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1384859381/2500000000 : ℝ)|^135 ≤ (23053437193371/50000000000000 : ℝ)^103
        have hw : |(1384859381/2500000000 : ℝ)|=(1384859381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(237904371/500000000 : ℝ)|^135 ≤ (37776110980649/100000000000000 : ℝ)^103
        have hw : |(237904371/500000000 : ℝ)|=(237904371/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1242102723/5000000000 : ℝ)|^135 ≤ (1007313413753/6250000000000 : ℝ)^103
        have hw : |(1242102723/5000000000 : ℝ)|=(1242102723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1081858879/5000000000 : ℝ)*x 0 + (5412589181/10000000000 : ℝ)*x 1 + (5142341809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081858879/5000000000 : ℝ)^135 ≤ (6724050976579/50000000000000 : ℝ)^103 := by
    have hnat : (1081858879 : ℕ)^135*50000000000000^103 ≤ 6724050976579^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081858879 5000000000 6724050976579 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412589181/10000000000 : ℝ)^135 ≤ (11181999356871/25000000000000 : ℝ)^103 := by
    have hnat : (5412589181 : ℕ)^135*25000000000000^103 ≤ 11181999356871^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412589181 10000000000 11181999356871 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5142341809/10000000000 : ℝ)^135 ≤ (41823900606653/100000000000000 : ℝ)^103 := by
    have hnat : (5142341809 : ℕ)^135*100000000000000^103 ≤ 41823900606653^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5142341809 10000000000 41823900606653 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1081858879/5000000000 : ℝ), (5412589181/10000000000 : ℝ), (5142341809/10000000000 : ℝ)] ![(6724050976579/50000000000000 : ℝ), (11181999356871/25000000000000 : ℝ), (41823900606653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1081858879/5000000000 : ℝ)|^135 ≤ (6724050976579/50000000000000 : ℝ)^103
        have hw : |(-1081858879/5000000000 : ℝ)|=(1081858879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412589181/10000000000 : ℝ)|^135 ≤ (11181999356871/25000000000000 : ℝ)^103
        have hw : |(5412589181/10000000000 : ℝ)|=(5412589181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5142341809/10000000000 : ℝ)|^135 ≤ (41823900606653/100000000000000 : ℝ)^103
        have hw : |(5142341809/10000000000 : ℝ)|=(5142341809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2259705557/5000000000 : ℝ)*x 0 + (-1755466493/10000000000 : ℝ)*x 1 + (6290110231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2259705557/5000000000 : ℝ)^135 ≤ (1412481614293/4000000000000 : ℝ)^103 := by
    have hnat : (2259705557 : ℕ)^135*4000000000000^103 ≤ 1412481614293^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259705557 5000000000 1412481614293 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1755466493/10000000000 : ℝ)^135 ≤ (5112233923459/50000000000000 : ℝ)^103 := by
    have hnat : (1755466493 : ℕ)^135*50000000000000^103 ≤ 5112233923459^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755466493 10000000000 5112233923459 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6290110231/10000000000 : ℝ)^135 ≤ (1701984118303/3125000000000 : ℝ)^103 := by
    have hnat : (6290110231 : ℕ)^135*3125000000000^103 ≤ 1701984118303^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6290110231 10000000000 1701984118303 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2259705557/5000000000 : ℝ), (-1755466493/10000000000 : ℝ), (6290110231/10000000000 : ℝ)] ![(1412481614293/4000000000000 : ℝ), (5112233923459/50000000000000 : ℝ), (1701984118303/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2259705557/5000000000 : ℝ)|^135 ≤ (1412481614293/4000000000000 : ℝ)^103
        have hw : |(2259705557/5000000000 : ℝ)|=(2259705557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1755466493/10000000000 : ℝ)|^135 ≤ (5112233923459/50000000000000 : ℝ)^103
        have hw : |(-1755466493/10000000000 : ℝ)|=(1755466493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6290110231/10000000000 : ℝ)|^135 ≤ (1701984118303/3125000000000 : ℝ)^103
        have hw : |(6290110231/10000000000 : ℝ)|=(6290110231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (642735109/1250000000 : ℝ)*x 0 + (1351868881/2500000000 : ℝ)*x 1 + (-542778753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (642735109/1250000000 : ℝ)^135 ≤ (10454746763369/25000000000000 : ℝ)^103 := by
    have hnat : (642735109 : ℕ)^135*25000000000000^103 ≤ 10454746763369^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642735109 1250000000 10454746763369 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351868881/2500000000 : ℝ)^135 ≤ (11168154808913/25000000000000 : ℝ)^103 := by
    have hnat : (1351868881 : ℕ)^135*25000000000000^103 ≤ 11168154808913^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351868881 2500000000 11168154808913 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542778753/2500000000 : ℝ)^135 ≤ (6754196849371/50000000000000 : ℝ)^103 := by
    have hnat : (542778753 : ℕ)^135*50000000000000^103 ≤ 6754196849371^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542778753 2500000000 6754196849371 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(642735109/1250000000 : ℝ), (1351868881/2500000000 : ℝ), (-542778753/2500000000 : ℝ)] ![(10454746763369/25000000000000 : ℝ), (11168154808913/25000000000000 : ℝ), (6754196849371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(642735109/1250000000 : ℝ)|^135 ≤ (10454746763369/25000000000000 : ℝ)^103
        have hw : |(642735109/1250000000 : ℝ)|=(642735109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351868881/2500000000 : ℝ)|^135 ≤ (11168154808913/25000000000000 : ℝ)^103
        have hw : |(1351868881/2500000000 : ℝ)|=(1351868881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542778753/2500000000 : ℝ)|^135 ≤ (6754196849371/50000000000000 : ℝ)^103
        have hw : |(-542778753/2500000000 : ℝ)|=(542778753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6197188207/10000000000 : ℝ)*x 0 + (2016303563/5000000000 : ℝ)*x 1 + (2491174617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6197188207/10000000000 : ℝ)^135 ≤ (52159552267/97656250000 : ℝ)^103 := by
    have hnat : (6197188207 : ℕ)^135*97656250000^103 ≤ 52159552267^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6197188207 10000000000 52159552267 97656250000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016303563/5000000000 : ℝ)^135 ≤ (3041231624713/10000000000000 : ℝ)^103 := by
    have hnat : (2016303563 : ℕ)^135*10000000000000^103 ≤ 3041231624713^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016303563 5000000000 3041231624713 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2491174617/10000000000 : ℝ)^135 ≤ (8088151108829/50000000000000 : ℝ)^103 := by
    have hnat : (2491174617 : ℕ)^135*50000000000000^103 ≤ 8088151108829^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2491174617 10000000000 8088151108829 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6197188207/10000000000 : ℝ), (2016303563/5000000000 : ℝ), (2491174617/10000000000 : ℝ)] ![(52159552267/97656250000 : ℝ), (3041231624713/10000000000000 : ℝ), (8088151108829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6197188207/10000000000 : ℝ)|^135 ≤ (52159552267/97656250000 : ℝ)^103
        have hw : |(6197188207/10000000000 : ℝ)|=(6197188207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016303563/5000000000 : ℝ)|^135 ≤ (3041231624713/10000000000000 : ℝ)^103
        have hw : |(2016303563/5000000000 : ℝ)|=(2016303563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2491174617/10000000000 : ℝ)|^135 ≤ (8088151108829/50000000000000 : ℝ)^103
        have hw : |(2491174617/10000000000 : ℝ)|=(2491174617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-437972731/2000000000 : ℝ)*x 0 + (5809043271/10000000000 : ℝ)*x 1 + (2354611003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (437972731/2000000000 : ℝ)^135 ≤ (6830745634817/50000000000000 : ℝ)^103 := by
    have hnat : (437972731 : ℕ)^135*50000000000000^103 ≤ 6830745634817^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437972731 2000000000 6830745634817 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5809043271/10000000000 : ℝ)^135 ≤ (9814015046317/20000000000000 : ℝ)^103 := by
    have hnat : (5809043271 : ℕ)^135*20000000000000^103 ≤ 9814015046317^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5809043271 10000000000 9814015046317 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2354611003/5000000000 : ℝ)^135 ≤ (37268433485753/100000000000000 : ℝ)^103 := by
    have hnat : (2354611003 : ℕ)^135*100000000000000^103 ≤ 37268433485753^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2354611003 5000000000 37268433485753 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-437972731/2000000000 : ℝ), (5809043271/10000000000 : ℝ), (2354611003/5000000000 : ℝ)] ![(6830745634817/50000000000000 : ℝ), (9814015046317/20000000000000 : ℝ), (37268433485753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-437972731/2000000000 : ℝ)|^135 ≤ (6830745634817/50000000000000 : ℝ)^103
        have hw : |(-437972731/2000000000 : ℝ)|=(437972731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5809043271/10000000000 : ℝ)|^135 ≤ (9814015046317/20000000000000 : ℝ)^103
        have hw : |(5809043271/10000000000 : ℝ)|=(5809043271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2354611003/5000000000 : ℝ)|^135 ≤ (37268433485753/100000000000000 : ℝ)^103
        have hw : |(2354611003/5000000000 : ℝ)|=(2354611003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (255773441/500000000 : ℝ)*x 0 + (-375788697/2500000000 : ℝ)*x 1 + (5903587491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255773441/500000000 : ℝ)^135 ≤ (41537665438271/100000000000000 : ℝ)^103 := by
    have hnat : (255773441 : ℕ)^135*100000000000000^103 ≤ 41537665438271^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255773441 500000000 41537665438271 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375788697/2500000000 : ℝ)^135 ≤ (834287112763/10000000000000 : ℝ)^103 := by
    have hnat : (375788697 : ℕ)^135*10000000000000^103 ≤ 834287112763^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375788697 2500000000 834287112763 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5903587491/10000000000 : ℝ)^135 ≤ (50119463424479/100000000000000 : ℝ)^103 := by
    have hnat : (5903587491 : ℕ)^135*100000000000000^103 ≤ 50119463424479^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5903587491 10000000000 50119463424479 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(255773441/500000000 : ℝ), (-375788697/2500000000 : ℝ), (5903587491/10000000000 : ℝ)] ![(41537665438271/100000000000000 : ℝ), (834287112763/10000000000000 : ℝ), (50119463424479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(255773441/500000000 : ℝ)|^135 ≤ (41537665438271/100000000000000 : ℝ)^103
        have hw : |(255773441/500000000 : ℝ)|=(255773441/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-375788697/2500000000 : ℝ)|^135 ≤ (834287112763/10000000000000 : ℝ)^103
        have hw : |(-375788697/2500000000 : ℝ)|=(375788697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5903587491/10000000000 : ℝ)|^135 ≤ (50119463424479/100000000000000 : ℝ)^103
        have hw : |(5903587491/10000000000 : ℝ)|=(5903587491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4493870899/10000000000 : ℝ)*x 0 + (1450983261/2500000000 : ℝ)*x 1 + (-1231431843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493870899/10000000000 : ℝ)^135 ≤ (3505071584927/10000000000000 : ℝ)^103 := by
    have hnat : (4493870899 : ℕ)^135*10000000000000^103 ≤ 3505071584927^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493870899 10000000000 3505071584927 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1450983261/2500000000 : ℝ)^135 ≤ (49013504800951/100000000000000 : ℝ)^103 := by
    have hnat : (1450983261 : ℕ)^135*100000000000000^103 ≤ 49013504800951^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1450983261 2500000000 49013504800951 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1231431843/5000000000 : ℝ)^135 ≤ (15935779335587/100000000000000 : ℝ)^103 := by
    have hnat : (1231431843 : ℕ)^135*100000000000000^103 ≤ 15935779335587^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231431843 5000000000 15935779335587 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493870899/10000000000 : ℝ), (1450983261/2500000000 : ℝ), (-1231431843/5000000000 : ℝ)] ![(3505071584927/10000000000000 : ℝ), (49013504800951/100000000000000 : ℝ), (15935779335587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493870899/10000000000 : ℝ)|^135 ≤ (3505071584927/10000000000000 : ℝ)^103
        have hw : |(4493870899/10000000000 : ℝ)|=(4493870899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1450983261/2500000000 : ℝ)|^135 ≤ (49013504800951/100000000000000 : ℝ)^103
        have hw : |(1450983261/2500000000 : ℝ)|=(1450983261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1231431843/5000000000 : ℝ)|^135 ≤ (15935779335587/100000000000000 : ℝ)^103
        have hw : |(-1231431843/5000000000 : ℝ)|=(1231431843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306055_s6_s6_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6250963377/10000000000 : ℝ)*x 0 + (701371159/2000000000 : ℝ)*x 1 + (3001997313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6250963377/10000000000 : ℝ)^135 ≤ (13504914599721/25000000000000 : ℝ)^103 := by
    have hnat : (6250963377 : ℕ)^135*25000000000000^103 ≤ 13504914599721^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6250963377 10000000000 13504914599721 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701371159/2000000000 : ℝ)^135 ≤ (12662025514309/50000000000000 : ℝ)^103 := by
    have hnat : (701371159 : ℕ)^135*50000000000000^103 ≤ 12662025514309^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701371159 2000000000 12662025514309 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3001997313/10000000000 : ℝ)^135 ≤ (10328145278767/50000000000000 : ℝ)^103 := by
    have hnat : (3001997313 : ℕ)^135*50000000000000^103 ≤ 10328145278767^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001997313 10000000000 10328145278767 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6250963377/10000000000 : ℝ), (701371159/2000000000 : ℝ), (3001997313/10000000000 : ℝ)] ![(13504914599721/25000000000000 : ℝ), (12662025514309/50000000000000 : ℝ), (10328145278767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6250963377/10000000000 : ℝ)|^135 ≤ (13504914599721/25000000000000 : ℝ)^103
        have hw : |(6250963377/10000000000 : ℝ)|=(6250963377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(701371159/2000000000 : ℝ)|^135 ≤ (12662025514309/50000000000000 : ℝ)^103
        have hw : |(701371159/2000000000 : ℝ)|=(701371159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3001997313/10000000000 : ℝ)|^135 ≤ (10328145278767/50000000000000 : ℝ)^103
        have hw : |(3001997313/10000000000 : ℝ)|=(3001997313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306055_s6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((1951/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1951/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39967/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39967/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39931/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39931/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4473/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4473/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11367/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11367/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (1951/5000 : ℝ) ^ (67/16 : ℝ) ≤ (1943190696147884721/100000000000000000000 : ℝ) := by
    have hpowers : (1951/5000 : ℝ)^67 ≤ (1943190696147884721/100000000000000000000 : ℝ)^16 := by
      have hnat : (1951 : ℕ)^67*100000000000000000000^16 ≤ 1943190696147884721^16*5000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1951 5000 1943190696147884721 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1951/5000 : ℝ)) (X := (1943190696147884721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner0a : (101943190696147884721/100000000000000000000 : ℝ) ≤ (2009213044384127/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (101943190696147884721/100000000000000000000 : ℝ)^16 ≤ (2009213044384127/2000000000000000 : ℝ)^67 := by
      have hnat : (101943190696147884721 : ℕ)^16*2000000000000000^67 ≤ 2009213044384127^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101943190696147884721 100000000000000000000 2009213044384127 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2009213044384127/2000000000000000 : ℝ)) (X := (101943190696147884721/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner0b : (51943190696147884721/50000000000000000000 : ℝ) ≤ (2018293366162709/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (51943190696147884721/50000000000000000000 : ℝ)^16 ≤ (2018293366162709/2000000000000000 : ℝ)^67 := by
      have hnat : (51943190696147884721 : ℕ)^16*2000000000000000^67 ≤ 2018293366162709^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51943190696147884721 50000000000000000000 2018293366162709 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2018293366162709/2000000000000000 : ℝ)) (X := (51943190696147884721/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(9213044384127/780400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4540160889291/390200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (1951/5000 : ℝ)) (alpha := (9213044384127/780400000000000 : ℝ)) (beta := (4540160889291/390200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1951/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(9213044384127/780400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4540160889291/390200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (39967/100000 : ℝ) ^ (67/16 : ℝ) ≤ (429689991840341243/20000000000000000000 : ℝ) := by
    have hpowers : (39967/100000 : ℝ)^67 ≤ (429689991840341243/20000000000000000000 : ℝ)^16 := by
      have hnat : (39967 : ℕ)^67*20000000000000000000^16 ≤ 429689991840341243^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39967 100000 429689991840341243 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39967/100000 : ℝ)) (X := (429689991840341243/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner1a : (20429689991840341243/20000000000000000000 : ℝ) ≤ (201017839075711/200000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (20429689991840341243/20000000000000000000 : ℝ)^16 ≤ (201017839075711/200000000000000 : ℝ)^67 := by
      have hnat : (20429689991840341243 : ℕ)^16*200000000000000^67 ≤ 201017839075711^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20429689991840341243 20000000000000000000 201017839075711 200000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201017839075711/200000000000000 : ℝ)) (X := (20429689991840341243/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner1b : (10429689991840341243/10000000000000000000 : ℝ) ≤ (5050487769005471/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (10429689991840341243/10000000000000000000 : ℝ)^16 ≤ (5050487769005471/5000000000000000 : ℝ)^67 := by
      have hnat : (10429689991840341243 : ℕ)^16*5000000000000000^67 ≤ 5050487769005471^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10429689991840341243 10000000000000000000 5050487769005471 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050487769005471/5000000000000000 : ℝ)) (X := (10429689991840341243/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1017839075711/79934000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(3130224014087/249793750000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (39967/100000 : ℝ)) (alpha := (1017839075711/79934000000000 : ℝ)) (beta := (3130224014087/249793750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (39967/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1017839075711/79934000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(3130224014087/249793750000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (39931/100000 : ℝ) ^ (67/16 : ℝ) ≤ (133772370533898637/6250000000000000000 : ℝ) := by
    have hpowers : (39931/100000 : ℝ)^67 ≤ (133772370533898637/6250000000000000000 : ℝ)^16 := by
      have hnat : (39931 : ℕ)^67*6250000000000000000^16 ≤ 133772370533898637^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39931 100000 133772370533898637 6250000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39931/100000 : ℝ)) (X := (133772370533898637/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner2a : (6383772370533898637/6250000000000000000 : ℝ) ≤ (10050701807162201/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (6383772370533898637/6250000000000000000 : ℝ)^16 ≤ (10050701807162201/10000000000000000 : ℝ)^67 := by
      have hnat : (6383772370533898637 : ℕ)^16*10000000000000000^67 ≤ 10050701807162201^67*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6383772370533898637 6250000000000000000 10050701807162201 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050701807162201/10000000000000000 : ℝ)) (X := (6383772370533898637/6250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner2b : (3258772370533898637/3125000000000000000 : ℝ) ≤ (2020120242355373/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3258772370533898637/3125000000000000000 : ℝ)^16 ≤ (2020120242355373/2000000000000000 : ℝ)^67 := by
      have hnat : (3258772370533898637 : ℕ)^16*2000000000000000^67 ≤ 2020120242355373^67*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3258772370533898637 3125000000000000000 2020120242355373 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2020120242355373/2000000000000000 : ℝ)) (X := (3258772370533898637/3125000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(50701807162201/3993100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(6237425576833/499137500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (39931/100000 : ℝ)) (alpha := (50701807162201/3993100000000000 : ℝ)) (beta := (6237425576833/499137500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39931/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(50701807162201/3993100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(6237425576833/499137500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-2555800693/10000000000 : ℝ)*X 0 0+(1374594109/2500000000 : ℝ)*X 0 1+(474231123/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((4741422773/10000000000 : ℝ)*X 1 0+(-902852921/5000000000 : ℝ)*X 1 1+(48423297/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((148177809/312500000 : ℝ)*X 2 0+(5493270007/10000000000 : ℝ)*X 2 1+(-2563028093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((5723599109/10000000000 : ℝ)*X 0 0+(2070734277/5000000000 : ℝ)*X 0 1+(2971412977/10000000000 : ℝ)*X 0 2+(5723599109/10000000000 : ℝ)*X 1 0+(2070734277/5000000000 : ℝ)*X 1 1+(2971412977/10000000000 : ℝ)*X 1 2+(5723599109/10000000000 : ℝ)*X 2 0+(2070734277/5000000000 : ℝ)*X 2 1+(2971412977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-2470259007/10000000000 : ℝ)*X 0 0+(5208563573/10000000000 : ℝ)*X 0 1+(1021826391/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((1175047827/2500000000 : ℝ)*X 1 0+(-1500527793/10000000000 : ℝ)*X 1 1+(1258690843/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((4700458023/10000000000 : ℝ)*X 2 0+(5806559373/10000000000 : ℝ)*X 2 1+(-220432633/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((1384859381/2500000000 : ℝ)*X 0 0+(237904371/500000000 : ℝ)*X 0 1+(1242102723/5000000000 : ℝ)*X 0 2+(1384859381/2500000000 : ℝ)*X 1 0+(237904371/500000000 : ℝ)*X 1 1+(1242102723/5000000000 : ℝ)*X 1 2+(1384859381/2500000000 : ℝ)*X 2 0+(237904371/500000000 : ℝ)*X 2 1+(1242102723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-1081858879/5000000000 : ℝ)*X 0 0+(5412589181/10000000000 : ℝ)*X 0 1+(5142341809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((2259705557/5000000000 : ℝ)*X 1 0+(-1755466493/10000000000 : ℝ)*X 1 1+(6290110231/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((642735109/1250000000 : ℝ)*X 2 0+(1351868881/2500000000 : ℝ)*X 2 1+(-542778753/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((6197188207/10000000000 : ℝ)*X 0 0+(2016303563/5000000000 : ℝ)*X 0 1+(2491174617/10000000000 : ℝ)*X 0 2+(6197188207/10000000000 : ℝ)*X 1 0+(2016303563/5000000000 : ℝ)*X 1 1+(2491174617/10000000000 : ℝ)*X 1 2+(6197188207/10000000000 : ℝ)*X 2 0+(2016303563/5000000000 : ℝ)*X 2 1+(2491174617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-437972731/2000000000 : ℝ)*X 0 0+(5809043271/10000000000 : ℝ)*X 0 1+(2354611003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((255773441/500000000 : ℝ)*X 1 0+(-375788697/2500000000 : ℝ)*X 1 1+(5903587491/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((4493870899/10000000000 : ℝ)*X 2 0+(1450983261/2500000000 : ℝ)*X 2 1+(-1231431843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((6250963377/10000000000 : ℝ)*X 0 0+(701371159/2000000000 : ℝ)*X 0 1+(3001997313/10000000000 : ℝ)*X 0 2+(6250963377/10000000000 : ℝ)*X 1 0+(701371159/2000000000 : ℝ)*X 1 1+(3001997313/10000000000 : ℝ)*X 1 2+(6250963377/10000000000 : ℝ)*X 2 0+(701371159/2000000000 : ℝ)*X 2 1+(3001997313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306055_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((4473/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4473/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (295699865315032562387277093/39898056925000000000000000000000 : ℝ) := by norm_num
    linear_combination (166721289827/100000000000 : ℝ)*(base49) + (133021/100000000000 : ℝ)*(base60) + (12269124413341/1000000000000 : ℝ)*(major_s6_0) + (12269124413341/1000000000000 : ℝ)*(major_s6_1) + (12269124413341/1000000000000 : ℝ)*(major_s6_2) + (140845671/1000000000000 : ℝ)*(sp_s6_0) + (1693269/40000000000 : ℝ)*(sp_s6_2) + (46259037/1000000000000 : ℝ)*(sp_s6_6) + (3316150486963/200000000000 : ℝ)*(sp_s6_7) + (16580740995363/1000000000000 : ℝ)*(sp_s6_8) + (16580700745827/1000000000000 : ℝ)*(sp_s6_9) + (795730681669/100000000000 : ℝ)*(sp_s6_13) + (38071281/250000000000 : ℝ)*(sp_s6_15) + (30040587/200000000000 : ℝ)*(sp_s6_23) + (7957353075727/1000000000000 : ℝ)*(f.failure) + (8290446640243/500000000000 : ℝ)*(f.sum) + (41921777592680875747/159592227700000000000000000000000 : ℝ)*base63 + (497315396489117/1996550000000000000000000000 : ℝ)*base65 + (754930878363/975756835937500000000000 : ℝ)*base67 + (729641462231311/3993100000000000000000000000 : ℝ)*base69 + (1139586153764075033/31162152400000000000000000000000 : ℝ)*base71 + (77406199622329/390200000000000000000000000 : ℝ)*base72 + (1570315075719/199835000000000000000000000 : ℝ)*base74 + (98787689513053/780400000000000000000000000 : ℝ)*base76 + (9632540149674682273/15595123400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (28389/50000000000000000 : ℝ)*base86 + (28389/50000000000000000 : ℝ)*base88 + (28389/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23167/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3475769555491827387968417334903/622728872485400000000000000000000000 : ℝ) := by norm_num
    linear_combination (576537/250000000000 : ℝ)*(base39) + (389320593443/250000000000 : ℝ)*(base49) + (13593/1000000000000 : ℝ)*(base59) + (11892530659423/1000000000000 : ℝ)*(major_s6_0) + (11892530659423/1000000000000 : ℝ)*(major_s6_1) + (11892530659423/1000000000000 : ℝ)*(major_s6_2) + (3504541/200000000000 : ℝ)*(sp_s6_1) + (710867/100000000000 : ℝ)*(sp_s6_2) + (5938343/50000000000 : ℝ)*(sp_s6_7) + (8035917007749/500000000000 : ℝ)*(sp_s6_14) + (16071935259653/1000000000000 : ℝ)*(sp_s6_15) + (16071945673687/1000000000000 : ℝ)*(sp_s6_16) + (3856518490013/500000000000 : ℝ)*(sp_s6_20) + (69695951/1000000000000 : ℝ)*(sp_s6_27) + (3856553337989/500000000000 : ℝ)*(f.failure) + (8035976391179/500000000000 : ℝ)*(f.sum) + (89689302707276629541/159592227700000000000000000000000 : ℝ)*base63 + (575249332623109/1996550000000000000000000000 : ℝ)*base64 + (179572042501947/1998350000000000000000000000 : ℝ)*base67 + (906905327848063/3993100000000000000000000000 : ℝ)*base69 + (1384643219714467659/31162152400000000000000000000000 : ℝ)*base71 + (168676296061367/390200000000000000000000000 : ℝ)*base72 + (144124463661777/199835000000000000000000000 : ℝ)*base75 + (440359056296761/780400000000000000000000000 : ℝ)*base77 + (2496162368811513441/15595123400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (10977/25000000000000000 : ℝ)*base87 + (10977/25000000000000000 : ℝ)*base89 + (10977/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11367/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11367/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3522564119475249190851840475737/622728872485400000000000000000000000 : ℝ) := by norm_num
    linear_combination (1980111/500000000000 : ℝ)*(base40) + (1633069830969/1000000000000 : ℝ)*(base49) + (335341/1000000000000 : ℝ)*(base59) + (11899015839581/1000000000000 : ℝ)*(major_s6_0) + (11899015839581/1000000000000 : ℝ)*(major_s6_1) + (11899015839581/1000000000000 : ℝ)*(major_s6_2) + (3835567/40000000000 : ℝ)*(sp_s6_0) + (2879027/50000000000 : ℝ)*(sp_s6_1) + (38155237/500000000000 : ℝ)*(sp_s6_2) + (5418109/50000000000 : ℝ)*(sp_s6_20) + (16080621152569/1000000000000 : ℝ)*(sp_s6_21) + (4020164865301/250000000000 : ℝ)*(sp_s6_22) + (16080640731269/1000000000000 : ℝ)*(sp_s6_23) + (3858602194839/500000000000 : ℝ)*(sp_s6_27) + (7717312751859/1000000000000 : ℝ)*(f.failure) + (1005044815109/62500000000 : ℝ)*(f.sum) + (100354348659240357357/159592227700000000000000000000000 : ℝ)*base63 + (315834283786903/1996550000000000000000000000 : ℝ)*base64 + (287408237672803/999175000000000000000000000 : ℝ)*base66 + (868710338568321/3993100000000000000000000000 : ℝ)*base69 + (16387990591841942113/31162152400000000000000000000000 : ℝ)*base71 + (151724433093689/390200000000000000000000000 : ℝ)*base72 + (34400634894819/49958750000000000000000000 : ℝ)*base75 + (630290289505027/780400000000000000000000000 : ℝ)*base77 + (6031807400624027367/15595123400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (15887/50000000000000000 : ℝ)*base87 + (15887/50000000000000000 : ℝ)*base89 + (15887/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((1951/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1951/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39967/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(39967/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39931/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39931/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4473/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4473/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23167/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23167/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11367/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11367/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306055_s6 p hpa hpb X hX hprev5

#print axioms solution
