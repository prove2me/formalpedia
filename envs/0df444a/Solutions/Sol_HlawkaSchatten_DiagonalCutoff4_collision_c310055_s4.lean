-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310055_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:27:06.39398+00:00
-- url     : https://prove2.me/submissions/be9b8581-04d3-42bd-ad51-6364eb0e7a8c

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
theorem collision_support_c310055_s4_s4_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1197222803/5000000000 : ℝ)*x 0 + (2749086949/5000000000 : ℝ)*x 1 + (4725980479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1197222803/5000000000 : ℝ)^71 ≤ (246848268707/1562500000000 : ℝ)^55 := by
    have hnat : (1197222803 : ℕ)^71*1562500000000^55 ≤ 246848268707^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197222803 5000000000 246848268707 1562500000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749086949/5000000000 : ℝ)^71 ≤ (23100196161787/50000000000000 : ℝ)^55 := by
    have hnat : (2749086949 : ℕ)^71*50000000000000^55 ≤ 23100196161787^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749086949 5000000000 23100196161787 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4725980479/10000000000 : ℝ)^71 ≤ (19000659229959/50000000000000 : ℝ)^55 := by
    have hnat : (4725980479 : ℕ)^71*50000000000000^55 ≤ 19000659229959^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4725980479 10000000000 19000659229959 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1197222803/5000000000 : ℝ), (2749086949/5000000000 : ℝ), (4725980479/10000000000 : ℝ)] ![(246848268707/1562500000000 : ℝ), (23100196161787/50000000000000 : ℝ), (19000659229959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1197222803/5000000000 : ℝ)|^71 ≤ (246848268707/1562500000000 : ℝ)^55
        have hw : |(-1197222803/5000000000 : ℝ)|=(1197222803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749086949/5000000000 : ℝ)|^71 ≤ (23100196161787/50000000000000 : ℝ)^55
        have hw : |(2749086949/5000000000 : ℝ)|=(2749086949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4725980479/10000000000 : ℝ)|^71 ≤ (19000659229959/50000000000000 : ℝ)^55
        have hw : |(4725980479/10000000000 : ℝ)|=(4725980479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4724464989/10000000000 : ℝ)*x 0 + (-325451127/2000000000 : ℝ)*x 1 + (6063213973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4724464989/10000000000 : ℝ)^71 ≤ (37985588224703/100000000000000 : ℝ)^55 := by
    have hnat : (4724464989 : ℕ)^71*100000000000000^55 ≤ 37985588224703^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724464989 10000000000 37985588224703 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325451127/2000000000 : ℝ)^71 ≤ (9595356240733/100000000000000 : ℝ)^55 := by
    have hnat : (325451127 : ℕ)^71*100000000000000^55 ≤ 9595356240733^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325451127 2000000000 9595356240733 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6063213973/10000000000 : ℝ)^71 ≤ (26209527759917/50000000000000 : ℝ)^55 := by
    have hnat : (6063213973 : ℕ)^71*50000000000000^55 ≤ 26209527759917^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6063213973 10000000000 26209527759917 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4724464989/10000000000 : ℝ), (-325451127/2000000000 : ℝ), (6063213973/10000000000 : ℝ)] ![(37985588224703/100000000000000 : ℝ), (9595356240733/100000000000000 : ℝ), (26209527759917/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4724464989/10000000000 : ℝ)|^71 ≤ (37985588224703/100000000000000 : ℝ)^55
        have hw : |(4724464989/10000000000 : ℝ)|=(4724464989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-325451127/2000000000 : ℝ)|^71 ≤ (9595356240733/100000000000000 : ℝ)^55
        have hw : |(-325451127/2000000000 : ℝ)|=(325451127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6063213973/10000000000 : ℝ)|^71 ≤ (26209527759917/50000000000000 : ℝ)^55
        have hw : |(6063213973/10000000000 : ℝ)|=(6063213973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4724949737/10000000000 : ℝ)*x 0 + (686747527/1250000000 : ℝ)*x 1 + (-2401039453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4724949737/10000000000 : ℝ)^71 ≤ (18995309786529/50000000000000 : ℝ)^55 := by
    have hnat : (4724949737 : ℕ)^71*50000000000000^55 ≤ 18995309786529^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4724949737 10000000000 18995309786529 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686747527/1250000000 : ℝ)^71 ≤ (9230981423791/20000000000000 : ℝ)^55 := by
    have hnat : (686747527 : ℕ)^71*20000000000000^55 ≤ 9230981423791^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686747527 1250000000 9230981423791 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2401039453/10000000000 : ℝ)^71 ≤ (1981809162011/12500000000000 : ℝ)^55 := by
    have hnat : (2401039453 : ℕ)^71*12500000000000^55 ≤ 1981809162011^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2401039453 10000000000 1981809162011 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4724949737/10000000000 : ℝ), (686747527/1250000000 : ℝ), (-2401039453/10000000000 : ℝ)] ![(18995309786529/50000000000000 : ℝ), (9230981423791/20000000000000 : ℝ), (1981809162011/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4724949737/10000000000 : ℝ)|^71 ≤ (18995309786529/50000000000000 : ℝ)^55
        have hw : |(4724949737/10000000000 : ℝ)|=(4724949737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686747527/1250000000 : ℝ)|^71 ≤ (9230981423791/20000000000000 : ℝ)^55
        have hw : |(686747527/1250000000 : ℝ)|=(686747527/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2401039453/10000000000 : ℝ)|^71 ≤ (1981809162011/12500000000000 : ℝ)^55
        have hw : |(-2401039453/10000000000 : ℝ)|=(2401039453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2901448731/5000000000 : ℝ)*x 0 + (4063999503/10000000000 : ℝ)*x 1 + (696031783/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2901448731/5000000000 : ℝ)^71 ≤ (24766067522761/50000000000000 : ℝ)^55 := by
    have hnat : (2901448731 : ℕ)^71*50000000000000^55 ≤ 24766067522761^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2901448731 5000000000 24766067522761 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4063999503/10000000000 : ℝ)^71 ≤ (15637405968907/50000000000000 : ℝ)^55 := by
    have hnat : (4063999503 : ℕ)^71*50000000000000^55 ≤ 15637405968907^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4063999503 10000000000 15637405968907 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696031783/2500000000 : ℝ)^71 ≤ (19193053004957/100000000000000 : ℝ)^55 := by
    have hnat : (696031783 : ℕ)^71*100000000000000^55 ≤ 19193053004957^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696031783 2500000000 19193053004957 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2901448731/5000000000 : ℝ), (4063999503/10000000000 : ℝ), (696031783/2500000000 : ℝ)] ![(24766067522761/50000000000000 : ℝ), (15637405968907/50000000000000 : ℝ), (19193053004957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2901448731/5000000000 : ℝ)|^71 ≤ (24766067522761/50000000000000 : ℝ)^55
        have hw : |(2901448731/5000000000 : ℝ)|=(2901448731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4063999503/10000000000 : ℝ)|^71 ≤ (15637405968907/50000000000000 : ℝ)^55
        have hw : |(4063999503/10000000000 : ℝ)|=(4063999503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(696031783/2500000000 : ℝ)|^71 ≤ (19193053004957/100000000000000 : ℝ)^55
        have hw : |(696031783/2500000000 : ℝ)|=(696031783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1118527583/5000000000 : ℝ)*x 0 + (1262727839/2500000000 : ℝ)*x 1 + (5305569997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118527583/5000000000 : ℝ)^71 ≤ (7235386522179/50000000000000 : ℝ)^55 := by
    have hnat : (1118527583 : ℕ)^71*50000000000000^55 ≤ 7235386522179^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118527583 5000000000 7235386522179 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262727839/2500000000 : ℝ)^71 ≤ (8281467560173/20000000000000 : ℝ)^55 := by
    have hnat : (1262727839 : ℕ)^71*20000000000000^55 ≤ 8281467560173^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262727839 2500000000 8281467560173 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5305569997/10000000000 : ℝ)^71 ≤ (8824377828429/20000000000000 : ℝ)^55 := by
    have hnat : (5305569997 : ℕ)^71*20000000000000^55 ≤ 8824377828429^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305569997 10000000000 8824377828429 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1118527583/5000000000 : ℝ), (1262727839/2500000000 : ℝ), (5305569997/10000000000 : ℝ)] ![(7235386522179/50000000000000 : ℝ), (8281467560173/20000000000000 : ℝ), (8824377828429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1118527583/5000000000 : ℝ)|^71 ≤ (7235386522179/50000000000000 : ℝ)^55
        have hw : |(-1118527583/5000000000 : ℝ)|=(1118527583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1262727839/2500000000 : ℝ)|^71 ≤ (8281467560173/20000000000000 : ℝ)^55
        have hw : |(1262727839/2500000000 : ℝ)|=(1262727839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5305569997/10000000000 : ℝ)|^71 ≤ (8824377828429/20000000000000 : ℝ)^55
        have hw : |(5305569997/10000000000 : ℝ)|=(5305569997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1163437723/2500000000 : ℝ)*x 0 + (-116189249/1000000000 : ℝ)*x 1 + (6428849159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1163437723/2500000000 : ℝ)^71 ≤ (7450647887039/20000000000000 : ℝ)^55 := by
    have hnat : (1163437723 : ℕ)^71*20000000000000^55 ≤ 7450647887039^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163437723 2500000000 7450647887039 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116189249/1000000000 : ℝ)^71 ≤ (621175358649/10000000000000 : ℝ)^55 := by
    have hnat : (116189249 : ℕ)^71*10000000000000^55 ≤ 621175358649^55*1000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116189249 1000000000 621175358649 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6428849159/10000000000 : ℝ)^71 ≤ (7066875871573/12500000000000 : ℝ)^55 := by
    have hnat : (6428849159 : ℕ)^71*12500000000000^55 ≤ 7066875871573^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6428849159 10000000000 7066875871573 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1163437723/2500000000 : ℝ), (-116189249/1000000000 : ℝ), (6428849159/10000000000 : ℝ)] ![(7450647887039/20000000000000 : ℝ), (621175358649/10000000000000 : ℝ), (7066875871573/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1163437723/2500000000 : ℝ)|^71 ≤ (7450647887039/20000000000000 : ℝ)^55
        have hw : |(1163437723/2500000000 : ℝ)|=(1163437723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-116189249/1000000000 : ℝ)|^71 ≤ (621175358649/10000000000000 : ℝ)^55
        have hw : |(-116189249/1000000000 : ℝ)|=(116189249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6428849159/10000000000 : ℝ)|^71 ≤ (7066875871573/12500000000000 : ℝ)^55
        have hw : |(6428849159/10000000000 : ℝ)|=(6428849159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4654236469/10000000000 : ℝ)*x 0 + (5979375483/10000000000 : ℝ)*x 1 + (-920748209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4654236469/10000000000 : ℝ)^71 ≤ (18629128663363/50000000000000 : ℝ)^55 := by
    have hnat : (4654236469 : ℕ)^71*50000000000000^55 ≤ 18629128663363^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4654236469 10000000000 18629128663363 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5979375483/10000000000 : ℝ)^71 ≤ (25742633889419/50000000000000 : ℝ)^55 := by
    have hnat : (5979375483 : ℕ)^71*50000000000000^55 ≤ 25742633889419^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5979375483 10000000000 25742633889419 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920748209/5000000000 : ℝ)^71 ≤ (11256474884529/100000000000000 : ℝ)^55 := by
    have hnat : (920748209 : ℕ)^71*100000000000000^55 ≤ 11256474884529^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920748209 5000000000 11256474884529 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4654236469/10000000000 : ℝ), (5979375483/10000000000 : ℝ), (-920748209/5000000000 : ℝ)] ![(18629128663363/50000000000000 : ℝ), (25742633889419/50000000000000 : ℝ), (11256474884529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4654236469/10000000000 : ℝ)|^71 ≤ (18629128663363/50000000000000 : ℝ)^55
        have hw : |(4654236469/10000000000 : ℝ)|=(4654236469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5979375483/10000000000 : ℝ)|^71 ≤ (25742633889419/50000000000000 : ℝ)^55
        have hw : |(5979375483/10000000000 : ℝ)|=(5979375483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-920748209/5000000000 : ℝ)|^71 ≤ (11256474884529/100000000000000 : ℝ)^55
        have hw : |(-920748209/5000000000 : ℝ)|=(920748209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1358983477/2500000000 : ℝ)*x 0 + (1274648673/2500000000 : ℝ)*x 1 + (501187647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358983477/2500000000 : ℝ)^71 ≤ (11381592315229/25000000000000 : ℝ)^55 := by
    have hnat : (1358983477 : ℕ)^71*25000000000000^55 ≤ 11381592315229^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358983477 2500000000 11381592315229 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274648673/2500000000 : ℝ)^71 ≤ (10478163866549/25000000000000 : ℝ)^55 := by
    have hnat : (1274648673 : ℕ)^71*25000000000000^55 ≤ 10478163866549^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274648673 2500000000 10478163866549 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501187647/2500000000 : ℝ)^71 ≤ (12560975262067/100000000000000 : ℝ)^55 := by
    have hnat : (501187647 : ℕ)^71*100000000000000^55 ≤ 12560975262067^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501187647 2500000000 12560975262067 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1358983477/2500000000 : ℝ), (1274648673/2500000000 : ℝ), (501187647/2500000000 : ℝ)] ![(11381592315229/25000000000000 : ℝ), (10478163866549/25000000000000 : ℝ), (12560975262067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1358983477/2500000000 : ℝ)|^71 ≤ (11381592315229/25000000000000 : ℝ)^55
        have hw : |(1358983477/2500000000 : ℝ)|=(1358983477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1274648673/2500000000 : ℝ)|^71 ≤ (10478163866549/25000000000000 : ℝ)^55
        have hw : |(1274648673/2500000000 : ℝ)|=(1274648673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501187647/2500000000 : ℝ)|^71 ≤ (12560975262067/100000000000000 : ℝ)^55
        have hw : |(501187647/2500000000 : ℝ)|=(501187647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-444045853/2500000000 : ℝ)*x 0 + (5341302181/10000000000 : ℝ)*x 1 + (2682009269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444045853/2500000000 : ℝ)^71 ≤ (10743777133581/100000000000000 : ℝ)^55 := by
    have hnat : (444045853 : ℕ)^71*100000000000000^55 ≤ 10743777133581^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444045853 2500000000 10743777133581 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5341302181/10000000000 : ℝ)^71 ≤ (86925513969/195312500000 : ℝ)^55 := by
    have hnat : (5341302181 : ℕ)^71*195312500000^55 ≤ 86925513969^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341302181 10000000000 86925513969 195312500000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2682009269/5000000000 : ℝ)^71 ≤ (8950071940013/20000000000000 : ℝ)^55 := by
    have hnat : (2682009269 : ℕ)^71*20000000000000^55 ≤ 8950071940013^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682009269 5000000000 8950071940013 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444045853/2500000000 : ℝ), (5341302181/10000000000 : ℝ), (2682009269/5000000000 : ℝ)] ![(10743777133581/100000000000000 : ℝ), (86925513969/195312500000 : ℝ), (8950071940013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444045853/2500000000 : ℝ)|^71 ≤ (10743777133581/100000000000000 : ℝ)^55
        have hw : |(-444045853/2500000000 : ℝ)|=(444045853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5341302181/10000000000 : ℝ)|^71 ≤ (86925513969/195312500000 : ℝ)^55
        have hw : |(5341302181/10000000000 : ℝ)|=(5341302181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2682009269/5000000000 : ℝ)|^71 ≤ (8950071940013/20000000000000 : ℝ)^55
        have hw : |(2682009269/5000000000 : ℝ)|=(2682009269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2198529303/5000000000 : ℝ)*x 0 + (-192345161/1250000000 : ℝ)*x 1 + (6421416807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2198529303/5000000000 : ℝ)^71 ≤ (17311109928039/50000000000000 : ℝ)^55 := by
    have hnat : (2198529303 : ℕ)^71*50000000000000^55 ≤ 17311109928039^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198529303 5000000000 17311109928039 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192345161/1250000000 : ℝ)^71 ≤ (4463566238201/50000000000000 : ℝ)^55 := by
    have hnat : (192345161 : ℕ)^71*50000000000000^55 ≤ 4463566238201^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192345161 1250000000 4463566238201 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6421416807/10000000000 : ℝ)^71 ≤ (28225323824719/50000000000000 : ℝ)^55 := by
    have hnat : (6421416807 : ℕ)^71*50000000000000^55 ≤ 28225323824719^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6421416807 10000000000 28225323824719 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2198529303/5000000000 : ℝ), (-192345161/1250000000 : ℝ), (6421416807/10000000000 : ℝ)] ![(17311109928039/50000000000000 : ℝ), (4463566238201/50000000000000 : ℝ), (28225323824719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2198529303/5000000000 : ℝ)|^71 ≤ (17311109928039/50000000000000 : ℝ)^55
        have hw : |(2198529303/5000000000 : ℝ)|=(2198529303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-192345161/1250000000 : ℝ)|^71 ≤ (4463566238201/50000000000000 : ℝ)^55
        have hw : |(-192345161/1250000000 : ℝ)|=(192345161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6421416807/10000000000 : ℝ)|^71 ≤ (28225323824719/50000000000000 : ℝ)^55
        have hw : |(6421416807/10000000000 : ℝ)|=(6421416807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1072647483/2000000000 : ℝ)*x 0 + (5337096947/10000000000 : ℝ)*x 1 + (-1783049051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072647483/2000000000 : ℝ)^71 ≤ (44741947450547/100000000000000 : ℝ)^55 := by
    have hnat : (1072647483 : ℕ)^71*100000000000000^55 ≤ 44741947450547^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072647483 2000000000 44741947450547 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5337096947/10000000000 : ℝ)^71 ≤ (44460635279579/100000000000000 : ℝ)^55 := by
    have hnat : (5337096947 : ℕ)^71*100000000000000^55 ≤ 44460635279579^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337096947 10000000000 44460635279579 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1783049051/10000000000 : ℝ)^71 ≤ (5398708623671/50000000000000 : ℝ)^55 := by
    have hnat : (1783049051 : ℕ)^71*50000000000000^55 ≤ 5398708623671^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783049051 10000000000 5398708623671 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072647483/2000000000 : ℝ), (5337096947/10000000000 : ℝ), (-1783049051/10000000000 : ℝ)] ![(44741947450547/100000000000000 : ℝ), (44460635279579/100000000000000 : ℝ), (5398708623671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072647483/2000000000 : ℝ)|^71 ≤ (44741947450547/100000000000000 : ℝ)^55
        have hw : |(1072647483/2000000000 : ℝ)|=(1072647483/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5337096947/10000000000 : ℝ)|^71 ≤ (44460635279579/100000000000000 : ℝ)^55
        have hw : |(5337096947/10000000000 : ℝ)|=(5337096947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1783049051/10000000000 : ℝ)|^71 ≤ (5398708623671/50000000000000 : ℝ)^55
        have hw : |(-1783049051/10000000000 : ℝ)|=(1783049051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6564646577/10000000000 : ℝ)*x 0 + (3855904957/10000000000 : ℝ)*x 1 + (505342269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6564646577/10000000000 : ℝ)^71 ≤ (11616263781633/20000000000000 : ℝ)^55 := by
    have hnat : (6564646577 : ℕ)^71*20000000000000^55 ≤ 11616263781633^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6564646577 10000000000 11616263781633 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3855904957/10000000000 : ℝ)^71 ≤ (29223128297463/100000000000000 : ℝ)^55 := by
    have hnat : (3855904957 : ℕ)^71*100000000000000^55 ≤ 29223128297463^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3855904957 10000000000 29223128297463 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505342269/2500000000 : ℝ)^71 ≤ (2539110554701/20000000000000 : ℝ)^55 := by
    have hnat : (505342269 : ℕ)^71*20000000000000^55 ≤ 2539110554701^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505342269 2500000000 2539110554701 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6564646577/10000000000 : ℝ), (3855904957/10000000000 : ℝ), (505342269/2500000000 : ℝ)] ![(11616263781633/20000000000000 : ℝ), (29223128297463/100000000000000 : ℝ), (2539110554701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6564646577/10000000000 : ℝ)|^71 ≤ (11616263781633/20000000000000 : ℝ)^55
        have hw : |(6564646577/10000000000 : ℝ)|=(6564646577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3855904957/10000000000 : ℝ)|^71 ≤ (29223128297463/100000000000000 : ℝ)^55
        have hw : |(3855904957/10000000000 : ℝ)|=(3855904957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(505342269/2500000000 : ℝ)|^71 ≤ (2539110554701/20000000000000 : ℝ)^55
        have hw : |(505342269/2500000000 : ℝ)|=(505342269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1783389433/10000000000 : ℝ)*x 0 + (2964233249/5000000000 : ℝ)*x 1 + (4752788919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1783389433/10000000000 : ℝ)^71 ≤ (108000781617/1000000000000 : ℝ)^55 := by
    have hnat : (1783389433 : ℕ)^71*1000000000000^55 ≤ 108000781617^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783389433 10000000000 108000781617 1000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2964233249/5000000000 : ℝ)^71 ≤ (12730024806213/25000000000000 : ℝ)^55 := by
    have hnat : (2964233249 : ℕ)^71*25000000000000^55 ≤ 12730024806213^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2964233249 5000000000 12730024806213 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4752788919/10000000000 : ℝ)^71 ≤ (7655964519731/20000000000000 : ℝ)^55 := by
    have hnat : (4752788919 : ℕ)^71*20000000000000^55 ≤ 7655964519731^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4752788919 10000000000 7655964519731 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1783389433/10000000000 : ℝ), (2964233249/5000000000 : ℝ), (4752788919/10000000000 : ℝ)] ![(108000781617/1000000000000 : ℝ), (12730024806213/25000000000000 : ℝ), (7655964519731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1783389433/10000000000 : ℝ)|^71 ≤ (108000781617/1000000000000 : ℝ)^55
        have hw : |(-1783389433/10000000000 : ℝ)|=(1783389433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2964233249/5000000000 : ℝ)|^71 ≤ (12730024806213/25000000000000 : ℝ)^55
        have hw : |(2964233249/5000000000 : ℝ)|=(2964233249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4752788919/10000000000 : ℝ)|^71 ≤ (7655964519731/20000000000000 : ℝ)^55
        have hw : |(4752788919/10000000000 : ℝ)|=(4752788919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5355546047/10000000000 : ℝ)*x 0 + (-1142268441/10000000000 : ℝ)*x 1 + (1155713563/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355546047/10000000000 : ℝ)^71 ≤ (8931826967843/20000000000000 : ℝ)^55 := by
    have hnat : (5355546047 : ℕ)^71*20000000000000^55 ≤ 8931826967843^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355546047 10000000000 8931826967843 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1142268441/10000000000 : ℝ)^71 ≤ (6076652135287/100000000000000 : ℝ)^55 := by
    have hnat : (1142268441 : ℕ)^71*100000000000000^55 ≤ 6076652135287^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142268441 10000000000 6076652135287 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1155713563/2000000000 : ℝ)^71 ≤ (6158026627081/12500000000000 : ℝ)^55 := by
    have hnat : (1155713563 : ℕ)^71*12500000000000^55 ≤ 6158026627081^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155713563 2000000000 6158026627081 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355546047/10000000000 : ℝ), (-1142268441/10000000000 : ℝ), (1155713563/2000000000 : ℝ)] ![(8931826967843/20000000000000 : ℝ), (6076652135287/100000000000000 : ℝ), (6158026627081/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355546047/10000000000 : ℝ)|^71 ≤ (8931826967843/20000000000000 : ℝ)^55
        have hw : |(5355546047/10000000000 : ℝ)|=(5355546047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1142268441/10000000000 : ℝ)|^71 ≤ (6076652135287/100000000000000 : ℝ)^55
        have hw : |(-1142268441/10000000000 : ℝ)|=(1142268441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1155713563/2000000000 : ℝ)|^71 ≤ (6158026627081/12500000000000 : ℝ)^55
        have hw : |(1155713563/2000000000 : ℝ)|=(1155713563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1087598351/2500000000 : ℝ)*x 0 + (5998998863/10000000000 : ℝ)*x 1 + (-2198289939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087598351/2500000000 : ℝ)^71 ≤ (8537155741479/25000000000000 : ℝ)^55 := by
    have hnat : (1087598351 : ℕ)^71*25000000000000^55 ≤ 8537155741479^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087598351 2500000000 8537155741479 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5998998863/10000000000 : ℝ)^71 ≤ (51703492389381/100000000000000 : ℝ)^55 := by
    have hnat : (5998998863 : ℕ)^71*100000000000000^55 ≤ 51703492389381^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5998998863 10000000000 51703492389381 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2198289939/10000000000 : ℝ)^71 ≤ (3536971157259/25000000000000 : ℝ)^55 := by
    have hnat : (2198289939 : ℕ)^71*25000000000000^55 ≤ 3536971157259^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2198289939 10000000000 3536971157259 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087598351/2500000000 : ℝ), (5998998863/10000000000 : ℝ), (-2198289939/10000000000 : ℝ)] ![(8537155741479/25000000000000 : ℝ), (51703492389381/100000000000000 : ℝ), (3536971157259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087598351/2500000000 : ℝ)|^71 ≤ (8537155741479/25000000000000 : ℝ)^55
        have hw : |(1087598351/2500000000 : ℝ)|=(1087598351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5998998863/10000000000 : ℝ)|^71 ≤ (51703492389381/100000000000000 : ℝ)^55
        have hw : |(5998998863/10000000000 : ℝ)|=(5998998863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2198289939/10000000000 : ℝ)|^71 ≤ (3536971157259/25000000000000 : ℝ)^55
        have hw : |(-2198289939/10000000000 : ℝ)|=(2198289939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310055_s4_s4_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6670069171/10000000000 : ℝ)*x 0 + (1568252409/5000000000 : ℝ)*x 1 + (2686279889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6670069171/10000000000 : ℝ)^71 ≤ (118576396961/200000000000 : ℝ)^55 := by
    have hnat : (6670069171 : ℕ)^71*200000000000^55 ≤ 118576396961^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6670069171 10000000000 118576396961 200000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1568252409/5000000000 : ℝ)^71 ≤ (1399063827191/6250000000000 : ℝ)^55 := by
    have hnat : (1568252409 : ℕ)^71*6250000000000^55 ≤ 1399063827191^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1568252409 5000000000 1399063827191 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2686279889/10000000000 : ℝ)^71 ≤ (18326780271989/100000000000000 : ℝ)^55 := by
    have hnat : (2686279889 : ℕ)^71*100000000000000^55 ≤ 18326780271989^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686279889 10000000000 18326780271989 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6670069171/10000000000 : ℝ), (1568252409/5000000000 : ℝ), (2686279889/10000000000 : ℝ)] ![(118576396961/200000000000 : ℝ), (1399063827191/6250000000000 : ℝ), (18326780271989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6670069171/10000000000 : ℝ)|^71 ≤ (118576396961/200000000000 : ℝ)^55
        have hw : |(6670069171/10000000000 : ℝ)|=(6670069171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1568252409/5000000000 : ℝ)|^71 ≤ (1399063827191/6250000000000 : ℝ)^55
        have hw : |(1568252409/5000000000 : ℝ)|=(1568252409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2686279889/10000000000 : ℝ)|^71 ≤ (18326780271989/100000000000000 : ℝ)^55
        have hw : |(2686279889/10000000000 : ℝ)|=(2686279889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310055_s4 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((1326/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1326/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43261/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43261/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5321/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5321/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6871/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6871/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13461/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13461/50000 : ℝ)*X 1 2) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (1326/3125 : ℝ) ^ (35/8 : ℝ) ≤ (2350493599651291291/100000000000000000000 : ℝ) := by
    have hpowers : (1326/3125 : ℝ)^35 ≤ (2350493599651291291/100000000000000000000 : ℝ)^8 := by
      have hnat : (1326 : ℕ)^35*100000000000000000000^8 ≤ 2350493599651291291^8*3125^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1326 3125 2350493599651291291 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1326/3125 : ℝ)) (X := (2350493599651291291/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner0a : (102350493599651291291/100000000000000000000 : ℝ) ≤ (2010649026789437/2000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (102350493599651291291/100000000000000000000 : ℝ)^8 ≤ (2010649026789437/2000000000000000 : ℝ)^35 := by
      have hnat : (102350493599651291291 : ℕ)^8*2000000000000000^35 ≤ 2010649026789437^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102350493599651291291 100000000000000000000 2010649026789437 2000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2010649026789437/2000000000000000 : ℝ)) (X := (102350493599651291291/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner0b : (52350493599651291291/50000000000000000000 : ℝ) ≤ (2526388793121971/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (52350493599651291291/50000000000000000000 : ℝ)^8 ≤ (2526388793121971/2500000000000000 : ℝ)^35 := by
      have hnat : (52350493599651291291 : ℕ)^8*2500000000000000^35 ≤ 2526388793121971^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52350493599651291291 50000000000000000000 2526388793121971 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2526388793121971/2500000000000000 : ℝ)) (X := (52350493599651291291/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(3549675596479/282880000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(52310038540699/4243200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (1326/3125 : ℝ)) (alpha := (3549675596479/282880000000000 : ℝ)) (beta := (52310038540699/4243200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1326/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(3549675596479/282880000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(52310038540699/4243200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (21663/50000 : ℝ) ^ (35/8 : ℝ) ≤ (1287493689623004413/50000000000000000000 : ℝ) := by
    have hpowers : (21663/50000 : ℝ)^35 ≤ (1287493689623004413/50000000000000000000 : ℝ)^8 := by
      have hnat : (21663 : ℕ)^35*50000000000000000000^8 ≤ 1287493689623004413^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21663 50000 1287493689623004413 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21663/50000 : ℝ)) (X := (1287493689623004413/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner1a : (51287493689623004413/50000000000000000000 : ℝ) ≤ (1257285126904657/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (51287493689623004413/50000000000000000000 : ℝ)^8 ≤ (1257285126904657/1250000000000000 : ℝ)^35 := by
      have hnat : (51287493689623004413 : ℕ)^8*1250000000000000^35 ≤ 1257285126904657^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51287493689623004413 50000000000000000000 1257285126904657 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257285126904657/1250000000000000 : ℝ)) (X := (51287493689623004413/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner1b : (26287493689623004413/25000000000000000000 : ℝ) ≤ (5057722042413383/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (26287493689623004413/25000000000000000000 : ℝ)^8 ≤ (5057722042413383/5000000000000000 : ℝ)^35 := by
      have hnat : (26287493689623004413 : ℕ)^8*5000000000000000^35 ≤ 5057722042413383^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26287493689623004413 25000000000000000000 5057722042413383 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057722042413383/5000000000000000 : ℝ)) (X := (26287493689623004413/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(7285126904657/541575000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(5716306958951/433260000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (21663/50000 : ℝ)) (alpha := (7285126904657/541575000000000 : ℝ)) (beta := (5716306958951/433260000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21663/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(7285126904657/541575000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(5716306958951/433260000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (43261/100000 : ℝ) ^ (35/8 : ℝ) ≤ (159883056375733331/6250000000000000000 : ℝ) := by
    have hpowers : (43261/100000 : ℝ)^35 ≤ (159883056375733331/6250000000000000000 : ℝ)^8 := by
      have hnat : (43261 : ℕ)^35*6250000000000000000^8 ≤ 159883056375733331^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43261 100000 159883056375733331 6250000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43261/100000 : ℝ)) (X := (159883056375733331/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner2a : (6409883056375733331/6250000000000000000 : ℝ) ≤ (1257237892317329/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (6409883056375733331/6250000000000000000 : ℝ)^8 ≤ (1257237892317329/1250000000000000 : ℝ)^35 := by
      have hnat : (6409883056375733331 : ℕ)^8*1250000000000000^35 ≤ 1257237892317329^35*6250000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6409883056375733331 6250000000000000000 1257237892317329 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257237892317329/1250000000000000 : ℝ)) (X := (6409883056375733331/6250000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s4_corner2b : (3284883056375733331/3125000000000000000 : ℝ) ≤ (2528675651060327/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3284883056375733331/3125000000000000000 : ℝ)^8 ≤ (2528675651060327/2500000000000000 : ℝ)^35 := by
      have hnat : (3284883056375733331 : ℕ)^8*2500000000000000^35 ≤ 2528675651060327^35*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3284883056375733331 3125000000000000000 2528675651060327 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528675651060327/2500000000000000 : ℝ)) (X := (3284883056375733331/3125000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(7237892317329/540762500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14199866425669/1081525000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (43261/100000 : ℝ)) (alpha := (7237892317329/540762500000000 : ℝ)) (beta := (14199866425669/1081525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (43261/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(7237892317329/540762500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14199866425669/1081525000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1197222803/5000000000 : ℝ)*X 0 0+(2749086949/5000000000 : ℝ)*X 0 1+(4725980479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((4724464989/10000000000 : ℝ)*X 1 0+(-325451127/2000000000 : ℝ)*X 1 1+(6063213973/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((4724949737/10000000000 : ℝ)*X 2 0+(686747527/1250000000 : ℝ)*X 2 1+(-2401039453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((2901448731/5000000000 : ℝ)*X 0 0+(4063999503/10000000000 : ℝ)*X 0 1+(696031783/2500000000 : ℝ)*X 0 2+(2901448731/5000000000 : ℝ)*X 1 0+(4063999503/10000000000 : ℝ)*X 1 1+(696031783/2500000000 : ℝ)*X 1 2+(2901448731/5000000000 : ℝ)*X 2 0+(4063999503/10000000000 : ℝ)*X 2 1+(696031783/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-1118527583/5000000000 : ℝ)*X 0 0+(1262727839/2500000000 : ℝ)*X 0 1+(5305569997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((1163437723/2500000000 : ℝ)*X 1 0+(-116189249/1000000000 : ℝ)*X 1 1+(6428849159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((4654236469/10000000000 : ℝ)*X 2 0+(5979375483/10000000000 : ℝ)*X 2 1+(-920748209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((1358983477/2500000000 : ℝ)*X 0 0+(1274648673/2500000000 : ℝ)*X 0 1+(501187647/2500000000 : ℝ)*X 0 2+(1358983477/2500000000 : ℝ)*X 1 0+(1274648673/2500000000 : ℝ)*X 1 1+(501187647/2500000000 : ℝ)*X 1 2+(1358983477/2500000000 : ℝ)*X 2 0+(1274648673/2500000000 : ℝ)*X 2 1+(501187647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-444045853/2500000000 : ℝ)*X 0 0+(5341302181/10000000000 : ℝ)*X 0 1+(2682009269/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((2198529303/5000000000 : ℝ)*X 1 0+(-192345161/1250000000 : ℝ)*X 1 1+(6421416807/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1072647483/2000000000 : ℝ)*X 2 0+(5337096947/10000000000 : ℝ)*X 2 1+(-1783049051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((6564646577/10000000000 : ℝ)*X 0 0+(3855904957/10000000000 : ℝ)*X 0 1+(505342269/2500000000 : ℝ)*X 0 2+(6564646577/10000000000 : ℝ)*X 1 0+(3855904957/10000000000 : ℝ)*X 1 1+(505342269/2500000000 : ℝ)*X 1 2+(6564646577/10000000000 : ℝ)*X 2 0+(3855904957/10000000000 : ℝ)*X 2 1+(505342269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-1783389433/10000000000 : ℝ)*X 0 0+(2964233249/5000000000 : ℝ)*X 0 1+(4752788919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((5355546047/10000000000 : ℝ)*X 1 0+(-1142268441/10000000000 : ℝ)*X 1 1+(1155713563/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((1087598351/2500000000 : ℝ)*X 2 0+(5998998863/10000000000 : ℝ)*X 2 1+(-2198289939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((6670069171/10000000000 : ℝ)*X 0 0+(1568252409/5000000000 : ℝ)*X 0 1+(2686279889/10000000000 : ℝ)*X 0 2+(6670069171/10000000000 : ℝ)*X 1 0+(1568252409/5000000000 : ℝ)*X 1 1+(2686279889/10000000000 : ℝ)*X 1 2+(6670069171/10000000000 : ℝ)*X 2 0+(1568252409/5000000000 : ℝ)*X 2 1+(2686279889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310055_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((5321/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5321/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (194417705574718118405007240459/18410047333600000000000000000000000 : ℝ) := by norm_num
    linear_combination (201272625847/200000000000 : ℝ)*(base49) + (1231023/500000000000 : ℝ)*(base60) + (7758714913659/1000000000000 : ℝ)*(major_s4_0) + (7758714913659/1000000000000 : ℝ)*(major_s4_1) + (7758714913659/1000000000000 : ℝ)*(major_s4_2) + (21478789/500000000000 : ℝ)*(sp_s4_0) + (34008749/1000000000000 : ℝ)*(sp_s4_6) + (10721885550453/1000000000000 : ℝ)*(sp_s4_7) + (2680465360397/250000000000 : ℝ)*(sp_s4_8) + (2144361125067/200000000000 : ℝ)*(sp_s4_9) + (4795423714181/1000000000000 : ℝ)*(sp_s4_13) + (20038107/500000000000 : ℝ)*(sp_s4_14) + (107142657/1000000000000 : ℝ)*(sp_s4_15) + (16295891/100000000000 : ℝ)*(sp_s4_23) + (4795457722929/1000000000000 : ℝ)*(f.failure) + (2144393716849/200000000000 : ℝ)*(f.sum) + (107669886578083821/2603230675000000000000000000000 : ℝ)*base63 + (1556961277332983/2163050000000000000000000000 : ℝ)*base64 + (1892378893827/9628000000000000000000000 : ℝ)*base66 + (72146312052731/540762500000000000000000000 : ℝ)*base69 + (49719802348004644619/61188358400000000000000000000000 : ℝ)*base70 + (145613401538733/1414400000000000000000000000 : ℝ)*base72 + (39835625254721/120350000000000000000000000 : ℝ)*base74 + (78396477263931/282880000000000000000000000 : ℝ)*base76 + (886073801250254171/3404460800000000000000000000000 : ℝ)*base78 + (48303/100000000000000000 : ℝ)*base86 + (48303/100000000000000000 : ℝ)*base88 + (48303/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6871/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6871/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1196918543761183106411183/340446080000000000000000000000 : ℝ) := by norm_num
    linear_combination (45186016037/50000000000 : ℝ)*(base49) + (97373/100000000000 : ℝ)*(base60) + (1498671513669/200000000000 : ℝ)*(major_s4_0) + (1498671513669/200000000000 : ℝ)*(major_s4_1) + (1498671513669/200000000000 : ℝ)*(major_s4_2) + (12021057/500000000000 : ℝ)*(sp_s4_1) + (12499273/1000000000000 : ℝ)*(sp_s4_2) + (24531037/1000000000000 : ℝ)*(sp_s4_7) + (4440383/500000000000 : ℝ)*(sp_s4_8) + (10355242110091/1000000000000 : ℝ)*(sp_s4_14) + (10355233718247/1000000000000 : ℝ)*(sp_s4_15) + (2071050828371/200000000000 : ℝ)*(sp_s4_16) + (185256967197/40000000000 : ℝ)*(sp_s4_20) + (578593/25000000000 : ℝ)*(sp_s4_27) + (926289464729/200000000000 : ℝ)*(f.failure) + (1294408330141/125000000000 : ℝ)*(f.sum) + (55743451073169133/624775362000000000000000000000 : ℝ)*base62 + (64033830212007/216305000000000000000000000 : ℝ)*base65 + (81091492966301/144420000000000000000000000 : ℝ)*base67 + (341843834847159/432610000000000000000000000 : ℝ)*base69 + (3286257564328766901/12237671680000000000000000000000 : ℝ)*base70 + (282284803578477/282880000000000000000000000 : ℝ)*base73 + (19216885753531/72210000000000000000000000 : ℝ)*base75 + (100507598711911/282880000000000000000000000 : ℝ)*base77 + (296781612020591569/2042676480000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (903/20000000000000000 : ℝ)*base86 + (903/20000000000000000 : ℝ)*base88 + (903/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13461/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13461/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (83322763752666819/5000000000000000000000 : ℝ) := by norm_num
    linear_combination (3716289961/50000000000 : ℝ)*(base40) + (113838847279/125000000000 : ℝ)*(base49) + (4372851/500000000000 : ℝ)*(base59) + (7195740258597/1000000000000 : ℝ)*(major_s4_0) + (7195740258597/1000000000000 : ℝ)*(major_s4_1) + (7195740258597/1000000000000 : ℝ)*(major_s4_2) + (64579581/1000000000000 : ℝ)*(sp_s4_0) + (45660637/500000000000 : ℝ)*(sp_s4_2) + (38244699/1000000000000 : ℝ)*(sp_s4_9) + (205706099/1000000000000 : ℝ)*(sp_s4_20) + (2485978123587/250000000000 : ℝ)*(sp_s4_21) + (9943977073929/1000000000000 : ℝ)*(sp_s4_22) + (2485961876989/250000000000 : ℝ)*(sp_s4_23) + (555911522789/125000000000 : ℝ)*(sp_s4_27) + (4447497888411/1000000000000 : ℝ)*(f.failure) + (9943977073929/1000000000000 : ℝ)*(f.sum) + (413067538114076587/15619384050000000000000000000000 : ℝ)*base62 + (382312862926481/2163050000000000000000000000 : ℝ)*base65 + (326271558617/5776800000000000000000000 : ℝ)*base67 + (374746391517281/1081525000000000000000000000 : ℝ)*base69 + (1485365141351644101/3599315200000000000000000000000 : ℝ)*base70 + (47570124422013/83200000000000000000000000 : ℝ)*base73 + (55206792702673/180525000000000000000000000 : ℝ)*base75 + (2287216201707/16640000000000000000000000 : ℝ)*base77 + (57335074276797407/600787200000000000000000000000 : ℝ)*base78 + (19077/100000000000000000 : ℝ)*base86 + (19077/100000000000000000 : ℝ)*base88 + (19077/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((1326/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1326/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43261/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43261/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5321/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5321/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6871/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(6871/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13461/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13461/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310055_s4 p hpa hpb X hX hprev3

#print axioms solution
