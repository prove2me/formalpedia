-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306086_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:01:03.558807+00:00
-- url     : https://prove2.me/submissions/75a361ba-7635-471e-8d05-3238485f08b4

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
theorem collision_support_c306086_s2_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-18976763/10000000000 : ℝ)*x 0 + (-811375571/1250000000 : ℝ)*x 1 + (5272639923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18976763/10000000000 : ℝ)^135 ≤ (2707829051/10000000000000 : ℝ)^103 := by
    have hnat : (18976763 : ℕ)^135*10000000000000^103 ≤ 2707829051^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18976763 10000000000 2707829051 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (811375571/1250000000 : ℝ)^135 ≤ (11350919638457/20000000000000 : ℝ)^103 := by
    have hnat : (811375571 : ℕ)^135*20000000000000^103 ≤ 11350919638457^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811375571 1250000000 11350919638457 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272639923/10000000000 : ℝ)^135 ≤ (21609161750659/50000000000000 : ℝ)^103 := by
    have hnat : (5272639923 : ℕ)^135*50000000000000^103 ≤ 21609161750659^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272639923 10000000000 21609161750659 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18976763/10000000000 : ℝ), (-811375571/1250000000 : ℝ), (5272639923/10000000000 : ℝ)] ![(2707829051/10000000000000 : ℝ), (11350919638457/20000000000000 : ℝ), (21609161750659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18976763/10000000000 : ℝ)|^135 ≤ (2707829051/10000000000000 : ℝ)^103
        have hw : |(-18976763/10000000000 : ℝ)|=(18976763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-811375571/1250000000 : ℝ)|^135 ≤ (11350919638457/20000000000000 : ℝ)^103
        have hw : |(-811375571/1250000000 : ℝ)|=(811375571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272639923/10000000000 : ℝ)|^135 ≤ (21609161750659/50000000000000 : ℝ)^103
        have hw : |(5272639923/10000000000 : ℝ)|=(5272639923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (745902773/2000000000 : ℝ)*x 0 + (-2839878523/10000000000 : ℝ)*x 1 + (309549671/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (745902773/2000000000 : ℝ)^135 ≤ (6862989187203/25000000000000 : ℝ)^103 := by
    have hnat : (745902773 : ℕ)^135*25000000000000^103 ≤ 6862989187203^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745902773 2000000000 6862989187203 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2839878523/10000000000 : ℝ)^135 ≤ (19206628936941/100000000000000 : ℝ)^103 := by
    have hnat : (2839878523 : ℕ)^135*100000000000000^103 ≤ 19206628936941^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2839878523 10000000000 19206628936941 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309549671/500000000 : ℝ)^135 ≤ (10668282861201/20000000000000 : ℝ)^103 := by
    have hnat : (309549671 : ℕ)^135*20000000000000^103 ≤ 10668282861201^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309549671 500000000 10668282861201 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(745902773/2000000000 : ℝ), (-2839878523/10000000000 : ℝ), (309549671/500000000 : ℝ)] ![(6862989187203/25000000000000 : ℝ), (19206628936941/100000000000000 : ℝ), (10668282861201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(745902773/2000000000 : ℝ)|^135 ≤ (6862989187203/25000000000000 : ℝ)^103
        have hw : |(745902773/2000000000 : ℝ)|=(745902773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2839878523/10000000000 : ℝ)|^135 ≤ (19206628936941/100000000000000 : ℝ)^103
        have hw : |(-2839878523/10000000000 : ℝ)|=(2839878523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(309549671/500000000 : ℝ)|^135 ≤ (10668282861201/20000000000000 : ℝ)^103
        have hw : |(309549671/500000000 : ℝ)|=(309549671/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2458653/2000000000 : ℝ)*x 0 + (-2033375333/2500000000 : ℝ)*x 1 + (416822649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2458653/2000000000 : ℝ)^135 ≤ (15328024753/100000000000000 : ℝ)^103 := by
    have hnat : (2458653 : ℕ)^135*100000000000000^103 ≤ 15328024753^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2458653 2000000000 15328024753 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2033375333/2500000000 : ℝ)^135 ≤ (38139290362287/50000000000000 : ℝ)^103 := by
    have hnat : (2033375333 : ℕ)^135*50000000000000^103 ≤ 38139290362287^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033375333 2500000000 38139290362287 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416822649/1250000000 : ℝ)^135 ≤ (23706091233187/100000000000000 : ℝ)^103 := by
    have hnat : (416822649 : ℕ)^135*100000000000000^103 ≤ 23706091233187^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416822649 1250000000 23706091233187 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2458653/2000000000 : ℝ), (-2033375333/2500000000 : ℝ), (416822649/1250000000 : ℝ)] ![(15328024753/100000000000000 : ℝ), (38139290362287/50000000000000 : ℝ), (23706091233187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2458653/2000000000 : ℝ)|^135 ≤ (15328024753/100000000000000 : ℝ)^103
        have hw : |(2458653/2000000000 : ℝ)|=(2458653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2033375333/2500000000 : ℝ)|^135 ≤ (38139290362287/50000000000000 : ℝ)^103
        have hw : |(-2033375333/2500000000 : ℝ)|=(2033375333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(416822649/1250000000 : ℝ)|^135 ≤ (23706091233187/100000000000000 : ℝ)^103
        have hw : |(416822649/1250000000 : ℝ)|=(416822649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (209145089/400000000 : ℝ)*x 0 + (1191449177/2500000000 : ℝ)*x 1 + (143069557/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209145089/400000000 : ℝ)^135 ≤ (42746097662803/100000000000000 : ℝ)^103 := by
    have hnat : (209145089 : ℕ)^135*100000000000000^103 ≤ 42746097662803^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209145089 400000000 42746097662803 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1191449177/2500000000 : ℝ)^135 ≤ (2366022097673/6250000000000 : ℝ)^103 := by
    have hnat : (1191449177 : ℕ)^135*6250000000000^103 ≤ 2366022097673^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191449177 2500000000 2366022097673 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (143069557/500000000 : ℝ)^135 ≤ (19397548764073/100000000000000 : ℝ)^103 := by
    have hnat : (143069557 : ℕ)^135*100000000000000^103 ≤ 19397548764073^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      143069557 500000000 19397548764073 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209145089/400000000 : ℝ), (1191449177/2500000000 : ℝ), (143069557/500000000 : ℝ)] ![(42746097662803/100000000000000 : ℝ), (2366022097673/6250000000000 : ℝ), (19397548764073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209145089/400000000 : ℝ)|^135 ≤ (42746097662803/100000000000000 : ℝ)^103
        have hw : |(209145089/400000000 : ℝ)|=(209145089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1191449177/2500000000 : ℝ)|^135 ≤ (2366022097673/6250000000000 : ℝ)^103
        have hw : |(1191449177/2500000000 : ℝ)|=(1191449177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(143069557/500000000 : ℝ)|^135 ≤ (19397548764073/100000000000000 : ℝ)^103
        have hw : |(143069557/500000000 : ℝ)|=(143069557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (48940961/80000000 : ℝ)*x 0 + (-211143223/625000000 : ℝ)*x 1 + (-51540713/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48940961/80000000 : ℝ)^135 ≤ (52514355723469/100000000000000 : ℝ)^103 := by
    have hnat : (48940961 : ℕ)^135*100000000000000^103 ≤ 52514355723469^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48940961 80000000 52514355723469 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211143223/625000000 : ℝ)^135 ≤ (12057102159573/50000000000000 : ℝ)^103 := by
    have hnat : (211143223 : ℕ)^135*50000000000000^103 ≤ 12057102159573^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211143223 625000000 12057102159573 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51540713/156250000 : ℝ)^135 ≤ (4674287989157/20000000000000 : ℝ)^103 := by
    have hnat : (51540713 : ℕ)^135*20000000000000^103 ≤ 4674287989157^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51540713 156250000 4674287989157 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48940961/80000000 : ℝ), (-211143223/625000000 : ℝ), (-51540713/156250000 : ℝ)] ![(52514355723469/100000000000000 : ℝ), (12057102159573/50000000000000 : ℝ), (4674287989157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48940961/80000000 : ℝ)|^135 ≤ (52514355723469/100000000000000 : ℝ)^103
        have hw : |(48940961/80000000 : ℝ)|=(48940961/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211143223/625000000 : ℝ)|^135 ≤ (12057102159573/50000000000000 : ℝ)^103
        have hw : |(-211143223/625000000 : ℝ)|=(211143223/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51540713/156250000 : ℝ)|^135 ≤ (4674287989157/20000000000000 : ℝ)^103
        have hw : |(-51540713/156250000 : ℝ)|=(51540713/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (580391991/2000000000 : ℝ)*x 0 + (-1392002359/10000000000 : ℝ)*x 1 + (122507973/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (580391991/2000000000 : ℝ)^135 ≤ (2469850155979/12500000000000 : ℝ)^103 := by
    have hnat : (580391991 : ℕ)^135*12500000000000^103 ≤ 2469850155979^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      580391991 2000000000 2469850155979 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1392002359/10000000000 : ℝ)^135 ≤ (7543734065779/100000000000000 : ℝ)^103 := by
    have hnat : (1392002359 : ℕ)^135*100000000000000^103 ≤ 7543734065779^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1392002359 10000000000 7543734065779 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122507973/156250000 : ℝ)^135 ≤ (36348732331533/50000000000000 : ℝ)^103 := by
    have hnat : (122507973 : ℕ)^135*50000000000000^103 ≤ 36348732331533^103*156250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122507973 156250000 36348732331533 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(580391991/2000000000 : ℝ), (-1392002359/10000000000 : ℝ), (122507973/156250000 : ℝ)] ![(2469850155979/12500000000000 : ℝ), (7543734065779/100000000000000 : ℝ), (36348732331533/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(580391991/2000000000 : ℝ)|^135 ≤ (2469850155979/12500000000000 : ℝ)^103
        have hw : |(580391991/2000000000 : ℝ)|=(580391991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1392002359/10000000000 : ℝ)|^135 ≤ (7543734065779/100000000000000 : ℝ)^103
        have hw : |(-1392002359/10000000000 : ℝ)|=(1392002359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122507973/156250000 : ℝ)|^135 ≤ (36348732331533/50000000000000 : ℝ)^103
        have hw : |(122507973/156250000 : ℝ)|=(122507973/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-5049/100000000 : ℝ)*x 0 + (-1116935491/2500000000 : ℝ)*x 1 + (3608516581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5049/100000000 : ℝ)^135 ≤ (233495699/100000000000000 : ℝ)^103 := by
    have hnat : (5049 : ℕ)^135*100000000000000^103 ≤ 233495699^103*100000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5049 100000000 233495699 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1116935491/2500000000 : ℝ)^135 ≤ (17391922359541/50000000000000 : ℝ)^103 := by
    have hnat : (1116935491 : ℕ)^135*50000000000000^103 ≤ 17391922359541^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1116935491 2500000000 17391922359541 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3608516581/5000000000 : ℝ)^135 ≤ (32607960887311/50000000000000 : ℝ)^103 := by
    have hnat : (3608516581 : ℕ)^135*50000000000000^103 ≤ 32607960887311^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3608516581 5000000000 32607960887311 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5049/100000000 : ℝ), (-1116935491/2500000000 : ℝ), (3608516581/5000000000 : ℝ)] ![(233495699/100000000000000 : ℝ), (17391922359541/50000000000000 : ℝ), (32607960887311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5049/100000000 : ℝ)|^135 ≤ (233495699/100000000000000 : ℝ)^103
        have hw : |(-5049/100000000 : ℝ)|=(5049/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1116935491/2500000000 : ℝ)|^135 ≤ (17391922359541/50000000000000 : ℝ)^103
        have hw : |(-1116935491/2500000000 : ℝ)|=(1116935491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3608516581/5000000000 : ℝ)|^135 ≤ (32607960887311/50000000000000 : ℝ)^103
        have hw : |(3608516581/5000000000 : ℝ)|=(3608516581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (167043701/200000000 : ℝ)*x 0 + (2039587227/10000000000 : ℝ)*x 1 + (767559899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167043701/200000000 : ℝ)^135 ≤ (78977793444543/100000000000000 : ℝ)^103 := by
    have hnat : (167043701 : ℕ)^135*100000000000000^103 ≤ 78977793444543^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167043701 200000000 78977793444543 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039587227/10000000000 : ℝ)^135 ≤ (6223019367807/50000000000000 : ℝ)^103 := by
    have hnat : (2039587227 : ℕ)^135*50000000000000^103 ≤ 6223019367807^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039587227 10000000000 6223019367807 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767559899/5000000000 : ℝ)^135 ≤ (8576167805351/100000000000000 : ℝ)^103 := by
    have hnat : (767559899 : ℕ)^135*100000000000000^103 ≤ 8576167805351^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767559899 5000000000 8576167805351 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167043701/200000000 : ℝ), (2039587227/10000000000 : ℝ), (767559899/5000000000 : ℝ)] ![(78977793444543/100000000000000 : ℝ), (6223019367807/50000000000000 : ℝ), (8576167805351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167043701/200000000 : ℝ)|^135 ≤ (78977793444543/100000000000000 : ℝ)^103
        have hw : |(167043701/200000000 : ℝ)|=(167043701/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2039587227/10000000000 : ℝ)|^135 ≤ (6223019367807/50000000000000 : ℝ)^103
        have hw : |(2039587227/10000000000 : ℝ)|=(2039587227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(767559899/5000000000 : ℝ)|^135 ≤ (8576167805351/100000000000000 : ℝ)^103
        have hw : |(767559899/5000000000 : ℝ)|=(767559899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (393987159/500000000 : ℝ)*x 0 + (-2690175817/10000000000 : ℝ)*x 1 + (-1583855309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (393987159/500000000 : ℝ)^135 ≤ (73174619180349/100000000000000 : ℝ)^103 := by
    have hnat : (393987159 : ℕ)^135*100000000000000^103 ≤ 73174619180349^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393987159 500000000 73174619180349 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2690175817/10000000000 : ℝ)^135 ≤ (8945304876607/50000000000000 : ℝ)^103 := by
    have hnat : (2690175817 : ℕ)^135*50000000000000^103 ≤ 8945304876607^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690175817 10000000000 8945304876607 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583855309/10000000000 : ℝ)^135 ≤ (1786954210377/20000000000000 : ℝ)^103 := by
    have hnat : (1583855309 : ℕ)^135*20000000000000^103 ≤ 1786954210377^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583855309 10000000000 1786954210377 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(393987159/500000000 : ℝ), (-2690175817/10000000000 : ℝ), (-1583855309/10000000000 : ℝ)] ![(73174619180349/100000000000000 : ℝ), (8945304876607/50000000000000 : ℝ), (1786954210377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(393987159/500000000 : ℝ)|^135 ≤ (73174619180349/100000000000000 : ℝ)^103
        have hw : |(393987159/500000000 : ℝ)|=(393987159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2690175817/10000000000 : ℝ)|^135 ≤ (8945304876607/50000000000000 : ℝ)^103
        have hw : |(-2690175817/10000000000 : ℝ)|=(2690175817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1583855309/10000000000 : ℝ)|^135 ≤ (1786954210377/20000000000000 : ℝ)^103
        have hw : |(-1583855309/10000000000 : ℝ)|=(1583855309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2292597923/10000000000 : ℝ)*x 0 + (-813559251/5000000000 : ℝ)*x 1 + (4065035927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292597923/10000000000 : ℝ)^135 ≤ (14507574629727/100000000000000 : ℝ)^103 := by
    have hnat : (2292597923 : ℕ)^135*100000000000000^103 ≤ 14507574629727^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292597923 10000000000 14507574629727 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (813559251/5000000000 : ℝ)^135 ≤ (578499807789/6250000000000 : ℝ)^103 := by
    have hnat : (813559251 : ℕ)^135*6250000000000^103 ≤ 578499807789^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813559251 5000000000 578499807789 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4065035927/5000000000 : ℝ)^135 ≤ (7623642843421/10000000000000 : ℝ)^103 := by
    have hnat : (4065035927 : ℕ)^135*10000000000000^103 ≤ 7623642843421^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4065035927 5000000000 7623642843421 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2292597923/10000000000 : ℝ), (-813559251/5000000000 : ℝ), (4065035927/5000000000 : ℝ)] ![(14507574629727/100000000000000 : ℝ), (578499807789/6250000000000 : ℝ), (7623642843421/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2292597923/10000000000 : ℝ)|^135 ≤ (14507574629727/100000000000000 : ℝ)^103
        have hw : |(2292597923/10000000000 : ℝ)|=(2292597923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-813559251/5000000000 : ℝ)|^135 ≤ (578499807789/6250000000000 : ℝ)^103
        have hw : |(-813559251/5000000000 : ℝ)|=(813559251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4065035927/5000000000 : ℝ)|^135 ≤ (7623642843421/10000000000000 : ℝ)^103
        have hw : |(4065035927/5000000000 : ℝ)|=(4065035927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2203107/400000000 : ℝ)*x 0 + (-8074062961/10000000000 : ℝ)*x 1 + (170129431/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203107/400000000 : ℝ)^135 ≤ (27357901661/25000000000000 : ℝ)^103 := by
    have hnat : (2203107 : ℕ)^135*25000000000000^103 ≤ 27357901661^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203107 400000000 27357901661 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8074062961/10000000000 : ℝ)^135 ≤ (4721799790653/6250000000000 : ℝ)^103 := by
    have hnat : (8074062961 : ℕ)^135*6250000000000^103 ≤ 4721799790653^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8074062961 10000000000 4721799790653 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (170129431/500000000 : ℝ)^135 ≤ (24341771729701/100000000000000 : ℝ)^103 := by
    have hnat : (170129431 : ℕ)^135*100000000000000^103 ≤ 24341771729701^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170129431 500000000 24341771729701 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2203107/400000000 : ℝ), (-8074062961/10000000000 : ℝ), (170129431/500000000 : ℝ)] ![(27357901661/25000000000000 : ℝ), (4721799790653/6250000000000 : ℝ), (24341771729701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2203107/400000000 : ℝ)|^135 ≤ (27357901661/25000000000000 : ℝ)^103
        have hw : |(2203107/400000000 : ℝ)|=(2203107/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8074062961/10000000000 : ℝ)|^135 ≤ (4721799790653/6250000000000 : ℝ)^103
        have hw : |(-8074062961/10000000000 : ℝ)|=(8074062961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(170129431/500000000 : ℝ)|^135 ≤ (24341771729701/100000000000000 : ℝ)^103
        have hw : |(170129431/500000000 : ℝ)|=(170129431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3996778609/5000000000 : ℝ)*x 0 + (2297097563/10000000000 : ℝ)*x 1 + (921131059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3996778609/5000000000 : ℝ)^135 ≤ (18640751846213/25000000000000 : ℝ)^103 := by
    have hnat : (3996778609 : ℕ)^135*25000000000000^103 ≤ 18640751846213^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3996778609 5000000000 18640751846213 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2297097563/10000000000 : ℝ)^135 ≤ (14544905968113/100000000000000 : ℝ)^103 := by
    have hnat : (2297097563 : ℕ)^135*100000000000000^103 ≤ 14544905968113^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2297097563 10000000000 14544905968113 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921131059/5000000000 : ℝ)^135 ≤ (170188853641/1562500000000 : ℝ)^103 := by
    have hnat : (921131059 : ℕ)^135*1562500000000^103 ≤ 170188853641^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921131059 5000000000 170188853641 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3996778609/5000000000 : ℝ), (2297097563/10000000000 : ℝ), (921131059/5000000000 : ℝ)] ![(18640751846213/25000000000000 : ℝ), (14544905968113/100000000000000 : ℝ), (170188853641/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3996778609/5000000000 : ℝ)|^135 ≤ (18640751846213/25000000000000 : ℝ)^103
        have hw : |(3996778609/5000000000 : ℝ)|=(3996778609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2297097563/10000000000 : ℝ)|^135 ≤ (14544905968113/100000000000000 : ℝ)^103
        have hw : |(2297097563/10000000000 : ℝ)|=(2297097563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921131059/5000000000 : ℝ)|^135 ≤ (170188853641/1562500000000 : ℝ)^103
        have hw : |(921131059/5000000000 : ℝ)|=(921131059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2157656613/5000000000 : ℝ)*x 0 + (-2659235903/5000000000 : ℝ)*x 1 + (-3264141917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157656613/5000000000 : ℝ)^135 ≤ (16618357574193/50000000000000 : ℝ)^103 := by
    have hnat : (2157656613 : ℕ)^135*50000000000000^103 ≤ 16618357574193^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157656613 5000000000 16618357574193 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2659235903/5000000000 : ℝ)^135 ≤ (546392139529/1250000000000 : ℝ)^103 := by
    have hnat : (2659235903 : ℕ)^135*1250000000000^103 ≤ 546392139529^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2659235903 5000000000 546392139529 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3264141917/10000000000 : ℝ)^135 ≤ (11525956834027/50000000000000 : ℝ)^103 := by
    have hnat : (3264141917 : ℕ)^135*50000000000000^103 ≤ 11525956834027^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3264141917 10000000000 11525956834027 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157656613/5000000000 : ℝ), (-2659235903/5000000000 : ℝ), (-3264141917/10000000000 : ℝ)] ![(16618357574193/50000000000000 : ℝ), (546392139529/1250000000000 : ℝ), (11525956834027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157656613/5000000000 : ℝ)|^135 ≤ (16618357574193/50000000000000 : ℝ)^103
        have hw : |(2157656613/5000000000 : ℝ)|=(2157656613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2659235903/5000000000 : ℝ)|^135 ≤ (546392139529/1250000000000 : ℝ)^103
        have hw : |(-2659235903/5000000000 : ℝ)|=(2659235903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3264141917/10000000000 : ℝ)|^135 ≤ (11525956834027/50000000000000 : ℝ)^103
        have hw : |(-3264141917/10000000000 : ℝ)|=(3264141917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306086_s2_s2_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6391197301/10000000000 : ℝ)*x 0 + (-40723219/250000000 : ℝ)*x 1 + (4500349227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6391197301/10000000000 : ℝ)^135 ≤ (27806772912409/50000000000000 : ℝ)^103 := by
    have hnat : (6391197301 : ℕ)^135*50000000000000^103 ≤ 27806772912409^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6391197301 10000000000 27806772912409 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40723219/250000000 : ℝ)^135 ≤ (1158687046803/12500000000000 : ℝ)^103 := by
    have hnat : (40723219 : ℕ)^135*12500000000000^103 ≤ 1158687046803^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40723219 250000000 1158687046803 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500349227/10000000000 : ℝ)^135 ≤ (17558478890459/50000000000000 : ℝ)^103 := by
    have hnat : (4500349227 : ℕ)^135*50000000000000^103 ≤ 17558478890459^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500349227 10000000000 17558478890459 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6391197301/10000000000 : ℝ), (-40723219/250000000 : ℝ), (4500349227/10000000000 : ℝ)] ![(27806772912409/50000000000000 : ℝ), (1158687046803/12500000000000 : ℝ), (17558478890459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6391197301/10000000000 : ℝ)|^135 ≤ (27806772912409/50000000000000 : ℝ)^103
        have hw : |(6391197301/10000000000 : ℝ)|=(6391197301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-40723219/250000000 : ℝ)|^135 ≤ (1158687046803/12500000000000 : ℝ)^103
        have hw : |(-40723219/250000000 : ℝ)|=(40723219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500349227/10000000000 : ℝ)|^135 ≤ (17558478890459/50000000000000 : ℝ)^103
        have hw : |(4500349227/10000000000 : ℝ)|=(4500349227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306086_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((76841/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76841/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-88247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-88247/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43451/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43451/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39161/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39161/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19009/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19009/25000 : ℝ)*X 1 2) := by
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
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (76841/100000 : ℝ) ^ (67/16 : ℝ) ≤ (6636677542712588679/20000000000000000000 : ℝ) := by
    have hpowers : (76841/100000 : ℝ)^67 ≤ (6636677542712588679/20000000000000000000 : ℝ)^16 := by
      have hnat : (76841 : ℕ)^67*20000000000000000000^16 ≤ 6636677542712588679^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76841 100000 6636677542712588679 20000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76841/100000 : ℝ)) (X := (6636677542712588679/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (26636677542712588679/20000000000000000000 : ℝ) ≤ (10708272557407063/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (26636677542712588679/20000000000000000000 : ℝ)^16 ≤ (10708272557407063/10000000000000000 : ℝ)^67 := by
      have hnat : (26636677542712588679 : ℕ)^16*10000000000000000^67 ≤ 10708272557407063^67*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26636677542712588679 20000000000000000000 10708272557407063 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10708272557407063/10000000000000000 : ℝ)) (X := (26636677542712588679/20000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (16636677542712588679/10000000000000000000 : ℝ) ≤ (11292550038849577/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (16636677542712588679/10000000000000000000 : ℝ)^16 ≤ (11292550038849577/10000000000000000 : ℝ)^67 := by
      have hnat : (16636677542712588679 : ℕ)^16*10000000000000000^67 ≤ 11292550038849577^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16636677542712588679 10000000000000000000 11292550038849577 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11292550038849577/10000000000000000 : ℝ)) (X := (16636677542712588679/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(708272557407063/7684100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(292138740721257/3842050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (76841/100000 : ℝ)) (alpha := (708272557407063/7684100000000000 : ℝ)) (beta := (292138740721257/3842050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (76841/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(708272557407063/7684100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(292138740721257/3842050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (88247/100000 : ℝ) ^ (67/16 : ℝ) ≤ (59240476308551551091/100000000000000000000 : ℝ) := by
    have hpowers : (88247/100000 : ℝ)^67 ≤ (59240476308551551091/100000000000000000000 : ℝ)^16 := by
      have hnat : (88247 : ℕ)^67*100000000000000000000^16 ≤ 59240476308551551091^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88247 100000 59240476308551551091 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88247/100000 : ℝ)) (X := (59240476308551551091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (159240476308551551091/100000000000000000000 : ℝ) ≤ (447004160919133/400000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (159240476308551551091/100000000000000000000 : ℝ)^16 ≤ (447004160919133/400000000000000 : ℝ)^67 := by
      have hnat : (159240476308551551091 : ℕ)^16*400000000000000^67 ≤ 447004160919133^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        159240476308551551091 100000000000000000000 447004160919133 400000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (447004160919133/400000000000000 : ℝ)) (X := (159240476308551551091/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (109240476308551551091/50000000000000000000 : ℝ) ≤ (12051857540368713/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (109240476308551551091/50000000000000000000 : ℝ)^16 ≤ (12051857540368713/10000000000000000 : ℝ)^67 := by
      have hnat : (109240476308551551091 : ℕ)^16*10000000000000000^67 ≤ 12051857540368713^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        109240476308551551091 50000000000000000000 12051857540368713 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12051857540368713/10000000000000000 : ℝ)) (X := (109240476308551551091/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(47004160919133/352988000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(219188379347597/2206175000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (88247/100000 : ℝ)) (alpha := (47004160919133/352988000000000 : ℝ)) (beta := (219188379347597/2206175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (88247/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(47004160919133/352988000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(219188379347597/2206175000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (43451/50000 : ℝ) ^ (67/16 : ℝ) ≤ (55550397197719099911/100000000000000000000 : ℝ) := by
    have hpowers : (43451/50000 : ℝ)^67 ≤ (55550397197719099911/100000000000000000000 : ℝ)^16 := by
      have hnat : (43451 : ℕ)^67*100000000000000000000^16 ≤ 55550397197719099911^16*50000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43451 50000 55550397197719099911 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43451/50000 : ℝ)) (X := (55550397197719099911/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (155550397197719099911/100000000000000000000 : ℝ) ≤ (11112709717748619/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (155550397197719099911/100000000000000000000 : ℝ)^16 ≤ (11112709717748619/10000000000000000 : ℝ)^67 := by
      have hnat : (155550397197719099911 : ℕ)^16*10000000000000000^67 ≤ 11112709717748619^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        155550397197719099911 100000000000000000000 11112709717748619 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11112709717748619/10000000000000000 : ℝ)) (X := (155550397197719099911/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (105550397197719099911/50000000000000000000 : ℝ) ≤ (5976681627551703/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (105550397197719099911/50000000000000000000 : ℝ)^16 ≤ (5976681627551703/5000000000000000 : ℝ)^67 := by
      have hnat : (105550397197719099911 : ℕ)^16*5000000000000000^67 ≤ 5976681627551703^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105550397197719099911 50000000000000000000 5976681627551703 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5976681627551703/5000000000000000 : ℝ)) (X := (105550397197719099911/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1112709717748619/8690200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(840653537354787/8690200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (43451/50000 : ℝ)) (alpha := (1112709717748619/8690200000000000 : ℝ)) (beta := (840653537354787/8690200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (43451/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1112709717748619/8690200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(840653537354787/8690200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-18976763/10000000000 : ℝ)*X 0 0+(-811375571/1250000000 : ℝ)*X 0 1+(5272639923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((745902773/2000000000 : ℝ)*X 0 0+(-2839878523/10000000000 : ℝ)*X 0 1+(309549671/500000000 : ℝ)*X 0 2+(745902773/2000000000 : ℝ)*X 1 0+(-2839878523/10000000000 : ℝ)*X 1 1+(309549671/500000000 : ℝ)*X 1 2+(745902773/2000000000 : ℝ)*X 2 0+(-2839878523/10000000000 : ℝ)*X 2 1+(309549671/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((2458653/2000000000 : ℝ)*X 0 0+(-2033375333/2500000000 : ℝ)*X 0 1+(416822649/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((209145089/400000000 : ℝ)*X 1 0+(1191449177/2500000000 : ℝ)*X 1 1+(143069557/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((48940961/80000000 : ℝ)*X 2 0+(-211143223/625000000 : ℝ)*X 2 1+(-51540713/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((580391991/2000000000 : ℝ)*X 0 0+(-1392002359/10000000000 : ℝ)*X 0 1+(122507973/156250000 : ℝ)*X 0 2+(580391991/2000000000 : ℝ)*X 1 0+(-1392002359/10000000000 : ℝ)*X 1 1+(122507973/156250000 : ℝ)*X 1 2+(580391991/2000000000 : ℝ)*X 2 0+(-1392002359/10000000000 : ℝ)*X 2 1+(122507973/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-5049/100000000 : ℝ)*X 0 0+(-1116935491/2500000000 : ℝ)*X 0 1+(3608516581/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((167043701/200000000 : ℝ)*X 1 0+(2039587227/10000000000 : ℝ)*X 1 1+(767559899/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((393987159/500000000 : ℝ)*X 2 0+(-2690175817/10000000000 : ℝ)*X 2 1+(-1583855309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2292597923/10000000000 : ℝ)*X 0 0+(-813559251/5000000000 : ℝ)*X 0 1+(4065035927/5000000000 : ℝ)*X 0 2+(2292597923/10000000000 : ℝ)*X 1 0+(-813559251/5000000000 : ℝ)*X 1 1+(4065035927/5000000000 : ℝ)*X 1 2+(2292597923/10000000000 : ℝ)*X 2 0+(-813559251/5000000000 : ℝ)*X 2 1+(4065035927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((2203107/400000000 : ℝ)*X 0 0+(-8074062961/10000000000 : ℝ)*X 0 1+(170129431/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3996778609/5000000000 : ℝ)*X 1 0+(2297097563/10000000000 : ℝ)*X 1 1+(921131059/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2157656613/5000000000 : ℝ)*X 2 0+(-2659235903/5000000000 : ℝ)*X 2 1+(-3264141917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6391197301/10000000000 : ℝ)*X 0 0+(-40723219/250000000 : ℝ)*X 0 1+(4500349227/10000000000 : ℝ)*X 0 2+(6391197301/10000000000 : ℝ)*X 1 0+(-40723219/250000000 : ℝ)*X 1 1+(4500349227/10000000000 : ℝ)*X 1 2+(6391197301/10000000000 : ℝ)*X 2 0+(-40723219/250000000 : ℝ)*X 2 1+(4500349227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306086_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((58261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22055711537457329313655360302579/3683008721573462500000000000000000000 : ℝ) := by norm_num
    linear_combination (250127105337/500000000000 : ℝ)*(base7) + (4649617/1000000000000 : ℝ)*(base40) + (24708803827/62500000000 : ℝ)*(base54) + (798359/1000000000000 : ℝ)*(base60) + (107519874023/50000000000 : ℝ)*(major_s2_0) + (107519874023/50000000000 : ℝ)*(major_s2_1) + (438764154807/250000000000 : ℝ)*(major_s2_2) + (3977789/250000000000 : ℝ)*(sp_s2_6) + (324414213419/125000000000 : ℝ)*(sp_s2_7) + (648991959889/250000000000 : ℝ)*(sp_s2_8) + (550156744581/250000000000 : ℝ)*(sp_s2_9) + (749768349751/500000000000 : ℝ)*(sp_s2_13) + (19129221/500000000000 : ℝ)*(sp_s2_20) + (163533051/250000000000 : ℝ)*(sp_s2_21) + (697338759829/500000000000 : ℝ)*(f.failure) + (648991959889/250000000000 : ℝ)*(f.sum) + (84607755167027407669/191721019850000000000000000000000 : ℝ)*base62 + (337115056042619/2172550000000000000000000000 : ℝ)*base64 + (102778474804631/441235000000000000000000000 : ℝ)*base66 + (1215047129656547/2172550000000000000000000000 : ℝ)*base68 + (28767042969875749431/166940914550000000000000000000000 : ℝ)*base71 + (25907780823763/48025625000000000000000000 : ℝ)*base72 + (47372442338713/110308750000000000000000000 : ℝ)*base74 + (5054795809411/7684100000000000000000000 : ℝ)*base77 + (4399128236042483841/6780987727000000000000000000000 : ℝ)*base78 + (2903/25000000000000000 : ℝ)*base86 + (2903/25000000000000000 : ℝ)*base88 + (2903/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-39161/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39161/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (746808570737852063197613564733/173318057485810000000000000000000000 : ℝ) := by norm_num
    linear_combination (830480435049/1000000000000 : ℝ)*(base7) + (1253423/500000000000 : ℝ)*(base33) + (23574813043/500000000000 : ℝ)*(base40) + (2046863/1000000000000 : ℝ)*(base54) + (2621525827/62500000000 : ℝ)*(base60) + (235614329343/125000000000 : ℝ)*(major_s2_0) + (1884917141589/1000000000000 : ℝ)*(major_s2_1) + (942457547363/500000000000 : ℝ)*(major_s2_2) + (23612301/1000000000000 : ℝ)*(sp_s2_13) + (203245593761/100000000000 : ℝ)*(sp_s2_14) + (1016207217801/500000000000 : ℝ)*(sp_s2_15) + (2032451383901/1000000000000 : ℝ)*(sp_s2_16) + (2052950425029/1000000000000 : ℝ)*(sp_s2_20) + (19497581/500000000000 : ℝ)*(sp_s2_22) + (152811956143/125000000000 : ℝ)*(f.failure) + (203245593761/100000000000 : ℝ)*(f.sum) + (5742674963076477897/22555414100000000000000000000000 : ℝ)*base62 + (1638861973896389/4345100000000000000000000000 : ℝ)*base65 + (62608278444151/103820000000000000000000000 : ℝ)*base66 + (956069724624317/4345100000000000000000000000 : ℝ)*base69 + (144200515422349683421/333881829100000000000000000000000 : ℝ)*base71 + (1692126701666271/1921025000000000000000000000 : ℝ)*base72 + (23381858315247/64887500000000000000000000 : ℝ)*base75 + (1605746369617453/1921025000000000000000000000 : ℝ)*base77 + (24569940580091764509/39888163100000000000000000000000 : ℝ)*base78 + (5201/6250000000000000 : ℝ)*base86 + (1049/6250000000000000 : ℝ)*base89 + (1049/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19009/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19009/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5046760141490325554797923/311626274218750000000000000000 : ℝ) := by norm_num
    linear_combination (101326839313/125000000000 : ℝ)*(base7) + (64232129733/250000000000 : ℝ)*(base40) + (169448194971/1000000000000 : ℝ)*(base43) + (32279/7812500000 : ℝ)*(base50) + (1204715700077/500000000000 : ℝ)*(major_s2_0) + (34999737581/15625000000 : ℝ)*(major_s2_1) + (1204715700077/500000000000 : ℝ)*(major_s2_2) + (3559927/200000000000 : ℝ)*(sp_s2_0) + (55048053/500000000000 : ℝ)*(sp_s2_15) + (5312927/250000000000 : ℝ)*(sp_s2_16) + (1292074021649/500000000000 : ℝ)*(sp_s2_21) + (1376751970899/500000000000 : ℝ)*(sp_s2_22) + (1292072295613/500000000000 : ℝ)*(sp_s2_23) + (2373293167901/1000000000000 : ℝ)*(sp_s2_27) + (1562678453397/1000000000000 : ℝ)*(f.failure) + (172100877369/62500000000 : ℝ)*(f.sum) + (1514618861295704349/22555414100000000000000000000000 : ℝ)*base63 + (3096675126289419/4345100000000000000000000000 : ℝ)*base64 + (266116180151/1622187500000000000000000 : ℝ)*base66 + (616756695583487/4345100000000000000000000000 : ℝ)*base68 + (158050856059692687683/333881829100000000000000000000000 : ℝ)*base71 + (3010433660104617/3842050000000000000000000000 : ℝ)*base72 + (100464637342047/259550000000000000000000000 : ℝ)*base74 + (1089338139344011/3842050000000000000000000000 : ℝ)*base77 + (8731226010420496917/19944081550000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (34921/50000000000000000 : ℝ)*base87 + (15079/50000000000000000 : ℝ)*base88 + (34921/50000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((76841/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(76841/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-88247/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-88247/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43451/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43451/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58261/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58261/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-39161/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-39161/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19009/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19009/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306086_s2 p hpa hpb X hX hprev1

#print axioms solution
