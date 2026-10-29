-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308052_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:36:14.254209+00:00
-- url     : https://prove2.me/submissions/2b920a6a-b5c0-4924-a2a8-a8fed1cd1e95

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
theorem collision_support_c308052_s2_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-217686431/1000000000 : ℝ)*x 0 + (874887717/2500000000 : ℝ)*x 1 + (-6786832563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217686431/1000000000 : ℝ)^35 ≤ (13855852238011/100000000000000 : ℝ)^27 := by
    have hnat : (217686431 : ℕ)^35*100000000000000^27 ≤ 13855852238011^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217686431 1000000000 13855852238011 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874887717/2500000000 : ℝ)^35 ≤ (5127844451243/20000000000000 : ℝ)^27 := by
    have hnat : (874887717 : ℕ)^35*20000000000000^27 ≤ 5127844451243^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874887717 2500000000 5127844451243 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6786832563/10000000000 : ℝ)^35 ≤ (236347365183/390625000000 : ℝ)^27 := by
    have hnat : (6786832563 : ℕ)^35*390625000000^27 ≤ 236347365183^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6786832563 10000000000 236347365183 390625000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217686431/1000000000 : ℝ), (874887717/2500000000 : ℝ), (-6786832563/10000000000 : ℝ)] ![(13855852238011/100000000000000 : ℝ), (5127844451243/20000000000000 : ℝ), (236347365183/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217686431/1000000000 : ℝ)|^35 ≤ (13855852238011/100000000000000 : ℝ)^27
        have hw : |(-217686431/1000000000 : ℝ)|=(217686431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(874887717/2500000000 : ℝ)|^35 ≤ (5127844451243/20000000000000 : ℝ)^27
        have hw : |(874887717/2500000000 : ℝ)|=(874887717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6786832563/10000000000 : ℝ)|^35 ≤ (236347365183/390625000000 : ℝ)^27
        have hw : |(-6786832563/10000000000 : ℝ)|=(6786832563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4593151389/10000000000 : ℝ)*x 0 + (-13339437/40000000 : ℝ)*x 1 + (-975695799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4593151389/10000000000 : ℝ)^35 ≤ (2279688176663/6250000000000 : ℝ)^27 := by
    have hnat : (4593151389 : ℕ)^35*6250000000000^27 ≤ 2279688176663^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4593151389 10000000000 2279688176663 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13339437/40000000 : ℝ)^35 ≤ (6021534097067/25000000000000 : ℝ)^27 := by
    have hnat : (13339437 : ℕ)^35*25000000000000^27 ≤ 6021534097067^27*40000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13339437 40000000 6021534097067 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975695799/2000000000 : ℝ)^35 ≤ (39438852767857/100000000000000 : ℝ)^27 := by
    have hnat : (975695799 : ℕ)^35*100000000000000^27 ≤ 39438852767857^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975695799 2000000000 39438852767857 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4593151389/10000000000 : ℝ), (-13339437/40000000 : ℝ), (-975695799/2000000000 : ℝ)] ![(2279688176663/6250000000000 : ℝ), (6021534097067/25000000000000 : ℝ), (39438852767857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4593151389/10000000000 : ℝ)|^35 ≤ (2279688176663/6250000000000 : ℝ)^27
        have hw : |(4593151389/10000000000 : ℝ)|=(4593151389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13339437/40000000 : ℝ)|^35 ≤ (6021534097067/25000000000000 : ℝ)^27
        have hw : |(-13339437/40000000 : ℝ)|=(13339437/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-975695799/2000000000 : ℝ)|^35 ≤ (39438852767857/100000000000000 : ℝ)^27
        have hw : |(-975695799/2000000000 : ℝ)|=(975695799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6170819609/10000000000 : ℝ)*x 0 + (27290513/62500000 : ℝ)*x 1 + (-1992891801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6170819609/10000000000 : ℝ)^35 ≤ (10696758966211/20000000000000 : ℝ)^27 := by
    have hnat : (6170819609 : ℕ)^35*20000000000000^27 ≤ 10696758966211^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6170819609 10000000000 10696758966211 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27290513/62500000 : ℝ)^35 ≤ (34158912232833/100000000000000 : ℝ)^27 := by
    have hnat : (27290513 : ℕ)^35*100000000000000^27 ≤ 34158912232833^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27290513 62500000 34158912232833 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1992891801/10000000000 : ℝ)^35 ≤ (61786464583/500000000000 : ℝ)^27 := by
    have hnat : (1992891801 : ℕ)^35*500000000000^27 ≤ 61786464583^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992891801 10000000000 61786464583 500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6170819609/10000000000 : ℝ), (27290513/62500000 : ℝ), (-1992891801/10000000000 : ℝ)] ![(10696758966211/20000000000000 : ℝ), (34158912232833/100000000000000 : ℝ), (61786464583/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6170819609/10000000000 : ℝ)|^35 ≤ (10696758966211/20000000000000 : ℝ)^27
        have hw : |(6170819609/10000000000 : ℝ)|=(6170819609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27290513/62500000 : ℝ)|^35 ≤ (34158912232833/100000000000000 : ℝ)^27
        have hw : |(27290513/62500000 : ℝ)|=(27290513/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1992891801/10000000000 : ℝ)|^35 ≤ (61786464583/500000000000 : ℝ)^27
        have hw : |(-1992891801/10000000000 : ℝ)|=(1992891801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001237229/10000000000 : ℝ)*x 0 + (2886455091/10000000000 : ℝ)*x 1 + (-7393023581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001237229/10000000000 : ℝ)^35 ≤ (12424414408017/100000000000000 : ℝ)^27 := by
    have hnat : (2001237229 : ℕ)^35*100000000000000^27 ≤ 12424414408017^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001237229 10000000000 12424414408017 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2886455091/10000000000 : ℝ)^35 ≤ (19974361025579/100000000000000 : ℝ)^27 := by
    have hnat : (2886455091 : ℕ)^35*100000000000000^27 ≤ 19974361025579^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2886455091 10000000000 19974361025579 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7393023581/10000000000 : ℝ)^35 ≤ (67601224552221/100000000000000 : ℝ)^27 := by
    have hnat : (7393023581 : ℕ)^35*100000000000000^27 ≤ 67601224552221^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7393023581 10000000000 67601224552221 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001237229/10000000000 : ℝ), (2886455091/10000000000 : ℝ), (-7393023581/10000000000 : ℝ)] ![(12424414408017/100000000000000 : ℝ), (19974361025579/100000000000000 : ℝ), (67601224552221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001237229/10000000000 : ℝ)|^35 ≤ (12424414408017/100000000000000 : ℝ)^27
        have hw : |(-2001237229/10000000000 : ℝ)|=(2001237229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2886455091/10000000000 : ℝ)|^35 ≤ (19974361025579/100000000000000 : ℝ)^27
        have hw : |(2886455091/10000000000 : ℝ)|=(2886455091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7393023581/10000000000 : ℝ)|^35 ≤ (67601224552221/100000000000000 : ℝ)^27
        have hw : |(-7393023581/10000000000 : ℝ)|=(7393023581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4204312993/10000000000 : ℝ)*x 0 + (-1236677501/5000000000 : ℝ)*x 1 + (-595992541/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204312993/10000000000 : ℝ)^35 ≤ (6504699972211/20000000000000 : ℝ)^27 := by
    have hnat : (4204312993 : ℕ)^35*20000000000000^27 ≤ 6504699972211^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204312993 10000000000 6504699972211 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1236677501/5000000000 : ℝ)^35 ≤ (4087516208823/25000000000000 : ℝ)^27 := by
    have hnat : (1236677501 : ℕ)^35*25000000000000^27 ≤ 4087516208823^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1236677501 5000000000 4087516208823 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595992541/1000000000 : ℝ)^35 ≤ (25563217639889/50000000000000 : ℝ)^27 := by
    have hnat : (595992541 : ℕ)^35*50000000000000^27 ≤ 25563217639889^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595992541 1000000000 25563217639889 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204312993/10000000000 : ℝ), (-1236677501/5000000000 : ℝ), (-595992541/1000000000 : ℝ)] ![(6504699972211/20000000000000 : ℝ), (4087516208823/25000000000000 : ℝ), (25563217639889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204312993/10000000000 : ℝ)|^35 ≤ (6504699972211/20000000000000 : ℝ)^27
        have hw : |(4204312993/10000000000 : ℝ)|=(4204312993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1236677501/5000000000 : ℝ)|^35 ≤ (4087516208823/25000000000000 : ℝ)^27
        have hw : |(-1236677501/5000000000 : ℝ)|=(1236677501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-595992541/1000000000 : ℝ)|^35 ≤ (25563217639889/50000000000000 : ℝ)^27
        have hw : |(-595992541/1000000000 : ℝ)|=(595992541/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2264048241/5000000000 : ℝ)*x 0 + (3350803493/5000000000 : ℝ)*x 1 + (940966739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2264048241/5000000000 : ℝ)^35 ≤ (1790336905967/5000000000000 : ℝ)^27 := by
    have hnat : (2264048241 : ℕ)^35*5000000000000^27 ≤ 1790336905967^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264048241 5000000000 1790336905967 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3350803493/5000000000 : ℝ)^35 ≤ (5952185031383/10000000000000 : ℝ)^27 := by
    have hnat : (3350803493 : ℕ)^35*10000000000000^27 ≤ 5952185031383^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3350803493 5000000000 5952185031383 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940966739/10000000000 : ℝ)^35 ≤ (2335705778699/50000000000000 : ℝ)^27 := by
    have hnat : (940966739 : ℕ)^35*50000000000000^27 ≤ 2335705778699^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940966739 10000000000 2335705778699 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2264048241/5000000000 : ℝ), (3350803493/5000000000 : ℝ), (940966739/10000000000 : ℝ)] ![(1790336905967/5000000000000 : ℝ), (5952185031383/10000000000000 : ℝ), (2335705778699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2264048241/5000000000 : ℝ)|^35 ≤ (1790336905967/5000000000000 : ℝ)^27
        have hw : |(2264048241/5000000000 : ℝ)|=(2264048241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3350803493/5000000000 : ℝ)|^35 ≤ (5952185031383/10000000000000 : ℝ)^27
        have hw : |(3350803493/5000000000 : ℝ)|=(3350803493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(940966739/10000000000 : ℝ)|^35 ≤ (2335705778699/50000000000000 : ℝ)^27
        have hw : |(940966739/10000000000 : ℝ)|=(940966739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1150430209/2000000000 : ℝ)*x 0 + (350030133/625000000 : ℝ)*x 1 + (-835840961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1150430209/2000000000 : ℝ)^35 ≤ (24413997057967/50000000000000 : ℝ)^27 := by
    have hnat : (1150430209 : ℕ)^35*50000000000000^27 ≤ 24413997057967^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150430209 2000000000 24413997057967 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (350030133/625000000 : ℝ)^35 ≤ (47165619038347/100000000000000 : ℝ)^27 := by
    have hnat : (350030133 : ℕ)^35*100000000000000^27 ≤ 47165619038347^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      350030133 625000000 47165619038347 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (835840961/10000000000 : ℝ)^35 ≤ (4006386833607/100000000000000 : ℝ)^27 := by
    have hnat : (835840961 : ℕ)^35*100000000000000^27 ≤ 4006386833607^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835840961 10000000000 4006386833607 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1150430209/2000000000 : ℝ), (350030133/625000000 : ℝ), (-835840961/10000000000 : ℝ)] ![(24413997057967/50000000000000 : ℝ), (47165619038347/100000000000000 : ℝ), (4006386833607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1150430209/2000000000 : ℝ)|^35 ≤ (24413997057967/50000000000000 : ℝ)^27
        have hw : |(1150430209/2000000000 : ℝ)|=(1150430209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(350030133/625000000 : ℝ)|^35 ≤ (47165619038347/100000000000000 : ℝ)^27
        have hw : |(350030133/625000000 : ℝ)|=(350030133/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-835840961/10000000000 : ℝ)|^35 ≤ (4006386833607/100000000000000 : ℝ)^27
        have hw : |(-835840961/10000000000 : ℝ)|=(835840961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1261950129/10000000000 : ℝ)*x 0 + (138042423/400000000 : ℝ)*x 1 + (-7425481479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1261950129/10000000000 : ℝ)^35 ≤ (6834147115803/100000000000000 : ℝ)^27 := by
    have hnat : (1261950129 : ℕ)^35*100000000000000^27 ≤ 6834147115803^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1261950129 10000000000 6834147115803 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138042423/400000000 : ℝ)^35 ≤ (12589823687063/50000000000000 : ℝ)^27 := by
    have hnat : (138042423 : ℕ)^35*50000000000000^27 ≤ 12589823687063^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138042423 400000000 12589823687063 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7425481479/10000000000 : ℝ)^35 ≤ (16996551374501/25000000000000 : ℝ)^27 := by
    have hnat : (7425481479 : ℕ)^35*25000000000000^27 ≤ 16996551374501^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7425481479 10000000000 16996551374501 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1261950129/10000000000 : ℝ), (138042423/400000000 : ℝ), (-7425481479/10000000000 : ℝ)] ![(6834147115803/100000000000000 : ℝ), (12589823687063/50000000000000 : ℝ), (16996551374501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1261950129/10000000000 : ℝ)|^35 ≤ (6834147115803/100000000000000 : ℝ)^27
        have hw : |(-1261950129/10000000000 : ℝ)|=(1261950129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138042423/400000000 : ℝ)|^35 ≤ (12589823687063/50000000000000 : ℝ)^27
        have hw : |(138042423/400000000 : ℝ)|=(138042423/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7425481479/10000000000 : ℝ)|^35 ≤ (16996551374501/25000000000000 : ℝ)^27
        have hw : |(-7425481479/10000000000 : ℝ)|=(7425481479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2029201709/5000000000 : ℝ)*x 0 + (-86779471/312500000 : ℝ)*x 1 + (-1170490031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2029201709/5000000000 : ℝ)^35 ≤ (31067929847869/100000000000000 : ℝ)^27 := by
    have hnat : (2029201709 : ℕ)^35*100000000000000^27 ≤ 31067929847869^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029201709 5000000000 31067929847869 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86779471/312500000 : ℝ)^35 ≤ (18997564721799/100000000000000 : ℝ)^27 := by
    have hnat : (86779471 : ℕ)^35*100000000000000^27 ≤ 18997564721799^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86779471 312500000 18997564721799 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1170490031/2000000000 : ℝ)^35 ≤ (499345054179/1000000000000 : ℝ)^27 := by
    have hnat : (1170490031 : ℕ)^35*1000000000000^27 ≤ 499345054179^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170490031 2000000000 499345054179 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2029201709/5000000000 : ℝ), (-86779471/312500000 : ℝ), (-1170490031/2000000000 : ℝ)] ![(31067929847869/100000000000000 : ℝ), (18997564721799/100000000000000 : ℝ), (499345054179/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2029201709/5000000000 : ℝ)|^35 ≤ (31067929847869/100000000000000 : ℝ)^27
        have hw : |(2029201709/5000000000 : ℝ)|=(2029201709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86779471/312500000 : ℝ)|^35 ≤ (18997564721799/100000000000000 : ℝ)^27
        have hw : |(-86779471/312500000 : ℝ)|=(86779471/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1170490031/2000000000 : ℝ)|^35 ≤ (499345054179/1000000000000 : ℝ)^27
        have hw : |(-1170490031/2000000000 : ℝ)|=(1170490031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (9433179/16000000 : ℝ)*x 0 + (2663958963/5000000000 : ℝ)*x 1 + (1048443123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9433179/16000000 : ℝ)^35 ≤ (12603448417941/25000000000000 : ℝ)^27 := by
    have hnat : (9433179 : ℕ)^35*25000000000000^27 ≤ 12603448417941^27*16000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9433179 16000000 12603448417941 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2663958963/5000000000 : ℝ)^35 ≤ (44211732516863/100000000000000 : ℝ)^27 := by
    have hnat : (2663958963 : ℕ)^35*100000000000000^27 ≤ 44211732516863^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663958963 5000000000 44211732516863 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048443123/10000000000 : ℝ)^35 ≤ (1343618448453/25000000000000 : ℝ)^27 := by
    have hnat : (1048443123 : ℕ)^35*25000000000000^27 ≤ 1343618448453^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048443123 10000000000 1343618448453 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9433179/16000000 : ℝ), (2663958963/5000000000 : ℝ), (1048443123/10000000000 : ℝ)] ![(12603448417941/25000000000000 : ℝ), (44211732516863/100000000000000 : ℝ), (1343618448453/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9433179/16000000 : ℝ)|^35 ≤ (12603448417941/25000000000000 : ℝ)^27
        have hw : |(9433179/16000000 : ℝ)|=(9433179/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2663958963/5000000000 : ℝ)|^35 ≤ (44211732516863/100000000000000 : ℝ)^27
        have hw : |(2663958963/5000000000 : ℝ)|=(2663958963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048443123/10000000000 : ℝ)|^35 ≤ (1343618448453/25000000000000 : ℝ)^27
        have hw : |(1048443123/10000000000 : ℝ)|=(1048443123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7404597597/10000000000 : ℝ)*x 0 + (3815603603/10000000000 : ℝ)*x 1 + (-191642531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7404597597/10000000000 : ℝ)^35 ≤ (33869222922683/50000000000000 : ℝ)^27 := by
    have hnat : (7404597597 : ℕ)^35*50000000000000^27 ≤ 33869222922683^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7404597597 10000000000 33869222922683 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3815603603/10000000000 : ℝ)^35 ≤ (28680187814339/100000000000000 : ℝ)^27 := by
    have hnat : (3815603603 : ℕ)^35*100000000000000^27 ≤ 28680187814339^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3815603603 10000000000 28680187814339 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (191642531/2500000000 : ℝ)^35 ≤ (3581366321701/100000000000000 : ℝ)^27 := by
    have hnat : (191642531 : ℕ)^35*100000000000000^27 ≤ 3581366321701^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191642531 2500000000 3581366321701 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7404597597/10000000000 : ℝ), (3815603603/10000000000 : ℝ), (-191642531/2500000000 : ℝ)] ![(33869222922683/50000000000000 : ℝ), (28680187814339/100000000000000 : ℝ), (3581366321701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7404597597/10000000000 : ℝ)|^35 ≤ (33869222922683/50000000000000 : ℝ)^27
        have hw : |(7404597597/10000000000 : ℝ)|=(7404597597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3815603603/10000000000 : ℝ)|^35 ≤ (28680187814339/100000000000000 : ℝ)^27
        have hw : |(3815603603/10000000000 : ℝ)|=(3815603603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-191642531/2500000000 : ℝ)|^35 ≤ (3581366321701/100000000000000 : ℝ)^27
        have hw : |(-191642531/2500000000 : ℝ)|=(191642531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-928140427/10000000000 : ℝ)*x 0 + (43050073/100000000 : ℝ)*x 1 + (-6905010031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928140427/10000000000 : ℝ)^35 ≤ (917807168051/20000000000000 : ℝ)^27 := by
    have hnat : (928140427 : ℕ)^35*20000000000000^27 ≤ 917807168051^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928140427 10000000000 917807168051 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43050073/100000000 : ℝ)^35 ≤ (33536807044059/100000000000000 : ℝ)^27 := by
    have hnat : (43050073 : ℕ)^35*100000000000000^27 ≤ 33536807044059^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43050073 100000000 33536807044059 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6905010031/10000000000 : ℝ)^35 ≤ (61874157103321/100000000000000 : ℝ)^27 := by
    have hnat : (6905010031 : ℕ)^35*100000000000000^27 ≤ 61874157103321^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6905010031 10000000000 61874157103321 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928140427/10000000000 : ℝ), (43050073/100000000 : ℝ), (-6905010031/10000000000 : ℝ)] ![(917807168051/20000000000000 : ℝ), (33536807044059/100000000000000 : ℝ), (61874157103321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928140427/10000000000 : ℝ)|^35 ≤ (917807168051/20000000000000 : ℝ)^27
        have hw : |(-928140427/10000000000 : ℝ)|=(928140427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43050073/100000000 : ℝ)|^35 ≤ (33536807044059/100000000000000 : ℝ)^27
        have hw : |(43050073/100000000 : ℝ)|=(43050073/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6905010031/10000000000 : ℝ)|^35 ≤ (61874157103321/100000000000000 : ℝ)^27
        have hw : |(-6905010031/10000000000 : ℝ)|=(6905010031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1476440863/2500000000 : ℝ)*x 0 + (-1296949609/5000000000 : ℝ)*x 1 + (-2080240389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1476440863/2500000000 : ℝ)^35 ≤ (5052496111633/10000000000000 : ℝ)^27 := by
    have hnat : (1476440863 : ℕ)^35*10000000000000^27 ≤ 5052496111633^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1476440863 2500000000 5052496111633 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296949609/5000000000 : ℝ)^35 ≤ (8695200007289/50000000000000 : ℝ)^27 := by
    have hnat : (1296949609 : ℕ)^35*50000000000000^27 ≤ 8695200007289^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296949609 5000000000 8695200007289 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080240389/5000000000 : ℝ)^35 ≤ (16042319432261/50000000000000 : ℝ)^27 := by
    have hnat : (2080240389 : ℕ)^35*50000000000000^27 ≤ 16042319432261^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080240389 5000000000 16042319432261 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1476440863/2500000000 : ℝ), (-1296949609/5000000000 : ℝ), (-2080240389/5000000000 : ℝ)] ![(5052496111633/10000000000000 : ℝ), (8695200007289/50000000000000 : ℝ), (16042319432261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1476440863/2500000000 : ℝ)|^35 ≤ (5052496111633/10000000000000 : ℝ)^27
        have hw : |(1476440863/2500000000 : ℝ)|=(1476440863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1296949609/5000000000 : ℝ)|^35 ≤ (8695200007289/50000000000000 : ℝ)^27
        have hw : |(-1296949609/5000000000 : ℝ)|=(1296949609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080240389/5000000000 : ℝ)|^35 ≤ (16042319432261/50000000000000 : ℝ)^27
        have hw : |(-2080240389/5000000000 : ℝ)|=(2080240389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4244888749/10000000000 : ℝ)*x 0 + (782502493/1250000000 : ℝ)*x 1 + (126290929/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244888749/10000000000 : ℝ)^35 ≤ (32930966668557/100000000000000 : ℝ)^27 := by
    have hnat : (4244888749 : ℕ)^35*100000000000000^27 ≤ 32930966668557^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244888749 10000000000 32930966668557 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (782502493/1250000000 : ℝ)^35 ≤ (6811015493091/12500000000000 : ℝ)^27 := by
    have hnat : (782502493 : ℕ)^35*12500000000000^27 ≤ 6811015493091^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782502493 1250000000 6811015493091 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126290929/625000000 : ℝ)^35 ≤ (6290454689461/50000000000000 : ℝ)^27 := by
    have hnat : (126290929 : ℕ)^35*50000000000000^27 ≤ 6290454689461^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126290929 625000000 6290454689461 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244888749/10000000000 : ℝ), (782502493/1250000000 : ℝ), (126290929/625000000 : ℝ)] ![(32930966668557/100000000000000 : ℝ), (6811015493091/12500000000000 : ℝ), (6290454689461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244888749/10000000000 : ℝ)|^35 ≤ (32930966668557/100000000000000 : ℝ)^27
        have hw : |(4244888749/10000000000 : ℝ)|=(4244888749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(782502493/1250000000 : ℝ)|^35 ≤ (6811015493091/12500000000000 : ℝ)^27
        have hw : |(782502493/1250000000 : ℝ)|=(782502493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126290929/625000000 : ℝ)|^35 ≤ (6290454689461/50000000000000 : ℝ)^27
        have hw : |(126290929/625000000 : ℝ)|=(126290929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s2_s2_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7697620939/10000000000 : ℝ)*x 0 + (3258152251/10000000000 : ℝ)*x 1 + (-1051690131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7697620939/10000000000 : ℝ)^35 ≤ (35616757823913/50000000000000 : ℝ)^27 := by
    have hnat : (7697620939 : ℕ)^35*50000000000000^27 ≤ 35616757823913^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7697620939 10000000000 35616757823913 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3258152251/10000000000 : ℝ)^35 ≤ (1460651517301/6250000000000 : ℝ)^27 := by
    have hnat : (3258152251 : ℕ)^35*6250000000000^27 ≤ 1460651517301^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3258152251 10000000000 1460651517301 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051690131/10000000000 : ℝ)^35 ≤ (5396060072631/100000000000000 : ℝ)^27 := by
    have hnat : (1051690131 : ℕ)^35*100000000000000^27 ≤ 5396060072631^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051690131 10000000000 5396060072631 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7697620939/10000000000 : ℝ), (3258152251/10000000000 : ℝ), (-1051690131/10000000000 : ℝ)] ![(35616757823913/50000000000000 : ℝ), (1460651517301/6250000000000 : ℝ), (5396060072631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7697620939/10000000000 : ℝ)|^35 ≤ (35616757823913/50000000000000 : ℝ)^27
        have hw : |(7697620939/10000000000 : ℝ)|=(7697620939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3258152251/10000000000 : ℝ)|^35 ≤ (1460651517301/6250000000000 : ℝ)^27
        have hw : |(3258152251/10000000000 : ℝ)|=(3258152251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051690131/10000000000 : ℝ)|^35 ≤ (5396060072631/100000000000000 : ℝ)^27
        have hw : |(-1051690131/10000000000 : ℝ)|=(1051690131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308052_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((16793/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16793/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70341/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70341/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10123/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10123/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40827/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40827/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44327/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44327/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-697/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-697/2500 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (16793/25000 : ℝ) ^ (17/4 : ℝ) ≤ (9215527329605228043/50000000000000000000 : ℝ) := by
    have hpowers : (16793/25000 : ℝ)^17 ≤ (9215527329605228043/50000000000000000000 : ℝ)^4 := by
      have hnat : (16793 : ℕ)^17*50000000000000000000^4 ≤ 9215527329605228043^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16793 25000 9215527329605228043 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16793/25000 : ℝ)) (X := (9215527329605228043/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (59215527329605228043/50000000000000000000 : ℝ) ≤ (10406052742832381/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (59215527329605228043/50000000000000000000 : ℝ)^4 ≤ (10406052742832381/10000000000000000 : ℝ)^17 := by
      have hnat : (59215527329605228043 : ℕ)^4*10000000000000000^17 ≤ 10406052742832381^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59215527329605228043 50000000000000000000 10406052742832381 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10406052742832381/10000000000000000 : ℝ)) (X := (59215527329605228043/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (34215527329605228043/25000000000000000000 : ℝ) ≤ (10766304090058187/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (34215527329605228043/25000000000000000000 : ℝ)^4 ≤ (10766304090058187/10000000000000000 : ℝ)^17 := by
      have hnat : (34215527329605228043 : ℕ)^4*10000000000000000^17 ≤ 10766304090058187^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34215527329605228043 25000000000000000000 10766304090058187 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10766304090058187/10000000000000000 : ℝ)) (X := (34215527329605228043/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(406052742832381/6717200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(180125673612903/3358600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (16793/25000 : ℝ)) (alpha := (406052742832381/6717200000000000 : ℝ)) (beta := (180125673612903/3358600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16793/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(406052742832381/6717200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(180125673612903/3358600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (70341/100000 : ℝ) ^ (17/4 : ℝ) ≤ (5605008761872883727/25000000000000000000 : ℝ) := by
    have hpowers : (70341/100000 : ℝ)^17 ≤ (5605008761872883727/25000000000000000000 : ℝ)^4 := by
      have hnat : (70341 : ℕ)^17*25000000000000000000^4 ≤ 5605008761872883727^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70341 100000 5605008761872883727 25000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70341/100000 : ℝ)) (X := (5605008761872883727/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (30605008761872883727/25000000000000000000 : ℝ) ≤ (10487480742072619/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (30605008761872883727/25000000000000000000 : ℝ)^4 ≤ (10487480742072619/10000000000000000 : ℝ)^17 := by
      have hnat : (30605008761872883727 : ℕ)^4*10000000000000000^17 ≤ 10487480742072619^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30605008761872883727 25000000000000000000 10487480742072619 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10487480742072619/10000000000000000 : ℝ)) (X := (30605008761872883727/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (18105008761872883727/12500000000000000000 : ℝ) ≤ (2182157868913421/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (18105008761872883727/12500000000000000000 : ℝ)^4 ≤ (2182157868913421/2000000000000000 : ℝ)^17 := by
      have hnat : (18105008761872883727 : ℕ)^4*2000000000000000^17 ≤ 2182157868913421^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18105008761872883727 12500000000000000000 2182157868913421 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2182157868913421/2000000000000000 : ℝ)) (X := (18105008761872883727/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(162493580690873/2344700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(70551433749081/1172350000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (70341/100000 : ℝ)) (alpha := (162493580690873/2344700000000000 : ℝ)) (beta := (70551433749081/1172350000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (70341/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(162493580690873/2344700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(70551433749081/1172350000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (10123/20000 : ℝ) ^ (17/4 : ℝ) ≤ (5535881371372643391/100000000000000000000 : ℝ) := by
    have hpowers : (10123/20000 : ℝ)^17 ≤ (5535881371372643391/100000000000000000000 : ℝ)^4 := by
      have hnat : (10123 : ℕ)^17*100000000000000000000^4 ≤ 5535881371372643391^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10123 20000 5535881371372643391 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10123/20000 : ℝ)) (X := (5535881371372643391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (105535881371372643391/100000000000000000000 : ℝ) ≤ (10127585437647497/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (105535881371372643391/100000000000000000000 : ℝ)^4 ≤ (10127585437647497/10000000000000000 : ℝ)^17 := by
      have hnat : (105535881371372643391 : ℕ)^4*10000000000000000^17 ≤ 10127585437647497^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105535881371372643391 100000000000000000000 10127585437647497 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10127585437647497/10000000000000000 : ℝ)) (X := (105535881371372643391/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (55535881371372643391/50000000000000000000 : ℝ) ≤ (5125075626399809/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (55535881371372643391/50000000000000000000 : ℝ)^4 ≤ (5125075626399809/5000000000000000 : ℝ)^17 := by
      have hnat : (55535881371372643391 : ℕ)^4*5000000000000000^17 ≤ 5125075626399809^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55535881371372643391 50000000000000000000 5125075626399809 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5125075626399809/5000000000000000 : ℝ)) (X := (55535881371372643391/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(127585437647497/5061500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(122565815152121/5061500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (10123/20000 : ℝ)) (alpha := (127585437647497/5061500000000000 : ℝ)) (beta := (122565815152121/5061500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (10123/20000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(127585437647497/5061500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(122565815152121/5061500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-217686431/1000000000 : ℝ)*X 0 0+(874887717/2500000000 : ℝ)*X 0 1+(-6786832563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4593151389/10000000000 : ℝ)*X 1 0+(-13339437/40000000 : ℝ)*X 1 1+(-975695799/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6170819609/10000000000 : ℝ)*X 0 0+(27290513/62500000 : ℝ)*X 0 1+(-1992891801/10000000000 : ℝ)*X 0 2+(6170819609/10000000000 : ℝ)*X 1 0+(27290513/62500000 : ℝ)*X 1 1+(-1992891801/10000000000 : ℝ)*X 1 2+(6170819609/10000000000 : ℝ)*X 2 0+(27290513/62500000 : ℝ)*X 2 1+(-1992891801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2001237229/10000000000 : ℝ)*X 0 0+(2886455091/10000000000 : ℝ)*X 0 1+(-7393023581/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4204312993/10000000000 : ℝ)*X 1 0+(-1236677501/5000000000 : ℝ)*X 1 1+(-595992541/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2264048241/5000000000 : ℝ)*X 2 0+(3350803493/5000000000 : ℝ)*X 2 1+(940966739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1150430209/2000000000 : ℝ)*X 0 0+(350030133/625000000 : ℝ)*X 0 1+(-835840961/10000000000 : ℝ)*X 0 2+(1150430209/2000000000 : ℝ)*X 1 0+(350030133/625000000 : ℝ)*X 1 1+(-835840961/10000000000 : ℝ)*X 1 2+(1150430209/2000000000 : ℝ)*X 2 0+(350030133/625000000 : ℝ)*X 2 1+(-835840961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1261950129/10000000000 : ℝ)*X 0 0+(138042423/400000000 : ℝ)*X 0 1+(-7425481479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2029201709/5000000000 : ℝ)*X 1 0+(-86779471/312500000 : ℝ)*X 1 1+(-1170490031/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((9433179/16000000 : ℝ)*X 2 0+(2663958963/5000000000 : ℝ)*X 2 1+(1048443123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7404597597/10000000000 : ℝ)*X 0 0+(3815603603/10000000000 : ℝ)*X 0 1+(-191642531/2500000000 : ℝ)*X 0 2+(7404597597/10000000000 : ℝ)*X 1 0+(3815603603/10000000000 : ℝ)*X 1 1+(-191642531/2500000000 : ℝ)*X 1 2+(7404597597/10000000000 : ℝ)*X 2 0+(3815603603/10000000000 : ℝ)*X 2 1+(-191642531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-928140427/10000000000 : ℝ)*X 0 0+(43050073/100000000 : ℝ)*X 0 1+(-6905010031/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1476440863/2500000000 : ℝ)*X 1 0+(-1296949609/5000000000 : ℝ)*X 1 1+(-2080240389/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4244888749/10000000000 : ℝ)*X 2 0+(782502493/1250000000 : ℝ)*X 2 1+(126290929/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((7697620939/10000000000 : ℝ)*X 0 0+(3258152251/10000000000 : ℝ)*X 0 1+(-1051690131/10000000000 : ℝ)*X 0 2+(7697620939/10000000000 : ℝ)*X 1 0+(3258152251/10000000000 : ℝ)*X 1 1+(-1051690131/10000000000 : ℝ)*X 1 2+(7697620939/10000000000 : ℝ)*X 2 0+(3258152251/10000000000 : ℝ)*X 2 1+(-1051690131/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((40827/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40827/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1236206503676058459086607543/84997769500000000000000000000000 : ℝ) := by norm_num
    linear_combination (388166908037/1000000000000 : ℝ)*(base39) + (2044851/1000000000000 : ℝ)*(base50) + (1074913709313/1000000000000 : ℝ)*(base59) + (4770874320209/1000000000000 : ℝ)*(major_s2_0) + (4770874320209/1000000000000 : ℝ)*(major_s2_1) + (4770874320209/1000000000000 : ℝ)*(major_s2_2) + (223493/20000000000 : ℝ)*(sp_s2_1) + (5564179/500000000000 : ℝ)*(sp_s2_6) + (6497366358663/1000000000000 : ℝ)*(sp_s2_7) + (6497011144561/1000000000000 : ℝ)*(sp_s2_8) + (649727371053/100000000000 : ℝ)*(sp_s2_9) + (608873261079/200000000000 : ℝ)*(sp_s2_13) + (344039451/1000000000000 : ℝ)*(sp_s2_15) + (92648133/1000000000000 : ℝ)*(sp_s2_23) + (3044377433753/1000000000000 : ℝ)*(f.failure) + (6497366358663/1000000000000 : ℝ)*(f.sum) + (20985943089289451893/59338495250000000000000000000000 : ℝ)*base63 + (1228408891508761/5061500000000000000000000000 : ℝ)*base65 + (785378956319731/1172350000000000000000000000 : ℝ)*base67 + (619320085953173/5061500000000000000000000000 : ℝ)*base69 + (195425926619743266327/339991078000000000000000000000000 : ℝ)*base71 + (1307825147857793/3358600000000000000000000000 : ℝ)*base72 + (624813344074323/2344700000000000000000000000 : ℝ)*base74 + (2960484758163411/6717200000000000000000000000 : ℝ)*base76 + (31509489280868885999/78749094200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (33617/100000000000000000 : ℝ)*base86 + (33617/100000000000000000 : ℝ)*base88 + (33617/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44327/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44327/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34289830945743369737424304041927/3985885402933000000000000000000000000 : ℝ) := by norm_num
    linear_combination (243580804731/500000000000 : ℝ)*(base39) + (485813/1000000000000 : ℝ)*(base49) + (207324416331/250000000000 : ℝ)*(base59) + (4851364664323/1000000000000 : ℝ)*(major_s2_0) + (4851364664323/1000000000000 : ℝ)*(major_s2_1) + (4851364664323/1000000000000 : ℝ)*(major_s2_2) + (7553871/1000000000000 : ℝ)*(sp_s2_6) + (12171911/500000000000 : ℝ)*(sp_s2_7) + (41764887/1000000000000 : ℝ)*(sp_s2_8) + (2642784961/400000000 : ℝ)*(sp_s2_14) + (3303472490717/500000000000 : ℝ)*(sp_s2_15) + (3303493373161/500000000000 : ℝ)*(sp_s2_16) + (386961870691/125000000000 : ℝ)*(sp_s2_20) + (37195313/1000000000000 : ℝ)*(sp_s2_27) + (386967464339/125000000000 : ℝ)*(f.failure) + (3303493373161/500000000000 : ℝ)*(f.sum) + (20468735892617391621/59338495250000000000000000000000 : ℝ)*base63 + (843155054142433/5061500000000000000000000000 : ℝ)*base64 + (627161336487417/1172350000000000000000000000 : ℝ)*base67 + (2428229879594781/5061500000000000000000000000 : ℝ)*base69 + (52184338345602948531/339991078000000000000000000000000 : ℝ)*base70 + (2924371054116371/3358600000000000000000000000 : ℝ)*base72 + (555807419339/2344700000000000000000000000 : ℝ)*base75 + (309545613981217/6717200000000000000000000000 : ℝ)*base76 + (26108212098464287193/78749094200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (8471/12500000000000000 : ℝ)*base86 + (8471/12500000000000000 : ℝ)*base88 + (8471/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-697/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-697/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3747225987191943247491753594417/996471350733250000000000000000000000 : ℝ) := by norm_num
    linear_combination (3650523/1000000000000 : ℝ)*(base11) + (438967155787/500000000000 : ℝ)*(base39) + (5241431917/62500000000 : ℝ)*(base49) + (134364267619/200000000000 : ℝ)*(base59) + (924942993963/250000000000 : ℝ)*(major_s2_0) + (924942993963/250000000000 : ℝ)*(major_s2_1) + (924942993963/250000000000 : ℝ)*(major_s2_2) + (8053037/1000000000000 : ℝ)*(sp_s2_0) + (4303327/250000000000 : ℝ)*(sp_s2_9) + (1507573/250000000000 : ℝ)*(sp_s2_20) + (5038642495523/1000000000000 : ℝ)*(sp_s2_21) + (5038654199083/1000000000000 : ℝ)*(sp_s2_22) + (201545479431/40000000000 : ℝ)*(sp_s2_23) + (94435298753/40000000000 : ℝ)*(sp_s2_27) + (1180444249559/500000000000 : ℝ)*(f.failure) + (5038654199083/1000000000000 : ℝ)*(f.sum) + (6137066045752423951/14834623812500000000000000000000 : ℝ)*base63 + (200322398629571/2530750000000000000000000000 : ℝ)*base64 + (306466290938833/1172350000000000000000000000 : ℝ)*base67 + (1011719925112597/2530750000000000000000000000 : ℝ)*base69 + (5437834019262926761/84997769500000000000000000000000 : ℝ)*base70 + (132699635641297/419825000000000000000000000 : ℝ)*base73 + (26192386175053/73271875000000000000000000 : ℝ)*base75 + (302842774004633/1679300000000000000000000000 : ℝ)*base77 + (3118171509012945743/4921818387500000000000000000000 : ℝ)*base79 + (40449/50000000000000000 : ℝ)*base87 + (40449/50000000000000000 : ℝ)*base89 + (40449/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((16793/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16793/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70341/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70341/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10123/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10123/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((40827/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40827/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44327/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44327/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-697/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-697/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308052_s2 p hpa hpb X hX hprev1

#print axioms solution
