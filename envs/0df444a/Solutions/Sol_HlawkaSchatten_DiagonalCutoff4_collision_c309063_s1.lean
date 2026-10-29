-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:05:22.261986+00:00
-- url     : https://prove2.me/submissions/0d7fddcf-0e66-4b23-9b84-16f2e073c023

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
theorem collision_support_c309063_s1_s1_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-37725269/1250000000 : ℝ)*x 0 + (2829082497/5000000000 : ℝ)*x 1 + (2980301847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37725269/1250000000 : ℝ)^35 ≤ (1069718951237/100000000000000 : ℝ)^27 := by
    have hnat : (37725269 : ℕ)^35*100000000000000^27 ≤ 1069718951237^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37725269 1250000000 1069718951237 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2829082497/5000000000 : ℝ)^35 ≤ (9559260607889/20000000000000 : ℝ)^27 := by
    have hnat : (2829082497 : ℕ)^35*20000000000000^27 ≤ 9559260607889^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829082497 5000000000 9559260607889 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2980301847/5000000000 : ℝ)^35 ≤ (1022679559953/2000000000000 : ℝ)^27 := by
    have hnat : (2980301847 : ℕ)^35*2000000000000^27 ≤ 1022679559953^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2980301847 5000000000 1022679559953 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-37725269/1250000000 : ℝ), (2829082497/5000000000 : ℝ), (2980301847/5000000000 : ℝ)] ![(1069718951237/100000000000000 : ℝ), (9559260607889/20000000000000 : ℝ), (1022679559953/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-37725269/1250000000 : ℝ)|^35 ≤ (1069718951237/100000000000000 : ℝ)^27
        have hw : |(-37725269/1250000000 : ℝ)|=(37725269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2829082497/5000000000 : ℝ)|^35 ≤ (9559260607889/20000000000000 : ℝ)^27
        have hw : |(2829082497/5000000000 : ℝ)|=(2829082497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2980301847/5000000000 : ℝ)|^35 ≤ (1022679559953/2000000000000 : ℝ)^27
        have hw : |(2980301847/5000000000 : ℝ)|=(2980301847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1141279783/2000000000 : ℝ)*x 0 + (742533169/1250000000 : ℝ)*x 1 + (-116738463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1141279783/2000000000 : ℝ)^35 ≤ (24162570477541/50000000000000 : ℝ)^27 := by
    have hnat : (1141279783 : ℕ)^35*50000000000000^27 ≤ 24162570477541^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141279783 2000000000 24162570477541 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (742533169/1250000000 : ℝ)^35 ≤ (50907920252597/100000000000000 : ℝ)^27 := by
    have hnat : (742533169 : ℕ)^35*100000000000000^27 ≤ 50907920252597^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742533169 1250000000 50907920252597 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116738463/5000000000 : ℝ)^35 ≤ (766938778699/100000000000000 : ℝ)^27 := by
    have hnat : (116738463 : ℕ)^35*100000000000000^27 ≤ 766938778699^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116738463 5000000000 766938778699 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1141279783/2000000000 : ℝ), (742533169/1250000000 : ℝ), (-116738463/5000000000 : ℝ)] ![(24162570477541/50000000000000 : ℝ), (50907920252597/100000000000000 : ℝ), (766938778699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1141279783/2000000000 : ℝ)|^35 ≤ (24162570477541/50000000000000 : ℝ)^27
        have hw : |(1141279783/2000000000 : ℝ)|=(1141279783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(742533169/1250000000 : ℝ)|^35 ≤ (50907920252597/100000000000000 : ℝ)^27
        have hw : |(742533169/1250000000 : ℝ)|=(742533169/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-116738463/5000000000 : ℝ)|^35 ≤ (766938778699/100000000000000 : ℝ)^27
        have hw : |(-116738463/5000000000 : ℝ)|=(116738463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4829276101/10000000000 : ℝ)*x 0 + (1080742337/2500000000 : ℝ)*x 1 + (1839573051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4829276101/10000000000 : ℝ)^35 ≤ (38923999090573/100000000000000 : ℝ)^27 := by
    have hnat : (4829276101 : ℕ)^35*100000000000000^27 ≤ 38923999090573^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829276101 10000000000 38923999090573 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080742337/2500000000 : ℝ)^35 ≤ (8429576701227/25000000000000 : ℝ)^27 := by
    have hnat : (1080742337 : ℕ)^35*25000000000000^27 ≤ 8429576701227^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080742337 2500000000 8429576701227 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1839573051/5000000000 : ℝ)^35 ≤ (13678847044471/50000000000000 : ℝ)^27 := by
    have hnat : (1839573051 : ℕ)^35*50000000000000^27 ≤ 13678847044471^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839573051 5000000000 13678847044471 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4829276101/10000000000 : ℝ), (1080742337/2500000000 : ℝ), (1839573051/5000000000 : ℝ)] ![(38923999090573/100000000000000 : ℝ), (8429576701227/25000000000000 : ℝ), (13678847044471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4829276101/10000000000 : ℝ)|^35 ≤ (38923999090573/100000000000000 : ℝ)^27
        have hw : |(4829276101/10000000000 : ℝ)|=(4829276101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080742337/2500000000 : ℝ)|^35 ≤ (8429576701227/25000000000000 : ℝ)^27
        have hw : |(1080742337/2500000000 : ℝ)|=(1080742337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1839573051/5000000000 : ℝ)|^35 ≤ (13678847044471/50000000000000 : ℝ)^27
        have hw : |(1839573051/5000000000 : ℝ)|=(1839573051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-892444321/10000000000 : ℝ)*x 0 + (1079740351/5000000000 : ℝ)*x 1 + (8574532211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892444321/10000000000 : ℝ)^35 ≤ (4361563562061/100000000000000 : ℝ)^27 := by
    have hnat : (892444321 : ℕ)^35*100000000000000^27 ≤ 4361563562061^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892444321 10000000000 4361563562061 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079740351/5000000000 : ℝ)^35 ≤ (685629511743/5000000000000 : ℝ)^27 := by
    have hnat : (1079740351 : ℕ)^35*5000000000000^27 ≤ 685629511743^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079740351 5000000000 685629511743 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8574532211/10000000000 : ℝ)^35 ≤ (1638516923667/2000000000000 : ℝ)^27 := by
    have hnat : (8574532211 : ℕ)^35*2000000000000^27 ≤ 1638516923667^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8574532211 10000000000 1638516923667 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892444321/10000000000 : ℝ), (1079740351/5000000000 : ℝ), (8574532211/10000000000 : ℝ)] ![(4361563562061/100000000000000 : ℝ), (685629511743/5000000000000 : ℝ), (1638516923667/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892444321/10000000000 : ℝ)|^35 ≤ (4361563562061/100000000000000 : ℝ)^27
        have hw : |(-892444321/10000000000 : ℝ)|=(892444321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1079740351/5000000000 : ℝ)|^35 ≤ (685629511743/5000000000000 : ℝ)^27
        have hw : |(1079740351/5000000000 : ℝ)|=(1079740351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8574532211/10000000000 : ℝ)|^35 ≤ (1638516923667/2000000000000 : ℝ)^27
        have hw : |(8574532211/10000000000 : ℝ)|=(8574532211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (328265877/1250000000 : ℝ)*x 0 + (-264969/25000000 : ℝ)*x 1 + (2146208959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328265877/1250000000 : ℝ)^35 ≤ (4417750013453/25000000000000 : ℝ)^27 := by
    have hnat : (328265877 : ℕ)^35*25000000000000^27 ≤ 4417750013453^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328265877 1250000000 4417750013453 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264969/25000000 : ℝ)^35 ≤ (275515125139/100000000000000 : ℝ)^27 := by
    have hnat : (264969 : ℕ)^35*100000000000000^27 ≤ 275515125139^27*25000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264969 25000000 275515125139 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2146208959/2500000000 : ℝ)^35 ≤ (41026742403087/50000000000000 : ℝ)^27 := by
    have hnat : (2146208959 : ℕ)^35*50000000000000^27 ≤ 41026742403087^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146208959 2500000000 41026742403087 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328265877/1250000000 : ℝ), (-264969/25000000 : ℝ), (2146208959/2500000000 : ℝ)] ![(4417750013453/25000000000000 : ℝ), (275515125139/100000000000000 : ℝ), (41026742403087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328265877/1250000000 : ℝ)|^35 ≤ (4417750013453/25000000000000 : ℝ)^27
        have hw : |(328265877/1250000000 : ℝ)|=(328265877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264969/25000000 : ℝ)|^35 ≤ (275515125139/100000000000000 : ℝ)^27
        have hw : |(-264969/25000000 : ℝ)|=(264969/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2146208959/2500000000 : ℝ)|^35 ≤ (41026742403087/50000000000000 : ℝ)^27
        have hw : |(2146208959/2500000000 : ℝ)|=(2146208959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (538870751/2000000000 : ℝ)*x 0 + (8552608583/10000000000 : ℝ)*x 1 + (-39717049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538870751/2000000000 : ℝ)^35 ≤ (3653679290363/20000000000000 : ℝ)^27 := by
    have hnat : (538870751 : ℕ)^35*20000000000000^27 ≤ 3653679290363^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538870751 2000000000 3653679290363 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8552608583/10000000000 : ℝ)^35 ≤ (81654413232637/100000000000000 : ℝ)^27 := by
    have hnat : (8552608583 : ℕ)^35*100000000000000^27 ≤ 81654413232637^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8552608583 10000000000 81654413232637 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39717049/10000000000 : ℝ)^35 ≤ (7719030241/10000000000000 : ℝ)^27 := by
    have hnat : (39717049 : ℕ)^35*10000000000000^27 ≤ 7719030241^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39717049 10000000000 7719030241 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538870751/2000000000 : ℝ), (8552608583/10000000000 : ℝ), (-39717049/10000000000 : ℝ)] ![(3653679290363/20000000000000 : ℝ), (81654413232637/100000000000000 : ℝ), (7719030241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538870751/2000000000 : ℝ)|^35 ≤ (3653679290363/20000000000000 : ℝ)^27
        have hw : |(538870751/2000000000 : ℝ)|=(538870751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8552608583/10000000000 : ℝ)|^35 ≤ (81654413232637/100000000000000 : ℝ)^27
        have hw : |(8552608583/10000000000 : ℝ)|=(8552608583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39717049/10000000000 : ℝ)|^35 ≤ (7719030241/10000000000000 : ℝ)^27
        have hw : |(-39717049/10000000000 : ℝ)|=(39717049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (94710509/312500000 : ℝ)*x 0 + (932976611/1250000000 : ℝ)*x 1 + (69166623/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (94710509/312500000 : ℝ)^35 ≤ (21278097064391/100000000000000 : ℝ)^27 := by
    have hnat : (94710509 : ℕ)^35*100000000000000^27 ≤ 21278097064391^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94710509 312500000 21278097064391 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932976611/1250000000 : ℝ)^35 ≤ (8555186772093/12500000000000 : ℝ)^27 := by
    have hnat : (932976611 : ℕ)^35*12500000000000^27 ≤ 8555186772093^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932976611 1250000000 8555186772093 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69166623/400000000 : ℝ)^35 ≤ (1285051093609/12500000000000 : ℝ)^27 := by
    have hnat : (69166623 : ℕ)^35*12500000000000^27 ≤ 1285051093609^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69166623 400000000 1285051093609 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(94710509/312500000 : ℝ), (932976611/1250000000 : ℝ), (69166623/400000000 : ℝ)] ![(21278097064391/100000000000000 : ℝ), (8555186772093/12500000000000 : ℝ), (1285051093609/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(94710509/312500000 : ℝ)|^35 ≤ (21278097064391/100000000000000 : ℝ)^27
        have hw : |(94710509/312500000 : ℝ)|=(94710509/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932976611/1250000000 : ℝ)|^35 ≤ (8555186772093/12500000000000 : ℝ)^27
        have hw : |(932976611/1250000000 : ℝ)|=(932976611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(69166623/400000000 : ℝ)|^35 ≤ (1285051093609/12500000000000 : ℝ)^27
        have hw : |(69166623/400000000 : ℝ)|=(69166623/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-79843777/10000000000 : ℝ)*x 0 + (2548435957/10000000000 : ℝ)*x 1 + (2161514759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79843777/10000000000 : ℝ)^35 ≤ (190845916751/100000000000000 : ℝ)^27 := by
    have hnat : (79843777 : ℕ)^35*100000000000000^27 ≤ 190845916751^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79843777 10000000000 190845916751 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548435957/10000000000 : ℝ)^35 ≤ (8498158597451/50000000000000 : ℝ)^27 := by
    have hnat : (2548435957 : ℕ)^35*50000000000000^27 ≤ 8498158597451^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548435957 10000000000 8498158597451 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161514759/2500000000 : ℝ)^35 ≤ (82812836870551/100000000000000 : ℝ)^27 := by
    have hnat : (2161514759 : ℕ)^35*100000000000000^27 ≤ 82812836870551^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161514759 2500000000 82812836870551 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79843777/10000000000 : ℝ), (2548435957/10000000000 : ℝ), (2161514759/2500000000 : ℝ)] ![(190845916751/100000000000000 : ℝ), (8498158597451/50000000000000 : ℝ), (82812836870551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79843777/10000000000 : ℝ)|^35 ≤ (190845916751/100000000000000 : ℝ)^27
        have hw : |(-79843777/10000000000 : ℝ)|=(79843777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548435957/10000000000 : ℝ)|^35 ≤ (8498158597451/50000000000000 : ℝ)^27
        have hw : |(2548435957/10000000000 : ℝ)|=(2548435957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2161514759/2500000000 : ℝ)|^35 ≤ (82812836870551/100000000000000 : ℝ)^27
        have hw : |(2161514759/2500000000 : ℝ)|=(2161514759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2062410671/10000000000 : ℝ)*x 0 + (-857082921/10000000000 : ℝ)*x 1 + (2164118813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062410671/10000000000 : ℝ)^35 ≤ (12918944797481/100000000000000 : ℝ)^27 := by
    have hnat : (2062410671 : ℕ)^35*100000000000000^27 ≤ 12918944797481^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062410671 10000000000 12918944797481 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (857082921/10000000000 : ℝ)^35 ≤ (32334897677/781250000000 : ℝ)^27 := by
    have hnat : (857082921 : ℕ)^35*781250000000^27 ≤ 32334897677^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857082921 10000000000 32334897677 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164118813/2500000000 : ℝ)^35 ≤ (16588437658479/20000000000000 : ℝ)^27 := by
    have hnat : (2164118813 : ℕ)^35*20000000000000^27 ≤ 16588437658479^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164118813 2500000000 16588437658479 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2062410671/10000000000 : ℝ), (-857082921/10000000000 : ℝ), (2164118813/2500000000 : ℝ)] ![(12918944797481/100000000000000 : ℝ), (32334897677/781250000000 : ℝ), (16588437658479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2062410671/10000000000 : ℝ)|^35 ≤ (12918944797481/100000000000000 : ℝ)^27
        have hw : |(2062410671/10000000000 : ℝ)|=(2062410671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-857082921/10000000000 : ℝ)|^35 ≤ (32334897677/781250000000 : ℝ)^27
        have hw : |(-857082921/10000000000 : ℝ)|=(857082921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2164118813/2500000000 : ℝ)|^35 ≤ (16588437658479/20000000000000 : ℝ)^27
        have hw : |(2164118813/2500000000 : ℝ)|=(2164118813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2091687021/2500000000 : ℝ)*x 0 + (73625591/250000000 : ℝ)*x 1 + (-61849639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091687021/2500000000 : ℝ)^35 ≤ (79361620626333/100000000000000 : ℝ)^27 := by
    have hnat : (2091687021 : ℕ)^35*100000000000000^27 ≤ 79361620626333^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091687021 2500000000 79361620626333 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73625591/250000000 : ℝ)^35 ≤ (20501316893393/100000000000000 : ℝ)^27 := by
    have hnat : (73625591 : ℕ)^35*100000000000000^27 ≤ 20501316893393^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73625591 250000000 20501316893393 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61849639/10000000000 : ℝ)^35 ≤ (68531234777/50000000000000 : ℝ)^27 := by
    have hnat : (61849639 : ℕ)^35*50000000000000^27 ≤ 68531234777^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61849639 10000000000 68531234777 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091687021/2500000000 : ℝ), (73625591/250000000 : ℝ), (-61849639/10000000000 : ℝ)] ![(79361620626333/100000000000000 : ℝ), (20501316893393/100000000000000 : ℝ), (68531234777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091687021/2500000000 : ℝ)|^35 ≤ (79361620626333/100000000000000 : ℝ)^27
        have hw : |(2091687021/2500000000 : ℝ)|=(2091687021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73625591/250000000 : ℝ)|^35 ≤ (20501316893393/100000000000000 : ℝ)^27
        have hw : |(73625591/250000000 : ℝ)|=(73625591/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61849639/10000000000 : ℝ)|^35 ≤ (68531234777/50000000000000 : ℝ)^27
        have hw : |(-61849639/10000000000 : ℝ)|=(61849639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (30882337/40000000 : ℝ)*x 0 + (2694804011/10000000000 : ℝ)*x 1 + (53785399/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (30882337/40000000 : ℝ)^35 ≤ (71509102444241/100000000000000 : ℝ)^27 := by
    have hnat : (30882337 : ℕ)^35*100000000000000^27 ≤ 71509102444241^27*40000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30882337 40000000 71509102444241 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694804011/10000000000 : ℝ)^35 ≤ (18272353946611/100000000000000 : ℝ)^27 := by
    have hnat : (2694804011 : ℕ)^35*100000000000000^27 ≤ 18272353946611^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694804011 10000000000 18272353946611 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53785399/312500000 : ℝ)^35 ≤ (10218543595343/100000000000000 : ℝ)^27 := by
    have hnat : (53785399 : ℕ)^35*100000000000000^27 ≤ 10218543595343^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53785399 312500000 10218543595343 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(30882337/40000000 : ℝ), (2694804011/10000000000 : ℝ), (53785399/312500000 : ℝ)] ![(71509102444241/100000000000000 : ℝ), (18272353946611/100000000000000 : ℝ), (10218543595343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(30882337/40000000 : ℝ)|^35 ≤ (71509102444241/100000000000000 : ℝ)^27
        have hw : |(30882337/40000000 : ℝ)|=(30882337/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694804011/10000000000 : ℝ)|^35 ≤ (18272353946611/100000000000000 : ℝ)^27
        have hw : |(2694804011/10000000000 : ℝ)|=(2694804011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53785399/312500000 : ℝ)|^35 ≤ (10218543595343/100000000000000 : ℝ)^27
        have hw : |(53785399/312500000 : ℝ)|=(53785399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-176955973/10000000000 : ℝ)*x 0 + (970328843/1250000000 : ℝ)*x 1 + (73774821/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (176955973/10000000000 : ℝ)^35 ≤ (133861038861/25000000000000 : ℝ)^27 := by
    have hnat : (176955973 : ℕ)^35*25000000000000^27 ≤ 133861038861^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176955973 10000000000 133861038861 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970328843/1250000000 : ℝ)^35 ≤ (72014339317121/100000000000000 : ℝ)^27 := by
    have hnat : (970328843 : ℕ)^35*100000000000000^27 ≤ 72014339317121^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970328843 1250000000 72014339317121 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73774821/200000000 : ℝ)^35 ≤ (3431277064567/12500000000000 : ℝ)^27 := by
    have hnat : (73774821 : ℕ)^35*12500000000000^27 ≤ 3431277064567^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73774821 200000000 3431277064567 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-176955973/10000000000 : ℝ), (970328843/1250000000 : ℝ), (73774821/200000000 : ℝ)] ![(133861038861/25000000000000 : ℝ), (72014339317121/100000000000000 : ℝ), (3431277064567/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-176955973/10000000000 : ℝ)|^35 ≤ (133861038861/25000000000000 : ℝ)^27
        have hw : |(-176955973/10000000000 : ℝ)|=(176955973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(970328843/1250000000 : ℝ)|^35 ≤ (72014339317121/100000000000000 : ℝ)^27
        have hw : |(970328843/1250000000 : ℝ)|=(970328843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73774821/200000000 : ℝ)|^35 ≤ (3431277064567/12500000000000 : ℝ)^27
        have hw : |(73774821/200000000 : ℝ)|=(73774821/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (332133837/400000000 : ℝ)*x 0 + (-8839873/2500000000 : ℝ)*x 1 + (759677387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332133837/400000000 : ℝ)^35 ≤ (125732663583/160000000000 : ℝ)^27 := by
    have hnat : (332133837 : ℕ)^35*160000000000^27 ≤ 125732663583^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332133837 400000000 125732663583 160000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8839873/2500000000 : ℝ)^35 ≤ (518713391/781250000000 : ℝ)^27 := by
    have hnat : (8839873 : ℕ)^35*781250000000^27 ≤ 518713391^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8839873 2500000000 518713391 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (759677387/2500000000 : ℝ)^35 ≤ (2668836241893/12500000000000 : ℝ)^27 := by
    have hnat : (759677387 : ℕ)^35*12500000000000^27 ≤ 2668836241893^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      759677387 2500000000 2668836241893 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332133837/400000000 : ℝ), (-8839873/2500000000 : ℝ), (759677387/2500000000 : ℝ)] ![(125732663583/160000000000 : ℝ), (518713391/781250000000 : ℝ), (2668836241893/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332133837/400000000 : ℝ)|^35 ≤ (125732663583/160000000000 : ℝ)^27
        have hw : |(332133837/400000000 : ℝ)|=(332133837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8839873/2500000000 : ℝ)|^35 ≤ (518713391/781250000000 : ℝ)^27
        have hw : |(-8839873/2500000000 : ℝ)|=(8839873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(759677387/2500000000 : ℝ)|^35 ≤ (2668836241893/12500000000000 : ℝ)^27
        have hw : |(759677387/2500000000 : ℝ)|=(759677387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (371243693/2000000000 : ℝ)*x 0 + (8824654533/10000000000 : ℝ)*x 1 + (-12264373/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371243693/2000000000 : ℝ)^35 ≤ (5635034776411/50000000000000 : ℝ)^27 := by
    have hnat : (371243693 : ℕ)^35*50000000000000^27 ≤ 5635034776411^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371243693 2000000000 5635034776411 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8824654533/10000000000 : ℝ)^35 ≤ (8503704222089/10000000000000 : ℝ)^27 := by
    have hnat : (8824654533 : ℕ)^35*10000000000000^27 ≤ 8503704222089^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8824654533 10000000000 8503704222089 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12264373/156250000 : ℝ)^35 ≤ (1846444105791/50000000000000 : ℝ)^27 := by
    have hnat : (12264373 : ℕ)^35*50000000000000^27 ≤ 1846444105791^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12264373 156250000 1846444105791 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(371243693/2000000000 : ℝ), (8824654533/10000000000 : ℝ), (-12264373/156250000 : ℝ)] ![(5635034776411/50000000000000 : ℝ), (8503704222089/10000000000000 : ℝ), (1846444105791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(371243693/2000000000 : ℝ)|^35 ≤ (5635034776411/50000000000000 : ℝ)^27
        have hw : |(371243693/2000000000 : ℝ)|=(371243693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8824654533/10000000000 : ℝ)|^35 ≤ (8503704222089/10000000000000 : ℝ)^27
        have hw : |(8824654533/10000000000 : ℝ)|=(8824654533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-12264373/156250000 : ℝ)|^35 ≤ (1846444105791/50000000000000 : ℝ)^27
        have hw : |(-12264373/156250000 : ℝ)|=(12264373/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309063_s1_s1_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3922263913/5000000000 : ℝ)*x 0 + (2502839669/10000000000 : ℝ)*x 1 + (1744154991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3922263913/5000000000 : ℝ)^35 ≤ (73000753614779/100000000000000 : ℝ)^27 := by
    have hnat : (3922263913 : ℕ)^35*100000000000000^27 ≤ 73000753614779^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3922263913 5000000000 73000753614779 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2502839669/10000000000 : ℝ)^35 ≤ (8301584040863/50000000000000 : ℝ)^27 := by
    have hnat : (2502839669 : ℕ)^35*50000000000000^27 ≤ 8301584040863^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2502839669 10000000000 8301584040863 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744154991/10000000000 : ℝ)^35 ≤ (5198039149211/50000000000000 : ℝ)^27 := by
    have hnat : (1744154991 : ℕ)^35*50000000000000^27 ≤ 5198039149211^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744154991 10000000000 5198039149211 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3922263913/5000000000 : ℝ), (2502839669/10000000000 : ℝ), (1744154991/10000000000 : ℝ)] ![(73000753614779/100000000000000 : ℝ), (8301584040863/50000000000000 : ℝ), (5198039149211/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3922263913/5000000000 : ℝ)|^35 ≤ (73000753614779/100000000000000 : ℝ)^27
        have hw : |(3922263913/5000000000 : ℝ)|=(3922263913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2502839669/10000000000 : ℝ)|^35 ≤ (8301584040863/50000000000000 : ℝ)^27
        have hw : |(2502839669/10000000000 : ℝ)|=(2502839669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1744154991/10000000000 : ℝ)|^35 ≤ (5198039149211/50000000000000 : ℝ)^27
        have hw : |(1744154991/10000000000 : ℝ)|=(1744154991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309063_s1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4517/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4517/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11221/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11221/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8791/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8791/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((79473/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79473/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19187/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19187/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (4517/5000 : ℝ) ^ (69/16 : ℝ) ≤ (32262860935878301167/50000000000000000000 : ℝ) := by
    have hpowers : (4517/5000 : ℝ)^69 ≤ (32262860935878301167/50000000000000000000 : ℝ)^16 := by
      have hnat : (4517 : ℕ)^69*50000000000000000000^16 ≤ 32262860935878301167^16*5000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4517 5000 32262860935878301167 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4517/5000 : ℝ)) (X := (32262860935878301167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (82262860935878301167/50000000000000000000 : ℝ) ≤ (87686190465173/78125000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (82262860935878301167/50000000000000000000 : ℝ)^16 ≤ (87686190465173/78125000000000 : ℝ)^69 := by
      have hnat : (82262860935878301167 : ℕ)^16*78125000000000^69 ≤ 87686190465173^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        82262860935878301167 50000000000000000000 87686190465173 78125000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (87686190465173/78125000000000 : ℝ)) (X := (82262860935878301167/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (57262860935878301167/25000000000000000000 : ℝ) ≤ (605944344990259/500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (57262860935878301167/25000000000000000000 : ℝ)^16 ≤ (605944344990259/500000000000000 : ℝ)^69 := by
      have hnat : (57262860935878301167 : ℕ)^16*500000000000000^69 ≤ 605944344990259^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57262860935878301167 25000000000000000000 605944344990259 500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (605944344990259/500000000000000 : ℝ)) (X := (57262860935878301167/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(9561190465173/70578125000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(223763630065759/2258500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (4517/5000 : ℝ)) (alpha := (9561190465173/70578125000000 : ℝ)) (beta := (223763630065759/2258500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (4517/5000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(9561190465173/70578125000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(223763630065759/2258500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (11221/12500 : ℝ) ^ (69/16 : ℝ) ≤ (62782221906023456333/100000000000000000000 : ℝ) := by
    have hpowers : (11221/12500 : ℝ)^69 ≤ (62782221906023456333/100000000000000000000 : ℝ)^16 := by
      have hnat : (11221 : ℕ)^69*100000000000000000000^16 ≤ 62782221906023456333^16*12500^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 12500 62782221906023456333 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/12500 : ℝ)) (X := (62782221906023456333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (162782221906023456333/100000000000000000000 : ℝ) ≤ (447845561854079/400000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (162782221906023456333/100000000000000000000 : ℝ)^16 ≤ (447845561854079/400000000000000 : ℝ)^69 := by
      have hnat : (162782221906023456333 : ℕ)^16*400000000000000^69 ≤ 447845561854079^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        162782221906023456333 100000000000000000000 447845561854079 400000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (447845561854079/400000000000000 : ℝ)) (X := (162782221906023456333/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (112782221906023456333/50000000000000000000 : ℝ) ≤ (12075853342821087/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (112782221906023456333/50000000000000000000 : ℝ)^16 ≤ (12075853342821087/10000000000000000 : ℝ)^69 := by
      have hnat : (112782221906023456333 : ℕ)^16*10000000000000000^69 ≤ 12075853342821087^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112782221906023456333 50000000000000000000 12075853342821087 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12075853342821087/10000000000000000 : ℝ)) (X := (112782221906023456333/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(47845561854079/359072000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(109964287058639/1122100000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (11221/12500 : ℝ)) (alpha := (47845561854079/359072000000000 : ℝ)) (beta := (109964287058639/1122100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (11221/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(47845561854079/359072000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(109964287058639/1122100000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (8791/10000 : ℝ) ^ (69/16 : ℝ) ≤ (11473477766581652073/20000000000000000000 : ℝ) := by
    have hpowers : (8791/10000 : ℝ)^69 ≤ (11473477766581652073/20000000000000000000 : ℝ)^16 := by
      have hnat : (8791 : ℕ)^69*20000000000000000000^16 ≤ 11473477766581652073^16*10000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8791 10000 11473477766581652073 20000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8791/10000 : ℝ)) (X := (11473477766581652073/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (31473477766581652073/20000000000000000000 : ℝ) ≤ (5554326343000073/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (31473477766581652073/20000000000000000000 : ℝ)^16 ≤ (5554326343000073/5000000000000000 : ℝ)^69 := by
      have hnat : (31473477766581652073 : ℕ)^16*5000000000000000^69 ≤ 5554326343000073^69*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31473477766581652073 20000000000000000000 5554326343000073 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5554326343000073/5000000000000000 : ℝ)) (X := (31473477766581652073/20000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (21473477766581652073/10000000000000000000 : ℝ) ≤ (5969430176093071/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (21473477766581652073/10000000000000000000 : ℝ)^16 ≤ (5969430176093071/5000000000000000 : ℝ)^69 := by
      have hnat : (21473477766581652073 : ℕ)^16*5000000000000000^69 ≤ 5969430176093071^69*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21473477766581652073 10000000000000000000 5969430176093071 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5969430176093071/5000000000000000 : ℝ)) (X := (21473477766581652073/10000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(554326343000073/4395500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(207551916546499/2197750000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (8791/10000 : ℝ)) (alpha := (554326343000073/4395500000000000 : ℝ)) (beta := (207551916546499/2197750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8791/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(554326343000073/4395500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(207551916546499/2197750000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-37725269/1250000000 : ℝ)*X 0 0+(2829082497/5000000000 : ℝ)*X 0 1+(2980301847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((1141279783/2000000000 : ℝ)*X 2 0+(742533169/1250000000 : ℝ)*X 2 1+(-116738463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4829276101/10000000000 : ℝ)*X 0 0+(1080742337/2500000000 : ℝ)*X 0 1+(1839573051/5000000000 : ℝ)*X 0 2+(4829276101/10000000000 : ℝ)*X 1 0+(1080742337/2500000000 : ℝ)*X 1 1+(1839573051/5000000000 : ℝ)*X 1 2+(4829276101/10000000000 : ℝ)*X 2 0+(1080742337/2500000000 : ℝ)*X 2 1+(1839573051/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-892444321/10000000000 : ℝ)*X 0 0+(1079740351/5000000000 : ℝ)*X 0 1+(8574532211/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((328265877/1250000000 : ℝ)*X 1 0+(-264969/25000000 : ℝ)*X 1 1+(2146208959/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((538870751/2000000000 : ℝ)*X 2 0+(8552608583/10000000000 : ℝ)*X 2 1+(-39717049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((94710509/312500000 : ℝ)*X 0 0+(932976611/1250000000 : ℝ)*X 0 1+(69166623/400000000 : ℝ)*X 0 2+(94710509/312500000 : ℝ)*X 1 0+(932976611/1250000000 : ℝ)*X 1 1+(69166623/400000000 : ℝ)*X 1 2+(94710509/312500000 : ℝ)*X 2 0+(932976611/1250000000 : ℝ)*X 2 1+(69166623/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-79843777/10000000000 : ℝ)*X 0 0+(2548435957/10000000000 : ℝ)*X 0 1+(2161514759/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2062410671/10000000000 : ℝ)*X 1 0+(-857082921/10000000000 : ℝ)*X 1 1+(2164118813/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2091687021/2500000000 : ℝ)*X 2 0+(73625591/250000000 : ℝ)*X 2 1+(-61849639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((30882337/40000000 : ℝ)*X 0 0+(2694804011/10000000000 : ℝ)*X 0 1+(53785399/312500000 : ℝ)*X 0 2+(30882337/40000000 : ℝ)*X 1 0+(2694804011/10000000000 : ℝ)*X 1 1+(53785399/312500000 : ℝ)*X 1 2+(30882337/40000000 : ℝ)*X 2 0+(2694804011/10000000000 : ℝ)*X 2 1+(53785399/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-176955973/10000000000 : ℝ)*X 0 0+(970328843/1250000000 : ℝ)*X 0 1+(73774821/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((332133837/400000000 : ℝ)*X 1 0+(-8839873/2500000000 : ℝ)*X 1 1+(759677387/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((371243693/2000000000 : ℝ)*X 2 0+(8824654533/10000000000 : ℝ)*X 2 1+(-12264373/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3922263913/5000000000 : ℝ)*X 0 0+(2502839669/10000000000 : ℝ)*X 0 1+(1744154991/10000000000 : ℝ)*X 0 2+(3922263913/5000000000 : ℝ)*X 1 0+(2502839669/10000000000 : ℝ)*X 1 1+(1744154991/10000000000 : ℝ)*X 1 2+(3922263913/5000000000 : ℝ)*X 2 0+(2502839669/10000000000 : ℝ)*X 2 1+(1744154991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((79473/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79473/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14907657016854907489474114556247/891148188574000000000000000000000000 : ℝ) := by norm_num
    linear_combination (208420747/244140625 : ℝ)*(base7) + (2415223/1000000000000 : ℝ)*(base50) + (63427/50000000000 : ℝ)*(base53) + (1168281/500000000000 : ℝ)*(base60) + (1593395504077/1000000000000 : ℝ)*(major_s1_0) + (1593395504077/1000000000000 : ℝ)*(major_s1_1) + (1593394235537/1000000000000 : ℝ)*(major_s1_2) + (11671127/1000000000000 : ℝ)*(sp_s1_0) + (64397/250000000000 : ℝ)*(sp_s1_6) + (52073371143/31250000000 : ℝ)*(sp_s1_7) + (1666458602413/1000000000000 : ℝ)*(sp_s1_8) + (1666459870953/1000000000000 : ℝ)*(sp_s1_9) + (115892018583/62500000000 : ℝ)*(sp_s1_13) + (9905471/100000000000 : ℝ)*(sp_s1_14) + (250145293801/250000000000 : ℝ)*(f.failure) + (1666459870953/1000000000000 : ℝ)*(f.sum) + (196798151627845018807/394575244000000000000000000000000 : ℝ)*base62 + (434700888463263/2197750000000000000000000000 : ℝ)*base65 + (101084990311103/1122100000000000000000000000 : ℝ)*base67 + (2047109067598799/4395500000000000000000000000 : ℝ)*base68 + (3414591749154380047/9927236750000000000000000000000 : ℝ)*base71 + (238530728467957/2258500000000000000000000000 : ℝ)*base72 + (806431207045297/1795360000000000000000000000 : ℝ)*base74 + (8431790545661/1129250000000000000000000000 : ℝ)*base77 + (1123284475953743627/6335657125000000000000000000000 : ℝ)*base79 + (2847/25000000000000000 : ℝ)*base87 + (2847/25000000000000000 : ℝ)*base89 + (2847/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79397/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3461074792457376343642725514149/222787047143500000000000000000000000 : ℝ) := by norm_num
    linear_combination (171830318963/200000000000 : ℝ)*(base7) + (54711/250000000000 : ℝ)*(base40) + (483277/40000000000 : ℝ)*(base53) + (1907883/1000000000000 : ℝ)*(base60) + (387529174791/250000000000 : ℝ)*(major_s1_0) + (387529174791/250000000000 : ℝ)*(major_s1_1) + (1550104617239/1000000000000 : ℝ)*(major_s1_2) + (5460861/500000000000 : ℝ)*(sp_s1_7) + (1236551/20000000000 : ℝ)*(sp_s1_8) + (400933130657/250000000000 : ℝ)*(sp_s1_14) + (2004602021/1250000000 : ℝ)*(sp_s1_15) + (64150221051/40000000000 : ℝ)*(sp_s1_16) + (1832190633333/1000000000000 : ℝ)*(sp_s1_20) + (182490563/500000000000 : ℝ)*(sp_s1_27) + (194680803929/200000000000 : ℝ)*(f.failure) + (64150221051/40000000000 : ℝ)*(f.sum) + (32610110715797058649/98643811000000000000000000000000 : ℝ)*base63 + (92715249680293/1098875000000000000000000000 : ℝ)*base65 + (50469284362451/280525000000000000000000000 : ℝ)*base66 + (852977918035147/4395500000000000000000000000 : ℝ)*base69 + (142590195993208503/4963618375000000000000000000000 : ℝ)*base70 + (10627448607311/141156250000000000000000000 : ℝ)*base73 + (47929782275861/448840000000000000000000000 : ℝ)*base75 + (296193588173273/1129250000000000000000000000 : ℝ)*base76 + (4273494502258533303/12671314250000000000000000000000 : ℝ)*base79 + (1463/20000000000000000 : ℝ)*base87 + (1463/20000000000000000 : ℝ)*base89 + (1463/20000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19187/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19187/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2646415309436785460511121237533/178229637714800000000000000000000000 : ℝ) := by norm_num
    linear_combination (276158491/320000000 : ℝ)*(base7) + (11549/2000000000 : ℝ)*(base27) + (25339716873/250000000000 : ℝ)*(base40) + (11892371/1000000000000 : ℝ)*(base43) + (1319733/1000000000000 : ℝ)*(base49) + (187665862893/125000000000 : ℝ)*(major_s1_0) + (1501315010773/1000000000000 : ℝ)*(major_s1_1) + (187665862893/125000000000 : ℝ)*(major_s1_2) + (3935041/1000000000000 : ℝ)*(sp_s1_2) + (40609311/500000000000 : ℝ)*(sp_s1_9) + (613784787/400000000 : ℝ)*(sp_s1_21) + (1534473859871/1000000000000 : ℝ)*(sp_s1_22) + (383594203459/250000000000 : ℝ)*(sp_s1_23) + (902877858903/500000000000 : ℝ)*(sp_s1_27) + (942766207931/1000000000000 : ℝ)*(f.failure) + (1534473859871/1000000000000 : ℝ)*(f.sum) + (41695485254635886441/394575244000000000000000000000000 : ℝ)*base63 + (193517993444497/1098875000000000000000000000 : ℝ)*base64 + (928938896230713/1122100000000000000000000000 : ℝ)*base66 + (94941969133269/2197750000000000000000000000 : ℝ)*base68 + (1592983122942384763/4963618375000000000000000000000 : ℝ)*base70 + (111675775912401/564625000000000000000000000 : ℝ)*base72 + (227490721121479/1795360000000000000000000000 : ℝ)*base75 + (121297679711773/282312500000000000000000000 : ℝ)*base77 + (8893634654501863089/25342628500000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (12043/100000000000000000 : ℝ)*base86 + (12043/100000000000000000 : ℝ)*base88 + (12043/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((4517/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4517/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11221/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11221/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8791/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8791/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((79473/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79473/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79397/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(79397/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19187/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19187/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309063_s1 p hpa hpb X hX hprev0

#print axioms solution
