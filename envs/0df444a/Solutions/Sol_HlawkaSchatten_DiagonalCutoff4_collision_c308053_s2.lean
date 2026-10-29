-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:36:18.328137+00:00
-- url     : https://prove2.me/submissions/933694cb-8429-4dd9-b3c2-c610c082076e

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
theorem collision_support_c308053_s2_s2_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-889757687/5000000000 : ℝ)*x 0 + (5309165477/10000000000 : ℝ)*x 1 + (1367170421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (889757687/5000000000 : ℝ)^69 ≤ (26419083737/250000000000 : ℝ)^53 := by
    have hnat : (889757687 : ℕ)^69*250000000000^53 ≤ 26419083737^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      889757687 5000000000 26419083737 250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5309165477/10000000000 : ℝ)^69 ≤ (43854616936123/100000000000000 : ℝ)^53 := by
    have hnat : (5309165477 : ℕ)^69*100000000000000^53 ≤ 43854616936123^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309165477 10000000000 43854616936123 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367170421/2500000000 : ℝ)^69 ≤ (45577749545533/100000000000000 : ℝ)^53 := by
    have hnat : (1367170421 : ℕ)^69*100000000000000^53 ≤ 45577749545533^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367170421 2500000000 45577749545533 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-889757687/5000000000 : ℝ), (5309165477/10000000000 : ℝ), (1367170421/2500000000 : ℝ)] ![(26419083737/250000000000 : ℝ), (43854616936123/100000000000000 : ℝ), (45577749545533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-889757687/5000000000 : ℝ)|^69 ≤ (26419083737/250000000000 : ℝ)^53
        have hw : |(-889757687/5000000000 : ℝ)|=(889757687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5309165477/10000000000 : ℝ)|^69 ≤ (43854616936123/100000000000000 : ℝ)^53
        have hw : |(5309165477/10000000000 : ℝ)|=(5309165477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367170421/2500000000 : ℝ)|^69 ≤ (45577749545533/100000000000000 : ℝ)^53
        have hw : |(1367170421/2500000000 : ℝ)|=(1367170421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4497636961/10000000000 : ℝ)*x 0 + (-521984519/5000000000 : ℝ)*x 1 + (6701337751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4497636961/10000000000 : ℝ)^69 ≤ (55213464143/156250000000 : ℝ)^53 := by
    have hnat : (4497636961 : ℕ)^69*156250000000^53 ≤ 55213464143^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497636961 10000000000 55213464143 156250000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521984519/5000000000 : ℝ)^69 ≤ (2638835850633/50000000000000 : ℝ)^53 := by
    have hnat : (521984519 : ℕ)^69*50000000000000^53 ≤ 2638835850633^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521984519 5000000000 2638835850633 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6701337751/10000000000 : ℝ)^69 ≤ (59385711231117/100000000000000 : ℝ)^53 := by
    have hnat : (6701337751 : ℕ)^69*100000000000000^53 ≤ 59385711231117^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6701337751 10000000000 59385711231117 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4497636961/10000000000 : ℝ), (-521984519/5000000000 : ℝ), (6701337751/10000000000 : ℝ)] ![(55213464143/156250000000 : ℝ), (2638835850633/50000000000000 : ℝ), (59385711231117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4497636961/10000000000 : ℝ)|^69 ≤ (55213464143/156250000000 : ℝ)^53
        have hw : |(4497636961/10000000000 : ℝ)|=(4497636961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521984519/5000000000 : ℝ)|^69 ≤ (2638835850633/50000000000000 : ℝ)^53
        have hw : |(-521984519/5000000000 : ℝ)|=(521984519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6701337751/10000000000 : ℝ)|^69 ≤ (59385711231117/100000000000000 : ℝ)^53
        have hw : |(6701337751/10000000000 : ℝ)|=(6701337751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1797726909/10000000000 : ℝ)*x 0 + (1881210057/5000000000 : ℝ)*x 1 + (6865083691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1797726909/10000000000 : ℝ)^69 ≤ (669290515341/6250000000000 : ℝ)^53 := by
    have hnat : (1797726909 : ℕ)^69*6250000000000^53 ≤ 669290515341^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797726909 10000000000 669290515341 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1881210057/5000000000 : ℝ)^69 ≤ (14004785870467/50000000000000 : ℝ)^53 := by
    have hnat : (1881210057 : ℕ)^69*50000000000000^53 ≤ 14004785870467^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1881210057 5000000000 14004785870467 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6865083691/10000000000 : ℝ)^69 ≤ (30640890001301/50000000000000 : ℝ)^53 := by
    have hnat : (6865083691 : ℕ)^69*50000000000000^53 ≤ 30640890001301^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6865083691 10000000000 30640890001301 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1797726909/10000000000 : ℝ), (1881210057/5000000000 : ℝ), (6865083691/10000000000 : ℝ)] ![(669290515341/6250000000000 : ℝ), (14004785870467/50000000000000 : ℝ), (30640890001301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1797726909/10000000000 : ℝ)|^69 ≤ (669290515341/6250000000000 : ℝ)^53
        have hw : |(-1797726909/10000000000 : ℝ)|=(1797726909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1881210057/5000000000 : ℝ)|^69 ≤ (14004785870467/50000000000000 : ℝ)^53
        have hw : |(1881210057/5000000000 : ℝ)|=(1881210057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6865083691/10000000000 : ℝ)|^69 ≤ (30640890001301/50000000000000 : ℝ)^53
        have hw : |(6865083691/10000000000 : ℝ)|=(6865083691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1542237381/5000000000 : ℝ)*x 0 + (-34498373/1250000000 : ℝ)*x 1 + (2054256659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1542237381/5000000000 : ℝ)^69 ≤ (21625779890837/100000000000000 : ℝ)^53 := by
    have hnat : (1542237381 : ℕ)^69*100000000000000^53 ≤ 21625779890837^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542237381 5000000000 21625779890837 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34498373/1250000000 : ℝ)^69 ≤ (933713119421/100000000000000 : ℝ)^53 := by
    have hnat : (34498373 : ℕ)^69*100000000000000^53 ≤ 933713119421^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34498373 1250000000 933713119421 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2054256659/2500000000 : ℝ)^69 ≤ (77440506983913/100000000000000 : ℝ)^53 := by
    have hnat : (2054256659 : ℕ)^69*100000000000000^53 ≤ 77440506983913^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054256659 2500000000 77440506983913 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1542237381/5000000000 : ℝ), (-34498373/1250000000 : ℝ), (2054256659/2500000000 : ℝ)] ![(21625779890837/100000000000000 : ℝ), (933713119421/100000000000000 : ℝ), (77440506983913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1542237381/5000000000 : ℝ)|^69 ≤ (21625779890837/100000000000000 : ℝ)^53
        have hw : |(1542237381/5000000000 : ℝ)|=(1542237381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34498373/1250000000 : ℝ)|^69 ≤ (933713119421/100000000000000 : ℝ)^53
        have hw : |(-34498373/1250000000 : ℝ)|=(34498373/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2054256659/2500000000 : ℝ)|^69 ≤ (77440506983913/100000000000000 : ℝ)^53
        have hw : |(2054256659/2500000000 : ℝ)|=(2054256659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (155495183/500000000 : ℝ)*x 0 + (8199362629/10000000000 : ℝ)*x 1 + (-272406609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155495183/500000000 : ℝ)^69 ≤ (21858176820977/100000000000000 : ℝ)^53 := by
    have hnat : (155495183 : ℕ)^69*100000000000000^53 ≤ 21858176820977^53*500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155495183 500000000 21858176820977 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8199362629/10000000000 : ℝ)^69 ≤ (77223848884787/100000000000000 : ℝ)^53 := by
    have hnat : (8199362629 : ℕ)^69*100000000000000^53 ≤ 77223848884787^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8199362629 10000000000 77223848884787 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272406609/10000000000 : ℝ)^69 ≤ (91797427843/10000000000000 : ℝ)^53 := by
    have hnat : (272406609 : ℕ)^69*10000000000000^53 ≤ 91797427843^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272406609 10000000000 91797427843 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(155495183/500000000 : ℝ), (8199362629/10000000000 : ℝ), (-272406609/10000000000 : ℝ)] ![(21858176820977/100000000000000 : ℝ), (77223848884787/100000000000000 : ℝ), (91797427843/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(155495183/500000000 : ℝ)|^69 ≤ (21858176820977/100000000000000 : ℝ)^53
        have hw : |(155495183/500000000 : ℝ)|=(155495183/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8199362629/10000000000 : ℝ)|^69 ≤ (77223848884787/100000000000000 : ℝ)^53
        have hw : |(8199362629/10000000000 : ℝ)|=(8199362629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272406609/10000000000 : ℝ)|^69 ≤ (91797427843/10000000000000 : ℝ)^53
        have hw : |(-272406609/10000000000 : ℝ)|=(272406609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (600929087/1000000000 : ℝ)*x 0 + (5605318459/10000000000 : ℝ)*x 1 + (377746129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600929087/1000000000 : ℝ)^69 ≤ (12882284543253/25000000000000 : ℝ)^53 := by
    have hnat : (600929087 : ℕ)^69*25000000000000^53 ≤ 12882284543253^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600929087 1000000000 12882284543253 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5605318459/10000000000 : ℝ)^69 ≤ (23532932235659/50000000000000 : ℝ)^53 := by
    have hnat : (5605318459 : ℕ)^69*50000000000000^53 ≤ 23532932235659^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5605318459 10000000000 23532932235659 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377746129/10000000000 : ℝ)^69 ≤ (17562466711/1250000000000 : ℝ)^53 := by
    have hnat : (377746129 : ℕ)^69*1250000000000^53 ≤ 17562466711^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377746129 10000000000 17562466711 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(600929087/1000000000 : ℝ), (5605318459/10000000000 : ℝ), (377746129/10000000000 : ℝ)] ![(12882284543253/25000000000000 : ℝ), (23532932235659/50000000000000 : ℝ), (17562466711/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(600929087/1000000000 : ℝ)|^69 ≤ (12882284543253/25000000000000 : ℝ)^53
        have hw : |(600929087/1000000000 : ℝ)|=(600929087/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5605318459/10000000000 : ℝ)|^69 ≤ (23532932235659/50000000000000 : ℝ)^53
        have hw : |(5605318459/10000000000 : ℝ)|=(5605318459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377746129/10000000000 : ℝ)|^69 ≤ (17562466711/1250000000000 : ℝ)^53
        have hw : |(377746129/10000000000 : ℝ)|=(377746129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1362606597/10000000000 : ℝ)*x 0 + (3686139183/10000000000 : ℝ)*x 1 + (7205073977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1362606597/10000000000 : ℝ)^69 ≤ (1493063799653/20000000000000 : ℝ)^53 := by
    have hnat : (1362606597 : ℕ)^69*20000000000000^53 ≤ 1493063799653^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362606597 10000000000 1493063799653 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3686139183/10000000000 : ℝ)^69 ≤ (13636265973199/50000000000000 : ℝ)^53 := by
    have hnat : (3686139183 : ℕ)^69*50000000000000^53 ≤ 13636265973199^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3686139183 10000000000 13636265973199 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7205073977/10000000000 : ℝ)^69 ≤ (16315537262353/25000000000000 : ℝ)^53 := by
    have hnat : (7205073977 : ℕ)^69*25000000000000^53 ≤ 16315537262353^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7205073977 10000000000 16315537262353 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1362606597/10000000000 : ℝ), (3686139183/10000000000 : ℝ), (7205073977/10000000000 : ℝ)] ![(1493063799653/20000000000000 : ℝ), (13636265973199/50000000000000 : ℝ), (16315537262353/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1362606597/10000000000 : ℝ)|^69 ≤ (1493063799653/20000000000000 : ℝ)^53
        have hw : |(-1362606597/10000000000 : ℝ)|=(1362606597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3686139183/10000000000 : ℝ)|^69 ≤ (13636265973199/50000000000000 : ℝ)^53
        have hw : |(3686139183/10000000000 : ℝ)|=(3686139183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7205073977/10000000000 : ℝ)|^69 ≤ (16315537262353/25000000000000 : ℝ)^53
        have hw : |(7205073977/10000000000 : ℝ)|=(7205073977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (233275399/1250000000 : ℝ)*x 0 + (-215440617/2500000000 : ℝ)*x 1 + (8798177349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233275399/1250000000 : ℝ)^69 ≤ (2248542252151/20000000000000 : ℝ)^53 := by
    have hnat : (233275399 : ℕ)^69*20000000000000^53 ≤ 2248542252151^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233275399 1250000000 2248542252151 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215440617/2500000000 : ℝ)^69 ≤ (4111451253147/100000000000000 : ℝ)^53 := by
    have hnat : (215440617 : ℕ)^69*100000000000000^53 ≤ 4111451253147^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215440617 2500000000 4111451253147 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8798177349/10000000000 : ℝ)^69 ≤ (42322918737263/50000000000000 : ℝ)^53 := by
    have hnat : (8798177349 : ℕ)^69*50000000000000^53 ≤ 42322918737263^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8798177349 10000000000 42322918737263 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(233275399/1250000000 : ℝ), (-215440617/2500000000 : ℝ), (8798177349/10000000000 : ℝ)] ![(2248542252151/20000000000000 : ℝ), (4111451253147/100000000000000 : ℝ), (42322918737263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(233275399/1250000000 : ℝ)|^69 ≤ (2248542252151/20000000000000 : ℝ)^53
        have hw : |(233275399/1250000000 : ℝ)|=(233275399/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215440617/2500000000 : ℝ)|^69 ≤ (4111451253147/100000000000000 : ℝ)^53
        have hw : |(-215440617/2500000000 : ℝ)|=(215440617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8798177349/10000000000 : ℝ)|^69 ≤ (42322918737263/50000000000000 : ℝ)^53
        have hw : |(8798177349/10000000000 : ℝ)|=(8798177349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3220097637/5000000000 : ℝ)*x 0 + (1016195467/2000000000 : ℝ)*x 1 + (-531660553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3220097637/5000000000 : ℝ)^69 ≤ (56390789991237/100000000000000 : ℝ)^53 := by
    have hnat : (3220097637 : ℕ)^69*100000000000000^53 ≤ 56390789991237^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220097637 5000000000 56390789991237 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1016195467/2000000000 : ℝ)^69 ≤ (10354201850409/25000000000000 : ℝ)^53 := by
    have hnat : (1016195467 : ℕ)^69*25000000000000^53 ≤ 10354201850409^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016195467 2000000000 10354201850409 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531660553/10000000000 : ℝ)^69 ≤ (438480518493/20000000000000 : ℝ)^53 := by
    have hnat : (531660553 : ℕ)^69*20000000000000^53 ≤ 438480518493^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531660553 10000000000 438480518493 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3220097637/5000000000 : ℝ), (1016195467/2000000000 : ℝ), (-531660553/10000000000 : ℝ)] ![(56390789991237/100000000000000 : ℝ), (10354201850409/25000000000000 : ℝ), (438480518493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3220097637/5000000000 : ℝ)|^69 ≤ (56390789991237/100000000000000 : ℝ)^53
        have hw : |(3220097637/5000000000 : ℝ)|=(3220097637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1016195467/2000000000 : ℝ)|^69 ≤ (10354201850409/25000000000000 : ℝ)^53
        have hw : |(1016195467/2000000000 : ℝ)|=(1016195467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531660553/10000000000 : ℝ)|^69 ≤ (438480518493/20000000000000 : ℝ)^53
        have hw : |(-531660553/10000000000 : ℝ)|=(531660553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4656723229/5000000000 : ℝ)*x 0 + (303461091/2500000000 : ℝ)*x 1 + (286946197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4656723229/5000000000 : ℝ)^69 ≤ (284862504529/312500000000 : ℝ)^53 := by
    have hnat : (4656723229 : ℕ)^69*312500000000^53 ≤ 284862504529^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4656723229 5000000000 284862504529 312500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (303461091/2500000000 : ℝ)^69 ≤ (642220129373/10000000000000 : ℝ)^53 := by
    have hnat : (303461091 : ℕ)^69*10000000000000^53 ≤ 642220129373^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303461091 2500000000 642220129373 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (286946197/5000000000 : ℝ)^69 ≤ (2421797242143/100000000000000 : ℝ)^53 := by
    have hnat : (286946197 : ℕ)^69*100000000000000^53 ≤ 2421797242143^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286946197 5000000000 2421797242143 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4656723229/5000000000 : ℝ), (303461091/2500000000 : ℝ), (286946197/5000000000 : ℝ)] ![(284862504529/312500000000 : ℝ), (642220129373/10000000000000 : ℝ), (2421797242143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4656723229/5000000000 : ℝ)|^69 ≤ (284862504529/312500000000 : ℝ)^53
        have hw : |(4656723229/5000000000 : ℝ)|=(4656723229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(303461091/2500000000 : ℝ)|^69 ≤ (642220129373/10000000000000 : ℝ)^53
        have hw : |(303461091/2500000000 : ℝ)|=(303461091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(286946197/5000000000 : ℝ)|^69 ≤ (2421797242143/100000000000000 : ℝ)^53
        have hw : |(286946197/5000000000 : ℝ)|=(286946197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-173549523/1250000000 : ℝ)*x 0 + (3317220463/5000000000 : ℝ)*x 1 + (4340227431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173549523/1250000000 : ℝ)^69 ≤ (7649790393569/100000000000000 : ℝ)^53 := by
    have hnat : (173549523 : ℕ)^69*100000000000000^53 ≤ 7649790393569^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173549523 1250000000 7649790393569 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3317220463/5000000000 : ℝ)^69 ≤ (58615086821719/100000000000000 : ℝ)^53 := by
    have hnat : (3317220463 : ℕ)^69*100000000000000^53 ≤ 58615086821719^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3317220463 5000000000 58615086821719 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4340227431/10000000000 : ℝ)^69 ≤ (33735122768931/100000000000000 : ℝ)^53 := by
    have hnat : (4340227431 : ℕ)^69*100000000000000^53 ≤ 33735122768931^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340227431 10000000000 33735122768931 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173549523/1250000000 : ℝ), (3317220463/5000000000 : ℝ), (4340227431/10000000000 : ℝ)] ![(7649790393569/100000000000000 : ℝ), (58615086821719/100000000000000 : ℝ), (33735122768931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173549523/1250000000 : ℝ)|^69 ≤ (7649790393569/100000000000000 : ℝ)^53
        have hw : |(-173549523/1250000000 : ℝ)|=(173549523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3317220463/5000000000 : ℝ)|^69 ≤ (58615086821719/100000000000000 : ℝ)^53
        have hw : |(3317220463/5000000000 : ℝ)|=(3317220463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4340227431/10000000000 : ℝ)|^69 ≤ (33735122768931/100000000000000 : ℝ)^53
        have hw : |(4340227431/10000000000 : ℝ)|=(4340227431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1637611449/2500000000 : ℝ)*x 0 + (-467917509/10000000000 : ℝ)*x 1 + (4993661719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1637611449/2500000000 : ℝ)^69 ≤ (7206351949081/12500000000000 : ℝ)^53 := by
    have hnat : (1637611449 : ℕ)^69*12500000000000^53 ≤ 7206351949081^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637611449 2500000000 7206351949081 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (467917509/10000000000 : ℝ)^69 ≤ (232071058829/12500000000000 : ℝ)^53 := by
    have hnat : (467917509 : ℕ)^69*12500000000000^53 ≤ 232071058829^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467917509 10000000000 232071058829 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4993661719/10000000000 : ℝ)^69 ≤ (20246307961631/50000000000000 : ℝ)^53 := by
    have hnat : (4993661719 : ℕ)^69*50000000000000^53 ≤ 20246307961631^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993661719 10000000000 20246307961631 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1637611449/2500000000 : ℝ), (-467917509/10000000000 : ℝ), (4993661719/10000000000 : ℝ)] ![(7206351949081/12500000000000 : ℝ), (232071058829/12500000000000 : ℝ), (20246307961631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1637611449/2500000000 : ℝ)|^69 ≤ (7206351949081/12500000000000 : ℝ)^53
        have hw : |(1637611449/2500000000 : ℝ)|=(1637611449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-467917509/10000000000 : ℝ)|^69 ≤ (232071058829/12500000000000 : ℝ)^53
        have hw : |(-467917509/10000000000 : ℝ)|=(467917509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4993661719/10000000000 : ℝ)|^69 ≤ (20246307961631/50000000000000 : ℝ)^53
        have hw : |(4993661719/10000000000 : ℝ)|=(4993661719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1955222729/10000000000 : ℝ)*x 0 + (873145337/1000000000 : ℝ)*x 1 + (-220718751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1955222729/10000000000 : ℝ)^69 ≤ (2986467214343/25000000000000 : ℝ)^53 := by
    have hnat : (1955222729 : ℕ)^69*25000000000000^53 ≤ 2986467214343^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955222729 10000000000 2986467214343 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (873145337/1000000000 : ℝ)^69 ≤ (83811061894321/100000000000000 : ℝ)^53 := by
    have hnat : (873145337 : ℕ)^69*100000000000000^53 ≤ 83811061894321^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873145337 1000000000 83811061894321 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220718751/2500000000 : ℝ)^69 ≤ (2121534617049/50000000000000 : ℝ)^53 := by
    have hnat : (220718751 : ℕ)^69*50000000000000^53 ≤ 2121534617049^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220718751 2500000000 2121534617049 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1955222729/10000000000 : ℝ), (873145337/1000000000 : ℝ), (-220718751/2500000000 : ℝ)] ![(2986467214343/25000000000000 : ℝ), (83811061894321/100000000000000 : ℝ), (2121534617049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1955222729/10000000000 : ℝ)|^69 ≤ (2986467214343/25000000000000 : ℝ)^53
        have hw : |(1955222729/10000000000 : ℝ)|=(1955222729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(873145337/1000000000 : ℝ)|^69 ≤ (83811061894321/100000000000000 : ℝ)^53
        have hw : |(873145337/1000000000 : ℝ)|=(873145337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220718751/2500000000 : ℝ)|^69 ≤ (2121534617049/50000000000000 : ℝ)^53
        have hw : |(-220718751/2500000000 : ℝ)|=(220718751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308053_s2_s2_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2337195617/2500000000 : ℝ)*x 0 + (936870597/10000000000 : ℝ)*x 1 + (406360461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2337195617/2500000000 : ℝ)^69 ≤ (45803260686261/50000000000000 : ℝ)^53 := by
    have hnat : (2337195617 : ℕ)^69*50000000000000^53 ≤ 45803260686261^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337195617 2500000000 45803260686261 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936870597/10000000000 : ℝ)^69 ≤ (4583985811723/100000000000000 : ℝ)^53 := by
    have hnat : (936870597 : ℕ)^69*100000000000000^53 ≤ 4583985811723^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936870597 10000000000 4583985811723 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (406360461/5000000000 : ℝ)^69 ≤ (3809492805771/100000000000000 : ℝ)^53 := by
    have hnat : (406360461 : ℕ)^69*100000000000000^53 ≤ 3809492805771^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406360461 5000000000 3809492805771 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2337195617/2500000000 : ℝ), (936870597/10000000000 : ℝ), (406360461/5000000000 : ℝ)] ![(45803260686261/50000000000000 : ℝ), (4583985811723/100000000000000 : ℝ), (3809492805771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2337195617/2500000000 : ℝ)|^69 ≤ (45803260686261/50000000000000 : ℝ)^53
        have hw : |(2337195617/2500000000 : ℝ)|=(2337195617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936870597/10000000000 : ℝ)|^69 ≤ (4583985811723/100000000000000 : ℝ)^53
        have hw : |(936870597/10000000000 : ℝ)|=(936870597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(406360461/5000000000 : ℝ)|^69 ≤ (3809492805771/100000000000000 : ℝ)^53
        have hw : |(406360461/5000000000 : ℝ)|=(406360461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308053_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((16309/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16309/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8451/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8451/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83617/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83617/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68353/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68353/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37501/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37501/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74083/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74083/100000 : ℝ)*X 1 2) := by
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
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s2_pow0 : (16309/20000 : ℝ) ^ (17/4 : ℝ) ≤ (21009159917965538373/50000000000000000000 : ℝ) := by
    have hpowers : (16309/20000 : ℝ)^17 ≤ (21009159917965538373/50000000000000000000 : ℝ)^4 := by
      have hnat : (16309 : ℕ)^17*50000000000000000000^4 ≤ 21009159917965538373^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16309 20000 21009159917965538373 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16309/20000 : ℝ)) (X := (21009159917965538373/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (71009159917965538373/50000000000000000000 : ℝ) ≤ (10860397827729679/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (71009159917965538373/50000000000000000000 : ℝ)^4 ≤ (10860397827729679/10000000000000000 : ℝ)^17 := by
      have hnat : (71009159917965538373 : ℕ)^4*10000000000000000^17 ≤ 10860397827729679^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71009159917965538373 50000000000000000000 10860397827729679 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10860397827729679/10000000000000000 : ℝ)) (X := (71009159917965538373/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (46009159917965538373/25000000000000000000 : ℝ) ≤ (11543311684177171/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (46009159917965538373/25000000000000000000 : ℝ)^4 ≤ (11543311684177171/10000000000000000 : ℝ)^17 := by
      have hnat : (46009159917965538373 : ℕ)^4*10000000000000000^17 ≤ 11543311684177171^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46009159917965538373 25000000000000000000 11543311684177171 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11543311684177171/10000000000000000 : ℝ)) (X := (46009159917965538373/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(860397827729679/8154500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(170728464111873/2038625000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (16309/20000 : ℝ)) (alpha := (860397827729679/8154500000000000 : ℝ)) (beta := (170728464111873/2038625000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16309/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(860397827729679/8154500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(170728464111873/2038625000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (8451/10000 : ℝ) ^ (17/4 : ℝ) ≤ (48905694683875580369/100000000000000000000 : ℝ) := by
    have hpowers : (8451/10000 : ℝ)^17 ≤ (48905694683875580369/100000000000000000000 : ℝ)^4 := by
      have hnat : (8451 : ℕ)^17*100000000000000000000^4 ≤ 48905694683875580369^4*10000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8451 10000 48905694683875580369 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8451/10000 : ℝ)) (X := (48905694683875580369/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (148905694683875580369/100000000000000000000 : ℝ) ≤ (5491045188631451/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (148905694683875580369/100000000000000000000 : ℝ)^4 ≤ (5491045188631451/5000000000000000 : ℝ)^17 := by
      have hnat : (148905694683875580369 : ℕ)^4*5000000000000000^17 ≤ 5491045188631451^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        148905694683875580369 100000000000000000000 5491045188631451 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5491045188631451/5000000000000000 : ℝ)) (X := (148905694683875580369/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (98905694683875580369/50000000000000000000 : ℝ) ≤ (1174102970058061/1000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (98905694683875580369/50000000000000000000 : ℝ)^4 ≤ (1174102970058061/1000000000000000 : ℝ)^17 := by
      have hnat : (98905694683875580369 : ℕ)^4*1000000000000000^17 ≤ 1174102970058061^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        98905694683875580369 50000000000000000000 1174102970058061 1000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1174102970058061/1000000000000000 : ℝ)) (X := (98905694683875580369/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(163681729543817/1408500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(63244943609809/704250000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (8451/10000 : ℝ)) (alpha := (163681729543817/1408500000000000 : ℝ)) (beta := (63244943609809/704250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8451/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(163681729543817/1408500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(63244943609809/704250000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (83617/100000 : ℝ) ^ (17/4 : ℝ) ≤ (46746809270866156457/100000000000000000000 : ℝ) := by
    have hpowers : (83617/100000 : ℝ)^17 ≤ (46746809270866156457/100000000000000000000 : ℝ)^4 := by
      have hnat : (83617 : ℕ)^17*100000000000000000000^4 ≤ 46746809270866156457^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83617 100000 46746809270866156457 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (83617/100000 : ℝ)) (X := (46746809270866156457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (146746809270866156457/100000000000000000000 : ℝ) ≤ (10944416887689281/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (146746809270866156457/100000000000000000000 : ℝ)^4 ≤ (10944416887689281/10000000000000000 : ℝ)^17 := by
      have hnat : (146746809270866156457 : ℕ)^4*10000000000000000^17 ≤ 10944416887689281^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        146746809270866156457 100000000000000000000 10944416887689281 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10944416887689281/10000000000000000 : ℝ)) (X := (146746809270866156457/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (96746809270866156457/50000000000000000000 : ℝ) ≤ (584010936443641/500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (96746809270866156457/50000000000000000000 : ℝ)^4 ≤ (584010936443641/500000000000000 : ℝ)^17 := by
      have hnat : (96746809270866156457 : ℕ)^4*500000000000000^17 ≤ 584010936443641^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        96746809270866156457 50000000000000000000 584010936443641 500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (584010936443641/500000000000000 : ℝ)) (X := (96746809270866156457/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(944416887689281/8361700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(735801841183539/8361700000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (83617/100000 : ℝ)) (alpha := (944416887689281/8361700000000000 : ℝ)) (beta := (735801841183539/8361700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (83617/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(944416887689281/8361700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(735801841183539/8361700000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-889757687/5000000000 : ℝ)*X 0 0+(5309165477/10000000000 : ℝ)*X 0 1+(1367170421/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((4497636961/10000000000 : ℝ)*X 1 0+(-521984519/5000000000 : ℝ)*X 1 1+(6701337751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1797726909/10000000000 : ℝ)*X 0 0+(1881210057/5000000000 : ℝ)*X 0 1+(6865083691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1542237381/5000000000 : ℝ)*X 1 0+(-34498373/1250000000 : ℝ)*X 1 1+(2054256659/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((155495183/500000000 : ℝ)*X 2 0+(8199362629/10000000000 : ℝ)*X 2 1+(-272406609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((600929087/1000000000 : ℝ)*X 0 0+(5605318459/10000000000 : ℝ)*X 0 1+(377746129/10000000000 : ℝ)*X 0 2+(600929087/1000000000 : ℝ)*X 1 0+(5605318459/10000000000 : ℝ)*X 1 1+(377746129/10000000000 : ℝ)*X 1 2+(600929087/1000000000 : ℝ)*X 2 0+(5605318459/10000000000 : ℝ)*X 2 1+(377746129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1362606597/10000000000 : ℝ)*X 0 0+(3686139183/10000000000 : ℝ)*X 0 1+(7205073977/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((233275399/1250000000 : ℝ)*X 1 0+(-215440617/2500000000 : ℝ)*X 1 1+(8798177349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3220097637/5000000000 : ℝ)*X 2 0+(1016195467/2000000000 : ℝ)*X 2 1+(-531660553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((4656723229/5000000000 : ℝ)*X 0 0+(303461091/2500000000 : ℝ)*X 0 1+(286946197/5000000000 : ℝ)*X 0 2+(4656723229/5000000000 : ℝ)*X 1 0+(303461091/2500000000 : ℝ)*X 1 1+(286946197/5000000000 : ℝ)*X 1 2+(4656723229/5000000000 : ℝ)*X 2 0+(303461091/2500000000 : ℝ)*X 2 1+(286946197/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-173549523/1250000000 : ℝ)*X 0 0+(3317220463/5000000000 : ℝ)*X 0 1+(4340227431/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((1637611449/2500000000 : ℝ)*X 1 0+(-467917509/10000000000 : ℝ)*X 1 1+(4993661719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1955222729/10000000000 : ℝ)*X 2 0+(873145337/1000000000 : ℝ)*X 2 1+(-220718751/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2337195617/2500000000 : ℝ)*X 0 0+(936870597/10000000000 : ℝ)*X 0 1+(406360461/5000000000 : ℝ)*X 0 2+(2337195617/2500000000 : ℝ)*X 1 0+(936870597/10000000000 : ℝ)*X 1 1+(406360461/5000000000 : ℝ)*X 1 2+(2337195617/2500000000 : ℝ)*X 2 0+(936870597/10000000000 : ℝ)*X 2 1+(406360461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((68353/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68353/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1286039090848008093514209318261/106710280347250000000000000000000000 : ℝ) := by norm_num
    linear_combination (16918464493/50000000000 : ℝ)*(base7) + (252259/1000000000000 : ℝ)*(base49) + (66037/125000000000 : ℝ)*(base59) + (2659089297573/1000000000000 : ℝ)*(major_s2_0) + (2659089297573/1000000000000 : ℝ)*(major_s2_1) + (2659089297573/1000000000000 : ℝ)*(major_s2_2) + (3362479/125000000000 : ℝ)*(sp_s2_0) + (579359/1000000000000 : ℝ)*(sp_s2_1) + (682679461851/200000000000 : ℝ)*(sp_s2_7) + (426690190209/125000000000 : ℝ)*(sp_s2_8) + (3413523745679/1000000000000 : ℝ)*(sp_s2_9) + (127198760593/62500000000 : ℝ)*(sp_s2_13) + (99536593/1000000000000 : ℝ)*(sp_s2_14) + (205581/125000000000 : ℝ)*(sp_s2_15) + (424202719907/250000000000 : ℝ)*(f.failure) + (3413523745679/1000000000000 : ℝ)*(f.sum) + (555985695468059061/6543030250000000000000000000000 : ℝ)*base62 + (7205804702036497/8361700000000000000000000000 : ℝ)*base64 + (84439937855123/78250000000000000000000000 : ℝ)*base66 + (3242282388765617/8361700000000000000000000000 : ℝ)*base68 + (24406314120607206747/85231853312500000000000000000000 : ℝ)*base70 + (854156810117667/4077250000000000000000000000 : ℝ)*base72 + (62425780387651/156500000000000000000000000 : ℝ)*base74 + (3407318481963283/8154500000000000000000000000 : ℝ)*base76 + (73788132958241507/319044812500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (20877/25000000000000000 : ℝ)*base87 + (20877/25000000000000000 : ℝ)*base89 + (20877/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37501/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37501/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13989863890419456949997911/3271515125000000000000000000000 : ℝ) := by norm_num
    linear_combination (620484930317/1000000000000 : ℝ)*(base7) + (65516524287/500000000000 : ℝ)*(base53) + (87661/1000000000000 : ℝ)*(base59) + (1879541542581/1000000000000 : ℝ)*(major_s2_0) + (1879541542581/1000000000000 : ℝ)*(major_s2_1) + (874254247003/500000000000 : ℝ)*(major_s2_2) + (4388209/1000000000000 : ℝ)*(sp_s2_0) + (8317941/250000000000 : ℝ)*(sp_s2_7) + (71543/3906250000 : ℝ)*(sp_s2_8) + (1023758157801/500000000000 : ℝ)*(sp_s2_14) + (1023767830283/500000000000 : ℝ)*(sp_s2_15) + (2178587024149/1000000000000 : ℝ)*(sp_s2_16) + (181981077953/100000000000 : ℝ)*(sp_s2_20) + (21061387/500000000000 : ℝ)*(sp_s2_27) + (1199367971987/1000000000000 : ℝ)*(f.failure) + (2178587024149/1000000000000 : ℝ)*(f.sum) + (15760299457519609273/39258181500000000000000000000000 : ℝ)*base63 + (955014216766811/2090425000000000000000000000 : ℝ)*base64 + (178568861757293/234750000000000000000000000 : ℝ)*base66 + (2533800656866943/4180850000000000000000000000 : ℝ)*base69 + (248876059232321105347/681854826500000000000000000000000 : ℝ)*base70 + (55678539209331/1019312500000000000000000000 : ℝ)*base72 + (167936762224459/469500000000000000000000000 : ℝ)*base75 + (1669124503305649/8154500000000000000000000000 : ℝ)*base77 + (60814412027938751/1914268875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (45243/100000000000000000 : ℝ)*base86 + (45243/100000000000000000 : ℝ)*base88 + (54757/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74083/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74083/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (993222365186111107397966169343/106710280347250000000000000000000000 : ℝ) := by norm_num
    linear_combination (29653653917/50000000000 : ℝ)*(base7) + (6766859/500000000000 : ℝ)*(base27) + (4191808763/125000000000 : ℝ)*(base40) + (55079422053/200000000000 : ℝ)*(base43) + (455254817589/250000000000 : ℝ)*(major_s2_0) + (1545622160091/1000000000000 : ℝ)*(major_s2_1) + (455254817589/250000000000 : ℝ)*(major_s2_2) + (673669/250000000000 : ℝ)*(sp_s2_0) + (73830421/1000000000000 : ℝ)*(sp_s2_9) + (2236739/250000000000 : ℝ)*(sp_s2_14) + (920156790451/500000000000 : ℝ)*(sp_s2_21) + (1057861166399/500000000000 : ℝ)*(sp_s2_22) + (115015712007/62500000000 : ℝ)*(sp_s2_23) + (877541721171/500000000000 : ℝ)*(sp_s2_27) + (29050597443/25000000000 : ℝ)*(f.failure) + (1057861166399/500000000000 : ℝ)*(f.sum) + (9383229851409578747/39258181500000000000000000000000 : ℝ)*base62 + (171809330995197/261303125000000000000000000 : ℝ)*base64 + (6182619625823/234750000000000000000000000 : ℝ)*base66 + (40796277896211/2090425000000000000000000000 : ℝ)*base68 + (1701204051443385749/5326990832031250000000000000000 : ℝ)*base70 + (897942633367113/2038625000000000000000000000 : ℝ)*base73 + (12070989377351/469500000000000000000000000 : ℝ)*base74 + (386794033119813/4077250000000000000000000000 : ℝ)*base76 + (452138649921160841/1914268875000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (27/2500000000000000 : ℝ)*base86 + (27/2500000000000000 : ℝ)*base88 + (27/2500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((16309/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16309/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8451/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8451/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(83617/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(83617/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((68353/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(68353/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37501/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37501/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(74083/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(74083/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308053_s2 p hpa hpb X hX hprev1

#print axioms solution
