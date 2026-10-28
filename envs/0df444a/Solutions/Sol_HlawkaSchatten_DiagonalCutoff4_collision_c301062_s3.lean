-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301062_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:39:01.988005+00:00
-- url     : https://prove2.me/submissions/d6290d61-f6fa-4e45-a8ec-58042a3cb263

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
theorem collision_support_c301062_s3_s3_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1390315743/10000000000 : ℝ)*x 0 + (199510807/400000000 : ℝ)*x 1 + (-387043671/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1390315743/10000000000 : ℝ)^65 ≤ (7299846829319/100000000000000 : ℝ)^49 := by
    have hnat : (1390315743 : ℕ)^65*100000000000000^49 ≤ 7299846829319^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390315743 10000000000 7299846829319 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199510807/400000000 : ℝ)^65 ≤ (39743273637127/100000000000000 : ℝ)^49 := by
    have hnat : (199510807 : ℕ)^65*100000000000000^49 ≤ 39743273637127^49*400000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199510807 400000000 39743273637127 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387043671/625000000 : ℝ)^65 ≤ (52956879522651/100000000000000 : ℝ)^49 := by
    have hnat : (387043671 : ℕ)^65*100000000000000^49 ≤ 52956879522651^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387043671 625000000 52956879522651 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1390315743/10000000000 : ℝ), (199510807/400000000 : ℝ), (-387043671/625000000 : ℝ)] ![(7299846829319/100000000000000 : ℝ), (39743273637127/100000000000000 : ℝ), (52956879522651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1390315743/10000000000 : ℝ)|^65 ≤ (7299846829319/100000000000000 : ℝ)^49
        have hw : |(-1390315743/10000000000 : ℝ)|=(1390315743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199510807/400000000 : ℝ)|^65 ≤ (39743273637127/100000000000000 : ℝ)^49
        have hw : |(199510807/400000000 : ℝ)|=(199510807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387043671/625000000 : ℝ)|^65 ≤ (52956879522651/100000000000000 : ℝ)^49
        have hw : |(-387043671/625000000 : ℝ)|=(387043671/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (312037719/625000000 : ℝ)*x 0 + (-1388622413/10000000000 : ℝ)*x 1 + (-1237846713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (312037719/625000000 : ℝ)^65 ≤ (9948592486459/25000000000000 : ℝ)^49 := by
    have hnat : (312037719 : ℕ)^65*25000000000000^49 ≤ 9948592486459^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312037719 625000000 9948592486459 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388622413/10000000000 : ℝ)^65 ≤ (7288055227773/100000000000000 : ℝ)^49 := by
    have hnat : (1388622413 : ℕ)^65*100000000000000^49 ≤ 7288055227773^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388622413 10000000000 7288055227773 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237846713/2000000000 : ℝ)^65 ≤ (52917574803357/100000000000000 : ℝ)^49 := by
    have hnat : (1237846713 : ℕ)^65*100000000000000^49 ≤ 52917574803357^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237846713 2000000000 52917574803357 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(312037719/625000000 : ℝ), (-1388622413/10000000000 : ℝ), (-1237846713/2000000000 : ℝ)] ![(9948592486459/25000000000000 : ℝ), (7288055227773/100000000000000 : ℝ), (52917574803357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(312037719/625000000 : ℝ)|^65 ≤ (9948592486459/25000000000000 : ℝ)^49
        have hw : |(312037719/625000000 : ℝ)|=(312037719/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1388622413/10000000000 : ℝ)|^65 ≤ (7288055227773/100000000000000 : ℝ)^49
        have hw : |(-1388622413/10000000000 : ℝ)|=(1388622413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1237846713/2000000000 : ℝ)|^65 ≤ (52917574803357/100000000000000 : ℝ)^49
        have hw : |(-1237846713/2000000000 : ℝ)|=(1237846713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-794409409/5000000000 : ℝ)*x 0 + (703656969/2500000000 : ℝ)*x 1 + (-7861984601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (794409409/5000000000 : ℝ)^65 ≤ (8713661833577/100000000000000 : ℝ)^49 := by
    have hnat : (794409409 : ℕ)^65*100000000000000^49 ≤ 8713661833577^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794409409 5000000000 8713661833577 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (703656969/2500000000 : ℝ)^65 ≤ (18605445847537/100000000000000 : ℝ)^49 := by
    have hnat : (703656969 : ℕ)^65*100000000000000^49 ≤ 18605445847537^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703656969 2500000000 18605445847537 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7861984601/10000000000 : ℝ)^65 ≤ (72680892304901/100000000000000 : ℝ)^49 := by
    have hnat : (7861984601 : ℕ)^65*100000000000000^49 ≤ 72680892304901^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7861984601 10000000000 72680892304901 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-794409409/5000000000 : ℝ), (703656969/2500000000 : ℝ), (-7861984601/10000000000 : ℝ)] ![(8713661833577/100000000000000 : ℝ), (18605445847537/100000000000000 : ℝ), (72680892304901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-794409409/5000000000 : ℝ)|^65 ≤ (8713661833577/100000000000000 : ℝ)^49
        have hw : |(-794409409/5000000000 : ℝ)|=(794409409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(703656969/2500000000 : ℝ)|^65 ≤ (18605445847537/100000000000000 : ℝ)^49
        have hw : |(703656969/2500000000 : ℝ)|=(703656969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7861984601/10000000000 : ℝ)|^65 ≤ (72680892304901/100000000000000 : ℝ)^49
        have hw : |(-7861984601/10000000000 : ℝ)|=(7861984601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (50142891/156250000 : ℝ)*x 0 + (-540496369/5000000000 : ℝ)*x 1 + (-1964465127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50142891/156250000 : ℝ)^65 ≤ (22141668986117/100000000000000 : ℝ)^49 := by
    have hnat : (50142891 : ℕ)^65*100000000000000^49 ≤ 22141668986117^49*156250000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50142891 156250000 22141668986117 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540496369/5000000000 : ℝ)^65 ≤ (5228009114569/100000000000000 : ℝ)^49 := by
    have hnat : (540496369 : ℕ)^65*100000000000000^49 ≤ 5228009114569^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540496369 5000000000 5228009114569 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1964465127/2500000000 : ℝ)^65 ≤ (3631516094083/5000000000000 : ℝ)^49 := by
    have hnat : (1964465127 : ℕ)^65*5000000000000^49 ≤ 3631516094083^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964465127 2500000000 3631516094083 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(50142891/156250000 : ℝ), (-540496369/5000000000 : ℝ), (-1964465127/2500000000 : ℝ)] ![(22141668986117/100000000000000 : ℝ), (5228009114569/100000000000000 : ℝ), (3631516094083/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(50142891/156250000 : ℝ)|^65 ≤ (22141668986117/100000000000000 : ℝ)^49
        have hw : |(50142891/156250000 : ℝ)|=(50142891/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-540496369/5000000000 : ℝ)|^65 ≤ (5228009114569/100000000000000 : ℝ)^49
        have hw : |(-540496369/5000000000 : ℝ)|=(540496369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1964465127/2500000000 : ℝ)|^65 ≤ (3631516094083/5000000000000 : ℝ)^49
        have hw : |(-1964465127/2500000000 : ℝ)|=(1964465127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7285249/20000000 : ℝ)*x 0 + (7138013429/10000000000 : ℝ)*x 1 + (1744890509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7285249/20000000 : ℝ)^65 ≤ (26194057782667/100000000000000 : ℝ)^49 := by
    have hnat : (7285249 : ℕ)^65*100000000000000^49 ≤ 26194057782667^49*20000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7285249 20000000 26194057782667 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7138013429/10000000000 : ℝ)^65 ≤ (31969503455739/50000000000000 : ℝ)^49 := by
    have hnat : (7138013429 : ℕ)^65*50000000000000^49 ≤ 31969503455739^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7138013429 10000000000 31969503455739 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1744890509/10000000000 : ℝ)^65 ≤ (4933467646333/50000000000000 : ℝ)^49 := by
    have hnat : (1744890509 : ℕ)^65*50000000000000^49 ≤ 4933467646333^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744890509 10000000000 4933467646333 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7285249/20000000 : ℝ), (7138013429/10000000000 : ℝ), (1744890509/10000000000 : ℝ)] ![(26194057782667/100000000000000 : ℝ), (31969503455739/50000000000000 : ℝ), (4933467646333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7285249/20000000 : ℝ)|^65 ≤ (26194057782667/100000000000000 : ℝ)^49
        have hw : |(7285249/20000000 : ℝ)|=(7285249/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7138013429/10000000000 : ℝ)|^65 ≤ (31969503455739/50000000000000 : ℝ)^49
        have hw : |(7138013429/10000000000 : ℝ)|=(7138013429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1744890509/10000000000 : ℝ)|^65 ≤ (4933467646333/50000000000000 : ℝ)^49
        have hw : |(1744890509/10000000000 : ℝ)|=(1744890509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2030443019/5000000000 : ℝ)*x 0 + (7621078721/10000000000 : ℝ)*x 1 + (-627849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030443019/5000000000 : ℝ)^65 ≤ (15128418050949/50000000000000 : ℝ)^49 := by
    have hnat : (2030443019 : ℕ)^65*50000000000000^49 ≤ 15128418050949^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030443019 5000000000 15128418050949 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7621078721/10000000000 : ℝ)^65 ≤ (34870743745997/50000000000000 : ℝ)^49 := by
    have hnat : (7621078721 : ℕ)^65*50000000000000^49 ≤ 34870743745997^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7621078721 10000000000 34870743745997 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627849/2500000000 : ℝ)^65 ≤ (26193729/1562500000000 : ℝ)^49 := by
    have hnat : (627849 : ℕ)^65*1562500000000^49 ≤ 26193729^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627849 2500000000 26193729 1562500000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2030443019/5000000000 : ℝ), (7621078721/10000000000 : ℝ), (-627849/2500000000 : ℝ)] ![(15128418050949/50000000000000 : ℝ), (34870743745997/50000000000000 : ℝ), (26193729/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2030443019/5000000000 : ℝ)|^65 ≤ (15128418050949/50000000000000 : ℝ)^49
        have hw : |(2030443019/5000000000 : ℝ)|=(2030443019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7621078721/10000000000 : ℝ)|^65 ≤ (34870743745997/50000000000000 : ℝ)^49
        have hw : |(7621078721/10000000000 : ℝ)|=(7621078721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-627849/2500000000 : ℝ)|^65 ≤ (26193729/1562500000000 : ℝ)^49
        have hw : |(-627849/2500000000 : ℝ)|=(627849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068851923/10000000000 : ℝ)*x 0 + (1588132079/5000000000 : ℝ)*x 1 + (-1972171199/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068851923/10000000000 : ℝ)^65 ≤ (5150262841933/100000000000000 : ℝ)^49 := by
    have hnat : (1068851923 : ℕ)^65*100000000000000^49 ≤ 5150262841933^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068851923 10000000000 5150262841933 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1588132079/5000000000 : ℝ)^65 ≤ (21841232446961/100000000000000 : ℝ)^49 := by
    have hnat : (1588132079 : ℕ)^65*100000000000000^49 ≤ 21841232446961^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588132079 5000000000 21841232446961 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972171199/2500000000 : ℝ)^65 ≤ (73008504699183/100000000000000 : ℝ)^49 := by
    have hnat : (1972171199 : ℕ)^65*100000000000000^49 ≤ 73008504699183^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972171199 2500000000 73008504699183 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068851923/10000000000 : ℝ), (1588132079/5000000000 : ℝ), (-1972171199/2500000000 : ℝ)] ![(5150262841933/100000000000000 : ℝ), (21841232446961/100000000000000 : ℝ), (73008504699183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068851923/10000000000 : ℝ)|^65 ≤ (5150262841933/100000000000000 : ℝ)^49
        have hw : |(-1068851923/10000000000 : ℝ)|=(1068851923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1588132079/5000000000 : ℝ)|^65 ≤ (21841232446961/100000000000000 : ℝ)^49
        have hw : |(1588132079/5000000000 : ℝ)|=(1588132079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972171199/2500000000 : ℝ)|^65 ≤ (73008504699183/100000000000000 : ℝ)^49
        have hw : |(-1972171199/2500000000 : ℝ)|=(1972171199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1393570767/5000000000 : ℝ)*x 0 + (-1583843137/10000000000 : ℝ)*x 1 + (-3942273407/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1393570767/5000000000 : ℝ)^65 ≤ (18364810837599/100000000000000 : ℝ)^49 := by
    have hnat : (1393570767 : ℕ)^65*100000000000000^49 ≤ 18364810837599^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393570767 5000000000 18364810837599 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1583843137/10000000000 : ℝ)^65 ≤ (4338740695867/50000000000000 : ℝ)^49 := by
    have hnat : (1583843137 : ℕ)^65*50000000000000^49 ≤ 4338740695867^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583843137 10000000000 4338740695867 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3942273407/5000000000 : ℝ)^65 ≤ (18239426940567/25000000000000 : ℝ)^49 := by
    have hnat : (3942273407 : ℕ)^65*25000000000000^49 ≤ 18239426940567^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3942273407 5000000000 18239426940567 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1393570767/5000000000 : ℝ), (-1583843137/10000000000 : ℝ), (-3942273407/5000000000 : ℝ)] ![(18364810837599/100000000000000 : ℝ), (4338740695867/50000000000000 : ℝ), (18239426940567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1393570767/5000000000 : ℝ)|^65 ≤ (18364810837599/100000000000000 : ℝ)^49
        have hw : |(1393570767/5000000000 : ℝ)|=(1393570767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1583843137/10000000000 : ℝ)|^65 ≤ (4338740695867/50000000000000 : ℝ)^49
        have hw : |(-1583843137/10000000000 : ℝ)|=(1583843137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3942273407/5000000000 : ℝ)|^65 ≤ (18239426940567/25000000000000 : ℝ)^49
        have hw : |(-3942273407/5000000000 : ℝ)|=(3942273407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (140841773/200000000 : ℝ)*x 0 + (3755857981/10000000000 : ℝ)*x 1 + (875890953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140841773/200000000 : ℝ)^65 ≤ (31400847221887/50000000000000 : ℝ)^49 := by
    have hnat : (140841773 : ℕ)^65*50000000000000^49 ≤ 31400847221887^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140841773 200000000 31400847221887 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3755857981/10000000000 : ℝ)^65 ≤ (2727964311521/10000000000000 : ℝ)^49 := by
    have hnat : (3755857981 : ℕ)^65*10000000000000^49 ≤ 2727964311521^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3755857981 10000000000 2727964311521 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (875890953/5000000000 : ℝ)^65 ≤ (9918662418279/100000000000000 : ℝ)^49 := by
    have hnat : (875890953 : ℕ)^65*100000000000000^49 ≤ 9918662418279^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875890953 5000000000 9918662418279 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140841773/200000000 : ℝ), (3755857981/10000000000 : ℝ), (875890953/5000000000 : ℝ)] ![(31400847221887/50000000000000 : ℝ), (2727964311521/10000000000000 : ℝ), (9918662418279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140841773/200000000 : ℝ)|^65 ≤ (31400847221887/50000000000000 : ℝ)^49
        have hw : |(140841773/200000000 : ℝ)|=(140841773/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3755857981/10000000000 : ℝ)|^65 ≤ (2727964311521/10000000000000 : ℝ)^49
        have hw : |(3755857981/10000000000 : ℝ)|=(3755857981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(875890953/5000000000 : ℝ)|^65 ≤ (9918662418279/100000000000000 : ℝ)^49
        have hw : |(875890953/5000000000 : ℝ)|=(875890953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3887271333/5000000000 : ℝ)*x 0 + (967555049/2500000000 : ℝ)*x 1 + (-684193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3887271333/5000000000 : ℝ)^65 ≤ (71610522663731/100000000000000 : ℝ)^49 := by
    have hnat : (3887271333 : ℕ)^65*100000000000000^49 ≤ 71610522663731^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3887271333 5000000000 71610522663731 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967555049/2500000000 : ℝ)^65 ≤ (14193475640239/50000000000000 : ℝ)^49 := by
    have hnat : (967555049 : ℕ)^65*50000000000000^49 ≤ 14193475640239^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967555049 2500000000 14193475640239 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (684193/2000000000 : ℝ)^65 ≤ (631512673/25000000000000 : ℝ)^49 := by
    have hnat : (684193 : ℕ)^65*25000000000000^49 ≤ 631512673^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684193 2000000000 631512673 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3887271333/5000000000 : ℝ), (967555049/2500000000 : ℝ), (-684193/2000000000 : ℝ)] ![(71610522663731/100000000000000 : ℝ), (14193475640239/50000000000000 : ℝ), (631512673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3887271333/5000000000 : ℝ)|^65 ≤ (71610522663731/100000000000000 : ℝ)^49
        have hw : |(3887271333/5000000000 : ℝ)|=(3887271333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(967555049/2500000000 : ℝ)|^65 ≤ (14193475640239/50000000000000 : ℝ)^49
        have hw : |(967555049/2500000000 : ℝ)|=(967555049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-684193/2000000000 : ℝ)|^65 ≤ (631512673/25000000000000 : ℝ)^49
        have hw : |(-684193/2000000000 : ℝ)|=(684193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-448533683/10000000000 : ℝ)*x 0 + (3255383851/5000000000 : ℝ)*x 1 + (-5179028523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448533683/10000000000 : ℝ)^65 ≤ (325532890337/20000000000000 : ℝ)^49 := by
    have hnat : (448533683 : ℕ)^65*20000000000000^49 ≤ 325532890337^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448533683 10000000000 325532890337 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3255383851/5000000000 : ℝ)^65 ≤ (1414872864303/2500000000000 : ℝ)^49 := by
    have hnat : (3255383851 : ℕ)^65*2500000000000^49 ≤ 1414872864303^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3255383851 5000000000 1414872864303 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179028523/10000000000 : ℝ)^65 ≤ (20888710480679/50000000000000 : ℝ)^49 := by
    have hnat : (5179028523 : ℕ)^65*50000000000000^49 ≤ 20888710480679^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179028523 10000000000 20888710480679 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-448533683/10000000000 : ℝ), (3255383851/5000000000 : ℝ), (-5179028523/10000000000 : ℝ)] ![(325532890337/20000000000000 : ℝ), (1414872864303/2500000000000 : ℝ), (20888710480679/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-448533683/10000000000 : ℝ)|^65 ≤ (325532890337/20000000000000 : ℝ)^49
        have hw : |(-448533683/10000000000 : ℝ)|=(448533683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3255383851/5000000000 : ℝ)|^65 ≤ (1414872864303/2500000000000 : ℝ)^49
        have hw : |(3255383851/5000000000 : ℝ)|=(3255383851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5179028523/10000000000 : ℝ)|^65 ≤ (20888710480679/50000000000000 : ℝ)^49
        have hw : |(-5179028523/10000000000 : ℝ)|=(5179028523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (420857867/625000000 : ℝ)*x 0 + (-332073809/5000000000 : ℝ)*x 1 + (-4829610817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420857867/625000000 : ℝ)^65 ≤ (59180083502043/100000000000000 : ℝ)^49 := by
    have hnat : (420857867 : ℕ)^65*100000000000000^49 ≤ 59180083502043^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420857867 625000000 59180083502043 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (332073809/5000000000 : ℝ)^65 ≤ (684917043171/25000000000000 : ℝ)^49 := by
    have hnat : (332073809 : ℕ)^65*25000000000000^49 ≤ 684917043171^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332073809 5000000000 684917043171 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829610817/10000000000 : ℝ)^65 ≤ (7616049662289/20000000000000 : ℝ)^49 := by
    have hnat : (4829610817 : ℕ)^65*20000000000000^49 ≤ 7616049662289^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829610817 10000000000 7616049662289 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420857867/625000000 : ℝ), (-332073809/5000000000 : ℝ), (-4829610817/10000000000 : ℝ)] ![(59180083502043/100000000000000 : ℝ), (684917043171/25000000000000 : ℝ), (7616049662289/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420857867/625000000 : ℝ)|^65 ≤ (59180083502043/100000000000000 : ℝ)^49
        have hw : |(420857867/625000000 : ℝ)|=(420857867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-332073809/5000000000 : ℝ)|^65 ≤ (684917043171/25000000000000 : ℝ)^49
        have hw : |(-332073809/5000000000 : ℝ)|=(332073809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4829610817/10000000000 : ℝ)|^65 ≤ (7616049662289/20000000000000 : ℝ)^49
        have hw : |(-4829610817/10000000000 : ℝ)|=(4829610817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (695080371/2000000000 : ℝ)*x 0 + (141136031/200000000 : ℝ)*x 1 + (2074568321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (695080371/2000000000 : ℝ)^65 ≤ (12305496008673/50000000000000 : ℝ)^49 := by
    have hnat : (695080371 : ℕ)^65*50000000000000^49 ≤ 12305496008673^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695080371 2000000000 12305496008673 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141136031/200000000 : ℝ)^65 ≤ (12595161671659/20000000000000 : ℝ)^49 := by
    have hnat : (141136031 : ℕ)^65*20000000000000^49 ≤ 12595161671659^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141136031 200000000 12595161671659 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074568321/10000000000 : ℝ)^65 ≤ (12413199612913/100000000000000 : ℝ)^49 := by
    have hnat : (2074568321 : ℕ)^65*100000000000000^49 ≤ 12413199612913^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074568321 10000000000 12413199612913 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(695080371/2000000000 : ℝ), (141136031/200000000 : ℝ), (2074568321/10000000000 : ℝ)] ![(12305496008673/50000000000000 : ℝ), (12595161671659/20000000000000 : ℝ), (12413199612913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(695080371/2000000000 : ℝ)|^65 ≤ (12305496008673/50000000000000 : ℝ)^49
        have hw : |(695080371/2000000000 : ℝ)|=(695080371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141136031/200000000 : ℝ)|^65 ≤ (12595161671659/20000000000000 : ℝ)^49
        have hw : |(141136031/200000000 : ℝ)|=(141136031/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074568321/10000000000 : ℝ)|^65 ≤ (12413199612913/100000000000000 : ℝ)^49
        have hw : |(2074568321/10000000000 : ℝ)|=(2074568321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301062_s3_s3_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (412709791/500000000 : ℝ)*x 0 + (803976209/2500000000 : ℝ)*x 1 + (-22963721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412709791/500000000 : ℝ)^65 ≤ (15505883771967/20000000000000 : ℝ)^49 := by
    have hnat : (412709791 : ℕ)^65*20000000000000^49 ≤ 15505883771967^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412709791 500000000 15505883771967 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803976209/2500000000 : ℝ)^65 ≤ (5550889806451/25000000000000 : ℝ)^49 := by
    have hnat : (803976209 : ℕ)^65*25000000000000^49 ≤ 5550889806451^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803976209 2500000000 5550889806451 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22963721/2000000000 : ℝ)^65 ≤ (267021901069/100000000000000 : ℝ)^49 := by
    have hnat : (22963721 : ℕ)^65*100000000000000^49 ≤ 267021901069^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22963721 2000000000 267021901069 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412709791/500000000 : ℝ), (803976209/2500000000 : ℝ), (-22963721/2000000000 : ℝ)] ![(15505883771967/20000000000000 : ℝ), (5550889806451/25000000000000 : ℝ), (267021901069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412709791/500000000 : ℝ)|^65 ≤ (15505883771967/20000000000000 : ℝ)^49
        have hw : |(412709791/500000000 : ℝ)|=(412709791/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(803976209/2500000000 : ℝ)|^65 ≤ (5550889806451/25000000000000 : ℝ)^49
        have hw : |(803976209/2500000000 : ℝ)|=(803976209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22963721/2000000000 : ℝ)|^65 ≤ (267021901069/100000000000000 : ℝ)^49
        have hw : |(-22963721/2000000000 : ℝ)|=(22963721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301062_s3 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((2676/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2676/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17079/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17079/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2156/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2156/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((37891/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37891/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75797/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75797/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7311/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7311/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (2676/3125 : ℝ) ^ (129/32 : ℝ) ≤ (53510526906013835921/100000000000000000000 : ℝ) := by
    have hpowers : (2676/3125 : ℝ)^129 ≤ (53510526906013835921/100000000000000000000 : ℝ)^32 := by
      have hnat : (2676 : ℕ)^129*100000000000000000000^32 ≤ 53510526906013835921^32*3125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2676 3125 53510526906013835921 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2676/3125 : ℝ)) (X := (53510526906013835921/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0a : (153510526906013835921/100000000000000000000 : ℝ) ≤ (11121767392066841/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (153510526906013835921/100000000000000000000 : ℝ)^32 ≤ (11121767392066841/10000000000000000 : ℝ)^129 := by
      have hnat : (153510526906013835921 : ℕ)^32*10000000000000000^129 ≤ 11121767392066841^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153510526906013835921 100000000000000000000 11121767392066841 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11121767392066841/10000000000000000 : ℝ)) (X := (153510526906013835921/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner0b : (103510526906013835921/50000000000000000000 : ℝ) ≤ (187159218689491/156250000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (103510526906013835921/50000000000000000000 : ℝ)^32 ≤ (187159218689491/156250000000000 : ℝ)^129 := by
      have hnat : (103510526906013835921 : ℕ)^32*156250000000000^129 ≤ 187159218689491^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103510526906013835921 50000000000000000000 187159218689491 156250000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (187159218689491/156250000000000 : ℝ)) (X := (103510526906013835921/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1121767392066841/8563200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(856422604060583/8563200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2676/3125 : ℝ)) (alpha := (1121767392066841/8563200000000000 : ℝ)) (beta := (856422604060583/8563200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (2676/3125 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1121767392066841/8563200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(856422604060583/8563200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (17079/20000 : ℝ) ^ (129/32 : ℝ) ≤ (10583200670753263157/20000000000000000000 : ℝ) := by
    have hpowers : (17079/20000 : ℝ)^129 ≤ (10583200670753263157/20000000000000000000 : ℝ)^32 := by
      have hnat : (17079 : ℕ)^129*20000000000000000000^32 ≤ 10583200670753263157^32*20000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17079 20000 10583200670753263157 20000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17079/20000 : ℝ)) (X := (10583200670753263157/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1a : (30583200670753263157/20000000000000000000 : ℝ) ≤ (2777766758482853/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (30583200670753263157/20000000000000000000 : ℝ)^32 ≤ (2777766758482853/2500000000000000 : ℝ)^129 := by
      have hnat : (30583200670753263157 : ℕ)^32*2500000000000000^129 ≤ 2777766758482853^129*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30583200670753263157 20000000000000000000 2777766758482853 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2777766758482853/2500000000000000 : ℝ)) (X := (30583200670753263157/20000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner1b : (20583200670753263157/10000000000000000000 : ℝ) ≤ (598054342564803/500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (20583200670753263157/10000000000000000000 : ℝ)^32 ≤ (598054342564803/500000000000000 : ℝ)^129 := by
      have hnat : (20583200670753263157 : ℕ)^32*500000000000000^129 ≤ 598054342564803^129*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20583200670753263157 10000000000000000000 598054342564803 500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (598054342564803/500000000000000 : ℝ)) (X := (20583200670753263157/10000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(277766758482853/2134875000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(106252477170581/1067437500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (17079/20000 : ℝ)) (alpha := (277766758482853/2134875000000000 : ℝ)) (beta := (106252477170581/1067437500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (17079/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(277766758482853/2134875000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(106252477170581/1067437500000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (2156/3125 : ℝ) ^ (129/32 : ℝ) ≤ (5598831643361871147/25000000000000000000 : ℝ) := by
    have hpowers : (2156/3125 : ℝ)^129 ≤ (5598831643361871147/25000000000000000000 : ℝ)^32 := by
      have hnat : (2156 : ℕ)^129*25000000000000000000^32 ≤ 5598831643361871147^32*3125^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2156 3125 5598831643361871147 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2156/3125 : ℝ)) (X := (5598831643361871147/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2a : (30598831643361871147/25000000000000000000 : ℝ) ≤ (2628519060640543/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (30598831643361871147/25000000000000000000 : ℝ)^32 ≤ (2628519060640543/2500000000000000 : ℝ)^129 := by
      have hnat : (30598831643361871147 : ℕ)^32*2500000000000000^129 ≤ 2628519060640543^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30598831643361871147 25000000000000000000 2628519060640543 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2628519060640543/2500000000000000 : ℝ)) (X := (30598831643361871147/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s3_corner2b : (18098831643361871147/12500000000000000000 : ℝ) ≤ (5480795822489949/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (18098831643361871147/12500000000000000000 : ℝ)^32 ≤ (5480795822489949/5000000000000000 : ℝ)^129 := by
      have hnat : (18098831643361871147 : ℕ)^32*5000000000000000^129 ≤ 5480795822489949^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18098831643361871147 12500000000000000000 5480795822489949 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5480795822489949/5000000000000000 : ℝ)) (X := (18098831643361871147/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(128519060640543/1724800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(223757701208863/3449600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (2156/3125 : ℝ)) (alpha := (128519060640543/1724800000000000 : ℝ)) (beta := (223757701208863/3449600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (2156/3125 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(128519060640543/1724800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(223757701208863/3449600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1390315743/10000000000 : ℝ)*X 0 0+(199510807/400000000 : ℝ)*X 0 1+(-387043671/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((312037719/625000000 : ℝ)*X 1 0+(-1388622413/10000000000 : ℝ)*X 1 1+(-1237846713/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-794409409/5000000000 : ℝ)*X 0 0+(703656969/2500000000 : ℝ)*X 0 1+(-7861984601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((50142891/156250000 : ℝ)*X 1 0+(-540496369/5000000000 : ℝ)*X 1 1+(-1964465127/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((7285249/20000000 : ℝ)*X 2 0+(7138013429/10000000000 : ℝ)*X 2 1+(1744890509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2030443019/5000000000 : ℝ)*X 0 0+(7621078721/10000000000 : ℝ)*X 0 1+(-627849/2500000000 : ℝ)*X 0 2+(2030443019/5000000000 : ℝ)*X 1 0+(7621078721/10000000000 : ℝ)*X 1 1+(-627849/2500000000 : ℝ)*X 1 2+(2030443019/5000000000 : ℝ)*X 2 0+(7621078721/10000000000 : ℝ)*X 2 1+(-627849/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1068851923/10000000000 : ℝ)*X 0 0+(1588132079/5000000000 : ℝ)*X 0 1+(-1972171199/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((1393570767/5000000000 : ℝ)*X 1 0+(-1583843137/10000000000 : ℝ)*X 1 1+(-3942273407/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((140841773/200000000 : ℝ)*X 2 0+(3755857981/10000000000 : ℝ)*X 2 1+(875890953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3887271333/5000000000 : ℝ)*X 0 0+(967555049/2500000000 : ℝ)*X 0 1+(-684193/2000000000 : ℝ)*X 0 2+(3887271333/5000000000 : ℝ)*X 1 0+(967555049/2500000000 : ℝ)*X 1 1+(-684193/2000000000 : ℝ)*X 1 2+(3887271333/5000000000 : ℝ)*X 2 0+(967555049/2500000000 : ℝ)*X 2 1+(-684193/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-448533683/10000000000 : ℝ)*X 0 0+(3255383851/5000000000 : ℝ)*X 0 1+(-5179028523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((420857867/625000000 : ℝ)*X 1 0+(-332073809/5000000000 : ℝ)*X 1 1+(-4829610817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((695080371/2000000000 : ℝ)*X 2 0+(141136031/200000000 : ℝ)*X 2 1+(2074568321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((412709791/500000000 : ℝ)*X 0 0+(803976209/2500000000 : ℝ)*X 0 1+(-22963721/2000000000 : ℝ)*X 0 2+(412709791/500000000 : ℝ)*X 1 0+(803976209/2500000000 : ℝ)*X 1 1+(-22963721/2000000000 : ℝ)*X 1 2+(412709791/500000000 : ℝ)*X 2 0+(803976209/2500000000 : ℝ)*X 2 1+(-22963721/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301062_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((37891/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37891/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (242303333311888503062939259893/21897008672000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34346486713/50000000000 : ℝ)*(base7) + (1983/12500000000 : ℝ)*(base39) + (14098188171/1000000000000 : ℝ)*(base60) + (2364398579261/1000000000000 : ℝ)*(major_s3_0) + (2364398579261/1000000000000 : ℝ)*(major_s3_1) + (2364398579261/1000000000000 : ℝ)*(major_s3_2) + (7350519/1000000000000 : ℝ)*(sp_s3_0) + (305157/62500000000 : ℝ)*(sp_s3_1) + (2707205126861/1000000000000 : ℝ)*(sp_s3_7) + (108291702953/40000000000 : ℝ)*(sp_s3_8) + (2707298568329/1000000000000 : ℝ)*(sp_s3_9) + (2285317135399/1000000000000 : ℝ)*(sp_s3_13) + (86090949/1000000000000 : ℝ)*(sp_s3_14) + (1111993/1000000000000 : ℝ)*(sp_s3_22) + (1598387401139/1000000000000 : ℝ)*(f.failure) + (2707298568329/1000000000000 : ℝ)*(f.sum) + (11575992107010162521/147289296000000000000000000000000 : ℝ)*base63 + (567985820152477/3449600000000000000000000000 : ℝ)*base64 + (1425303562332761/4269750000000000000000000000 : ℝ)*base66 + (235198257488157/1724800000000000000000000000 : ℝ)*base68 + (793242787461948347/4615564800000000000000000000000 : ℝ)*base70 + (4979178357781963/8563200000000000000000000000 : ℝ)*base73 + (35769957321301/266859375000000000000000000 : ℝ)*base75 + (1407109475322101/8563200000000000000000000000 : ℝ)*base77 + (49372219443448836827/243751488000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (3641/25000000000000000 : ℝ)*base86 + (3641/25000000000000000 : ℝ)*base88 + (3641/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75797/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75797/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7540152800476443562600701/1402755200000000000000000000000 : ℝ) := by norm_num
    linear_combination (69086999149/100000000000 : ℝ)*(base7) + (75667/1000000000000 : ℝ)*(base40) + (152023/500000000000 : ℝ)*(base59) + (2326082886477/1000000000000 : ℝ)*(major_s3_0) + (2326082886477/1000000000000 : ℝ)*(major_s3_1) + (2326082886477/1000000000000 : ℝ)*(major_s3_2) + (297171/500000000000 : ℝ)*(sp_s3_0) + (141737/500000000000 : ℝ)*(sp_s3_1) + (10709729/250000000000 : ℝ)*(sp_s3_8) + (1327071902973/500000000000 : ℝ)*(sp_s3_14) + (2654101277897/1000000000000 : ℝ)*(sp_s3_15) + (82942012509/31250000000 : ℝ)*(sp_s3_16) + (1131673002533/500000000000 : ℝ)*(sp_s3_20) + (455239/50000000000 : ℝ)*(sp_s3_27) + (393121279589/250000000000 : ℝ)*(f.failure) + (82942012509/31250000000 : ℝ)*(f.sum) + (667774334506869957/7013776000000000000000000000000 : ℝ)*base63 + (87194614784427/492800000000000000000000000 : ℝ)*base64 + (62386365430933/711625000000000000000000000 : ℝ)*base67 + (110938773785813/246400000000000000000000000 : ℝ)*base69 + (93641347480320319/219788800000000000000000000000 : ℝ)*base70 + (1779902221261463/2854400000000000000000000000 : ℝ)*base72 + (29548550460777/711625000000000000000000000 : ℝ)*base75 + (42746849510359/2854400000000000000000000000 : ℝ)*base77 + (5266236230510578713/81250496000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (441/6250000000000000 : ℝ)*base86 + (441/6250000000000000 : ℝ)*base88 + (441/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7311/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7311/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10276769251748093963300464377/1094850433600000000000000000000000 : ℝ) := by norm_num
    linear_combination (101698666189/250000000000 : ℝ)*(base7) + (2940361/200000000000 : ℝ)*(base11) + (92942366283/1000000000000 : ℝ)*(base39) + (579021/1000000000000 : ℝ)*(base59) + (1110537583269/500000000000 : ℝ)*(major_s3_0) + (1110537583269/500000000000 : ℝ)*(major_s3_1) + (1110537583269/500000000000 : ℝ)*(major_s3_2) + (5802481/250000000000 : ℝ)*(sp_s3_0) + (29669987/200000000000 : ℝ)*(sp_s3_9) + (15403567/1000000000000 : ℝ)*(sp_s3_20) + (2690050683577/1000000000000 : ℝ)*(sp_s3_21) + (1345044297653/500000000000 : ℝ)*(sp_s3_22) + (2689940245371/1000000000000 : ℝ)*(sp_s3_23) + (76331070573/40000000000 : ℝ)*(sp_s3_27) + (300299500627/200000000000 : ℝ)*(f.failure) + (1345044297653/500000000000 : ℝ)*(f.sum) + (5817490288778315797/24548216000000000000000000000000 : ℝ)*base62 + (298771535040133/1724800000000000000000000000 : ℝ)*base64 + (132061910937021/1423250000000000000000000000 : ℝ)*base66 + (134781744477893/862400000000000000000000000 : ℝ)*base68 + (203350948192904881/769260800000000000000000000000 : ℝ)*base70 + (291184146104351/1427200000000000000000000000 : ℝ)*base72 + (266226058612499/1423250000000000000000000000 : ℝ)*base74 + (24233035384097/1427200000000000000000000000 : ℝ)*base76 + (4545530761823629039/40625248000000000000000000000000 : ℝ)*base78 + (2913/5000000000000000 : ℝ)*base86 + (2913/5000000000000000 : ℝ)*base88 + (2913/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev2 : (0 : ℝ) ≤ ((2676/3125 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2676/3125 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17079/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(17079/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-2156/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-2156/3125 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((37891/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(37891/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75797/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75797/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-7311/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-7311/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301062_s3 p hpa hpb X hX hprev2

#print axioms solution
