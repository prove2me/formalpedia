-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310048_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:25:25.610275+00:00
-- url     : https://prove2.me/submissions/865a3196-4913-4abf-bd62-8f24a4fe866a

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
theorem collision_support_c310048_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2636057699/5000000000 : ℝ)*x 0 + (2637472913/5000000000 : ℝ)*x 1 + (-485287713/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2636057699/5000000000 : ℝ)^9 ≤ (8781769218623/20000000000000 : ℝ)^7 := by
    have hnat : (2636057699 : ℕ)^9*20000000000000^7 ≤ 8781769218623^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636057699 5000000000 8781769218623 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2637472913/5000000000 : ℝ)^9 ≤ (1373098652041/3125000000000 : ℝ)^7 := by
    have hnat : (2637472913 : ℕ)^9*3125000000000^7 ≤ 1373098652041^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637472913 5000000000 1373098652041 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485287713/2500000000 : ℝ)^9 ≤ (1215199702577/10000000000000 : ℝ)^7 := by
    have hnat : (485287713 : ℕ)^9*10000000000000^7 ≤ 1215199702577^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485287713 2500000000 1215199702577 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2636057699/5000000000 : ℝ), (2637472913/5000000000 : ℝ), (-485287713/2500000000 : ℝ)] ![(8781769218623/20000000000000 : ℝ), (1373098652041/3125000000000 : ℝ), (1215199702577/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2636057699/5000000000 : ℝ)|^9 ≤ (8781769218623/20000000000000 : ℝ)^7
        have hw : |(2636057699/5000000000 : ℝ)|=(2636057699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2637472913/5000000000 : ℝ)|^9 ≤ (1373098652041/3125000000000 : ℝ)^7
        have hw : |(2637472913/5000000000 : ℝ)|=(2637472913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485287713/2500000000 : ℝ)|^9 ≤ (1215199702577/10000000000000 : ℝ)^7
        have hw : |(-485287713/2500000000 : ℝ)|=(485287713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2441280329/10000000000 : ℝ)*x 0 + (6669071/31250000 : ℝ)*x 1 + (-7573703837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2441280329/10000000000 : ℝ)^9 ≤ (16317411523131/100000000000000 : ℝ)^7 := by
    have hnat : (2441280329 : ℕ)^9*100000000000000^7 ≤ 16317411523131^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441280329 10000000000 16317411523131 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6669071/31250000 : ℝ)^9 ≤ (6863293285469/50000000000000 : ℝ)^7 := by
    have hnat : (6669071 : ℕ)^9*50000000000000^7 ≤ 6863293285469^7*31250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6669071 31250000 6863293285469 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7573703837/10000000000 : ℝ)^9 ≤ (34978000945441/50000000000000 : ℝ)^7 := by
    have hnat : (7573703837 : ℕ)^9*50000000000000^7 ≤ 34978000945441^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7573703837 10000000000 34978000945441 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2441280329/10000000000 : ℝ), (6669071/31250000 : ℝ), (-7573703837/10000000000 : ℝ)] ![(16317411523131/100000000000000 : ℝ), (6863293285469/50000000000000 : ℝ), (34978000945441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2441280329/10000000000 : ℝ)|^9 ≤ (16317411523131/100000000000000 : ℝ)^7
        have hw : |(-2441280329/10000000000 : ℝ)|=(2441280329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6669071/31250000 : ℝ)|^9 ≤ (6863293285469/50000000000000 : ℝ)^7
        have hw : |(6669071/31250000 : ℝ)|=(6669071/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7573703837/10000000000 : ℝ)|^9 ≤ (34978000945441/50000000000000 : ℝ)^7
        have hw : |(-7573703837/10000000000 : ℝ)|=(7573703837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (330758183/1000000000 : ℝ)*x 0 + (-722850147/2500000000 : ℝ)*x 1 + (-6335122547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330758183/1000000000 : ℝ)^9 ≤ (12055852209427/50000000000000 : ℝ)^7 := by
    have hnat : (330758183 : ℕ)^9*50000000000000^7 ≤ 12055852209427^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330758183 1000000000 12055852209427 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (722850147/2500000000 : ℝ)^9 ≤ (811333090501/4000000000000 : ℝ)^7 := by
    have hnat : (722850147 : ℕ)^9*4000000000000^7 ≤ 811333090501^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722850147 2500000000 811333090501 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6335122547/10000000000 : ℝ)^9 ≤ (27802484153651/50000000000000 : ℝ)^7 := by
    have hnat : (6335122547 : ℕ)^9*50000000000000^7 ≤ 27802484153651^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6335122547 10000000000 27802484153651 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330758183/1000000000 : ℝ), (-722850147/2500000000 : ℝ), (-6335122547/10000000000 : ℝ)] ![(12055852209427/50000000000000 : ℝ), (811333090501/4000000000000 : ℝ), (27802484153651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330758183/1000000000 : ℝ)|^9 ≤ (12055852209427/50000000000000 : ℝ)^7
        have hw : |(330758183/1000000000 : ℝ)|=(330758183/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-722850147/2500000000 : ℝ)|^9 ≤ (811333090501/4000000000000 : ℝ)^7
        have hw : |(-722850147/2500000000 : ℝ)|=(722850147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6335122547/10000000000 : ℝ)|^9 ≤ (27802484153651/50000000000000 : ℝ)^7
        have hw : |(-6335122547/10000000000 : ℝ)|=(6335122547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4978488273/10000000000 : ℝ)*x 0 + (6544102903/10000000000 : ℝ)*x 1 + (164015191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4978488273/10000000000 : ℝ)^9 ≤ (40790019576257/100000000000000 : ℝ)^7 := by
    have hnat : (4978488273 : ℕ)^9*100000000000000^7 ≤ 40790019576257^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978488273 10000000000 40790019576257 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6544102903/10000000000 : ℝ)^9 ≤ (28987173679797/50000000000000 : ℝ)^7 := by
    have hnat : (6544102903 : ℕ)^9*50000000000000^7 ≤ 28987173679797^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6544102903 10000000000 28987173679797 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164015191/5000000000 : ℝ)^9 ≤ (617816528047/50000000000000 : ℝ)^7 := by
    have hnat : (164015191 : ℕ)^9*50000000000000^7 ≤ 617816528047^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164015191 5000000000 617816528047 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4978488273/10000000000 : ℝ), (6544102903/10000000000 : ℝ), (164015191/5000000000 : ℝ)] ![(40790019576257/100000000000000 : ℝ), (28987173679797/50000000000000 : ℝ), (617816528047/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4978488273/10000000000 : ℝ)|^9 ≤ (40790019576257/100000000000000 : ℝ)^7
        have hw : |(4978488273/10000000000 : ℝ)|=(4978488273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6544102903/10000000000 : ℝ)|^9 ≤ (28987173679797/50000000000000 : ℝ)^7
        have hw : |(6544102903/10000000000 : ℝ)|=(6544102903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164015191/5000000000 : ℝ)|^9 ≤ (617816528047/50000000000000 : ℝ)^7
        have hw : |(164015191/5000000000 : ℝ)|=(164015191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (987554221/2000000000 : ℝ)*x 0 + (6490581167/10000000000 : ℝ)*x 1 + (-526979571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987554221/2000000000 : ℝ)^9 ≤ (20180799781327/50000000000000 : ℝ)^7 := by
    have hnat : (987554221 : ℕ)^9*50000000000000^7 ≤ 20180799781327^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987554221 2000000000 20180799781327 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6490581167/10000000000 : ℝ)^9 ≤ (286827196647/500000000000 : ℝ)^7 := by
    have hnat : (6490581167 : ℕ)^9*500000000000^7 ≤ 286827196647^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6490581167 10000000000 286827196647 500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526979571/10000000000 : ℝ)^9 ≤ (2272961095599/100000000000000 : ℝ)^7 := by
    have hnat : (526979571 : ℕ)^9*100000000000000^7 ≤ 2272961095599^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526979571 10000000000 2272961095599 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(987554221/2000000000 : ℝ), (6490581167/10000000000 : ℝ), (-526979571/10000000000 : ℝ)] ![(20180799781327/50000000000000 : ℝ), (286827196647/500000000000 : ℝ), (2272961095599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(987554221/2000000000 : ℝ)|^9 ≤ (20180799781327/50000000000000 : ℝ)^7
        have hw : |(987554221/2000000000 : ℝ)|=(987554221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6490581167/10000000000 : ℝ)|^9 ≤ (286827196647/500000000000 : ℝ)^7
        have hw : |(6490581167/10000000000 : ℝ)|=(6490581167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526979571/10000000000 : ℝ)|^9 ≤ (2272961095599/100000000000000 : ℝ)^7
        have hw : |(-526979571/10000000000 : ℝ)|=(526979571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-533968313/2500000000 : ℝ)*x 0 + (2439569219/10000000000 : ℝ)*x 1 + (-378685443/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533968313/2500000000 : ℝ)^9 ≤ (3435307535029/25000000000000 : ℝ)^7 := by
    have hnat : (533968313 : ℕ)^9*25000000000000^7 ≤ 3435307535029^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533968313 2500000000 3435307535029 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439569219/10000000000 : ℝ)^9 ≤ (16302708301/100000000000 : ℝ)^7 := by
    have hnat : (2439569219 : ℕ)^9*100000000000^7 ≤ 16302708301^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439569219 10000000000 16302708301 100000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378685443/500000000 : ℝ)^9 ≤ (8744507692849/12500000000000 : ℝ)^7 := by
    have hnat : (378685443 : ℕ)^9*12500000000000^7 ≤ 8744507692849^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378685443 500000000 8744507692849 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533968313/2500000000 : ℝ), (2439569219/10000000000 : ℝ), (-378685443/500000000 : ℝ)] ![(3435307535029/25000000000000 : ℝ), (16302708301/100000000000 : ℝ), (8744507692849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533968313/2500000000 : ℝ)|^9 ≤ (3435307535029/25000000000000 : ℝ)^7
        have hw : |(-533968313/2500000000 : ℝ)|=(533968313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2439569219/10000000000 : ℝ)|^9 ≤ (16302708301/100000000000 : ℝ)^7
        have hw : |(2439569219/10000000000 : ℝ)|=(2439569219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378685443/500000000 : ℝ)|^9 ≤ (8744507692849/12500000000000 : ℝ)^7
        have hw : |(-378685443/500000000 : ℝ)|=(378685443/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (578759977/2000000000 : ℝ)*x 0 + (-1652632037/5000000000 : ℝ)*x 1 + (-1267025903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578759977/2000000000 : ℝ)^9 ≤ (20304969934783/100000000000000 : ℝ)^7 := by
    have hnat : (578759977 : ℕ)^9*100000000000000^7 ≤ 20304969934783^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578759977 2000000000 20304969934783 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1652632037/5000000000 : ℝ)^9 ≤ (6022495777233/25000000000000 : ℝ)^7 := by
    have hnat : (1652632037 : ℕ)^9*25000000000000^7 ≤ 6022495777233^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652632037 5000000000 6022495777233 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267025903/2000000000 : ℝ)^9 ≤ (55605046941463/100000000000000 : ℝ)^7 := by
    have hnat : (1267025903 : ℕ)^9*100000000000000^7 ≤ 55605046941463^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267025903 2000000000 55605046941463 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(578759977/2000000000 : ℝ), (-1652632037/5000000000 : ℝ), (-1267025903/2000000000 : ℝ)] ![(20304969934783/100000000000000 : ℝ), (6022495777233/25000000000000 : ℝ), (55605046941463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(578759977/2000000000 : ℝ)|^9 ≤ (20304969934783/100000000000000 : ℝ)^7
        have hw : |(578759977/2000000000 : ℝ)|=(578759977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1652632037/5000000000 : ℝ)|^9 ≤ (6022495777233/25000000000000 : ℝ)^7
        have hw : |(-1652632037/5000000000 : ℝ)|=(1652632037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1267025903/2000000000 : ℝ)|^9 ≤ (55605046941463/100000000000000 : ℝ)^7
        have hw : |(-1267025903/2000000000 : ℝ)|=(1267025903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6541212803/10000000000 : ℝ)*x 0 + (2490807587/5000000000 : ℝ)*x 1 + (65605017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6541212803/10000000000 : ℝ)^9 ≤ (3621339419091/6250000000000 : ℝ)^7 := by
    have hnat : (6541212803 : ℕ)^9*6250000000000^7 ≤ 3621339419091^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6541212803 10000000000 3621339419091 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2490807587/5000000000 : ℝ)^9 ≤ (2551435117589/6250000000000 : ℝ)^7 := by
    have hnat : (2490807587 : ℕ)^9*6250000000000^7 ≤ 2551435117589^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490807587 5000000000 2551435117589 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65605017/2000000000 : ℝ)^9 ≤ (61780370123/5000000000000 : ℝ)^7 := by
    have hnat : (65605017 : ℕ)^9*5000000000000^7 ≤ 61780370123^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65605017 2000000000 61780370123 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6541212803/10000000000 : ℝ), (2490807587/5000000000 : ℝ), (65605017/2000000000 : ℝ)] ![(3621339419091/6250000000000 : ℝ), (2551435117589/6250000000000 : ℝ), (61780370123/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6541212803/10000000000 : ℝ)|^9 ≤ (3621339419091/6250000000000 : ℝ)^7
        have hw : |(6541212803/10000000000 : ℝ)|=(6541212803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2490807587/5000000000 : ℝ)|^9 ≤ (2551435117589/6250000000000 : ℝ)^7
        have hw : |(2490807587/5000000000 : ℝ)|=(2490807587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65605017/2000000000 : ℝ)|^9 ≤ (61780370123/5000000000000 : ℝ)^7
        have hw : |(65605017/2000000000 : ℝ)|=(65605017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_18 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1621928961/2500000000 : ℝ)*x 0 + (4940873301/10000000000 : ℝ)*x 1 + (-526971011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1621928961/2500000000 : ℝ)^9 ≤ (5733288135321/10000000000000 : ℝ)^7 := by
    have hnat : (1621928961 : ℕ)^9*10000000000000^7 ≤ 5733288135321^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1621928961 2500000000 5733288135321 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4940873301/10000000000 : ℝ)^9 ≤ (20197102502227/50000000000000 : ℝ)^7 := by
    have hnat : (4940873301 : ℕ)^9*50000000000000^7 ≤ 20197102502227^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4940873301 10000000000 20197102502227 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526971011/10000000000 : ℝ)^9 ≤ (568228406503/25000000000000 : ℝ)^7 := by
    have hnat : (526971011 : ℕ)^9*25000000000000^7 ≤ 568228406503^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526971011 10000000000 568228406503 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1621928961/2500000000 : ℝ), (4940873301/10000000000 : ℝ), (-526971011/10000000000 : ℝ)] ![(5733288135321/10000000000000 : ℝ), (20197102502227/50000000000000 : ℝ), (568228406503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1621928961/2500000000 : ℝ)|^9 ≤ (5733288135321/10000000000000 : ℝ)^7
        have hw : |(1621928961/2500000000 : ℝ)|=(1621928961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4940873301/10000000000 : ℝ)|^9 ≤ (20197102502227/50000000000000 : ℝ)^7
        have hw : |(4940873301/10000000000 : ℝ)|=(4940873301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-526971011/10000000000 : ℝ)|^9 ≤ (568228406503/25000000000000 : ℝ)^7
        have hw : |(-526971011/10000000000 : ℝ)|=(526971011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1580542249/5000000000 : ℝ)*x 0 + (1934588069/10000000000 : ℝ)*x 1 + (-3583061837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1580542249/5000000000 : ℝ)^9 ≤ (11373709702619/50000000000000 : ℝ)^7 := by
    have hnat : (1580542249 : ℕ)^9*50000000000000^7 ≤ 11373709702619^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580542249 5000000000 11373709702619 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1934588069/10000000000 : ℝ)^9 ≤ (12099199824039/100000000000000 : ℝ)^7 := by
    have hnat : (1934588069 : ℕ)^9*100000000000000^7 ≤ 12099199824039^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1934588069 10000000000 12099199824039 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3583061837/5000000000 : ℝ)^9 ≤ (65153380763679/100000000000000 : ℝ)^7 := by
    have hnat : (3583061837 : ℕ)^9*100000000000000^7 ≤ 65153380763679^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3583061837 5000000000 65153380763679 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1580542249/5000000000 : ℝ), (1934588069/10000000000 : ℝ), (-3583061837/5000000000 : ℝ)] ![(11373709702619/50000000000000 : ℝ), (12099199824039/100000000000000 : ℝ), (65153380763679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1580542249/5000000000 : ℝ)|^9 ≤ (11373709702619/50000000000000 : ℝ)^7
        have hw : |(-1580542249/5000000000 : ℝ)|=(1580542249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1934588069/10000000000 : ℝ)|^9 ≤ (12099199824039/100000000000000 : ℝ)^7
        have hw : |(1934588069/10000000000 : ℝ)|=(1934588069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3583061837/5000000000 : ℝ)|^9 ≤ (65153380763679/100000000000000 : ℝ)^7
        have hw : |(-3583061837/5000000000 : ℝ)|=(3583061837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (134246277/400000000 : ℝ)*x 0 + (-4578381741/10000000000 : ℝ)*x 1 + (-2394625983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134246277/400000000 : ℝ)^9 ≤ (6141983246773/25000000000000 : ℝ)^7 := by
    have hnat : (134246277 : ℕ)^9*25000000000000^7 ≤ 6141983246773^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134246277 400000000 6141983246773 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4578381741/10000000000 : ℝ)^9 ≤ (18312286607991/50000000000000 : ℝ)^7 := by
    have hnat : (4578381741 : ℕ)^9*50000000000000^7 ≤ 18312286607991^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4578381741 10000000000 18312286607991 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394625983/5000000000 : ℝ)^9 ≤ (9701873444557/25000000000000 : ℝ)^7 := by
    have hnat : (2394625983 : ℕ)^9*25000000000000^7 ≤ 9701873444557^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394625983 5000000000 9701873444557 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134246277/400000000 : ℝ), (-4578381741/10000000000 : ℝ), (-2394625983/5000000000 : ℝ)] ![(6141983246773/25000000000000 : ℝ), (18312286607991/50000000000000 : ℝ), (9701873444557/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134246277/400000000 : ℝ)|^9 ≤ (6141983246773/25000000000000 : ℝ)^7
        have hw : |(134246277/400000000 : ℝ)|=(134246277/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4578381741/10000000000 : ℝ)|^9 ≤ (18312286607991/50000000000000 : ℝ)^7
        have hw : |(-4578381741/10000000000 : ℝ)|=(4578381741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2394625983/5000000000 : ℝ)|^9 ≤ (9701873444557/25000000000000 : ℝ)^7
        have hw : |(-2394625983/5000000000 : ℝ)|=(2394625983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5621582831/10000000000 : ℝ)*x 0 + (2749888771/5000000000 : ℝ)*x 1 + (1114276437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5621582831/10000000000 : ℝ)^9 ≤ (9537172600499/20000000000000 : ℝ)^7 := by
    have hnat : (5621582831 : ℕ)^9*20000000000000^7 ≤ 9537172600499^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621582831 10000000000 9537172600499 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749888771/5000000000 : ℝ)^9 ≤ (4636155730009/10000000000000 : ℝ)^7 := by
    have hnat : (2749888771 : ℕ)^9*10000000000000^7 ≤ 4636155730009^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749888771 5000000000 4636155730009 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1114276437/10000000000 : ℝ)^9 ≤ (93009057469/1562500000000 : ℝ)^7 := by
    have hnat : (1114276437 : ℕ)^9*1562500000000^7 ≤ 93009057469^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114276437 10000000000 93009057469 1562500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5621582831/10000000000 : ℝ), (2749888771/5000000000 : ℝ), (1114276437/10000000000 : ℝ)] ![(9537172600499/20000000000000 : ℝ), (4636155730009/10000000000000 : ℝ), (93009057469/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5621582831/10000000000 : ℝ)|^9 ≤ (9537172600499/20000000000000 : ℝ)^7
        have hw : |(5621582831/10000000000 : ℝ)|=(5621582831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749888771/5000000000 : ℝ)|^9 ≤ (4636155730009/10000000000000 : ℝ)^7
        have hw : |(2749888771/5000000000 : ℝ)|=(2749888771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1114276437/10000000000 : ℝ)|^9 ≤ (93009057469/1562500000000 : ℝ)^7
        have hw : |(1114276437/10000000000 : ℝ)|=(1114276437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310048_s1_s1_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (646005193/2000000000 : ℝ)*x 0 + (2749888771/5000000000 : ℝ)*x 1 + (-3945781713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646005193/2000000000 : ℝ)^9 ≤ (116936250561/500000000000 : ℝ)^7 := by
    have hnat : (646005193 : ℕ)^9*500000000000^7 ≤ 116936250561^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646005193 2000000000 116936250561 500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749888771/5000000000 : ℝ)^9 ≤ (4636155730009/10000000000000 : ℝ)^7 := by
    have hnat : (2749888771 : ℕ)^9*10000000000000^7 ≤ 4636155730009^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749888771 5000000000 4636155730009 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3945781713/10000000000 : ℝ)^9 ≤ (15125596285301/50000000000000 : ℝ)^7 := by
    have hnat : (3945781713 : ℕ)^9*50000000000000^7 ≤ 15125596285301^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3945781713 10000000000 15125596285301 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646005193/2000000000 : ℝ), (2749888771/5000000000 : ℝ), (-3945781713/10000000000 : ℝ)] ![(116936250561/500000000000 : ℝ), (4636155730009/10000000000000 : ℝ), (15125596285301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646005193/2000000000 : ℝ)|^9 ≤ (116936250561/500000000000 : ℝ)^7
        have hw : |(646005193/2000000000 : ℝ)|=(646005193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749888771/5000000000 : ℝ)|^9 ≤ (4636155730009/10000000000000 : ℝ)^7
        have hw : |(2749888771/5000000000 : ℝ)|=(2749888771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3945781713/10000000000 : ℝ)|^9 ≤ (15125596285301/50000000000000 : ℝ)^7
        have hw : |(-3945781713/10000000000 : ℝ)|=(3945781713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310048_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((40751/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40751/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81333/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(81333/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-26581/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-26581/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((25829/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25829/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25819/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25819/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-9549/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-9549/100000 : ℝ)*X 1 2) := by
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
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (40751/50000 : ℝ) ^ (35/8 : ℝ) ≤ (40865909074422652229/100000000000000000000 : ℝ) := by
    have hpowers : (40751/50000 : ℝ)^35 ≤ (40865909074422652229/100000000000000000000 : ℝ)^8 := by
      have hnat : (40751 : ℕ)^35*100000000000000000000^8 ≤ 40865909074422652229^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40751 50000 40865909074422652229 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40751/50000 : ℝ)) (X := (40865909074422652229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (140865909074422652229/100000000000000000000 : ℝ) ≤ (10814657693692017/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (140865909074422652229/100000000000000000000 : ℝ)^8 ≤ (10814657693692017/10000000000000000 : ℝ)^35 := by
      have hnat : (140865909074422652229 : ℕ)^8*10000000000000000^35 ≤ 10814657693692017^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140865909074422652229 100000000000000000000 10814657693692017 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10814657693692017/10000000000000000 : ℝ)) (X := (140865909074422652229/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (90865909074422652229/50000000000000000000 : ℝ) ≤ (2865751421162511/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (90865909074422652229/50000000000000000000 : ℝ)^8 ≤ (2865751421162511/2500000000000000 : ℝ)^35 := by
      have hnat : (90865909074422652229 : ℕ)^8*2500000000000000^35 ≤ 2865751421162511^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90865909074422652229 50000000000000000000 2865751421162511 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2865751421162511/2500000000000000 : ℝ)) (X := (90865909074422652229/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(814657693692017/8150200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(648347990958027/8150200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (40751/50000 : ℝ)) (alpha := (814657693692017/8150200000000000 : ℝ)) (beta := (648347990958027/8150200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40751/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(814657693692017/8150200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(648347990958027/8150200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (81333/100000 : ℝ) ^ (35/8 : ℝ) ≤ (10124118561416470137/25000000000000000000 : ℝ) := by
    have hpowers : (81333/100000 : ℝ)^35 ≤ (10124118561416470137/25000000000000000000 : ℝ)^8 := by
      have hnat : (81333 : ℕ)^35*25000000000000000000^8 ≤ 10124118561416470137^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81333 100000 10124118561416470137 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (81333/100000 : ℝ)) (X := (10124118561416470137/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (35124118561416470137/25000000000000000000 : ℝ) ≤ (2702042066363249/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (35124118561416470137/25000000000000000000 : ℝ)^8 ≤ (2702042066363249/2500000000000000 : ℝ)^35 := by
      have hnat : (35124118561416470137 : ℕ)^8*2500000000000000^35 ≤ 2702042066363249^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35124118561416470137 25000000000000000000 2702042066363249 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2702042066363249/2500000000000000 : ℝ)) (X := (35124118561416470137/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (22624118561416470137/12500000000000000000 : ℝ) ≤ (11452336297431587/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (22624118561416470137/12500000000000000000 : ℝ)^8 ≤ (11452336297431587/10000000000000000 : ℝ)^35 := by
      have hnat : (22624118561416470137 : ℕ)^8*10000000000000000^35 ≤ 11452336297431587^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22624118561416470137 12500000000000000000 11452336297431587 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11452336297431587/10000000000000000 : ℝ)) (X := (22624118561416470137/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(28863152337607/290475000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(71574225775399/903700000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (81333/100000 : ℝ)) (alpha := (28863152337607/290475000000000 : ℝ)) (beta := (71574225775399/903700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (81333/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(28863152337607/290475000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(71574225775399/903700000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (26581/100000 : ℝ) ^ (35/8 : ℝ) ≤ (151869131524474149/50000000000000000000 : ℝ) := by
    have hpowers : (26581/100000 : ℝ)^35 ≤ (151869131524474149/50000000000000000000 : ℝ)^8 := by
      have hnat : (26581 : ℕ)^35*50000000000000000000^8 ≤ 151869131524474149^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26581 100000 151869131524474149 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26581/100000 : ℝ)) (X := (151869131524474149/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (50151869131524474149/50000000000000000000 : ℝ) ≤ (10006934469754409/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (50151869131524474149/50000000000000000000 : ℝ)^8 ≤ (10006934469754409/10000000000000000 : ℝ)^35 := by
      have hnat : (50151869131524474149 : ℕ)^8*10000000000000000^35 ≤ 10006934469754409^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50151869131524474149 50000000000000000000 10006934469754409 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006934469754409/10000000000000000 : ℝ)) (X := (50151869131524474149/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (25151869131524474149/25000000000000000000 : ℝ) ≤ (5006926379631427/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (25151869131524474149/25000000000000000000 : ℝ)^8 ≤ (5006926379631427/5000000000000000 : ℝ)^35 := by
      have hnat : (25151869131524474149 : ℕ)^8*5000000000000000^35 ≤ 5006926379631427^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25151869131524474149 25000000000000000000 5006926379631427 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006926379631427/5000000000000000 : ℝ)) (X := (25151869131524474149/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(6934469754409/2658100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(1383657901689/531620000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (26581/100000 : ℝ)) (alpha := (6934469754409/2658100000000000 : ℝ)) (beta := (1383657901689/531620000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (26581/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(6934469754409/2658100000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(1383657901689/531620000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_6 : ((2636057699/5000000000 : ℝ)*X 0 0+(2637472913/5000000000 : ℝ)*X 0 1+(-485287713/2500000000 : ℝ)*X 0 2+(2636057699/5000000000 : ℝ)*X 1 0+(2637472913/5000000000 : ℝ)*X 1 1+(-485287713/2500000000 : ℝ)*X 1 2+(2636057699/5000000000 : ℝ)*X 2 0+(2637472913/5000000000 : ℝ)*X 2 1+(-485287713/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-2441280329/10000000000 : ℝ)*X 0 0+(6669071/31250000 : ℝ)*X 0 1+(-7573703837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((330758183/1000000000 : ℝ)*X 1 0+(-722850147/2500000000 : ℝ)*X 1 1+(-6335122547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4978488273/10000000000 : ℝ)*X 2 0+(6544102903/10000000000 : ℝ)*X 2 1+(164015191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((987554221/2000000000 : ℝ)*X 0 0+(6490581167/10000000000 : ℝ)*X 0 1+(-526979571/10000000000 : ℝ)*X 0 2+(987554221/2000000000 : ℝ)*X 1 0+(6490581167/10000000000 : ℝ)*X 1 1+(-526979571/10000000000 : ℝ)*X 1 2+(987554221/2000000000 : ℝ)*X 2 0+(6490581167/10000000000 : ℝ)*X 2 1+(-526979571/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-533968313/2500000000 : ℝ)*X 0 0+(2439569219/10000000000 : ℝ)*X 0 1+(-378685443/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((578759977/2000000000 : ℝ)*X 1 0+(-1652632037/5000000000 : ℝ)*X 1 1+(-1267025903/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((6541212803/10000000000 : ℝ)*X 2 0+(2490807587/5000000000 : ℝ)*X 2 1+(65605017/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_18 : ((1621928961/2500000000 : ℝ)*X 0 0+(4940873301/10000000000 : ℝ)*X 0 1+(-526971011/10000000000 : ℝ)*X 0 2+(1621928961/2500000000 : ℝ)*X 1 0+(4940873301/10000000000 : ℝ)*X 1 1+(-526971011/10000000000 : ℝ)*X 1 2+(1621928961/2500000000 : ℝ)*X 2 0+(4940873301/10000000000 : ℝ)*X 2 1+(-526971011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((-1580542249/5000000000 : ℝ)*X 0 0+(1934588069/10000000000 : ℝ)*X 0 1+(-3583061837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((134246277/400000000 : ℝ)*X 1 0+(-4578381741/10000000000 : ℝ)*X 1 1+(-2394625983/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((5621582831/10000000000 : ℝ)*X 2 0+(2749888771/5000000000 : ℝ)*X 2 1+(1114276437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((646005193/2000000000 : ℝ)*X 0 0+(2749888771/5000000000 : ℝ)*X 0 1+(-3945781713/10000000000 : ℝ)*X 0 2+(646005193/2000000000 : ℝ)*X 1 0+(2749888771/5000000000 : ℝ)*X 1 1+(-3945781713/10000000000 : ℝ)*X 1 2+(646005193/2000000000 : ℝ)*X 2 0+(2749888771/5000000000 : ℝ)*X 2 1+(-3945781713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310048_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((25829/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25829/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (22979376404274822986333595563431/1468334919787050000000000000000000000 : ℝ) := by norm_num
    linear_combination (4951679/1000000000000 : ℝ)*(base23) + (12075137877/200000000000 : ℝ)*(base39) + (3969841/1000000000000 : ℝ)*(base49) + (2093094115601/1000000000000 : ℝ)*(base59) + (627241821833/1000000000000 : ℝ)*(base60) + (1216212633581/250000000000 : ℝ)*(major_s1_0) + (1216212633581/250000000000 : ℝ)*(major_s1_1) + (1216212633581/250000000000 : ℝ)*(major_s1_2) + (1680714906623/250000000000 : ℝ)*(sp_s1_7) + (1680676173197/250000000000 : ℝ)*(sp_s1_8) + (6722854674813/1000000000000 : ℝ)*(sp_s1_9) + (3006812391063/1000000000000 : ℝ)*(sp_s1_12) + (19366713/125000000000 : ℝ)*(sp_s1_14) + (11917219/500000000000 : ℝ)*(sp_s1_25) + (3006836225501/1000000000000 : ℝ)*(f.failure) + (1680714906623/250000000000 : ℝ)*(f.sum) + (8037326382324611801/15442231950000000000000000000000 : ℝ)*base62 + (11742477553967/53162000000000000000000000 : ℝ)*base64 + (135365076579503/451850000000000000000000000 : ℝ)*base66 + (581532399042583/1329050000000000000000000000 : ℝ)*base68 + (2023164362165940811/6770014568750000000000000000000 : ℝ)*base70 + (15679684026187/509387500000000000000000000 : ℝ)*base72 + (10647292061947/290475000000000000000000000 : ℝ)*base74 + (461741614507403/2037550000000000000000000000 : ℝ)*base76 + (945893452549864071/4603334837500000000000000000000 : ℝ)*base78 + (83293/100000000000000000 : ℝ)*base87 + (83293/100000000000000000 : ℝ)*base89 + (83293/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25819/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25819/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (88911997409314014763190129031/6992071046605000000000000000000000 : ℝ) := by norm_num
    linear_combination (15038049/1000000000000 : ℝ)*(base21) + (7546474867/125000000000 : ℝ)*(base39) + (315731/125000000000 : ℝ)*(base49) + (216585249693/100000000000 : ℝ)*(base59) + (955886615351/1000000000000 : ℝ)*(base60) + (4864516322407/1000000000000 : ℝ)*(major_s1_0) + (4864516322407/1000000000000 : ℝ)*(major_s1_1) + (4864516322407/1000000000000 : ℝ)*(major_s1_2) + (36494259/1000000000000 : ℝ)*(sp_s1_6) + (41559197/250000000000 : ℝ)*(sp_s1_7) + (840279063927/125000000000 : ℝ)*(sp_s1_13) + (1680599687051/250000000000 : ℝ)*(sp_s1_14) + (1344476742031/200000000000 : ℝ)*(sp_s1_15) + (1503296581821/500000000000 : ℝ)*(sp_s1_18) + (3006629657901/1000000000000 : ℝ)*(f.failure) + (1680599687051/250000000000 : ℝ)*(f.sum) + (372620823128923661/30884463900000000000000000000000 : ℝ)*base62 + (274076364793103/531620000000000000000000000 : ℝ)*base64 + (14647347338339/129100000000000000000000000 : ℝ)*base66 + (517088083326837/2658100000000000000000000000 : ℝ)*base69 + (157467912337427024391/216640466200000000000000000000000 : ℝ)*base70 + (3813051548903211/8150200000000000000000000000 : ℝ)*base72 + (41103221762573/580950000000000000000000000 : ℝ)*base75 + (1608484842408001/8150200000000000000000000000 : ℝ)*base76 + (880232428346190999/10521908200000000000000000000000 : ℝ)*base78 + (76493/100000000000000000 : ℝ)*base87 + (76493/100000000000000000 : ℝ)*base89 + (76493/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-9549/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-9549/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15069860840597508721963553/900796863750000000000000000000 : ℝ) := by norm_num
    linear_combination (513878578517/500000000000 : ℝ)*(base5) + (339513118261/1000000000000 : ℝ)*(base39) + (4204213/250000000000 : ℝ)*(base50) + (168203612063/125000000000 : ℝ)*(base59) + (400071048917/200000000000 : ℝ)*(major_s1_0) + (400071048917/200000000000 : ℝ)*(major_s1_1) + (400071048917/200000000000 : ℝ)*(major_s1_2) + (46361837/250000000000 : ℝ)*(sp_s1_7) + (36989817/1000000000000 : ℝ)*(sp_s1_9) + (6948747/500000000000 : ℝ)*(sp_s1_15) + (1382076237519/500000000000 : ℝ)*(sp_s1_19) + (552867584477/200000000000 : ℝ)*(sp_s1_20) + (948011048027/250000000000 : ℝ)*(sp_s1_21) + (208609833247/1000000000000 : ℝ)*(sp_s1_25) + (30909174757/25000000000 : ℝ)*(f.failure) + (552867584477/200000000000 : ℝ)*(f.sum) + (3284220061232133707/6176892780000000000000000000000 : ℝ)*base63 + (43609278404863/531620000000000000000000000 : ℝ)*base65 + (74910177053043/180740000000000000000000000 : ℝ)*base67 + (281537182169187/531620000000000000000000000 : ℝ)*base69 + (15259363971597630257/43328093240000000000000000000000 : ℝ)*base70 + (847358178086157/1630040000000000000000000000 : ℝ)*base72 + (5978976062059/7261875000000000000000000 : ℝ)*base75 + (660215531564121/1630040000000000000000000000 : ℝ)*base77 + (1333313551643078161/2946134296000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (3199/2500000000000000 : ℝ)*base86 + (3199/2500000000000000 : ℝ)*base88 + (3199/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![false, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((40751/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40751/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(81333/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(81333/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-26581/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-26581/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((25829/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(25829/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25819/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(25819/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-9549/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-9549/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310048_s1 p hpa hpb X hX hprev0

#print axioms solution
