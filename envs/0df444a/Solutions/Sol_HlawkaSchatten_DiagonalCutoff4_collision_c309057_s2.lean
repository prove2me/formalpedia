-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309057_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:03:51.286799+00:00
-- url     : https://prove2.me/submissions/f5f1347d-f9a8-4e81-aa95-0d304f507da4

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
theorem collision_support_c309057_s2_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (818609843/2500000000 : ℝ)*x 0 + (-1636196899/5000000000 : ℝ)*x 1 + (765686609/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (818609843/2500000000 : ℝ)^35 ≤ (5880494355857/25000000000000 : ℝ)^27 := by
    have hnat : (818609843 : ℕ)^35*25000000000000^27 ≤ 5880494355857^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818609843 2500000000 5880494355857 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1636196899/5000000000 : ℝ)^35 ≤ (2937866360123/12500000000000 : ℝ)^27 := by
    have hnat : (1636196899 : ℕ)^35*12500000000000^27 ≤ 2937866360123^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636196899 5000000000 2937866360123 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (765686609/1250000000 : ℝ)^35 ≤ (52975091681979/100000000000000 : ℝ)^27 := by
    have hnat : (765686609 : ℕ)^35*100000000000000^27 ≤ 52975091681979^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765686609 1250000000 52975091681979 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(818609843/2500000000 : ℝ), (-1636196899/5000000000 : ℝ), (765686609/1250000000 : ℝ)] ![(5880494355857/25000000000000 : ℝ), (2937866360123/12500000000000 : ℝ), (52975091681979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(818609843/2500000000 : ℝ)|^35 ≤ (5880494355857/25000000000000 : ℝ)^27
        have hw : |(818609843/2500000000 : ℝ)|=(818609843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1636196899/5000000000 : ℝ)|^35 ≤ (2937866360123/12500000000000 : ℝ)^27
        have hw : |(-1636196899/5000000000 : ℝ)|=(1636196899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(765686609/1250000000 : ℝ)|^35 ≤ (52975091681979/100000000000000 : ℝ)^27
        have hw : |(765686609/1250000000 : ℝ)|=(765686609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7191867/12500000 : ℝ)*x 0 + (5756493871/10000000000 : ℝ)*x 1 + (-541347703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7191867/12500000 : ℝ)^35 ≤ (48842767840037/100000000000000 : ℝ)^27 := by
    have hnat : (7191867 : ℕ)^35*100000000000000^27 ≤ 48842767840037^27*12500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7191867 12500000 48842767840037 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5756493871/10000000000 : ℝ)^35 ≤ (9775157414027/20000000000000 : ℝ)^27 := by
    have hnat : (5756493871 : ℕ)^35*20000000000000^27 ≤ 9775157414027^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5756493871 10000000000 9775157414027 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541347703/10000000000 : ℝ)^35 ≤ (1140722533941/50000000000000 : ℝ)^27 := by
    have hnat : (541347703 : ℕ)^35*50000000000000^27 ≤ 1140722533941^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541347703 10000000000 1140722533941 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7191867/12500000 : ℝ), (5756493871/10000000000 : ℝ), (-541347703/10000000000 : ℝ)] ![(48842767840037/100000000000000 : ℝ), (9775157414027/20000000000000 : ℝ), (1140722533941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7191867/12500000 : ℝ)|^35 ≤ (48842767840037/100000000000000 : ℝ)^27
        have hw : |(7191867/12500000 : ℝ)|=(7191867/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5756493871/10000000000 : ℝ)|^35 ≤ (9775157414027/20000000000000 : ℝ)^27
        have hw : |(5756493871/10000000000 : ℝ)|=(5756493871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-541347703/10000000000 : ℝ)|^35 ≤ (1140722533941/50000000000000 : ℝ)^27
        have hw : |(-541347703/10000000000 : ℝ)|=(541347703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2316572733/5000000000 : ℝ)*x 0 + (463556151/1000000000 : ℝ)*x 1 + (3558511219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2316572733/5000000000 : ℝ)^35 ≤ (36887244398549/100000000000000 : ℝ)^27 := by
    have hnat : (2316572733 : ℕ)^35*100000000000000^27 ≤ 36887244398549^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316572733 5000000000 36887244398549 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463556151/1000000000 : ℝ)^35 ≤ (36912181326047/100000000000000 : ℝ)^27 := by
    have hnat : (463556151 : ℕ)^35*100000000000000^27 ≤ 36912181326047^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463556151 1000000000 36912181326047 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3558511219/10000000000 : ℝ)^35 ≤ (26200574264837/100000000000000 : ℝ)^27 := by
    have hnat : (3558511219 : ℕ)^35*100000000000000^27 ≤ 26200574264837^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3558511219 10000000000 26200574264837 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2316572733/5000000000 : ℝ), (463556151/1000000000 : ℝ), (3558511219/10000000000 : ℝ)] ![(36887244398549/100000000000000 : ℝ), (36912181326047/100000000000000 : ℝ), (26200574264837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2316572733/5000000000 : ℝ)|^35 ≤ (36887244398549/100000000000000 : ℝ)^27
        have hw : |(2316572733/5000000000 : ℝ)|=(2316572733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(463556151/1000000000 : ℝ)|^35 ≤ (36912181326047/100000000000000 : ℝ)^27
        have hw : |(463556151/1000000000 : ℝ)|=(463556151/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3558511219/10000000000 : ℝ)|^35 ≤ (26200574264837/100000000000000 : ℝ)^27
        have hw : |(3558511219/10000000000 : ℝ)|=(3558511219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507271609/5000000000 : ℝ)*x 0 + (551596111/2000000000 : ℝ)*x 1 + (210829089/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507271609/5000000000 : ℝ)^35 ≤ (10565420400357/50000000000000 : ℝ)^27 := by
    have hnat : (1507271609 : ℕ)^35*50000000000000^27 ≤ 10565420400357^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507271609 5000000000 10565420400357 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551596111/2000000000 : ℝ)^35 ≤ (3765914363247/20000000000000 : ℝ)^27 := by
    have hnat : (551596111 : ℕ)^35*20000000000000^27 ≤ 3765914363247^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551596111 2000000000 3765914363247 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210829089/312500000 : ℝ)^35 ≤ (15009896840259/25000000000000 : ℝ)^27 := by
    have hnat : (210829089 : ℕ)^35*25000000000000^27 ≤ 15009896840259^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210829089 312500000 15009896840259 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507271609/5000000000 : ℝ), (551596111/2000000000 : ℝ), (210829089/312500000 : ℝ)] ![(10565420400357/50000000000000 : ℝ), (3765914363247/20000000000000 : ℝ), (15009896840259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507271609/5000000000 : ℝ)|^35 ≤ (10565420400357/50000000000000 : ℝ)^27
        have hw : |(-1507271609/5000000000 : ℝ)|=(1507271609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(551596111/2000000000 : ℝ)|^35 ≤ (3765914363247/20000000000000 : ℝ)^27
        have hw : |(551596111/2000000000 : ℝ)|=(551596111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210829089/312500000 : ℝ)|^35 ≤ (15009896840259/25000000000000 : ℝ)^27
        have hw : |(210829089/312500000 : ℝ)|=(210829089/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1506393029/5000000000 : ℝ)*x 0 + (-172273309/625000000 : ℝ)*x 1 + (6749147827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1506393029/5000000000 : ℝ)^35 ≤ (21114875638261/100000000000000 : ℝ)^27 := by
    have hnat : (1506393029 : ℕ)^35*100000000000000^27 ≤ 21114875638261^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506393029 5000000000 21114875638261 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172273309/625000000 : ℝ)^35 ≤ (18815345351763/100000000000000 : ℝ)^27 := by
    have hnat : (172273309 : ℕ)^35*100000000000000^27 ≤ 18815345351763^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172273309 625000000 18815345351763 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6749147827/10000000000 : ℝ)^35 ≤ (60069778997991/100000000000000 : ℝ)^27 := by
    have hnat : (6749147827 : ℕ)^35*100000000000000^27 ≤ 60069778997991^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6749147827 10000000000 60069778997991 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1506393029/5000000000 : ℝ), (-172273309/625000000 : ℝ), (6749147827/10000000000 : ℝ)] ![(21114875638261/100000000000000 : ℝ), (18815345351763/100000000000000 : ℝ), (60069778997991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1506393029/5000000000 : ℝ)|^35 ≤ (21114875638261/100000000000000 : ℝ)^27
        have hw : |(1506393029/5000000000 : ℝ)|=(1506393029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-172273309/625000000 : ℝ)|^35 ≤ (18815345351763/100000000000000 : ℝ)^27
        have hw : |(-172273309/625000000 : ℝ)|=(172273309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6749147827/10000000000 : ℝ)|^35 ≤ (60069778997991/100000000000000 : ℝ)^27
        have hw : |(6749147827/10000000000 : ℝ)|=(6749147827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2617512257/5000000000 : ℝ)*x 0 + (6462605589/10000000000 : ℝ)*x 1 + (-251501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2617512257/5000000000 : ℝ)^35 ≤ (43215085578917/100000000000000 : ℝ)^27 := by
    have hnat : (2617512257 : ℕ)^35*100000000000000^27 ≤ 43215085578917^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617512257 5000000000 43215085578917 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6462605589/10000000000 : ℝ)^35 ≤ (28392402666961/50000000000000 : ℝ)^27 := by
    have hnat : (6462605589 : ℕ)^35*50000000000000^27 ≤ 28392402666961^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6462605589 10000000000 28392402666961 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251501/10000000000 : ℝ)^35 ≤ (27269469/25000000000000 : ℝ)^27 := by
    have hnat : (251501 : ℕ)^35*25000000000000^27 ≤ 27269469^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251501 10000000000 27269469 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2617512257/5000000000 : ℝ), (6462605589/10000000000 : ℝ), (-251501/10000000000 : ℝ)] ![(43215085578917/100000000000000 : ℝ), (28392402666961/50000000000000 : ℝ), (27269469/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2617512257/5000000000 : ℝ)|^35 ≤ (43215085578917/100000000000000 : ℝ)^27
        have hw : |(2617512257/5000000000 : ℝ)|=(2617512257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6462605589/10000000000 : ℝ)|^35 ≤ (28392402666961/50000000000000 : ℝ)^27
        have hw : |(6462605589/10000000000 : ℝ)|=(6462605589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251501/10000000000 : ℝ)|^35 ≤ (27269469/25000000000000 : ℝ)^27
        have hw : |(-251501/10000000000 : ℝ)|=(251501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_12 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4601450853/10000000000 : ℝ)*x 0 + (5680462799/10000000000 : ℝ)*x 1 + (1180801137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4601450853/10000000000 : ℝ)^35 ≤ (18280234655631/50000000000000 : ℝ)^27 := by
    have hnat : (4601450853 : ℕ)^35*50000000000000^27 ≤ 18280234655631^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4601450853 10000000000 18280234655631 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5680462799/10000000000 : ℝ)^35 ≤ (48040611403731/100000000000000 : ℝ)^27 := by
    have hnat : (5680462799 : ℕ)^35*100000000000000^27 ≤ 48040611403731^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5680462799 10000000000 48040611403731 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1180801137/5000000000 : ℝ)^35 ≤ (15398919273971/100000000000000 : ℝ)^27 := by
    have hnat : (1180801137 : ℕ)^35*100000000000000^27 ≤ 15398919273971^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180801137 5000000000 15398919273971 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4601450853/10000000000 : ℝ), (5680462799/10000000000 : ℝ), (1180801137/5000000000 : ℝ)] ![(18280234655631/50000000000000 : ℝ), (48040611403731/100000000000000 : ℝ), (15398919273971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4601450853/10000000000 : ℝ)|^35 ≤ (18280234655631/50000000000000 : ℝ)^27
        have hw : |(4601450853/10000000000 : ℝ)|=(4601450853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5680462799/10000000000 : ℝ)|^35 ≤ (48040611403731/100000000000000 : ℝ)^27
        have hw : |(5680462799/10000000000 : ℝ)|=(5680462799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1180801137/5000000000 : ℝ)|^35 ≤ (15398919273971/100000000000000 : ℝ)^27
        have hw : |(1180801137/5000000000 : ℝ)|=(1180801137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2760013573/10000000000 : ℝ)*x 0 + (3012562647/10000000000 : ℝ)*x 1 + (1686632717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2760013573/10000000000 : ℝ)^35 ≤ (4711891603727/25000000000000 : ℝ)^27 := by
    have hnat : (2760013573 : ℕ)^35*25000000000000^27 ≤ 4711891603727^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2760013573 10000000000 4711891603727 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3012562647/10000000000 : ℝ)^35 ≤ (2111284597357/10000000000000 : ℝ)^27 := by
    have hnat : (3012562647 : ℕ)^35*10000000000000^27 ≤ 2111284597357^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3012562647 10000000000 2111284597357 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1686632717/2500000000 : ℝ)^35 ≤ (750494844897/1250000000000 : ℝ)^27 := by
    have hnat : (1686632717 : ℕ)^35*1250000000000^27 ≤ 750494844897^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1686632717 2500000000 750494844897 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2760013573/10000000000 : ℝ), (3012562647/10000000000 : ℝ), (1686632717/2500000000 : ℝ)] ![(4711891603727/25000000000000 : ℝ), (2111284597357/10000000000000 : ℝ), (750494844897/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2760013573/10000000000 : ℝ)|^35 ≤ (4711891603727/25000000000000 : ℝ)^27
        have hw : |(-2760013573/10000000000 : ℝ)|=(2760013573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3012562647/10000000000 : ℝ)|^35 ≤ (2111284597357/10000000000000 : ℝ)^27
        have hw : |(3012562647/10000000000 : ℝ)|=(3012562647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1686632717/2500000000 : ℝ)|^35 ≤ (750494844897/1250000000000 : ℝ)^27
        have hw : |(1686632717/2500000000 : ℝ)|=(1686632717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2758404817/10000000000 : ℝ)*x 0 + (-602161337/2000000000 : ℝ)*x 1 + (3374573891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758404817/10000000000 : ℝ)^35 ≤ (3766665341831/20000000000000 : ℝ)^27 := by
    have hnat : (2758404817 : ℕ)^35*20000000000000^27 ≤ 3766665341831^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758404817 10000000000 3766665341831 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602161337/2000000000 : ℝ)^35 ≤ (21096894802353/100000000000000 : ℝ)^27 := by
    have hnat : (602161337 : ℕ)^35*100000000000000^27 ≤ 21096894802353^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602161337 2000000000 21096894802353 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3374573891/5000000000 : ℝ)^35 ≤ (15017444619701/25000000000000 : ℝ)^27 := by
    have hnat : (3374573891 : ℕ)^35*25000000000000^27 ≤ 15017444619701^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374573891 5000000000 15017444619701 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758404817/10000000000 : ℝ), (-602161337/2000000000 : ℝ), (3374573891/5000000000 : ℝ)] ![(3766665341831/20000000000000 : ℝ), (21096894802353/100000000000000 : ℝ), (15017444619701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758404817/10000000000 : ℝ)|^35 ≤ (3766665341831/20000000000000 : ℝ)^27
        have hw : |(2758404817/10000000000 : ℝ)|=(2758404817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-602161337/2000000000 : ℝ)|^35 ≤ (21096894802353/100000000000000 : ℝ)^27
        have hw : |(-602161337/2000000000 : ℝ)|=(602161337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3374573891/5000000000 : ℝ)|^35 ≤ (15017444619701/25000000000000 : ℝ)^27
        have hw : |(3374573891/5000000000 : ℝ)|=(3374573891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3229853509/5000000000 : ℝ)*x 0 + (52381093/100000000 : ℝ)*x 1 + (-251479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3229853509/5000000000 : ℝ)^35 ≤ (28375896210321/50000000000000 : ℝ)^27 := by
    have hnat : (3229853509 : ℕ)^35*50000000000000^27 ≤ 28375896210321^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3229853509 5000000000 28375896210321 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52381093/100000000 : ℝ)^35 ≤ (43248098494783/100000000000000 : ℝ)^27 := by
    have hnat : (52381093 : ℕ)^35*100000000000000^27 ≤ 43248098494783^27*100000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52381093 100000000 43248098494783 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251479/10000000000 : ℝ)^35 ≤ (109065507/100000000000000 : ℝ)^27 := by
    have hnat : (251479 : ℕ)^35*100000000000000^27 ≤ 109065507^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251479 10000000000 109065507 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3229853509/5000000000 : ℝ), (52381093/100000000 : ℝ), (-251479/10000000000 : ℝ)] ![(28375896210321/50000000000000 : ℝ), (43248098494783/100000000000000 : ℝ), (109065507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3229853509/5000000000 : ℝ)|^35 ≤ (28375896210321/50000000000000 : ℝ)^27
        have hw : |(3229853509/5000000000 : ℝ)|=(3229853509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52381093/100000000 : ℝ)|^35 ≤ (43248098494783/100000000000000 : ℝ)^27
        have hw : |(52381093/100000000 : ℝ)|=(52381093/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251479/10000000000 : ℝ)|^35 ≤ (109065507/100000000000000 : ℝ)^27
        have hw : |(-251479/10000000000 : ℝ)|=(251479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_18 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2838957533/5000000000 : ℝ)*x 0 + (460416233/1000000000 : ℝ)*x 1 + (236160219/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2838957533/5000000000 : ℝ)^35 ≤ (48012682484019/100000000000000 : ℝ)^27 := by
    have hnat : (2838957533 : ℕ)^35*100000000000000^27 ≤ 48012682484019^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838957533 5000000000 48012682484019 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (460416233/1000000000 : ℝ)^35 ≤ (18294199467521/50000000000000 : ℝ)^27 := by
    have hnat : (460416233 : ℕ)^35*50000000000000^27 ≤ 18294199467521^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460416233 1000000000 18294199467521 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236160219/1000000000 : ℝ)^35 ≤ (15398918563957/100000000000000 : ℝ)^27 := by
    have hnat : (236160219 : ℕ)^35*100000000000000^27 ≤ 15398918563957^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236160219 1000000000 15398918563957 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2838957533/5000000000 : ℝ), (460416233/1000000000 : ℝ), (236160219/1000000000 : ℝ)] ![(48012682484019/100000000000000 : ℝ), (18294199467521/50000000000000 : ℝ), (15398918563957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2838957533/5000000000 : ℝ)|^35 ≤ (48012682484019/100000000000000 : ℝ)^27
        have hw : |(2838957533/5000000000 : ℝ)|=(2838957533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(460416233/1000000000 : ℝ)|^35 ≤ (18294199467521/50000000000000 : ℝ)^27
        have hw : |(460416233/1000000000 : ℝ)|=(460416233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(236160219/1000000000 : ℝ)|^35 ≤ (15398918563957/100000000000000 : ℝ)^27
        have hw : |(236160219/1000000000 : ℝ)|=(236160219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_19 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-502198091/1250000000 : ℝ)*x 0 + (2613333359/10000000000 : ℝ)*x 1 + (6018347851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502198091/1250000000 : ℝ)^35 ≤ (30663473825787/100000000000000 : ℝ)^27 := by
    have hnat : (502198091 : ℕ)^35*100000000000000^27 ≤ 30663473825787^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502198091 1250000000 30663473825787 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613333359/10000000000 : ℝ)^35 ≤ (17559485778113/100000000000000 : ℝ)^27 := by
    have hnat : (2613333359 : ℕ)^35*100000000000000^27 ≤ 17559485778113^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613333359 10000000000 17559485778113 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6018347851/10000000000 : ℝ)^35 ≤ (12944260094829/25000000000000 : ℝ)^27 := by
    have hnat : (6018347851 : ℕ)^35*25000000000000^27 ≤ 12944260094829^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6018347851 10000000000 12944260094829 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502198091/1250000000 : ℝ), (2613333359/10000000000 : ℝ), (6018347851/10000000000 : ℝ)] ![(30663473825787/100000000000000 : ℝ), (17559485778113/100000000000000 : ℝ), (12944260094829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502198091/1250000000 : ℝ)|^35 ≤ (30663473825787/100000000000000 : ℝ)^27
        have hw : |(-502198091/1250000000 : ℝ)|=(502198091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613333359/10000000000 : ℝ)|^35 ≤ (17559485778113/100000000000000 : ℝ)^27
        have hw : |(2613333359/10000000000 : ℝ)|=(2613333359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6018347851/10000000000 : ℝ)|^35 ≤ (12944260094829/25000000000000 : ℝ)^27
        have hw : |(6018347851/10000000000 : ℝ)|=(6018347851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2613967367/10000000000 : ℝ)*x 0 + (-4014076223/10000000000 : ℝ)*x 1 + (301048233/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613967367/10000000000 : ℝ)^35 ≤ (17565008225761/100000000000000 : ℝ)^27 := by
    have hnat : (2613967367 : ℕ)^35*100000000000000^27 ≤ 17565008225761^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613967367 10000000000 17565008225761 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4014076223/10000000000 : ℝ)^35 ≤ (30628766073669/100000000000000 : ℝ)^27 := by
    have hnat : (4014076223 : ℕ)^35*100000000000000^27 ≤ 30628766073669^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4014076223 10000000000 30628766073669 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (301048233/500000000 : ℝ)^35 ≤ (25903112841379/50000000000000 : ℝ)^27 := by
    have hnat : (301048233 : ℕ)^35*50000000000000^27 ≤ 25903112841379^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301048233 500000000 25903112841379 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613967367/10000000000 : ℝ), (-4014076223/10000000000 : ℝ), (301048233/500000000 : ℝ)] ![(17565008225761/100000000000000 : ℝ), (30628766073669/100000000000000 : ℝ), (25903112841379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613967367/10000000000 : ℝ)|^35 ≤ (17565008225761/100000000000000 : ℝ)^27
        have hw : |(2613967367/10000000000 : ℝ)|=(2613967367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4014076223/10000000000 : ℝ)|^35 ≤ (30628766073669/100000000000000 : ℝ)^27
        have hw : |(-4014076223/10000000000 : ℝ)|=(4014076223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(301048233/500000000 : ℝ)|^35 ≤ (25903112841379/50000000000000 : ℝ)^27
        have hw : |(301048233/500000000 : ℝ)|=(301048233/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1225360139/2000000000 : ℝ)*x 0 + (5453449143/10000000000 : ℝ)*x 1 + (-380297463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1225360139/2000000000 : ℝ)^35 ≤ (52989753832213/100000000000000 : ℝ)^27 := by
    have hnat : (1225360139 : ℕ)^35*100000000000000^27 ≤ 52989753832213^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1225360139 2000000000 52989753832213 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453449143/10000000000 : ℝ)^35 ≤ (45566737948607/100000000000000 : ℝ)^27 := by
    have hnat : (5453449143 : ℕ)^35*100000000000000^27 ≤ 45566737948607^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453449143 10000000000 45566737948607 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (380297463/10000000000 : ℝ)^35 ≤ (721754105819/50000000000000 : ℝ)^27 := by
    have hnat : (380297463 : ℕ)^35*50000000000000^27 ≤ 721754105819^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380297463 10000000000 721754105819 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1225360139/2000000000 : ℝ), (5453449143/10000000000 : ℝ), (-380297463/10000000000 : ℝ)] ![(52989753832213/100000000000000 : ℝ), (45566737948607/100000000000000 : ℝ), (721754105819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1225360139/2000000000 : ℝ)|^35 ≤ (52989753832213/100000000000000 : ℝ)^27
        have hw : |(1225360139/2000000000 : ℝ)|=(1225360139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453449143/10000000000 : ℝ)|^35 ≤ (45566737948607/100000000000000 : ℝ)^27
        have hw : |(5453449143/10000000000 : ℝ)|=(5453449143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-380297463/10000000000 : ℝ)|^35 ≤ (721754105819/50000000000000 : ℝ)^27
        have hw : |(-380297463/10000000000 : ℝ)|=(380297463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309057_s2_s2_25 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (744971173/2000000000 : ℝ)*x 0 + (5453449143/10000000000 : ℝ)*x 1 + (3603854163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (744971173/2000000000 : ℝ)^35 ≤ (3474887991923/12500000000000 : ℝ)^27 := by
    have hnat : (744971173 : ℕ)^35*12500000000000^27 ≤ 3474887991923^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744971173 2000000000 3474887991923 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453449143/10000000000 : ℝ)^35 ≤ (45566737948607/100000000000000 : ℝ)^27 := by
    have hnat : (5453449143 : ℕ)^35*100000000000000^27 ≤ 45566737948607^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453449143 10000000000 45566737948607 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3603854163/10000000000 : ℝ)^35 ≤ (1664634881497/6250000000000 : ℝ)^27 := by
    have hnat : (3603854163 : ℕ)^35*6250000000000^27 ≤ 1664634881497^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3603854163 10000000000 1664634881497 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(744971173/2000000000 : ℝ), (5453449143/10000000000 : ℝ), (3603854163/10000000000 : ℝ)] ![(3474887991923/12500000000000 : ℝ), (45566737948607/100000000000000 : ℝ), (1664634881497/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(744971173/2000000000 : ℝ)|^35 ≤ (3474887991923/12500000000000 : ℝ)^27
        have hw : |(744971173/2000000000 : ℝ)|=(744971173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453449143/10000000000 : ℝ)|^35 ≤ (45566737948607/100000000000000 : ℝ)^27
        have hw : |(5453449143/10000000000 : ℝ)|=(5453449143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3603854163/10000000000 : ℝ)|^35 ≤ (1664634881497/6250000000000 : ℝ)^27
        have hw : |(3603854163/10000000000 : ℝ)|=(3603854163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309057_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((78021/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78021/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1557/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1557/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7499/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7499/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27143/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27143/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27133/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27133/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(53/500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(53/500 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (78021/100000 : ℝ) ^ (69/16 : ℝ) ≤ (8572394635729494647/25000000000000000000 : ℝ) := by
    have hpowers : (78021/100000 : ℝ)^69 ≤ (8572394635729494647/25000000000000000000 : ℝ)^16 := by
      have hnat : (78021 : ℕ)^69*25000000000000000000^16 ≤ 8572394635729494647^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78021 100000 8572394635729494647 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78021/100000 : ℝ)) (X := (8572394635729494647/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (33572394635729494647/25000000000000000000 : ℝ) ≤ (10707571192793399/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (33572394635729494647/25000000000000000000 : ℝ)^16 ≤ (10707571192793399/10000000000000000 : ℝ)^69 := by
      have hnat : (33572394635729494647 : ℕ)^16*10000000000000000^69 ≤ 10707571192793399^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33572394635729494647 25000000000000000000 10707571192793399 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10707571192793399/10000000000000000 : ℝ)) (X := (33572394635729494647/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (21072394635729494647/12500000000000000000 : ℝ) ≤ (5643677750571223/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (21072394635729494647/12500000000000000000 : ℝ)^16 ≤ (5643677750571223/5000000000000000 : ℝ)^69 := by
      have hnat : (21072394635729494647 : ℕ)^16*5000000000000000^69 ≤ 5643677750571223^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21072394635729494647 12500000000000000000 5643677750571223 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5643677750571223/5000000000000000 : ℝ)) (X := (21072394635729494647/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(707571192793399/7802100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(193261436116349/2600700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (78021/100000 : ℝ)) (alpha := (707571192793399/7802100000000000 : ℝ)) (beta := (193261436116349/2600700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (78021/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(707571192793399/7802100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(193261436116349/2600700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (1557/2000 : ℝ) ^ (69/16 : ℝ) ≤ (16983327706525120859/50000000000000000000 : ℝ) := by
    have hpowers : (1557/2000 : ℝ)^69 ≤ (16983327706525120859/50000000000000000000 : ℝ)^16 := by
      have hnat : (1557 : ℕ)^69*50000000000000000000^16 ≤ 16983327706525120859^16*2000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1557 2000 16983327706525120859 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1557/2000 : ℝ)) (X := (16983327706525120859/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (66983327706525120859/50000000000000000000 : ℝ) ≤ (5350797530441589/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (66983327706525120859/50000000000000000000 : ℝ)^16 ≤ (5350797530441589/5000000000000000 : ℝ)^69 := by
      have hnat : (66983327706525120859 : ℕ)^16*5000000000000000^69 ≤ 5350797530441589^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66983327706525120859 50000000000000000000 5350797530441589 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5350797530441589/5000000000000000 : ℝ)) (X := (66983327706525120859/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (41983327706525120859/25000000000000000000 : ℝ) ≤ (11277313313100953/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (41983327706525120859/25000000000000000000 : ℝ)^16 ≤ (11277313313100953/10000000000000000 : ℝ)^69 := by
      have hnat : (41983327706525120859 : ℕ)^16*10000000000000000^69 ≤ 11277313313100953^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41983327706525120859 25000000000000000000 11277313313100953 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11277313313100953/10000000000000000 : ℝ)) (X := (41983327706525120859/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(350797530441589/3892500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(23028730088711/311400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (1557/2000 : ℝ)) (alpha := (350797530441589/3892500000000000 : ℝ)) (beta := (23028730088711/311400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1557/2000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(350797530441589/3892500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(23028730088711/311400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (7499/25000 : ℝ) ^ (69/16 : ℝ) ≤ (555693958291295233/100000000000000000000 : ℝ) := by
    have hpowers : (7499/25000 : ℝ)^69 ≤ (555693958291295233/100000000000000000000 : ℝ)^16 := by
      have hnat : (7499 : ℕ)^69*100000000000000000000^16 ≤ 555693958291295233^16*25000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7499 25000 555693958291295233 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7499/25000 : ℝ)) (X := (555693958291295233/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (100555693958291295233/100000000000000000000 : ℝ) ≤ (10012858246324723/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (100555693958291295233/100000000000000000000 : ℝ)^16 ≤ (10012858246324723/10000000000000000 : ℝ)^69 := by
      have hnat : (100555693958291295233 : ℕ)^16*10000000000000000^69 ≤ 10012858246324723^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100555693958291295233 100000000000000000000 10012858246324723 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012858246324723/10000000000000000 : ℝ)) (X := (100555693958291295233/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (50555693958291295233/50000000000000000000 : ℝ) ≤ (10025662027441871/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50555693958291295233/50000000000000000000 : ℝ)^16 ≤ (10025662027441871/10000000000000000 : ℝ)^69 := by
      have hnat : (50555693958291295233 : ℕ)^16*10000000000000000^69 ≤ 10025662027441871^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50555693958291295233 50000000000000000000 10025662027441871 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025662027441871/10000000000000000 : ℝ)) (X := (50555693958291295233/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(12858246324723/2999600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(3200945279287/749900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (7499/25000 : ℝ)) (alpha := (12858246324723/2999600000000000 : ℝ)) (beta := (3200945279287/749900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (7499/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(12858246324723/2999600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(3200945279287/749900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((818609843/2500000000 : ℝ)*X 1 0+(-1636196899/5000000000 : ℝ)*X 1 1+(765686609/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((7191867/12500000 : ℝ)*X 2 0+(5756493871/10000000000 : ℝ)*X 2 1+(-541347703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2316572733/5000000000 : ℝ)*X 0 0+(463556151/1000000000 : ℝ)*X 0 1+(3558511219/10000000000 : ℝ)*X 0 2+(2316572733/5000000000 : ℝ)*X 1 0+(463556151/1000000000 : ℝ)*X 1 1+(3558511219/10000000000 : ℝ)*X 1 2+(2316572733/5000000000 : ℝ)*X 2 0+(463556151/1000000000 : ℝ)*X 2 1+(3558511219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1507271609/5000000000 : ℝ)*X 0 0+(551596111/2000000000 : ℝ)*X 0 1+(210829089/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1506393029/5000000000 : ℝ)*X 1 0+(-172273309/625000000 : ℝ)*X 1 1+(6749147827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2617512257/5000000000 : ℝ)*X 2 0+(6462605589/10000000000 : ℝ)*X 2 1+(-251501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_12 : ((4601450853/10000000000 : ℝ)*X 0 0+(5680462799/10000000000 : ℝ)*X 0 1+(1180801137/5000000000 : ℝ)*X 0 2+(4601450853/10000000000 : ℝ)*X 1 0+(5680462799/10000000000 : ℝ)*X 1 1+(1180801137/5000000000 : ℝ)*X 1 2+(4601450853/10000000000 : ℝ)*X 2 0+(5680462799/10000000000 : ℝ)*X 2 1+(1180801137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((-2760013573/10000000000 : ℝ)*X 0 0+(3012562647/10000000000 : ℝ)*X 0 1+(1686632717/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((2758404817/10000000000 : ℝ)*X 1 0+(-602161337/2000000000 : ℝ)*X 1 1+(3374573891/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3229853509/5000000000 : ℝ)*X 2 0+(52381093/100000000 : ℝ)*X 2 1+(-251479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_18 : ((2838957533/5000000000 : ℝ)*X 0 0+(460416233/1000000000 : ℝ)*X 0 1+(236160219/1000000000 : ℝ)*X 0 2+(2838957533/5000000000 : ℝ)*X 1 0+(460416233/1000000000 : ℝ)*X 1 1+(236160219/1000000000 : ℝ)*X 1 2+(2838957533/5000000000 : ℝ)*X 2 0+(460416233/1000000000 : ℝ)*X 2 1+(236160219/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_18 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((-502198091/1250000000 : ℝ)*X 0 0+(2613333359/10000000000 : ℝ)*X 0 1+(6018347851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_19 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2613967367/10000000000 : ℝ)*X 1 0+(-4014076223/10000000000 : ℝ)*X 1 1+(301048233/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_20 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((1225360139/2000000000 : ℝ)*X 2 0+(5453449143/10000000000 : ℝ)*X 2 1+(-380297463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_21 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((744971173/2000000000 : ℝ)*X 0 0+(5453449143/10000000000 : ℝ)*X 0 1+(3603854163/10000000000 : ℝ)*X 0 2+(744971173/2000000000 : ℝ)*X 1 0+(5453449143/10000000000 : ℝ)*X 1 1+(3603854163/10000000000 : ℝ)*X 1 2+(744971173/2000000000 : ℝ)*X 2 0+(5453449143/10000000000 : ℝ)*X 2 1+(3603854163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309057_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((27143/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27143/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72273605126866011267886099911/5623263881500000000000000000000000 : ℝ) := by norm_num
    linear_combination (12090801/1000000000000 : ℝ)*(base23) + (17849/500000000000 : ℝ)*(base49) + (771217509013/250000000000 : ℝ)*(base59) + (1378327151901/1000000000000 : ℝ)*(base60) + (654811175253/100000000000 : ℝ)*(major_s2_0) + (654811175253/100000000000 : ℝ)*(major_s2_1) + (654811175253/100000000000 : ℝ)*(major_s2_2) + (53282331/1000000000000 : ℝ)*(sp_s2_2) + (224602298627/25000000000 : ℝ)*(sp_s2_7) + (8984297644599/1000000000000 : ℝ)*(sp_s2_8) + (2246058067867/250000000000 : ℝ)*(sp_s2_9) + (1027974520479/250000000000 : ℝ)*(sp_s2_12) + (642811/3125000000 : ℝ)*(sp_s2_13) + (11747167/500000000000 : ℝ)*(sp_s2_25) + (3289537261/800000000 : ℝ)*(f.failure) + (8984297644599/1000000000000 : ℝ)*(f.sum) + (696906823559478181/3891981000000000000000000000000 : ℝ)*base62 + (527688063857/599920000000000000000000 : ℝ)*base64 + (12000377426827/10380000000000000000000000 : ℝ)*base66 + (153631449903919/299960000000000000000000000 : ℝ)*base68 + (130073210938164137/243783116250000000000000000000 : ℝ)*base70 + (421310875451/2709062500000000000000000 : ℝ)*base72 + (101175620612411/129750000000000000000000000 : ℝ)*base74 + (1906464060223/2031796875000000000000000 : ℝ)*base76 + (39071164272584159/89984220000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (67/80000000000000 : ℝ)*base87 + (67/80000000000000 : ℝ)*base89 + (67/80000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27133/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27133/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (456988538883010635842695836509/28116319407500000000000000000000000 : ℝ) := by norm_num
    linear_combination (290339/1000000000000 : ℝ)*(base19) + (173161/10000000000 : ℝ)*(base21) + (3084570026273/1000000000000 : ℝ)*(base59) + (1706973438589/1000000000000 : ℝ)*(base60) + (3273828395207/500000000000 : ℝ)*(major_s2_0) + (3273828395207/500000000000 : ℝ)*(major_s2_1) + (3273828395207/500000000000 : ℝ)*(major_s2_2) + (7653599/250000000000 : ℝ)*(sp_s2_6) + (32787763/125000000000 : ℝ)*(sp_s2_8) + (8983672282621/1000000000000 : ℝ)*(sp_s2_13) + (4491704845089/500000000000 : ℝ)*(sp_s2_14) + (1796711785903/200000000000 : ℝ)*(sp_s2_15) + (164464210639/40000000000 : ℝ)*(sp_s2_18) + (48018503/500000000000 : ℝ)*(sp_s2_21) + (4111635880371/1000000000000 : ℝ)*(f.failure) + (8983672282621/1000000000000 : ℝ)*(f.sum) + (9004121938372134617/58379715000000000000000000000000 : ℝ)*base62 + (503991011577/732324218750000000000000 : ℝ)*base64 + (45100876052963/155700000000000000000000000 : ℝ)*base66 + (505768111175781/1499800000000000000000000000 : ℝ)*base68 + (7543528878444260131/14626986975000000000000000000000 : ℝ)*base70 + (440874451451987/1300350000000000000000000000 : ℝ)*base72 + (689153891258827/1946250000000000000000000000 : ℝ)*base74 + (763185764163547/3901050000000000000000000000 : ℝ)*base76 + (109710210782033983/1349763300000000000000000000000 : ℝ)*base78 + (40637/100000000000000000 : ℝ)*base87 + (40637/100000000000000000 : ℝ)*base89 + (40637/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(53/500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(53/500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (492444319327287577929724233371/168697916445000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75957866027/500000000000 : ℝ)*(base5) + (324229/500000000000 : ℝ)*(base40) + (597741/1000000000000 : ℝ)*(base50) + (772499568577/1000000000000 : ℝ)*(base59) + (2340041167739/1000000000000 : ℝ)*(major_s2_0) + (2340041167739/1000000000000 : ℝ)*(major_s2_1) + (2340041167739/1000000000000 : ℝ)*(major_s2_2) + (19701/12500000000 : ℝ)*(sp_s2_1) + (17893033/1000000000000 : ℝ)*(sp_s2_9) + (6992141/250000000000 : ℝ)*(sp_s2_15) + (3210640074547/1000000000000 : ℝ)*(sp_s2_19) + (3210638498467/1000000000000 : ℝ)*(sp_s2_20) + (672501989001/200000000000 : ℝ)*(sp_s2_21) + (329381388961/250000000000 : ℝ)*(sp_s2_25) + (734720643949/500000000000 : ℝ)*(f.failure) + (3210640074547/1000000000000 : ℝ)*(f.sum) + (13647674218289213191/116759430000000000000000000000000 : ℝ)*base63 + (63272224353557/749900000000000000000000000 : ℝ)*base65 + (30179725634231/311400000000000000000000000 : ℝ)*base66 + (423591386517063/2999600000000000000000000000 : ℝ)*base69 + (4743245028718605251/14626986975000000000000000000000 : ℝ)*base70 + (859040757786271/2600700000000000000000000000 : ℝ)*base73 + (168097095074021/3892500000000000000000000000 : ℝ)*base75 + (3162261697464379/7802100000000000000000000000 : ℝ)*base76 + (699264585502348261/2699526600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (3597/50000000000000000 : ℝ)*base86 + (3597/50000000000000000 : ℝ)*base88 + (3597/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((78021/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(78021/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1557/2000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1557/2000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(7499/25000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(7499/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((27143/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(27143/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27133/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27133/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(53/500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(53/500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309057_s2 p hpa hpb X hX hprev1

#print axioms solution
