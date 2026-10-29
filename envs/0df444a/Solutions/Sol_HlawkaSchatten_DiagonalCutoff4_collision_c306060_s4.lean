-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306060_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:58:10.431052+00:00
-- url     : https://prove2.me/submissions/317c18a9-2a47-4292-bcf1-d355e6585814

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
theorem collision_support_c306060_s4_s4_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2494065087/10000000000 : ℝ)*x 0 + (401006237/1000000000 : ℝ)*x 1 + (-3107356321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2494065087/10000000000 : ℝ)^135 ≤ (8100453466377/50000000000000 : ℝ)^103 := by
    have hnat : (2494065087 : ℕ)^135*50000000000000^103 ≤ 8100453466377^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2494065087 10000000000 8100453466377 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401006237/1000000000 : ℝ)^135 ≤ (30189663603019/100000000000000 : ℝ)^103 := by
    have hnat : (401006237 : ℕ)^135*100000000000000^103 ≤ 30189663603019^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401006237 1000000000 30189663603019 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3107356321/5000000000 : ℝ)^135 ≤ (53609429448671/100000000000000 : ℝ)^103 := by
    have hnat : (3107356321 : ℕ)^135*100000000000000^103 ≤ 53609429448671^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107356321 5000000000 53609429448671 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2494065087/10000000000 : ℝ), (401006237/1000000000 : ℝ), (-3107356321/5000000000 : ℝ)] ![(8100453466377/50000000000000 : ℝ), (30189663603019/100000000000000 : ℝ), (53609429448671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2494065087/10000000000 : ℝ)|^135 ≤ (8100453466377/50000000000000 : ℝ)^103
        have hw : |(-2494065087/10000000000 : ℝ)|=(2494065087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401006237/1000000000 : ℝ)|^135 ≤ (30189663603019/100000000000000 : ℝ)^103
        have hw : |(401006237/1000000000 : ℝ)|=(401006237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3107356321/5000000000 : ℝ)|^135 ≤ (53609429448671/100000000000000 : ℝ)^103
        have hw : |(-3107356321/5000000000 : ℝ)|=(3107356321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2240387821/5000000000 : ℝ)*x 0 + (-1515892509/5000000000 : ℝ)*x 1 + (-5359859731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2240387821/5000000000 : ℝ)^135 ≤ (34916905376767/100000000000000 : ℝ)^103 := by
    have hnat : (2240387821 : ℕ)^135*100000000000000^103 ≤ 34916905376767^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240387821 5000000000 34916905376767 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1515892509/5000000000 : ℝ)^135 ≤ (10462673378177/50000000000000 : ℝ)^103 := by
    have hnat : (1515892509 : ℕ)^135*50000000000000^103 ≤ 10462673378177^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1515892509 5000000000 10462673378177 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5359859731/10000000000 : ℝ)^135 ≤ (5519718481559/12500000000000 : ℝ)^103 := by
    have hnat : (5359859731 : ℕ)^135*12500000000000^103 ≤ 5519718481559^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359859731 10000000000 5519718481559 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2240387821/5000000000 : ℝ), (-1515892509/5000000000 : ℝ), (-5359859731/10000000000 : ℝ)] ![(34916905376767/100000000000000 : ℝ), (10462673378177/50000000000000 : ℝ), (5519718481559/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2240387821/5000000000 : ℝ)|^135 ≤ (34916905376767/100000000000000 : ℝ)^103
        have hw : |(2240387821/5000000000 : ℝ)|=(2240387821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1515892509/5000000000 : ℝ)|^135 ≤ (10462673378177/50000000000000 : ℝ)^103
        have hw : |(-1515892509/5000000000 : ℝ)|=(1515892509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5359859731/10000000000 : ℝ)|^135 ≤ (5519718481559/12500000000000 : ℝ)^103
        have hw : |(-5359859731/10000000000 : ℝ)|=(5359859731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1184908777/2500000000 : ℝ)*x 0 + (175431997/312500000 : ℝ)*x 1 + (482160477/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1184908777/2500000000 : ℝ)^135 ≤ (37584213081417/100000000000000 : ℝ)^103 := by
    have hnat : (1184908777 : ℕ)^135*100000000000000^103 ≤ 37584213081417^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1184908777 2500000000 37584213081417 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175431997/312500000 : ℝ)^135 ≤ (1876802587857/4000000000000 : ℝ)^103 := by
    have hnat : (175431997 : ℕ)^135*4000000000000^103 ≤ 1876802587857^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175431997 312500000 1876802587857 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482160477/2000000000 : ℝ)^135 ≤ (15495722206389/100000000000000 : ℝ)^103 := by
    have hnat : (482160477 : ℕ)^135*100000000000000^103 ≤ 15495722206389^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482160477 2000000000 15495722206389 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1184908777/2500000000 : ℝ), (175431997/312500000 : ℝ), (482160477/2000000000 : ℝ)] ![(37584213081417/100000000000000 : ℝ), (1876802587857/4000000000000 : ℝ), (15495722206389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1184908777/2500000000 : ℝ)|^135 ≤ (37584213081417/100000000000000 : ℝ)^103
        have hw : |(1184908777/2500000000 : ℝ)|=(1184908777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175431997/312500000 : ℝ)|^135 ≤ (1876802587857/4000000000000 : ℝ)^103
        have hw : |(175431997/312500000 : ℝ)|=(175431997/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(482160477/2000000000 : ℝ)|^135 ≤ (15495722206389/100000000000000 : ℝ)^103
        have hw : |(482160477/2000000000 : ℝ)|=(482160477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6409464157/10000000000 : ℝ)*x 0 + (4446826557/10000000000 : ℝ)*x 1 + (-209256007/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6409464157/10000000000 : ℝ)^135 ≤ (1744436611509/3125000000000 : ℝ)^103 := by
    have hnat : (6409464157 : ℕ)^135*3125000000000^103 ≤ 1744436611509^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6409464157 10000000000 1744436611509 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4446826557/10000000000 : ℝ)^135 ≤ (17285285808583/50000000000000 : ℝ)^103 := by
    have hnat : (4446826557 : ℕ)^135*50000000000000^103 ≤ 17285285808583^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4446826557 10000000000 17285285808583 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209256007/1250000000 : ℝ)^135 ≤ (1200932099103/12500000000000 : ℝ)^103 := by
    have hnat : (209256007 : ℕ)^135*12500000000000^103 ≤ 1200932099103^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209256007 1250000000 1200932099103 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6409464157/10000000000 : ℝ), (4446826557/10000000000 : ℝ), (-209256007/1250000000 : ℝ)] ![(1744436611509/3125000000000 : ℝ), (17285285808583/50000000000000 : ℝ), (1200932099103/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6409464157/10000000000 : ℝ)|^135 ≤ (1744436611509/3125000000000 : ℝ)^103
        have hw : |(6409464157/10000000000 : ℝ)|=(6409464157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4446826557/10000000000 : ℝ)|^135 ≤ (17285285808583/50000000000000 : ℝ)^103
        have hw : |(4446826557/10000000000 : ℝ)|=(4446826557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209256007/1250000000 : ℝ)|^135 ≤ (1200932099103/12500000000000 : ℝ)^103
        have hw : |(-209256007/1250000000 : ℝ)|=(209256007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1230995661/5000000000 : ℝ)*x 0 + (3843231471/10000000000 : ℝ)*x 1 + (-6382765723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1230995661/5000000000 : ℝ)^135 ≤ (1592838152321/10000000000000 : ℝ)^103 := by
    have hnat : (1230995661 : ℕ)^135*10000000000000^103 ≤ 1592838152321^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230995661 5000000000 1592838152321 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3843231471/10000000000 : ℝ)^135 ≤ (35692768731/125000000000 : ℝ)^103 := by
    have hnat : (3843231471 : ℕ)^135*125000000000^103 ≤ 35692768731^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843231471 10000000000 35692768731 125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6382765723/10000000000 : ℝ)^135 ≤ (1387935086889/2500000000000 : ℝ)^103 := by
    have hnat : (6382765723 : ℕ)^135*2500000000000^103 ≤ 1387935086889^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6382765723 10000000000 1387935086889 2500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1230995661/5000000000 : ℝ), (3843231471/10000000000 : ℝ), (-6382765723/10000000000 : ℝ)] ![(1592838152321/10000000000000 : ℝ), (35692768731/125000000000 : ℝ), (1387935086889/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1230995661/5000000000 : ℝ)|^135 ≤ (1592838152321/10000000000000 : ℝ)^103
        have hw : |(-1230995661/5000000000 : ℝ)|=(1230995661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3843231471/10000000000 : ℝ)|^135 ≤ (35692768731/125000000000 : ℝ)^103
        have hw : |(3843231471/10000000000 : ℝ)|=(3843231471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6382765723/10000000000 : ℝ)|^135 ≤ (1387935086889/2500000000000 : ℝ)^103
        have hw : |(-6382765723/10000000000 : ℝ)|=(6382765723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4391495283/10000000000 : ℝ)*x 0 + (-1364720953/5000000000 : ℝ)*x 1 + (-1422549811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4391495283/10000000000 : ℝ)^135 ≤ (17003933215361/50000000000000 : ℝ)^103 := by
    have hnat : (4391495283 : ℕ)^135*50000000000000^103 ≤ 17003933215361^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391495283 10000000000 17003933215361 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364720953/5000000000 : ℝ)^135 ≤ (569801412011/3125000000000 : ℝ)^103 := by
    have hnat : (1364720953 : ℕ)^135*3125000000000^103 ≤ 569801412011^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364720953 5000000000 569801412011 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1422549811/2500000000 : ℝ)^135 ≤ (47758488365679/100000000000000 : ℝ)^103 := by
    have hnat : (1422549811 : ℕ)^135*100000000000000^103 ≤ 47758488365679^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422549811 2500000000 47758488365679 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4391495283/10000000000 : ℝ), (-1364720953/5000000000 : ℝ), (-1422549811/2500000000 : ℝ)] ![(17003933215361/50000000000000 : ℝ), (569801412011/3125000000000 : ℝ), (47758488365679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4391495283/10000000000 : ℝ)|^135 ≤ (17003933215361/50000000000000 : ℝ)^103
        have hw : |(4391495283/10000000000 : ℝ)|=(4391495283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1364720953/5000000000 : ℝ)|^135 ≤ (569801412011/3125000000000 : ℝ)^103
        have hw : |(-1364720953/5000000000 : ℝ)|=(1364720953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1422549811/2500000000 : ℝ)|^135 ≤ (47758488365679/100000000000000 : ℝ)^103
        have hw : |(-1422549811/2500000000 : ℝ)|=(1422549811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1162636537/2500000000 : ℝ)*x 0 + (2969719779/5000000000 : ℝ)*x 1 + (8344833/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1162636537/2500000000 : ℝ)^135 ≤ (36660992416963/100000000000000 : ℝ)^103 := by
    have hnat : (1162636537 : ℕ)^135*100000000000000^103 ≤ 36660992416963^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162636537 2500000000 36660992416963 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2969719779/5000000000 : ℝ)^135 ≤ (10103754666907/20000000000000 : ℝ)^103 := by
    have hnat : (2969719779 : ℕ)^135*20000000000000^103 ≤ 10103754666907^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2969719779 5000000000 10103754666907 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8344833/40000000 : ℝ)^135 ≤ (1602529279549/12500000000000 : ℝ)^103 := by
    have hnat : (8344833 : ℕ)^135*12500000000000^103 ≤ 1602529279549^103*40000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8344833 40000000 1602529279549 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1162636537/2500000000 : ℝ), (2969719779/5000000000 : ℝ), (8344833/40000000 : ℝ)] ![(36660992416963/100000000000000 : ℝ), (10103754666907/20000000000000 : ℝ), (1602529279549/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1162636537/2500000000 : ℝ)|^135 ≤ (36660992416963/100000000000000 : ℝ)^103
        have hw : |(1162636537/2500000000 : ℝ)|=(1162636537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2969719779/5000000000 : ℝ)|^135 ≤ (10103754666907/20000000000000 : ℝ)^103
        have hw : |(2969719779/5000000000 : ℝ)|=(2969719779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8344833/40000000 : ℝ)|^135 ≤ (1602529279549/12500000000000 : ℝ)^103
        have hw : |(8344833/40000000 : ℝ)|=(8344833/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6338788877/10000000000 : ℝ)*x 0 + (595682519/1250000000 : ℝ)*x 1 + (-1333447057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6338788877/10000000000 : ℝ)^135 ≤ (55016591091443/100000000000000 : ℝ)^103 := by
    have hnat : (6338788877 : ℕ)^135*100000000000000^103 ≤ 55016591091443^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6338788877 10000000000 55016591091443 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595682519/1250000000 : ℝ)^135 ≤ (37852849657281/100000000000000 : ℝ)^103 := by
    have hnat : (595682519 : ℕ)^135*100000000000000^103 ≤ 37852849657281^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595682519 1250000000 37852849657281 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1333447057/10000000000 : ℝ)^135 ≤ (71305592263/1000000000000 : ℝ)^103 := by
    have hnat : (1333447057 : ℕ)^135*1000000000000^103 ≤ 71305592263^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1333447057 10000000000 71305592263 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6338788877/10000000000 : ℝ), (595682519/1250000000 : ℝ), (-1333447057/10000000000 : ℝ)] ![(55016591091443/100000000000000 : ℝ), (37852849657281/100000000000000 : ℝ), (71305592263/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6338788877/10000000000 : ℝ)|^135 ≤ (55016591091443/100000000000000 : ℝ)^103
        have hw : |(6338788877/10000000000 : ℝ)|=(6338788877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(595682519/1250000000 : ℝ)|^135 ≤ (37852849657281/100000000000000 : ℝ)^103
        have hw : |(595682519/1250000000 : ℝ)|=(595682519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1333447057/10000000000 : ℝ)|^135 ≤ (71305592263/1000000000000 : ℝ)^103
        have hw : |(-1333447057/10000000000 : ℝ)|=(1333447057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208588187/10000000000 : ℝ)*x 0 + (404391351/1000000000 : ℝ)*x 1 + (-6395364439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208588187/10000000000 : ℝ)^135 ≤ (13814798940521/100000000000000 : ℝ)^103 := by
    have hnat : (2208588187 : ℕ)^135*100000000000000^103 ≤ 13814798940521^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208588187 10000000000 13814798940521 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404391351/1000000000 : ℝ)^135 ≤ (1526206211937/5000000000000 : ℝ)^103 := by
    have hnat : (404391351 : ℕ)^135*5000000000000^103 ≤ 1526206211937^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404391351 1000000000 1526206211937 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6395364439/10000000000 : ℝ)^135 ≤ (27830538402249/50000000000000 : ℝ)^103 := by
    have hnat : (6395364439 : ℕ)^135*50000000000000^103 ≤ 27830538402249^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6395364439 10000000000 27830538402249 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208588187/10000000000 : ℝ), (404391351/1000000000 : ℝ), (-6395364439/10000000000 : ℝ)] ![(13814798940521/100000000000000 : ℝ), (1526206211937/5000000000000 : ℝ), (27830538402249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208588187/10000000000 : ℝ)|^135 ≤ (13814798940521/100000000000000 : ℝ)^103
        have hw : |(-2208588187/10000000000 : ℝ)|=(2208588187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404391351/1000000000 : ℝ)|^135 ≤ (1526206211937/5000000000000 : ℝ)^103
        have hw : |(404391351/1000000000 : ℝ)|=(404391351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6395364439/10000000000 : ℝ)|^135 ≤ (27830538402249/50000000000000 : ℝ)^103
        have hw : |(-6395364439/10000000000 : ℝ)|=(6395364439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2152832363/5000000000 : ℝ)*x 0 + (-2865540537/10000000000 : ℝ)*x 1 + (-2829985259/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2152832363/5000000000 : ℝ)^135 ≤ (6627869657321/20000000000000 : ℝ)^103 := by
    have hnat : (2152832363 : ℕ)^135*20000000000000^103 ≤ 6627869657321^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152832363 5000000000 6627869657321 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2865540537/10000000000 : ℝ)^135 ≤ (4858606300073/25000000000000 : ℝ)^103 := by
    have hnat : (2865540537 : ℕ)^135*25000000000000^103 ≤ 4858606300073^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2865540537 10000000000 4858606300073 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829985259/5000000000 : ℝ)^135 ≤ (9485245298867/20000000000000 : ℝ)^103 := by
    have hnat : (2829985259 : ℕ)^135*20000000000000^103 ≤ 9485245298867^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829985259 5000000000 9485245298867 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2152832363/5000000000 : ℝ), (-2865540537/10000000000 : ℝ), (-2829985259/5000000000 : ℝ)] ![(6627869657321/20000000000000 : ℝ), (4858606300073/25000000000000 : ℝ), (9485245298867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2152832363/5000000000 : ℝ)|^135 ≤ (6627869657321/20000000000000 : ℝ)^103
        have hw : |(2152832363/5000000000 : ℝ)|=(2152832363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2865540537/10000000000 : ℝ)|^135 ≤ (4858606300073/25000000000000 : ℝ)^103
        have hw : |(-2865540537/10000000000 : ℝ)|=(2865540537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2829985259/5000000000 : ℝ)|^135 ≤ (9485245298867/20000000000000 : ℝ)^103
        have hw : |(-2829985259/5000000000 : ℝ)|=(2829985259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5030462969/10000000000 : ℝ)*x 0 + (5557172053/10000000000 : ℝ)*x 1 + (2116435437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5030462969/10000000000 : ℝ)^135 ≤ (20317657566189/50000000000000 : ℝ)^103 := by
    have hnat : (5030462969 : ℕ)^135*50000000000000^103 ≤ 20317657566189^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030462969 10000000000 20317657566189 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5557172053/10000000000 : ℝ)^135 ≤ (2893777605291/6250000000000 : ℝ)^103 := by
    have hnat : (5557172053 : ℕ)^135*6250000000000^103 ≤ 2893777605291^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5557172053 10000000000 2893777605291 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116435437/10000000000 : ℝ)^135 ≤ (6532121586143/50000000000000 : ℝ)^103 := by
    have hnat : (2116435437 : ℕ)^135*50000000000000^103 ≤ 6532121586143^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116435437 10000000000 6532121586143 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5030462969/10000000000 : ℝ), (5557172053/10000000000 : ℝ), (2116435437/10000000000 : ℝ)] ![(20317657566189/50000000000000 : ℝ), (2893777605291/6250000000000 : ℝ), (6532121586143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5030462969/10000000000 : ℝ)|^135 ≤ (20317657566189/50000000000000 : ℝ)^103
        have hw : |(5030462969/10000000000 : ℝ)|=(5030462969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5557172053/10000000000 : ℝ)|^135 ≤ (2893777605291/6250000000000 : ℝ)^103
        have hw : |(5557172053/10000000000 : ℝ)|=(5557172053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116435437/10000000000 : ℝ)|^135 ≤ (6532121586143/50000000000000 : ℝ)^103
        have hw : |(2116435437/10000000000 : ℝ)|=(2116435437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3390625231/5000000000 : ℝ)*x 0 + (33490629/78125000 : ℝ)*x 1 + (-163399339/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3390625231/5000000000 : ℝ)^135 ≤ (6010369537159/10000000000000 : ℝ)^103 := by
    have hnat : (3390625231 : ℕ)^135*10000000000000^103 ≤ 6010369537159^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3390625231 5000000000 6010369537159 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33490629/78125000 : ℝ)^135 ≤ (8237294458501/25000000000000 : ℝ)^103 := by
    have hnat : (33490629 : ℕ)^135*25000000000000^103 ≤ 8237294458501^103*78125000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33490629 78125000 8237294458501 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163399339/1250000000 : ℝ)^135 ≤ (3473563389361/50000000000000 : ℝ)^103 := by
    have hnat : (163399339 : ℕ)^135*50000000000000^103 ≤ 3473563389361^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163399339 1250000000 3473563389361 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3390625231/5000000000 : ℝ), (33490629/78125000 : ℝ), (-163399339/1250000000 : ℝ)] ![(6010369537159/10000000000000 : ℝ), (8237294458501/25000000000000 : ℝ), (3473563389361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3390625231/5000000000 : ℝ)|^135 ≤ (6010369537159/10000000000000 : ℝ)^103
        have hw : |(3390625231/5000000000 : ℝ)|=(3390625231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33490629/78125000 : ℝ)|^135 ≤ (8237294458501/25000000000000 : ℝ)^103
        have hw : |(33490629/78125000 : ℝ)|=(33490629/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-163399339/1250000000 : ℝ)|^135 ≤ (3473563389361/50000000000000 : ℝ)^103
        have hw : |(-163399339/1250000000 : ℝ)|=(163399339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-42555587/200000000 : ℝ)*x 0 + (1066125433/2500000000 : ℝ)*x 1 + (-3129874151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42555587/200000000 : ℝ)^135 ≤ (1644512188601/12500000000000 : ℝ)^103 := by
    have hnat : (42555587 : ℕ)^135*12500000000000^103 ≤ 1644512188601^103*200000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42555587 200000000 1644512188601 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066125433/2500000000 : ℝ)^135 ≤ (4090589825617/12500000000000 : ℝ)^103 := by
    have hnat : (1066125433 : ℕ)^135*12500000000000^103 ≤ 4090589825617^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066125433 2500000000 4090589825617 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3129874151/5000000000 : ℝ)^135 ≤ (1691224496001/3125000000000 : ℝ)^103 := by
    have hnat : (3129874151 : ℕ)^135*3125000000000^103 ≤ 1691224496001^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3129874151 5000000000 1691224496001 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42555587/200000000 : ℝ), (1066125433/2500000000 : ℝ), (-3129874151/5000000000 : ℝ)] ![(1644512188601/12500000000000 : ℝ), (4090589825617/12500000000000 : ℝ), (1691224496001/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42555587/200000000 : ℝ)|^135 ≤ (1644512188601/12500000000000 : ℝ)^103
        have hw : |(-42555587/200000000 : ℝ)|=(42555587/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1066125433/2500000000 : ℝ)|^135 ≤ (4090589825617/12500000000000 : ℝ)^103
        have hw : |(1066125433/2500000000 : ℝ)|=(1066125433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3129874151/5000000000 : ℝ)|^135 ≤ (1691224496001/3125000000000 : ℝ)^103
        have hw : |(-3129874151/5000000000 : ℝ)|=(3129874151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4852218519/10000000000 : ℝ)*x 0 + (-556510451/2000000000 : ℝ)*x 1 + (-5209503861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4852218519/10000000000 : ℝ)^135 ≤ (4844828790077/12500000000000 : ℝ)^103 := by
    have hnat : (4852218519 : ℕ)^135*12500000000000^103 ≤ 4844828790077^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4852218519 10000000000 4844828790077 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556510451/2000000000 : ℝ)^135 ≤ (9350034265251/50000000000000 : ℝ)^103 := by
    have hnat : (556510451 : ℕ)^135*50000000000000^103 ≤ 9350034265251^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556510451 2000000000 9350034265251 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5209503861/10000000000 : ℝ)^135 ≤ (425413011257/1000000000000 : ℝ)^103 := by
    have hnat : (5209503861 : ℕ)^135*1000000000000^103 ≤ 425413011257^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5209503861 10000000000 425413011257 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4852218519/10000000000 : ℝ), (-556510451/2000000000 : ℝ), (-5209503861/10000000000 : ℝ)] ![(4844828790077/12500000000000 : ℝ), (9350034265251/50000000000000 : ℝ), (425413011257/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4852218519/10000000000 : ℝ)|^135 ≤ (4844828790077/12500000000000 : ℝ)^103
        have hw : |(4852218519/10000000000 : ℝ)|=(4852218519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556510451/2000000000 : ℝ)|^135 ≤ (9350034265251/50000000000000 : ℝ)^103
        have hw : |(-556510451/2000000000 : ℝ)|=(556510451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5209503861/10000000000 : ℝ)|^135 ≤ (425413011257/1000000000000 : ℝ)^103
        have hw : |(-5209503861/10000000000 : ℝ)|=(5209503861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2263997273/5000000000 : ℝ)*x 0 + (5765683911/10000000000 : ℝ)*x 1 + (308943297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2263997273/5000000000 : ℝ)^135 ≤ (35399968223013/100000000000000 : ℝ)^103 := by
    have hnat : (2263997273 : ℕ)^135*100000000000000^103 ≤ 35399968223013^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263997273 5000000000 35399968223013 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5765683911/10000000000 : ℝ)^135 ≤ (1518455538259/3125000000000 : ℝ)^103 := by
    have hnat : (5765683911 : ℕ)^135*3125000000000^103 ≤ 1518455538259^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5765683911 10000000000 1518455538259 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (308943297/1250000000 : ℝ)^135 ≤ (8004727270213/50000000000000 : ℝ)^103 := by
    have hnat : (308943297 : ℕ)^135*50000000000000^103 ≤ 8004727270213^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      308943297 1250000000 8004727270213 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2263997273/5000000000 : ℝ), (5765683911/10000000000 : ℝ), (308943297/1250000000 : ℝ)] ![(35399968223013/100000000000000 : ℝ), (1518455538259/3125000000000 : ℝ), (8004727270213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2263997273/5000000000 : ℝ)|^135 ≤ (35399968223013/100000000000000 : ℝ)^103
        have hw : |(2263997273/5000000000 : ℝ)|=(2263997273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5765683911/10000000000 : ℝ)|^135 ≤ (1518455538259/3125000000000 : ℝ)^103
        have hw : |(5765683911/10000000000 : ℝ)|=(5765683911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(308943297/1250000000 : ℝ)|^135 ≤ (8004727270213/50000000000000 : ℝ)^103
        have hw : |(308943297/1250000000 : ℝ)|=(308943297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306060_s4_s4_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1371553229/2000000000 : ℝ)*x 0 + (827808357/2000000000 : ℝ)*x 1 + (-1391083777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1371553229/2000000000 : ℝ)^135 ≤ (60994119625743/100000000000000 : ℝ)^103 := by
    have hnat : (1371553229 : ℕ)^135*100000000000000^103 ≤ 60994119625743^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371553229 2000000000 60994119625743 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (827808357/2000000000 : ℝ)^135 ≤ (393358379157/1250000000000 : ℝ)^103 := by
    have hnat : (827808357 : ℕ)^135*1250000000000^103 ≤ 393358379157^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827808357 2000000000 393358379157 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1391083777/10000000000 : ℝ)^135 ≤ (7537210029827/100000000000000 : ℝ)^103 := by
    have hnat : (1391083777 : ℕ)^135*100000000000000^103 ≤ 7537210029827^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391083777 10000000000 7537210029827 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1371553229/2000000000 : ℝ), (827808357/2000000000 : ℝ), (-1391083777/10000000000 : ℝ)] ![(60994119625743/100000000000000 : ℝ), (393358379157/1250000000000 : ℝ), (7537210029827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1371553229/2000000000 : ℝ)|^135 ≤ (60994119625743/100000000000000 : ℝ)^103
        have hw : |(1371553229/2000000000 : ℝ)|=(1371553229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(827808357/2000000000 : ℝ)|^135 ≤ (393358379157/1250000000000 : ℝ)^103
        have hw : |(827808357/2000000000 : ℝ)|=(827808357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1391083777/10000000000 : ℝ)|^135 ≤ (7537210029827/100000000000000 : ℝ)^103
        have hw : |(-1391083777/10000000000 : ℝ)|=(1391083777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306060_s4 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((6119/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6119/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8109/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8109/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47359/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-47359/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26669/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26669/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5909/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5909/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16349/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16349/100000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (6119/10000 : ℝ) ^ (67/16 : ℝ) ≤ (1278569669401192791/10000000000000000000 : ℝ) := by
    have hpowers : (6119/10000 : ℝ)^67 ≤ (1278569669401192791/10000000000000000000 : ℝ)^16 := by
      have hnat : (6119 : ℕ)^67*10000000000000000000^16 ≤ 1278569669401192791^16*10000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6119 10000 1278569669401192791 10000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6119/10000 : ℝ)) (X := (1278569669401192791/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (11278569669401192791/10000000000000000000 : ℝ) ≤ (411659900597707/400000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (11278569669401192791/10000000000000000000 : ℝ)^16 ≤ (411659900597707/400000000000000 : ℝ)^67 := by
      have hnat : (11278569669401192791 : ℕ)^16*400000000000000^67 ≤ 411659900597707^67*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11278569669401192791 10000000000000000000 411659900597707 400000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (411659900597707/400000000000000 : ℝ)) (X := (11278569669401192791/10000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (6278569669401192791/5000000000000000000 : ℝ) ≤ (2111765489771283/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (6278569669401192791/5000000000000000000 : ℝ)^16 ≤ (2111765489771283/2000000000000000 : ℝ)^67 := by
      have hnat : (6278569669401192791 : ℕ)^16*2000000000000000^67 ≤ 2111765489771283^67*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6278569669401192791 5000000000000000000 2111765489771283 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2111765489771283/2000000000000000 : ℝ)) (X := (6278569669401192791/5000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(11659900597707/244760000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(13366496695687/305950000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (6119/10000 : ℝ)) (alpha := (11659900597707/244760000000000 : ℝ)) (beta := (13366496695687/305950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6119/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(11659900597707/244760000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(13366496695687/305950000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (8109/12500 : ℝ) ^ (67/16 : ℝ) ≤ (4082534840438542379/25000000000000000000 : ℝ) := by
    have hpowers : (8109/12500 : ℝ)^67 ≤ (4082534840438542379/25000000000000000000 : ℝ)^16 := by
      have hnat : (8109 : ℕ)^67*25000000000000000000^16 ≤ 4082534840438542379^16*12500^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8109 12500 4082534840438542379 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8109/12500 : ℝ)) (X := (4082534840438542379/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (29082534840438542379/25000000000000000000 : ℝ) ≤ (10367826027341333/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (29082534840438542379/25000000000000000000 : ℝ)^16 ≤ (10367826027341333/10000000000000000 : ℝ)^67 := by
      have hnat : (29082534840438542379 : ℕ)^16*10000000000000000^67 ≤ 10367826027341333^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29082534840438542379 25000000000000000000 10367826027341333 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10367826027341333/10000000000000000 : ℝ)) (X := (29082534840438542379/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (16582534840438542379/12500000000000000000 : ℝ) ≤ (5349106753820003/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (16582534840438542379/12500000000000000000 : ℝ)^16 ≤ (5349106753820003/5000000000000000 : ℝ)^67 := by
      have hnat : (16582534840438542379 : ℕ)^16*5000000000000000^67 ≤ 5349106753820003^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16582534840438542379 12500000000000000000 5349106753820003 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5349106753820003/5000000000000000 : ℝ)) (X := (16582534840438542379/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(367826027341333/6487200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(330387480298673/6487200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (8109/12500 : ℝ)) (alpha := (367826027341333/6487200000000000 : ℝ)) (beta := (330387480298673/6487200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8109/12500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(367826027341333/6487200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(330387480298673/6487200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (47359/100000 : ℝ) ^ (67/16 : ℝ) ≤ (4372683737876505871/100000000000000000000 : ℝ) := by
    have hpowers : (47359/100000 : ℝ)^67 ≤ (4372683737876505871/100000000000000000000 : ℝ)^16 := by
      have hnat : (47359 : ℕ)^67*100000000000000000000^16 ≤ 4372683737876505871^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47359 100000 4372683737876505871 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47359/100000 : ℝ)) (X := (4372683737876505871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (104372683737876505871/100000000000000000000 : ℝ) ≤ (631420486108147/625000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (104372683737876505871/100000000000000000000 : ℝ)^16 ≤ (631420486108147/625000000000000 : ℝ)^67 := by
      have hnat : (104372683737876505871 : ℕ)^16*625000000000000^67 ≤ 631420486108147^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104372683737876505871 100000000000000000000 631420486108147 625000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631420486108147/625000000000000 : ℝ)) (X := (104372683737876505871/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (54372683737876505871/50000000000000000000 : ℝ) ≤ (2040445990721363/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (54372683737876505871/50000000000000000000 : ℝ)^16 ≤ (2040445990721363/2000000000000000 : ℝ)^67 := by
      have hnat : (54372683737876505871 : ℕ)^16*2000000000000000^67 ≤ 2040445990721363^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54372683737876505871 50000000000000000000 2040445990721363 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2040445990721363/2000000000000000 : ℝ)) (X := (54372683737876505871/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(6420486108147/295993750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(99502175876463/4735900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (47359/100000 : ℝ)) (alpha := (6420486108147/295993750000000 : ℝ)) (beta := (99502175876463/4735900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (47359/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(6420486108147/295993750000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(99502175876463/4735900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-2494065087/10000000000 : ℝ)*X 0 0+(401006237/1000000000 : ℝ)*X 0 1+(-3107356321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((2240387821/5000000000 : ℝ)*X 1 0+(-1515892509/5000000000 : ℝ)*X 1 1+(-5359859731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((1184908777/2500000000 : ℝ)*X 2 0+(175431997/312500000 : ℝ)*X 2 1+(482160477/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((6409464157/10000000000 : ℝ)*X 0 0+(4446826557/10000000000 : ℝ)*X 0 1+(-209256007/1250000000 : ℝ)*X 0 2+(6409464157/10000000000 : ℝ)*X 1 0+(4446826557/10000000000 : ℝ)*X 1 1+(-209256007/1250000000 : ℝ)*X 1 2+(6409464157/10000000000 : ℝ)*X 2 0+(4446826557/10000000000 : ℝ)*X 2 1+(-209256007/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-1230995661/5000000000 : ℝ)*X 0 0+(3843231471/10000000000 : ℝ)*X 0 1+(-6382765723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((4391495283/10000000000 : ℝ)*X 1 0+(-1364720953/5000000000 : ℝ)*X 1 1+(-1422549811/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1162636537/2500000000 : ℝ)*X 2 0+(2969719779/5000000000 : ℝ)*X 2 1+(8344833/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((6338788877/10000000000 : ℝ)*X 0 0+(595682519/1250000000 : ℝ)*X 0 1+(-1333447057/10000000000 : ℝ)*X 0 2+(6338788877/10000000000 : ℝ)*X 1 0+(595682519/1250000000 : ℝ)*X 1 1+(-1333447057/10000000000 : ℝ)*X 1 2+(6338788877/10000000000 : ℝ)*X 2 0+(595682519/1250000000 : ℝ)*X 2 1+(-1333447057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-2208588187/10000000000 : ℝ)*X 0 0+(404391351/1000000000 : ℝ)*X 0 1+(-6395364439/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((2152832363/5000000000 : ℝ)*X 1 0+(-2865540537/10000000000 : ℝ)*X 1 1+(-2829985259/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((5030462969/10000000000 : ℝ)*X 2 0+(5557172053/10000000000 : ℝ)*X 2 1+(2116435437/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((3390625231/5000000000 : ℝ)*X 0 0+(33490629/78125000 : ℝ)*X 0 1+(-163399339/1250000000 : ℝ)*X 0 2+(3390625231/5000000000 : ℝ)*X 1 0+(33490629/78125000 : ℝ)*X 1 1+(-163399339/1250000000 : ℝ)*X 1 2+(3390625231/5000000000 : ℝ)*X 2 0+(33490629/78125000 : ℝ)*X 2 1+(-163399339/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-42555587/200000000 : ℝ)*X 0 0+(1066125433/2500000000 : ℝ)*X 0 1+(-3129874151/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((4852218519/10000000000 : ℝ)*X 1 0+(-556510451/2000000000 : ℝ)*X 1 1+(-5209503861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((2263997273/5000000000 : ℝ)*X 2 0+(5765683911/10000000000 : ℝ)*X 2 1+(308943297/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((1371553229/2000000000 : ℝ)*X 0 0+(827808357/2000000000 : ℝ)*X 0 1+(-1391083777/10000000000 : ℝ)*X 0 2+(1371553229/2000000000 : ℝ)*X 1 0+(827808357/2000000000 : ℝ)*X 1 1+(-1391083777/10000000000 : ℝ)*X 1 2+(1371553229/2000000000 : ℝ)*X 2 0+(827808357/2000000000 : ℝ)*X 2 1+(-1391083777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306060_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((26669/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26669/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (82231927535096702830671542503/19582540396575000000000000000000000 : ℝ) := by norm_num
    linear_combination (760441/1000000000000 : ℝ)*(base5) + (1572887558077/1000000000000 : ℝ)*(base39) + (139941/100000000000 : ℝ)*(base49) + (2348038719069/1000000000000 : ℝ)*(base59) + (15598390628663/1000000000000 : ℝ)*(major_s4_0) + (15598390628663/1000000000000 : ℝ)*(major_s4_1) + (15598390628663/1000000000000 : ℝ)*(major_s4_2) + (37996457/1000000000000 : ℝ)*(sp_s4_1) + (10540086766157/500000000000 : ℝ)*(sp_s4_7) + (5269991639847/250000000000 : ℝ)*(sp_s4_8) + (21080064672639/1000000000000 : ℝ)*(sp_s4_9) + (10116605564817/1000000000000 : ℝ)*(sp_s4_13) + (168976469/1000000000000 : ℝ)*(sp_s4_15) + (27405029/250000000000 : ℝ)*(sp_s4_23) + (10116606325259/1000000000000 : ℝ)*(f.failure) + (10540086766157/500000000000 : ℝ)*(f.sum) + (14349342385566663053/307227304800000000000000000000000 : ℝ)*base63 + (670568883861011/4735900000000000000000000000 : ℝ)*base65 + (1166158078422281/6487200000000000000000000000 : ℝ)*base66 + (216011647756107/2367950000000000000000000000 : ℝ)*base68 + (16896528367374387133/57957944200000000000000000000000 : ℝ)*base71 + (111731579724769/305950000000000000000000000 : ℝ)*base72 + (722439808071539/6487200000000000000000000000 : ℝ)*base75 + (40611300742869/244760000000000000000000000 : ℝ)*base77 + (5597051268651073283/7939035360000000000000000000000 : ℝ)*base78 + (42087/50000000000000000 : ℝ)*base87 + (42087/50000000000000000 : ℝ)*base89 + (42087/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5909/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5909/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (43112896955956853568546130537/2611005386210000000000000000000000 : ℝ) := by norm_num
    linear_combination (211750348609/125000000000 : ℝ)*(base39) + (215847163131/100000000000 : ℝ)*(base59) + (15887614170351/1000000000000 : ℝ)*(major_s4_0) + (15887614170351/1000000000000 : ℝ)*(major_s4_1) + (15887614170351/1000000000000 : ℝ)*(major_s4_2) + (2886243/250000000000 : ℝ)*(sp_s4_0) + (131056833/500000000000 : ℝ)*(sp_s4_2) + (1194347/31250000000 : ℝ)*(sp_s4_6) + (242128653/1000000000000 : ℝ)*(sp_s4_7) + (10735390951003/500000000000 : ℝ)*(sp_s4_14) + (21471035575631/1000000000000 : ℝ)*(sp_s4_15) + (4294154692393/200000000000 : ℝ)*(sp_s4_16) + (1287970998329/125000000000 : ℝ)*(sp_s4_20) + (381055333/1000000000000 : ℝ)*(sp_s4_27) + (10304187261069/1000000000000 : ℝ)*(f.failure) + (21471035575631/1000000000000 : ℝ)*(f.sum) + (25478002873736777753/102409101600000000000000000000000 : ℝ)*base62 + (4132405261064713/4735900000000000000000000000 : ℝ)*base64 + (769595021948981/2162400000000000000000000000 : ℝ)*base67 + (1265271693110109/2367950000000000000000000000 : ℝ)*base68 + (34239619370486579679/57957944200000000000000000000000 : ℝ)*base70 + (70125039936651/152975000000000000000000000 : ℝ)*base73 + (1163592147700439/2162400000000000000000000000 : ℝ)*base74 + (118385209074819/244760000000000000000000000 : ℝ)*base76 + (345779436390276839/2646345120000000000000000000000 : ℝ)*base79 + (42417/50000000000000000 : ℝ)*base87 + (42417/50000000000000000 : ℝ)*base89 + (42417/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16349/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16349/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (818692901872219898302490041/153588552130000000000000000000000 : ℝ) := by norm_num
    linear_combination (1892463286727/1000000000000 : ℝ)*(base39) + (201991/100000000000 : ℝ)*(base40) + (1702828142261/1000000000000 : ℝ)*(base59) + (79289132523/6250000000 : ℝ)*(major_s4_0) + (79289132523/6250000000 : ℝ)*(major_s4_1) + (79289132523/6250000000 : ℝ)*(major_s4_2) + (4154639/125000000000 : ℝ)*(sp_s4_0) + (123274769/1000000000000 : ℝ)*(sp_s4_2) + (17015693/500000000000 : ℝ)*(sp_s4_9) + (59621509/200000000000 : ℝ)*(sp_s4_20) + (1714459302969/100000000000 : ℝ)*(sp_s4_21) + (8572313133401/500000000000 : ℝ)*(sp_s4_22) + (17144468960647/1000000000000 : ℝ)*(sp_s4_23) + (8227596256197/1000000000000 : ℝ)*(sp_s4_27) + (4113947181871/500000000000 : ℝ)*(f.failure) + (8572313133401/500000000000 : ℝ)*(f.sum) + (3740546969008459/15060162000000000000000000000 : ℝ)*base63 + (128206312466021/473590000000000000000000000 : ℝ)*base65 + (79762668091/318000000000000000000000 : ℝ)*base66 + (212659591097649/473590000000000000000000000 : ℝ)*base69 + (364916976046999089/2897897210000000000000000000000 : ℝ)*base71 + (13305487273279/61190000000000000000000000 : ℝ)*base72 + (149213155339/318000000000000000000000 : ℝ)*base75 + (12803223232593/30595000000000000000000000 : ℝ)*base77 + (96447952123951/4864605000000000000000000000 : ℝ)*base79 + (18997/25000000000000000 : ℝ)*base86 + (18997/25000000000000000 : ℝ)*base88 + (18997/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev3 : (0 : ℝ) ≤ ((6119/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6119/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8109/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8109/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-47359/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-47359/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26669/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26669/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5909/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5909/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-16349/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-16349/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306060_s4 p hpa hpb X hX hprev3

#print axioms solution
