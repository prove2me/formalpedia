-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305059_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:30:55.245615+00:00
-- url     : https://prove2.me/submissions/40e3db5d-358c-4a52-aee5-eb9671dbc07e

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
theorem collision_support_c305059_s2_s2_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3102374481/10000000000 : ℝ)*x 0 + (3103401383/10000000000 : ℝ)*x 1 + (3259952839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3102374481/10000000000 : ℝ)^67 ≤ (10744735858503/50000000000000 : ℝ)^51 := by
    have hnat : (3102374481 : ℕ)^67*50000000000000^51 ≤ 10744735858503^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102374481 10000000000 10744735858503 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3103401383/10000000000 : ℝ)^67 ≤ (5374704224373/25000000000000 : ℝ)^51 := by
    have hnat : (3103401383 : ℕ)^67*25000000000000^51 ≤ 5374704224373^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103401383 10000000000 5374704224373 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3259952839/5000000000 : ℝ)^67 ≤ (57011711368221/100000000000000 : ℝ)^51 := by
    have hnat : (3259952839 : ℕ)^67*100000000000000^51 ≤ 57011711368221^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3259952839 5000000000 57011711368221 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3102374481/10000000000 : ℝ), (3103401383/10000000000 : ℝ), (3259952839/5000000000 : ℝ)] ![(10744735858503/50000000000000 : ℝ), (5374704224373/25000000000000 : ℝ), (57011711368221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3102374481/10000000000 : ℝ)|^67 ≤ (10744735858503/50000000000000 : ℝ)^51
        have hw : |(-3102374481/10000000000 : ℝ)|=(3102374481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3103401383/10000000000 : ℝ)|^67 ≤ (5374704224373/25000000000000 : ℝ)^51
        have hw : |(3103401383/10000000000 : ℝ)|=(3103401383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3259952839/5000000000 : ℝ)|^67 ≤ (57011711368221/100000000000000 : ℝ)^51
        have hw : |(3259952839/5000000000 : ℝ)|=(3259952839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (387857077/1250000000 : ℝ)*x 0 + (-3104446331/10000000000 : ℝ)*x 1 + (3259347911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (387857077/1250000000 : ℝ)^67 ≤ (21493859199461/100000000000000 : ℝ)^51 := by
    have hnat : (387857077 : ℕ)^67*100000000000000^51 ≤ 21493859199461^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387857077 1250000000 21493859199461 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104446331/10000000000 : ℝ)^67 ≤ (21508327299019/100000000000000 : ℝ)^51 := by
    have hnat : (3104446331 : ℕ)^67*100000000000000^51 ≤ 21508327299019^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104446331 10000000000 21508327299019 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3259347911/5000000000 : ℝ)^67 ≤ (712472668653/1250000000000 : ℝ)^51 := by
    have hnat : (3259347911 : ℕ)^67*1250000000000^51 ≤ 712472668653^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3259347911 5000000000 712472668653 1250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(387857077/1250000000 : ℝ), (-3104446331/10000000000 : ℝ), (3259347911/5000000000 : ℝ)] ![(21493859199461/100000000000000 : ℝ), (21508327299019/100000000000000 : ℝ), (712472668653/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(387857077/1250000000 : ℝ)|^67 ≤ (21493859199461/100000000000000 : ℝ)^51
        have hw : |(387857077/1250000000 : ℝ)|=(387857077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3104446331/10000000000 : ℝ)|^67 ≤ (21508327299019/100000000000000 : ℝ)^51
        have hw : |(-3104446331/10000000000 : ℝ)|=(3104446331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3259347911/5000000000 : ℝ)|^67 ≤ (712472668653/1250000000000 : ℝ)^51
        have hw : |(3259347911/5000000000 : ℝ)|=(3259347911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1803330271/10000000000 : ℝ)*x 0 + (1208288197/10000000000 : ℝ)*x 1 + (8696557273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1803330271/10000000000 : ℝ)^67 ≤ (1053627562801/10000000000000 : ℝ)^51 := by
    have hnat : (1803330271 : ℕ)^67*10000000000000^51 ≤ 1053627562801^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803330271 10000000000 1053627562801 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1208288197/10000000000 : ℝ)^67 ≤ (6226213858103/100000000000000 : ℝ)^51 := by
    have hnat : (1208288197 : ℕ)^67*100000000000000^51 ≤ 6226213858103^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208288197 10000000000 6226213858103 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8696557273/10000000000 : ℝ)^67 ≤ (2601172203081/3125000000000 : ℝ)^51 := by
    have hnat : (8696557273 : ℕ)^67*3125000000000^51 ≤ 2601172203081^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8696557273 10000000000 2601172203081 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1803330271/10000000000 : ℝ), (1208288197/10000000000 : ℝ), (8696557273/10000000000 : ℝ)] ![(1053627562801/10000000000000 : ℝ), (6226213858103/100000000000000 : ℝ), (2601172203081/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1803330271/10000000000 : ℝ)|^67 ≤ (1053627562801/10000000000000 : ℝ)^51
        have hw : |(-1803330271/10000000000 : ℝ)|=(1803330271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1208288197/10000000000 : ℝ)|^67 ≤ (6226213858103/100000000000000 : ℝ)^51
        have hw : |(1208288197/10000000000 : ℝ)|=(1208288197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8696557273/10000000000 : ℝ)|^67 ≤ (2601172203081/3125000000000 : ℝ)^51
        have hw : |(8696557273/10000000000 : ℝ)|=(8696557273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1635436771/10000000000 : ℝ)*x 0 + (-1394463711/10000000000 : ℝ)*x 1 + (1086867709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1635436771/10000000000 : ℝ)^67 ≤ (4633408892139/50000000000000 : ℝ)^51 := by
    have hnat : (1635436771 : ℕ)^67*50000000000000^51 ≤ 4633408892139^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635436771 10000000000 4633408892139 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394463711/10000000000 : ℝ)^67 ≤ (7515985810579/100000000000000 : ℝ)^51 := by
    have hnat : (1394463711 : ℕ)^67*100000000000000^51 ≤ 7515985810579^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394463711 10000000000 7515985810579 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086867709/1250000000 : ℝ)^67 ≤ (83217196388369/100000000000000 : ℝ)^51 := by
    have hnat : (1086867709 : ℕ)^67*100000000000000^51 ≤ 83217196388369^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086867709 1250000000 83217196388369 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1635436771/10000000000 : ℝ), (-1394463711/10000000000 : ℝ), (1086867709/1250000000 : ℝ)] ![(4633408892139/50000000000000 : ℝ), (7515985810579/100000000000000 : ℝ), (83217196388369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1635436771/10000000000 : ℝ)|^67 ≤ (4633408892139/50000000000000 : ℝ)^51
        have hw : |(1635436771/10000000000 : ℝ)|=(1635436771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1394463711/10000000000 : ℝ)|^67 ≤ (7515985810579/100000000000000 : ℝ)^51
        have hw : |(-1394463711/10000000000 : ℝ)|=(1394463711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086867709/1250000000 : ℝ)|^67 ≤ (83217196388369/100000000000000 : ℝ)^51
        have hw : |(1086867709/1250000000 : ℝ)|=(1086867709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4114146653/10000000000 : ℝ)*x 0 + (3763963697/5000000000 : ℝ)*x 1 + (-1077171/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4114146653/10000000000 : ℝ)^67 ≤ (6227295800437/20000000000000 : ℝ)^51 := by
    have hnat : (4114146653 : ℕ)^67*20000000000000^51 ≤ 6227295800437^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4114146653 10000000000 6227295800437 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3763963697/5000000000 : ℝ)^67 ≤ (68862907911313/100000000000000 : ℝ)^51 := by
    have hnat : (3763963697 : ℕ)^67*100000000000000^51 ≤ 68862907911313^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3763963697 5000000000 68862907911313 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077171/10000000000 : ℝ)^67 ≤ (306535809/50000000000000 : ℝ)^51 := by
    have hnat : (1077171 : ℕ)^67*50000000000000^51 ≤ 306535809^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077171 10000000000 306535809 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4114146653/10000000000 : ℝ), (3763963697/5000000000 : ℝ), (-1077171/10000000000 : ℝ)] ![(6227295800437/20000000000000 : ℝ), (68862907911313/100000000000000 : ℝ), (306535809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4114146653/10000000000 : ℝ)|^67 ≤ (6227295800437/20000000000000 : ℝ)^51
        have hw : |(4114146653/10000000000 : ℝ)|=(4114146653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3763963697/5000000000 : ℝ)|^67 ≤ (68862907911313/100000000000000 : ℝ)^51
        have hw : |(3763963697/5000000000 : ℝ)|=(3763963697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077171/10000000000 : ℝ)|^67 ≤ (306535809/50000000000000 : ℝ)^51
        have hw : |(-1077171/10000000000 : ℝ)|=(1077171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1963687277/10000000000 : ℝ)*x 0 + (1645418853/2000000000 : ℝ)*x 1 + (920799243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1963687277/10000000000 : ℝ)^67 ≤ (1472994442603/12500000000000 : ℝ)^51 := by
    have hnat : (1963687277 : ℕ)^67*12500000000000^51 ≤ 1472994442603^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963687277 10000000000 1472994442603 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1645418853/2000000000 : ℝ)^67 ≤ (15477012288617/20000000000000 : ℝ)^51 := by
    have hnat : (1645418853 : ℕ)^67*20000000000000^51 ≤ 15477012288617^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645418853 2000000000 15477012288617 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920799243/5000000000 : ℝ)^67 ≤ (5415491504023/50000000000000 : ℝ)^51 := by
    have hnat : (920799243 : ℕ)^67*50000000000000^51 ≤ 5415491504023^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920799243 5000000000 5415491504023 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1963687277/10000000000 : ℝ), (1645418853/2000000000 : ℝ), (920799243/5000000000 : ℝ)] ![(1472994442603/12500000000000 : ℝ), (15477012288617/20000000000000 : ℝ), (5415491504023/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1963687277/10000000000 : ℝ)|^67 ≤ (1472994442603/12500000000000 : ℝ)^51
        have hw : |(1963687277/10000000000 : ℝ)|=(1963687277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1645418853/2000000000 : ℝ)|^67 ≤ (15477012288617/20000000000000 : ℝ)^51
        have hw : |(1645418853/2000000000 : ℝ)|=(1645418853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920799243/5000000000 : ℝ)|^67 ≤ (5415491504023/50000000000000 : ℝ)^51
        have hw : |(920799243/5000000000 : ℝ)|=(920799243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-49231733/312500000 : ℝ)*x 0 + (937475293/5000000000 : ℝ)*x 1 + (8444929451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (49231733/312500000 : ℝ)^67 ≤ (4411309113591/50000000000000 : ℝ)^51 := by
    have hnat : (49231733 : ℕ)^67*50000000000000^51 ≤ 4411309113591^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49231733 312500000 4411309113591 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937475293/5000000000 : ℝ)^67 ≤ (11089403942961/100000000000000 : ℝ)^51 := by
    have hnat : (937475293 : ℕ)^67*100000000000000^51 ≤ 11089403942961^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937475293 5000000000 11089403942961 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8444929451/10000000000 : ℝ)^67 ≤ (20021994452763/25000000000000 : ℝ)^51 := by
    have hnat : (8444929451 : ℕ)^67*25000000000000^51 ≤ 20021994452763^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8444929451 10000000000 20021994452763 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-49231733/312500000 : ℝ), (937475293/5000000000 : ℝ), (8444929451/10000000000 : ℝ)] ![(4411309113591/50000000000000 : ℝ), (11089403942961/100000000000000 : ℝ), (20021994452763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-49231733/312500000 : ℝ)|^67 ≤ (4411309113591/50000000000000 : ℝ)^51
        have hw : |(-49231733/312500000 : ℝ)|=(49231733/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(937475293/5000000000 : ℝ)|^67 ≤ (11089403942961/100000000000000 : ℝ)^51
        have hw : |(937475293/5000000000 : ℝ)|=(937475293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8444929451/10000000000 : ℝ)|^67 ≤ (20021994452763/25000000000000 : ℝ)^51
        have hw : |(8444929451/10000000000 : ℝ)|=(8444929451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (749231851/5000000000 : ℝ)*x 0 + (-243663329/1250000000 : ℝ)*x 1 + (1055419967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749231851/5000000000 : ℝ)^67 ≤ (1032607913191/12500000000000 : ℝ)^51 := by
    have hnat : (749231851 : ℕ)^67*12500000000000^51 ≤ 1032607913191^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749231851 5000000000 1032607913191 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (243663329/1250000000 : ℝ)^67 ≤ (2917678762779/25000000000000 : ℝ)^51 := by
    have hnat : (243663329 : ℕ)^67*25000000000000^51 ≤ 2917678762779^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243663329 1250000000 2917678762779 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1055419967/1250000000 : ℝ)^67 ≤ (10008552703613/12500000000000 : ℝ)^51 := by
    have hnat : (1055419967 : ℕ)^67*12500000000000^51 ≤ 10008552703613^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055419967 1250000000 10008552703613 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(749231851/5000000000 : ℝ), (-243663329/1250000000 : ℝ), (1055419967/1250000000 : ℝ)] ![(1032607913191/12500000000000 : ℝ), (2917678762779/25000000000000 : ℝ), (10008552703613/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(749231851/5000000000 : ℝ)|^67 ≤ (1032607913191/12500000000000 : ℝ)^51
        have hw : |(749231851/5000000000 : ℝ)|=(749231851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-243663329/1250000000 : ℝ)|^67 ≤ (2917678762779/25000000000000 : ℝ)^51
        have hw : |(-243663329/1250000000 : ℝ)|=(243663329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1055419967/1250000000 : ℝ)|^67 ≤ (10008552703613/12500000000000 : ℝ)^51
        have hw : |(1055419967/1250000000 : ℝ)|=(1055419967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8576937167/10000000000 : ℝ)*x 0 + (548209851/2000000000 : ℝ)*x 1 + (351599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8576937167/10000000000 : ℝ)^67 ≤ (81736652858849/100000000000000 : ℝ)^51 := by
    have hnat : (8576937167 : ℕ)^67*100000000000000^51 ≤ 81736652858849^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8576937167 10000000000 81736652858849 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548209851/2000000000 : ℝ)^67 ≤ (18263206287097/100000000000000 : ℝ)^51 := by
    have hnat : (548209851 : ℕ)^67*100000000000000^51 ≤ 18263206287097^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548209851 2000000000 18263206287097 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (351599/10000000000 : ℝ)^67 ≤ (70420523/50000000000000 : ℝ)^51 := by
    have hnat : (351599 : ℕ)^67*50000000000000^51 ≤ 70420523^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351599 10000000000 70420523 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8576937167/10000000000 : ℝ), (548209851/2000000000 : ℝ), (351599/10000000000 : ℝ)] ![(81736652858849/100000000000000 : ℝ), (18263206287097/100000000000000 : ℝ), (70420523/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8576937167/10000000000 : ℝ)|^67 ≤ (81736652858849/100000000000000 : ℝ)^51
        have hw : |(8576937167/10000000000 : ℝ)|=(8576937167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548209851/2000000000 : ℝ)|^67 ≤ (18263206287097/100000000000000 : ℝ)^51
        have hw : |(548209851/2000000000 : ℝ)|=(548209851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(351599/10000000000 : ℝ)|^67 ≤ (70420523/50000000000000 : ℝ)^51
        have hw : |(351599/10000000000 : ℝ)|=(351599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (670526017/1000000000 : ℝ)*x 0 + (3782452977/10000000000 : ℝ)*x 1 + (264025521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670526017/1000000000 : ℝ)^67 ≤ (11830082920181/20000000000000 : ℝ)^51 := by
    have hnat : (670526017 : ℕ)^67*20000000000000^51 ≤ 11830082920181^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670526017 1000000000 11830082920181 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3782452977/10000000000 : ℝ)^67 ≤ (27881127583543/100000000000000 : ℝ)^51 := by
    have hnat : (3782452977 : ℕ)^67*100000000000000^51 ≤ 27881127583543^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3782452977 10000000000 27881127583543 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264025521/1250000000 : ℝ)^67 ≤ (6484228897841/50000000000000 : ℝ)^51 := by
    have hnat : (264025521 : ℕ)^67*50000000000000^51 ≤ 6484228897841^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264025521 1250000000 6484228897841 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670526017/1000000000 : ℝ), (3782452977/10000000000 : ℝ), (264025521/1250000000 : ℝ)] ![(11830082920181/20000000000000 : ℝ), (27881127583543/100000000000000 : ℝ), (6484228897841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670526017/1000000000 : ℝ)|^67 ≤ (11830082920181/20000000000000 : ℝ)^51
        have hw : |(670526017/1000000000 : ℝ)|=(670526017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3782452977/10000000000 : ℝ)|^67 ≤ (27881127583543/100000000000000 : ℝ)^51
        have hw : |(3782452977/10000000000 : ℝ)|=(3782452977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264025521/1250000000 : ℝ)|^67 ≤ (6484228897841/50000000000000 : ℝ)^51
        have hw : |(264025521/1250000000 : ℝ)|=(264025521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-6084636239/10000000000 : ℝ)*x 0 + (620048303/2500000000 : ℝ)*x 1 + (2096385431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6084636239/10000000000 : ℝ)^67 ≤ (52064717943981/100000000000000 : ℝ)^51 := by
    have hnat : (6084636239 : ℕ)^67*100000000000000^51 ≤ 52064717943981^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6084636239 10000000000 52064717943981 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620048303/2500000000 : ℝ)^67 ≤ (16014750823463/100000000000000 : ℝ)^51 := by
    have hnat : (620048303 : ℕ)^67*100000000000000^51 ≤ 16014750823463^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620048303 2500000000 16014750823463 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096385431/5000000000 : ℝ)^67 ≤ (6384106240999/20000000000000 : ℝ)^51 := by
    have hnat : (2096385431 : ℕ)^67*20000000000000^51 ≤ 6384106240999^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096385431 5000000000 6384106240999 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6084636239/10000000000 : ℝ), (620048303/2500000000 : ℝ), (2096385431/5000000000 : ℝ)] ![(52064717943981/100000000000000 : ℝ), (16014750823463/100000000000000 : ℝ), (6384106240999/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6084636239/10000000000 : ℝ)|^67 ≤ (52064717943981/100000000000000 : ℝ)^51
        have hw : |(-6084636239/10000000000 : ℝ)|=(6084636239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(620048303/2500000000 : ℝ)|^67 ≤ (16014750823463/100000000000000 : ℝ)^51
        have hw : |(620048303/2500000000 : ℝ)|=(620048303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2096385431/5000000000 : ℝ)|^67 ≤ (6384106240999/20000000000000 : ℝ)^51
        have hw : |(2096385431/5000000000 : ℝ)|=(2096385431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (119353303/1000000000 : ℝ)*x 0 + (-2235116239/10000000000 : ℝ)*x 1 + (8430213403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119353303/1000000000 : ℝ)^67 ≤ (1531630068739/25000000000000 : ℝ)^51 := by
    have hnat : (119353303 : ℕ)^67*25000000000000^51 ≤ 1531630068739^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119353303 1000000000 1531630068739 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235116239/10000000000 : ℝ)^67 ≤ (13968795941279/100000000000000 : ℝ)^51 := by
    have hnat : (2235116239 : ℕ)^67*100000000000000^51 ≤ 13968795941279^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235116239 10000000000 13968795941279 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8430213403/10000000000 : ℝ)^67 ≤ (19976170942339/25000000000000 : ℝ)^51 := by
    have hnat : (8430213403 : ℕ)^67*25000000000000^51 ≤ 19976170942339^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8430213403 10000000000 19976170942339 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(119353303/1000000000 : ℝ), (-2235116239/10000000000 : ℝ), (8430213403/10000000000 : ℝ)] ![(1531630068739/25000000000000 : ℝ), (13968795941279/100000000000000 : ℝ), (19976170942339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(119353303/1000000000 : ℝ)|^67 ≤ (1531630068739/25000000000000 : ℝ)^51
        have hw : |(119353303/1000000000 : ℝ)|=(119353303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235116239/10000000000 : ℝ)|^67 ≤ (13968795941279/100000000000000 : ℝ)^51
        have hw : |(-2235116239/10000000000 : ℝ)|=(2235116239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8430213403/10000000000 : ℝ)|^67 ≤ (19976170942339/25000000000000 : ℝ)^51
        have hw : |(8430213403/10000000000 : ℝ)|=(8430213403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4134420093/5000000000 : ℝ)*x 0 + (3159521139/10000000000 : ℝ)*x 1 + (188363/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4134420093/5000000000 : ℝ)^67 ≤ (19475332142447/25000000000000 : ℝ)^51 := by
    have hnat : (4134420093 : ℕ)^67*25000000000000^51 ≤ 19475332142447^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134420093 5000000000 19475332142447 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3159521139/10000000000 : ℝ)^67 ≤ (22010996340409/100000000000000 : ℝ)^51 := by
    have hnat : (3159521139 : ℕ)^67*100000000000000^51 ≤ 22010996340409^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3159521139 10000000000 22010996340409 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188363/40000000 : ℝ)^67 ≤ (43837541943/50000000000000 : ℝ)^51 := by
    have hnat : (188363 : ℕ)^67*50000000000000^51 ≤ 43837541943^51*40000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188363 40000000 43837541943 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4134420093/5000000000 : ℝ), (3159521139/10000000000 : ℝ), (188363/40000000 : ℝ)] ![(19475332142447/25000000000000 : ℝ), (22010996340409/100000000000000 : ℝ), (43837541943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4134420093/5000000000 : ℝ)|^67 ≤ (19475332142447/25000000000000 : ℝ)^51
        have hw : |(4134420093/5000000000 : ℝ)|=(4134420093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3159521139/10000000000 : ℝ)|^67 ≤ (22010996340409/100000000000000 : ℝ)^51
        have hw : |(3159521139/10000000000 : ℝ)|=(3159521139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(188363/40000000 : ℝ)|^67 ≤ (43837541943/50000000000000 : ℝ)^51
        have hw : |(188363/40000000 : ℝ)|=(188363/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305059_s2_s2_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2099044681/10000000000 : ℝ)*x 0 + (7467474603/10000000000 : ℝ)*x 1 + (706213317/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2099044681/10000000000 : ℝ)^67 ≤ (12862417537123/100000000000000 : ℝ)^51 := by
    have hnat : (2099044681 : ℕ)^67*100000000000000^51 ≤ 12862417537123^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2099044681 10000000000 12862417537123 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7467474603/10000000000 : ℝ)^67 ≤ (34068666304171/50000000000000 : ℝ)^51 := by
    have hnat : (7467474603 : ℕ)^67*50000000000000^51 ≤ 34068666304171^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7467474603 10000000000 34068666304171 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706213317/2500000000 : ℝ)^67 ≤ (19000249847709/100000000000000 : ℝ)^51 := by
    have hnat : (706213317 : ℕ)^67*100000000000000^51 ≤ 19000249847709^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706213317 2500000000 19000249847709 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2099044681/10000000000 : ℝ), (7467474603/10000000000 : ℝ), (706213317/2500000000 : ℝ)] ![(12862417537123/100000000000000 : ℝ), (34068666304171/50000000000000 : ℝ), (19000249847709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2099044681/10000000000 : ℝ)|^67 ≤ (12862417537123/100000000000000 : ℝ)^51
        have hw : |(2099044681/10000000000 : ℝ)|=(2099044681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7467474603/10000000000 : ℝ)|^67 ≤ (34068666304171/50000000000000 : ℝ)^51
        have hw : |(7467474603/10000000000 : ℝ)|=(7467474603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706213317/2500000000 : ℝ)|^67 ≤ (19000249847709/100000000000000 : ℝ)^51
        have hw : |(706213317/2500000000 : ℝ)|=(706213317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305059_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((22977/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22977/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91999/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91999/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4011/5000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4011/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((42623/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42623/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84983/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84983/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13541/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13541/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (22977/25000 : ℝ) ^ (133/32 : ℝ) ≤ (8802321580386544699/12500000000000000000 : ℝ) := by
    have hpowers : (22977/25000 : ℝ)^133 ≤ (8802321580386544699/12500000000000000000 : ℝ)^32 := by
      have hnat : (22977 : ℕ)^133*12500000000000000000^32 ≤ 8802321580386544699^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22977 25000 8802321580386544699 12500000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22977/25000 : ℝ)) (X := (8802321580386544699/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (21302321580386544699/12500000000000000000 : ℝ) ≤ (1421063003320243/1250000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (21302321580386544699/12500000000000000000 : ℝ)^32 ≤ (1421063003320243/1250000000000000 : ℝ)^133 := by
      have hnat : (21302321580386544699 : ℕ)^32*1250000000000000^133 ≤ 1421063003320243^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21302321580386544699 12500000000000000000 1421063003320243 1250000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1421063003320243/1250000000000000 : ℝ)) (X := (21302321580386544699/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (15052321580386544699/6250000000000000000 : ℝ) ≤ (12355013977959729/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (15052321580386544699/6250000000000000000 : ℝ)^32 ≤ (12355013977959729/10000000000000000 : ℝ)^133 := by
      have hnat : (15052321580386544699 : ℕ)^32*10000000000000000^133 ≤ 12355013977959729^133*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15052321580386544699 6250000000000000000 12355013977959729 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12355013977959729/10000000000000000 : ℝ)) (X := (15052321580386544699/6250000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(171063003320243/1148850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(8578347403459/79920000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (22977/25000 : ℝ)) (alpha := (171063003320243/1148850000000000 : ℝ)) (beta := (8578347403459/79920000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (22977/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(171063003320243/1148850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(8578347403459/79920000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (91999/100000 : ℝ) ^ (133/32 : ℝ) ≤ (70708811469855837623/100000000000000000000 : ℝ) := by
    have hpowers : (91999/100000 : ℝ)^133 ≤ (70708811469855837623/100000000000000000000 : ℝ)^32 := by
      have hnat : (91999 : ℕ)^133*100000000000000000000^32 ≤ 70708811469855837623^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        91999 100000 70708811469855837623 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (91999/100000 : ℝ)) (X := (70708811469855837623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (170708811469855837623/100000000000000000000 : ℝ) ≤ (5686579727154683/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (170708811469855837623/100000000000000000000 : ℝ)^32 ≤ (5686579727154683/5000000000000000 : ℝ)^133 := by
      have hnat : (170708811469855837623 : ℕ)^32*5000000000000000^133 ≤ 5686579727154683^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        170708811469855837623 100000000000000000000 5686579727154683 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5686579727154683/5000000000000000 : ℝ)) (X := (170708811469855837623/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (120708811469855837623/50000000000000000000 : ℝ) ≤ (12362172222642121/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (120708811469855837623/50000000000000000000 : ℝ)^32 ≤ (12362172222642121/10000000000000000 : ℝ)^133 := by
      have hnat : (120708811469855837623 : ℕ)^32*10000000000000000^133 ≤ 12362172222642121^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120708811469855837623 50000000000000000000 12362172222642121 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12362172222642121/10000000000000000 : ℝ)) (X := (120708811469855837623/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(686579727154683/4599950000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(197802553666551/1839980000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (91999/100000 : ℝ)) (alpha := (686579727154683/4599950000000000 : ℝ)) (beta := (197802553666551/1839980000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (91999/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(686579727154683/4599950000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(197802553666551/1839980000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (4011/5000 : ℝ) ^ (133/32 : ℝ) ≤ (40010575283999568001/100000000000000000000 : ℝ) := by
    have hpowers : (4011/5000 : ℝ)^133 ≤ (40010575283999568001/100000000000000000000 : ℝ)^32 := by
      have hnat : (4011 : ℕ)^133*100000000000000000000^32 ≤ 40010575283999568001^32*5000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4011 5000 40010575283999568001 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4011/5000 : ℝ)) (X := (40010575283999568001/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (140010575283999568001/100000000000000000000 : ℝ) ≤ (2710856486901987/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (140010575283999568001/100000000000000000000 : ℝ)^32 ≤ (2710856486901987/2500000000000000 : ℝ)^133 := by
      have hnat : (140010575283999568001 : ℕ)^32*2500000000000000^133 ≤ 2710856486901987^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140010575283999568001 100000000000000000000 2710856486901987 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2710856486901987/2500000000000000 : ℝ)) (X := (140010575283999568001/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (90010575283999568001/50000000000000000000 : ℝ) ≤ (11519436259168471/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (90010575283999568001/50000000000000000000 : ℝ)^32 ≤ (11519436259168471/10000000000000000 : ℝ)^133 := by
      have hnat : (90010575283999568001 : ℕ)^32*10000000000000000^133 ≤ 11519436259168471^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        90010575283999568001 50000000000000000000 11519436259168471 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11519436259168471/10000000000000000 : ℝ)) (X := (90010575283999568001/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(210856486901987/2005500000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(676010311560523/8022000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (4011/5000 : ℝ)) (alpha := (210856486901987/2005500000000000 : ℝ)) (beta := (676010311560523/8022000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (4011/5000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(210856486901987/2005500000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(676010311560523/8022000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3102374481/10000000000 : ℝ)*X 0 0+(3103401383/10000000000 : ℝ)*X 0 1+(3259952839/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((387857077/1250000000 : ℝ)*X 1 0+(-3104446331/10000000000 : ℝ)*X 1 1+(3259347911/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1803330271/10000000000 : ℝ)*X 0 0+(1208288197/10000000000 : ℝ)*X 0 1+(8696557273/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1635436771/10000000000 : ℝ)*X 1 0+(-1394463711/10000000000 : ℝ)*X 1 1+(1086867709/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4114146653/10000000000 : ℝ)*X 2 0+(3763963697/5000000000 : ℝ)*X 2 1+(-1077171/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1963687277/10000000000 : ℝ)*X 0 0+(1645418853/2000000000 : ℝ)*X 0 1+(920799243/5000000000 : ℝ)*X 0 2+(1963687277/10000000000 : ℝ)*X 1 0+(1645418853/2000000000 : ℝ)*X 1 1+(920799243/5000000000 : ℝ)*X 1 2+(1963687277/10000000000 : ℝ)*X 2 0+(1645418853/2000000000 : ℝ)*X 2 1+(920799243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-49231733/312500000 : ℝ)*X 0 0+(937475293/5000000000 : ℝ)*X 0 1+(8444929451/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((749231851/5000000000 : ℝ)*X 1 0+(-243663329/1250000000 : ℝ)*X 1 1+(1055419967/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((8576937167/10000000000 : ℝ)*X 2 0+(548209851/2000000000 : ℝ)*X 2 1+(351599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((670526017/1000000000 : ℝ)*X 0 0+(3782452977/10000000000 : ℝ)*X 0 1+(264025521/1250000000 : ℝ)*X 0 2+(670526017/1000000000 : ℝ)*X 1 0+(3782452977/10000000000 : ℝ)*X 1 1+(264025521/1250000000 : ℝ)*X 1 2+(670526017/1000000000 : ℝ)*X 2 0+(3782452977/10000000000 : ℝ)*X 2 1+(264025521/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-6084636239/10000000000 : ℝ)*X 0 0+(620048303/2500000000 : ℝ)*X 0 1+(2096385431/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((119353303/1000000000 : ℝ)*X 1 0+(-2235116239/10000000000 : ℝ)*X 1 1+(8430213403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((4134420093/5000000000 : ℝ)*X 2 0+(3159521139/10000000000 : ℝ)*X 2 1+(188363/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2099044681/10000000000 : ℝ)*X 0 0+(7467474603/10000000000 : ℝ)*X 0 1+(706213317/2500000000 : ℝ)*X 0 2+(2099044681/10000000000 : ℝ)*X 1 0+(7467474603/10000000000 : ℝ)*X 1 1+(706213317/2500000000 : ℝ)*X 1 2+(2099044681/10000000000 : ℝ)*X 2 0+(7467474603/10000000000 : ℝ)*X 2 1+(706213317/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305059_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((42623/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42623/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4242450343420306776881106149/819197735580000000000000000000000 : ℝ) := by norm_num
    linear_combination (87895878919/100000000000 : ℝ)*(base7) + (131381/1000000000000 : ℝ)*(base39) + (32063/40000000000 : ℝ)*(base50) + (2073553/500000000000 : ℝ)*(base53) + (115407/250000000000 : ℝ)*(base60) + (1712412710861/1000000000000 : ℝ)*(major_s2_0) + (1712412710861/1000000000000 : ℝ)*(major_s2_1) + (342481712751/200000000000 : ℝ)*(major_s2_2) + (87872656357/50000000000 : ℝ)*(sp_s2_7) + (1757485867091/1000000000000 : ℝ)*(sp_s2_8) + (1757499013323/1000000000000 : ℝ)*(sp_s2_9) + (999354862417/500000000000 : ℝ)*(sp_s2_13) + (41739077/1000000000000 : ℝ)*(sp_s2_14) + (4499563/500000000000 : ℝ)*(sp_s2_15) + (279937733911/250000000000 : ℝ)*(f.failure) + (1757499013323/1000000000000 : ℝ)*(f.sum) + (5479936573408965961/12300266300000000000000000000000 : ℝ)*base63 + (14552160871831/534800000000000000000000000 : ℝ)*base65 + (553223034659047/1839980000000000000000000000 : ℝ)*base66 + (9736682171451/133700000000000000000000000 : ℝ)*base69 + (695881992714979739/2457619920000000000000000000000 : ℝ)*base71 + (7968936832421/15984000000000000000000000 : ℝ)*base72 + (217607942983313/1149987500000000000000000000 : ℝ)*base74 + (206560692084497/1148850000000000000000000000 : ℝ)*base76 + (3859099467189870571/7352560080000000000000000000000 : ℝ)*base78 + (2051/3125000000000000 : ℝ)*base87 + (2051/3125000000000000 : ℝ)*base89 + (2051/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84983/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84983/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (274976808993565404099878077/35231017050000000000000000000000 : ℝ) := by norm_num
    linear_combination (191845052969/1000000000000 : ℝ)*(base5) + (882287698451/1000000000000 : ℝ)*(base7) + (8697/5000000000 : ℝ)*(base33) + (20758285883/200000000000 : ℝ)*(base60) + (950924627329/500000000000 : ℝ)*(major_s2_0) + (950925497029/500000000000 : ℝ)*(major_s2_1) + (950925497029/500000000000 : ℝ)*(major_s2_2) + (4771777/1000000000000 : ℝ)*(sp_s2_0) + (770961/200000000000 : ℝ)*(sp_s2_1) + (9629927/200000000000 : ℝ)*(sp_s2_8) + (2010421923561/1000000000000 : ℝ)*(sp_s2_14) + (1005186475749/500000000000 : ℝ)*(sp_s2_15) + (1101135004453/500000000000 : ℝ)*(sp_s2_16) + (1934067746221/1000000000000 : ℝ)*(sp_s2_20) + (1243625100739/1000000000000 : ℝ)*(f.failure) + (2010426695337/1000000000000 : ℝ)*(f.sum) + (11106297164850678517/23062999312500000000000000000000 : ℝ)*base63 + (267077313093233/4011000000000000000000000000 : ℝ)*base64 + (145759989292269/229997500000000000000000000 : ℝ)*base66 + (9130279123787/250687500000000000000000000 : ℝ)*base68 + (9957712921273997713/30720249000000000000000000000000 : ℝ)*base71 + (4918796164129/7992000000000000000000000 : ℝ)*base72 + (220324138693987/2299975000000000000000000000 : ℝ)*base75 + (31620825255799/1148850000000000000000000000 : ℝ)*base77 + (8855616714862757/735256008000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (431/3125000000000000 : ℝ)*base87 + (431/3125000000000000 : ℝ)*base89 + (431/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13541/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13541/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10690974642644323219143179/2048016600000000000000000000000 : ℝ) := by norm_num
    linear_combination (1209126569/125000000000 : ℝ)*(base5) + (435536738387/1000000000000 : ℝ)*(base7) + (170356748403/1000000000000 : ℝ)*(base33) + (140404491289/200000000000 : ℝ)*(base44) + (6292722467/250000000000 : ℝ)*(base50) + (732233712511/500000000000 : ℝ)*(major_s2_0) + (46640085849/50000000000 : ℝ)*(major_s2_1) + (65392966937/40000000000 : ℝ)*(major_s2_2) + (32049221/500000000000 : ℝ)*(sp_s2_1) + (49190147/1000000000000 : ℝ)*(sp_s2_16) + (1929300331699/1000000000000 : ℝ)*(sp_s2_21) + (132107128551/125000000000 : ℝ)*(sp_s2_22) + (1768567405701/1000000000000 : ℝ)*(sp_s2_23) + (198214216801/250000000000 : ℝ)*(sp_s2_27) + (534507798907/500000000000 : ℝ)*(f.failure) + (1929300331699/1000000000000 : ℝ)*(f.sum) + (1691976604054149101/7380159780000000000000000000000 : ℝ)*base63 + (165718780474451/320880000000000000000000000 : ℝ)*base65 + (238408855937/2299975000000000000000000 : ℝ)*base66 + (10284907198589/80220000000000000000000000 : ℝ)*base69 + (1888640778712701781/12288099600000000000000000000000 : ℝ)*base71 + (453217166771/39960000000000000000000000 : ℝ)*base72 + (552451281168673/919990000000000000000000000 : ℝ)*base74 + (205039447966493/574425000000000000000000000 : ℝ)*base77 + (561805048023586591/3676280040000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (19/3125000000000000 : ℝ)*base86 + (19/3125000000000000 : ℝ)*base88 + (19/3125000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((22977/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22977/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91999/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91999/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4011/5000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4011/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((42623/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42623/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(84983/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(84983/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(13541/20000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(13541/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305059_s2 p hpa hpb X hX hprev1

#print axioms solution
