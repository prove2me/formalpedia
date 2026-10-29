-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306058_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:56:26.529983+00:00
-- url     : https://prove2.me/submissions/4e301324-2dec-405d-9f79-e417c9bf3ee6

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
theorem collision_support_c306058_s2_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3401635511/10000000000 : ℝ)*x 0 + (1648854667/5000000000 : ℝ)*x 1 + (-3049459453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3401635511/10000000000 : ℝ)^135 ≤ (12166417661191/50000000000000 : ℝ)^103 := by
    have hnat : (3401635511 : ℕ)^135*50000000000000^103 ≤ 12166417661191^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3401635511 10000000000 12166417661191 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1648854667/5000000000 : ℝ)^135 ≤ (11681558417139/50000000000000 : ℝ)^103 := by
    have hnat : (1648854667 : ℕ)^135*50000000000000^103 ≤ 11681558417139^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648854667 5000000000 11681558417139 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3049459453/5000000000 : ℝ)^135 ≤ (26152023915737/50000000000000 : ℝ)^103 := by
    have hnat : (3049459453 : ℕ)^135*50000000000000^103 ≤ 26152023915737^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3049459453 5000000000 26152023915737 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3401635511/10000000000 : ℝ), (1648854667/5000000000 : ℝ), (-3049459453/5000000000 : ℝ)] ![(12166417661191/50000000000000 : ℝ), (11681558417139/50000000000000 : ℝ), (26152023915737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3401635511/10000000000 : ℝ)|^135 ≤ (12166417661191/50000000000000 : ℝ)^103
        have hw : |(-3401635511/10000000000 : ℝ)|=(3401635511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1648854667/5000000000 : ℝ)|^135 ≤ (11681558417139/50000000000000 : ℝ)^103
        have hw : |(1648854667/5000000000 : ℝ)|=(1648854667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3049459453/5000000000 : ℝ)|^135 ≤ (26152023915737/50000000000000 : ℝ)^103
        have hw : |(-3049459453/5000000000 : ℝ)|=(3049459453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4121331657/10000000000 : ℝ)*x 0 + (7127544613/10000000000 : ℝ)*x 1 + (-946420053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4121331657/10000000000 : ℝ)^135 ≤ (6258461441653/20000000000000 : ℝ)^103 := by
    have hnat : (4121331657 : ℕ)^135*20000000000000^103 ≤ 6258461441653^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121331657 10000000000 6258461441653 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7127544613/10000000000 : ℝ)^135 ≤ (32079041818821/50000000000000 : ℝ)^103 := by
    have hnat : (7127544613 : ℕ)^135*50000000000000^103 ≤ 32079041818821^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7127544613 10000000000 32079041818821 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946420053/10000000000 : ℝ)^135 ≤ (4549609140899/100000000000000 : ℝ)^103 := by
    have hnat : (946420053 : ℕ)^135*100000000000000^103 ≤ 4549609140899^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946420053 10000000000 4549609140899 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4121331657/10000000000 : ℝ), (7127544613/10000000000 : ℝ), (-946420053/10000000000 : ℝ)] ![(6258461441653/20000000000000 : ℝ), (32079041818821/50000000000000 : ℝ), (4549609140899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4121331657/10000000000 : ℝ)|^135 ≤ (6258461441653/20000000000000 : ℝ)^103
        have hw : |(4121331657/10000000000 : ℝ)|=(4121331657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7127544613/10000000000 : ℝ)|^135 ≤ (32079041818821/50000000000000 : ℝ)^103
        have hw : |(7127544613/10000000000 : ℝ)|=(7127544613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-946420053/10000000000 : ℝ)|^135 ≤ (4549609140899/100000000000000 : ℝ)^103
        have hw : |(-946420053/10000000000 : ℝ)|=(946420053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-120100849/400000000 : ℝ)*x 0 + (278456111/1000000000 : ℝ)*x 1 + (-1365150921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120100849/400000000 : ℝ)^135 ≤ (10330507816219/50000000000000 : ℝ)^103 := by
    have hnat : (120100849 : ℕ)^135*50000000000000^103 ≤ 10330507816219^103*400000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120100849 400000000 10330507816219 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (278456111/1000000000 : ℝ)^135 ≤ (584930165247/3125000000000 : ℝ)^103 := by
    have hnat : (278456111 : ℕ)^135*3125000000000^103 ≤ 584930165247^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      278456111 1000000000 584930165247 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365150921/2000000000 : ℝ)^135 ≤ (15155304765253/25000000000000 : ℝ)^103 := by
    have hnat : (1365150921 : ℕ)^135*25000000000000^103 ≤ 15155304765253^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365150921 2000000000 15155304765253 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120100849/400000000 : ℝ), (278456111/1000000000 : ℝ), (-1365150921/2000000000 : ℝ)] ![(10330507816219/50000000000000 : ℝ), (584930165247/3125000000000 : ℝ), (15155304765253/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120100849/400000000 : ℝ)|^135 ≤ (10330507816219/50000000000000 : ℝ)^103
        have hw : |(-120100849/400000000 : ℝ)|=(120100849/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(278456111/1000000000 : ℝ)|^135 ≤ (584930165247/3125000000000 : ℝ)^103
        have hw : |(278456111/1000000000 : ℝ)|=(278456111/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1365150921/2000000000 : ℝ)|^135 ≤ (15155304765253/25000000000000 : ℝ)^103
        have hw : |(-1365150921/2000000000 : ℝ)|=(1365150921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3142291161/10000000000 : ℝ)*x 0 + (-351513627/1250000000 : ℝ)*x 1 + (-3347707453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3142291161/10000000000 : ℝ)^135 ≤ (21930631522933/100000000000000 : ℝ)^103 := by
    have hnat : (3142291161 : ℕ)^135*100000000000000^103 ≤ 21930631522933^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3142291161 10000000000 21930631522933 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351513627/1250000000 : ℝ)^135 ≤ (9480422238427/50000000000000 : ℝ)^103 := by
    have hnat : (351513627 : ℕ)^135*50000000000000^103 ≤ 9480422238427^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351513627 1250000000 9480422238427 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3347707453/5000000000 : ℝ)^135 ≤ (59108523983941/100000000000000 : ℝ)^103 := by
    have hnat : (3347707453 : ℕ)^135*100000000000000^103 ≤ 59108523983941^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3347707453 5000000000 59108523983941 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3142291161/10000000000 : ℝ), (-351513627/1250000000 : ℝ), (-3347707453/5000000000 : ℝ)] ![(21930631522933/100000000000000 : ℝ), (9480422238427/50000000000000 : ℝ), (59108523983941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3142291161/10000000000 : ℝ)|^135 ≤ (21930631522933/100000000000000 : ℝ)^103
        have hw : |(3142291161/10000000000 : ℝ)|=(3142291161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-351513627/1250000000 : ℝ)|^135 ≤ (9480422238427/50000000000000 : ℝ)^103
        have hw : |(-351513627/1250000000 : ℝ)|=(351513627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3347707453/5000000000 : ℝ)|^135 ≤ (59108523983941/100000000000000 : ℝ)^103
        have hw : |(-3347707453/5000000000 : ℝ)|=(3347707453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5639421793/10000000000 : ℝ)*x 0 + (5539570533/10000000000 : ℝ)*x 1 + (635130557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5639421793/10000000000 : ℝ)^135 ≤ (47200677640529/100000000000000 : ℝ)^103 := by
    have hnat : (5639421793 : ℕ)^135*100000000000000^103 ≤ 47200677640529^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5639421793 10000000000 47200677640529 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5539570533/10000000000 : ℝ)^135 ≤ (46108325426143/100000000000000 : ℝ)^103 := by
    have hnat : (5539570533 : ℕ)^135*100000000000000^103 ≤ 46108325426143^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5539570533 10000000000 46108325426143 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (635130557/5000000000 : ℝ)^135 ≤ (6690996916051/100000000000000 : ℝ)^103 := by
    have hnat : (635130557 : ℕ)^135*100000000000000^103 ≤ 6690996916051^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635130557 5000000000 6690996916051 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5639421793/10000000000 : ℝ), (5539570533/10000000000 : ℝ), (635130557/5000000000 : ℝ)] ![(47200677640529/100000000000000 : ℝ), (46108325426143/100000000000000 : ℝ), (6690996916051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5639421793/10000000000 : ℝ)|^135 ≤ (47200677640529/100000000000000 : ℝ)^103
        have hw : |(5639421793/10000000000 : ℝ)|=(5639421793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5539570533/10000000000 : ℝ)|^135 ≤ (46108325426143/100000000000000 : ℝ)^103
        have hw : |(5539570533/10000000000 : ℝ)|=(5539570533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(635130557/5000000000 : ℝ)|^135 ≤ (6690996916051/100000000000000 : ℝ)^103
        have hw : |(635130557/5000000000 : ℝ)|=(635130557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (985950077/2500000000 : ℝ)*x 0 + (7655808039/10000000000 : ℝ)*x 1 + (-6147/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (985950077/2500000000 : ℝ)^135 ≤ (29537512592571/100000000000000 : ℝ)^103 := by
    have hnat : (985950077 : ℕ)^135*100000000000000^103 ≤ 29537512592571^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985950077 2500000000 29537512592571 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7655808039/10000000000 : ℝ)^135 ≤ (2201909357389/3125000000000 : ℝ)^103 := by
    have hnat : (7655808039 : ℕ)^135*3125000000000^103 ≤ 2201909357389^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7655808039 10000000000 2201909357389 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6147/31250000 : ℝ)^135 ≤ (1387958603/100000000000000 : ℝ)^103 := by
    have hnat : (6147 : ℕ)^135*100000000000000^103 ≤ 1387958603^103*31250000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6147 31250000 1387958603 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(985950077/2500000000 : ℝ), (7655808039/10000000000 : ℝ), (-6147/31250000 : ℝ)] ![(29537512592571/100000000000000 : ℝ), (2201909357389/3125000000000 : ℝ), (1387958603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(985950077/2500000000 : ℝ)|^135 ≤ (29537512592571/100000000000000 : ℝ)^103
        have hw : |(985950077/2500000000 : ℝ)|=(985950077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7655808039/10000000000 : ℝ)|^135 ≤ (2201909357389/3125000000000 : ℝ)^103
        have hw : |(7655808039/10000000000 : ℝ)|=(7655808039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6147/31250000 : ℝ)|^135 ≤ (1387958603/100000000000000 : ℝ)^103
        have hw : |(-6147/31250000 : ℝ)|=(6147/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1427188603/5000000000 : ℝ)*x 0 + (586784821/2000000000 : ℝ)*x 1 + (-682566769/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1427188603/5000000000 : ℝ)^135 ≤ (386705049003/2000000000000 : ℝ)^103 := by
    have hnat : (1427188603 : ℕ)^135*2000000000000^103 ≤ 386705049003^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427188603 5000000000 386705049003 2000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586784821/2000000000 : ℝ)^135 ≤ (10022270105049/50000000000000 : ℝ)^103 := by
    have hnat : (586784821 : ℕ)^135*50000000000000^103 ≤ 10022270105049^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586784821 2000000000 10022270105049 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682566769/1000000000 : ℝ)^135 ≤ (6062020733151/10000000000000 : ℝ)^103 := by
    have hnat : (682566769 : ℕ)^135*10000000000000^103 ≤ 6062020733151^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682566769 1000000000 6062020733151 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1427188603/5000000000 : ℝ), (586784821/2000000000 : ℝ), (-682566769/1000000000 : ℝ)] ![(386705049003/2000000000000 : ℝ), (10022270105049/50000000000000 : ℝ), (6062020733151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1427188603/5000000000 : ℝ)|^135 ≤ (386705049003/2000000000000 : ℝ)^103
        have hw : |(-1427188603/5000000000 : ℝ)|=(1427188603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586784821/2000000000 : ℝ)|^135 ≤ (10022270105049/50000000000000 : ℝ)^103
        have hw : |(586784821/2000000000 : ℝ)|=(586784821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-682566769/1000000000 : ℝ)|^135 ≤ (6062020733151/10000000000000 : ℝ)^103
        have hw : |(-682566769/1000000000 : ℝ)|=(682566769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2914842859/10000000000 : ℝ)*x 0 + (-3042090397/10000000000 : ℝ)*x 1 + (-836916119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2914842859/10000000000 : ℝ)^135 ≤ (4968462279213/25000000000000 : ℝ)^103 := by
    have hnat : (2914842859 : ℕ)^135*25000000000000^103 ≤ 4968462279213^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914842859 10000000000 4968462279213 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3042090397/10000000000 : ℝ)^135 ≤ (105093107269/500000000000 : ℝ)^103 := by
    have hnat : (3042090397 : ℕ)^135*500000000000^103 ≤ 105093107269^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3042090397 10000000000 105093107269 500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (836916119/1250000000 : ℝ)^135 ≤ (7388441177019/12500000000000 : ℝ)^103 := by
    have hnat : (836916119 : ℕ)^135*12500000000000^103 ≤ 7388441177019^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836916119 1250000000 7388441177019 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2914842859/10000000000 : ℝ), (-3042090397/10000000000 : ℝ), (-836916119/1250000000 : ℝ)] ![(4968462279213/25000000000000 : ℝ), (105093107269/500000000000 : ℝ), (7388441177019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2914842859/10000000000 : ℝ)|^135 ≤ (4968462279213/25000000000000 : ℝ)^103
        have hw : |(2914842859/10000000000 : ℝ)|=(2914842859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3042090397/10000000000 : ℝ)|^135 ≤ (105093107269/500000000000 : ℝ)^103
        have hw : |(-3042090397/10000000000 : ℝ)|=(3042090397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-836916119/1250000000 : ℝ)|^135 ≤ (7388441177019/12500000000000 : ℝ)^103
        have hw : |(-836916119/1250000000 : ℝ)|=(836916119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (624131987/1000000000 : ℝ)*x 0 + (5127328753/10000000000 : ℝ)*x 1 + (926675609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (624131987/1000000000 : ℝ)^135 ≤ (13477613992603/25000000000000 : ℝ)^103 := by
    have hnat : (624131987 : ℕ)^135*25000000000000^103 ≤ 13477613992603^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624131987 1000000000 13477613992603 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127328753/10000000000 : ℝ)^135 ≤ (41663932978409/100000000000000 : ℝ)^103 := by
    have hnat : (5127328753 : ℕ)^135*100000000000000^103 ≤ 41663932978409^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127328753 10000000000 41663932978409 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926675609/10000000000 : ℝ)^135 ≤ (4425611033063/100000000000000 : ℝ)^103 := by
    have hnat : (926675609 : ℕ)^135*100000000000000^103 ≤ 4425611033063^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926675609 10000000000 4425611033063 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(624131987/1000000000 : ℝ), (5127328753/10000000000 : ℝ), (926675609/10000000000 : ℝ)] ![(13477613992603/25000000000000 : ℝ), (41663932978409/100000000000000 : ℝ), (4425611033063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(624131987/1000000000 : ℝ)|^135 ≤ (13477613992603/25000000000000 : ℝ)^103
        have hw : |(624131987/1000000000 : ℝ)|=(624131987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127328753/10000000000 : ℝ)|^135 ≤ (41663932978409/100000000000000 : ℝ)^103
        have hw : |(5127328753/10000000000 : ℝ)|=(5127328753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(926675609/10000000000 : ℝ)|^135 ≤ (4425611033063/100000000000000 : ℝ)^103
        have hw : |(926675609/10000000000 : ℝ)|=(926675609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1052534419/2500000000 : ℝ)*x 0 + (3717488769/5000000000 : ℝ)*x 1 + (-5014971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052534419/2500000000 : ℝ)^135 ≤ (32179020298439/100000000000000 : ℝ)^103 := by
    have hnat : (1052534419 : ℕ)^135*100000000000000^103 ≤ 32179020298439^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052534419 2500000000 32179020298439 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3717488769/5000000000 : ℝ)^135 ≤ (8476154979279/12500000000000 : ℝ)^103 := by
    have hnat : (3717488769 : ℕ)^135*12500000000000^103 ≤ 8476154979279^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717488769 5000000000 8476154979279 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5014971/5000000000 : ℝ)^135 ≤ (5869930837/50000000000000 : ℝ)^103 := by
    have hnat : (5014971 : ℕ)^135*50000000000000^103 ≤ 5869930837^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014971 5000000000 5869930837 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052534419/2500000000 : ℝ), (3717488769/5000000000 : ℝ), (-5014971/5000000000 : ℝ)] ![(32179020298439/100000000000000 : ℝ), (8476154979279/12500000000000 : ℝ), (5869930837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052534419/2500000000 : ℝ)|^135 ≤ (32179020298439/100000000000000 : ℝ)^103
        have hw : |(1052534419/2500000000 : ℝ)|=(1052534419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3717488769/5000000000 : ℝ)|^135 ≤ (8476154979279/12500000000000 : ℝ)^103
        have hw : |(3717488769/5000000000 : ℝ)|=(3717488769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5014971/5000000000 : ℝ)|^135 ≤ (5869930837/50000000000000 : ℝ)^103
        have hw : |(-5014971/5000000000 : ℝ)|=(5014971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-823470553/2500000000 : ℝ)*x 0 + (3219402153/10000000000 : ℝ)*x 1 + (-6252206387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (823470553/2500000000 : ℝ)^135 ≤ (4665517142221/20000000000000 : ℝ)^103 := by
    have hnat : (823470553 : ℕ)^135*20000000000000^103 ≤ 4665517142221^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823470553 2500000000 4665517142221 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3219402153/10000000000 : ℝ)^135 ≤ (4527735260769/20000000000000 : ℝ)^103 := by
    have hnat : (3219402153 : ℕ)^135*20000000000000^103 ≤ 4527735260769^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3219402153 10000000000 4527735260769 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6252206387/10000000000 : ℝ)^135 ≤ (540337379711/1000000000000 : ℝ)^103 := by
    have hnat : (6252206387 : ℕ)^135*1000000000000^103 ≤ 540337379711^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6252206387 10000000000 540337379711 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-823470553/2500000000 : ℝ), (3219402153/10000000000 : ℝ), (-6252206387/10000000000 : ℝ)] ![(4665517142221/20000000000000 : ℝ), (4527735260769/20000000000000 : ℝ), (540337379711/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-823470553/2500000000 : ℝ)|^135 ≤ (4665517142221/20000000000000 : ℝ)^103
        have hw : |(-823470553/2500000000 : ℝ)|=(823470553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3219402153/10000000000 : ℝ)|^135 ≤ (4527735260769/20000000000000 : ℝ)^103
        have hw : |(3219402153/10000000000 : ℝ)|=(3219402153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6252206387/10000000000 : ℝ)|^135 ≤ (540337379711/1000000000000 : ℝ)^103
        have hw : |(-6252206387/10000000000 : ℝ)|=(6252206387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (13310663/39062500 : ℝ)*x 0 + (-814186193/2500000000 : ℝ)*x 1 + (-3063877803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13310663/39062500 : ℝ)^135 ≤ (3048514039903/12500000000000 : ℝ)^103 := by
    have hnat : (13310663 : ℕ)^135*12500000000000^103 ≤ 3048514039903^103*39062500^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13310663 39062500 3048514039903 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (814186193/2500000000 : ℝ)^135 ≤ (1436466753249/6250000000000 : ℝ)^103 := by
    have hnat : (814186193 : ℕ)^135*6250000000000^103 ≤ 1436466753249^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814186193 2500000000 1436466753249 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3063877803/5000000000 : ℝ)^135 ≤ (26314209803971/50000000000000 : ℝ)^103 := by
    have hnat : (3063877803 : ℕ)^135*50000000000000^103 ≤ 26314209803971^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3063877803 5000000000 26314209803971 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13310663/39062500 : ℝ), (-814186193/2500000000 : ℝ), (-3063877803/5000000000 : ℝ)] ![(3048514039903/12500000000000 : ℝ), (1436466753249/6250000000000 : ℝ), (26314209803971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13310663/39062500 : ℝ)|^135 ≤ (3048514039903/12500000000000 : ℝ)^103
        have hw : |(13310663/39062500 : ℝ)|=(13310663/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-814186193/2500000000 : ℝ)|^135 ≤ (1436466753249/6250000000000 : ℝ)^103
        have hw : |(-814186193/2500000000 : ℝ)|=(814186193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3063877803/5000000000 : ℝ)|^135 ≤ (26314209803971/50000000000000 : ℝ)^103
        have hw : |(-3063877803/5000000000 : ℝ)|=(3063877803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (6856353469/10000000000 : ℝ)*x 0 + (834569701/2000000000 : ℝ)*x 1 + (1345672771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6856353469/10000000000 : ℝ)^135 ≤ (15244413004547/25000000000000 : ℝ)^103 := by
    have hnat : (6856353469 : ℕ)^135*25000000000000^103 ≤ 15244413004547^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6856353469 10000000000 15244413004547 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834569701/2000000000 : ℝ)^135 ≤ (31805979238197/100000000000000 : ℝ)^103 := by
    have hnat : (834569701 : ℕ)^135*100000000000000^103 ≤ 31805979238197^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834569701 2000000000 31805979238197 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1345672771/10000000000 : ℝ)^135 ≤ (902046091261/12500000000000 : ℝ)^103 := by
    have hnat : (1345672771 : ℕ)^135*12500000000000^103 ≤ 902046091261^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345672771 10000000000 902046091261 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6856353469/10000000000 : ℝ), (834569701/2000000000 : ℝ), (1345672771/10000000000 : ℝ)] ![(15244413004547/25000000000000 : ℝ), (31805979238197/100000000000000 : ℝ), (902046091261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6856353469/10000000000 : ℝ)|^135 ≤ (15244413004547/25000000000000 : ℝ)^103
        have hw : |(6856353469/10000000000 : ℝ)|=(6856353469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834569701/2000000000 : ℝ)|^135 ≤ (31805979238197/100000000000000 : ℝ)^103
        have hw : |(834569701/2000000000 : ℝ)|=(834569701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1345672771/10000000000 : ℝ)|^135 ≤ (902046091261/12500000000000 : ℝ)^103
        have hw : |(1345672771/10000000000 : ℝ)|=(1345672771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306058_s2_s2_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (517322639/2000000000 : ℝ)*x 0 + (540479667/625000000 : ℝ)*x 1 + (-26550921/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517322639/2000000000 : ℝ)^135 ≤ (4248338804043/25000000000000 : ℝ)^103 := by
    have hnat : (517322639 : ℕ)^135*25000000000000^103 ≤ 4248338804043^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517322639 2000000000 4248338804043 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540479667/625000000 : ℝ)^135 ≤ (41329986144133/50000000000000 : ℝ)^103 := by
    have hnat : (540479667 : ℕ)^135*50000000000000^103 ≤ 41329986144133^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540479667 625000000 41329986144133 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26550921/2000000000 : ℝ)^135 ≤ (173336241831/50000000000000 : ℝ)^103 := by
    have hnat : (26550921 : ℕ)^135*50000000000000^103 ≤ 173336241831^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26550921 2000000000 173336241831 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517322639/2000000000 : ℝ), (540479667/625000000 : ℝ), (-26550921/2000000000 : ℝ)] ![(4248338804043/25000000000000 : ℝ), (41329986144133/50000000000000 : ℝ), (173336241831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517322639/2000000000 : ℝ)|^135 ≤ (4248338804043/25000000000000 : ℝ)^103
        have hw : |(517322639/2000000000 : ℝ)|=(517322639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540479667/625000000 : ℝ)|^135 ≤ (41329986144133/50000000000000 : ℝ)^103
        have hw : |(540479667/625000000 : ℝ)|=(540479667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26550921/2000000000 : ℝ)|^135 ≤ (173336241831/50000000000000 : ℝ)^103
        have hw : |(-26550921/2000000000 : ℝ)|=(26550921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306058_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((86039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77493/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77493/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-66349/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-66349/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7911/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7911/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13413/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13413/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-26953/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-26953/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (86039/100000 : ℝ) ^ (67/16 : ℝ) ≤ (53276636065468468357/100000000000000000000 : ℝ) := by
    have hpowers : (86039/100000 : ℝ)^67 ≤ (53276636065468468357/100000000000000000000 : ℝ)^16 := by
      have hnat : (86039 : ℕ)^67*100000000000000000000^16 ≤ 53276636065468468357^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86039 100000 53276636065468468357 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (86039/100000 : ℝ)) (X := (53276636065468468357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (153276636065468468357/100000000000000000000 : ℝ) ≤ (138421254113693/125000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (153276636065468468357/100000000000000000000 : ℝ)^16 ≤ (138421254113693/125000000000000 : ℝ)^67 := by
      have hnat : (153276636065468468357 : ℕ)^16*125000000000000^67 ≤ 138421254113693^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        153276636065468468357 100000000000000000000 138421254113693 125000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (138421254113693/125000000000000 : ℝ)) (X := (153276636065468468357/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (103276636065468468357/50000000000000000000 : ℝ) ≤ (11891360387259509/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (103276636065468468357/50000000000000000000 : ℝ)^16 ≤ (11891360387259509/10000000000000000 : ℝ)^67 := by
      have hnat : (103276636065468468357 : ℕ)^16*10000000000000000^67 ≤ 11891360387259509^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103276636065468468357 50000000000000000000 11891360387259509 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11891360387259509/10000000000000000 : ℝ)) (X := (103276636065468468357/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13421254113693/107548750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(817660058164069/8603900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (86039/100000 : ℝ)) (alpha := (13421254113693/107548750000000 : ℝ)) (beta := (817660058164069/8603900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (86039/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13421254113693/107548750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(817660058164069/8603900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (77493/100000 : ℝ) ^ (67/16 : ℝ) ≤ (8594618801502416471/25000000000000000000 : ℝ) := by
    have hpowers : (77493/100000 : ℝ)^67 ≤ (8594618801502416471/25000000000000000000 : ℝ)^16 := by
      have hnat : (77493 : ℕ)^67*25000000000000000000^16 ≤ 8594618801502416471^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77493 100000 8594618801502416471 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77493/100000 : ℝ)) (X := (8594618801502416471/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (33594618801502416471/25000000000000000000 : ℝ) ≤ (268278524612931/250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (33594618801502416471/25000000000000000000 : ℝ)^16 ≤ (268278524612931/250000000000000 : ℝ)^67 := by
      have hnat : (33594618801502416471 : ℕ)^16*250000000000000^67 ≤ 268278524612931^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33594618801502416471 25000000000000000000 268278524612931 250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (268278524612931/250000000000000 : ℝ)) (X := (33594618801502416471/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (21094618801502416471/12500000000000000000 : ℝ) ≤ (5665541793667941/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (21094618801502416471/12500000000000000000 : ℝ)^16 ≤ (5665541793667941/5000000000000000 : ℝ)^67 := by
      have hnat : (21094618801502416471 : ℕ)^16*5000000000000000^67 ≤ 5665541793667941^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21094618801502416471 12500000000000000000 5665541793667941 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5665541793667941/5000000000000000 : ℝ)) (X := (21094618801502416471/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(18278524612931/193732500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(99990433803107/1291550000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (77493/100000 : ℝ)) (alpha := (18278524612931/193732500000000 : ℝ)) (beta := (99990433803107/1291550000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (77493/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(18278524612931/193732500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(99990433803107/1291550000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (66349/100000 : ℝ) ^ (67/16 : ℝ) ≤ (17944504600357710579/100000000000000000000 : ℝ) := by
    have hpowers : (66349/100000 : ℝ)^67 ≤ (17944504600357710579/100000000000000000000 : ℝ)^16 := by
      have hnat : (66349 : ℕ)^67*100000000000000000000^16 ≤ 17944504600357710579^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66349 100000 17944504600357710579 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66349/100000 : ℝ)) (X := (17944504600357710579/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (117944504600357710579/100000000000000000000 : ℝ) ≤ (10402005168051793/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (117944504600357710579/100000000000000000000 : ℝ)^16 ≤ (10402005168051793/10000000000000000 : ℝ)^67 := by
      have hnat : (117944504600357710579 : ℕ)^16*10000000000000000^67 ≤ 10402005168051793^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117944504600357710579 100000000000000000000 10402005168051793 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10402005168051793/10000000000000000 : ℝ)) (X := (117944504600357710579/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (67944504600357710579/50000000000000000000 : ℝ) ≤ (10759825141327739/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (67944504600357710579/50000000000000000000 : ℝ)^16 ≤ (10759825141327739/10000000000000000 : ℝ)^67 := by
      have hnat : (67944504600357710579 : ℕ)^16*10000000000000000^67 ≤ 10759825141327739^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67944504600357710579 50000000000000000000 10759825141327739 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10759825141327739/10000000000000000 : ℝ)) (X := (67944504600357710579/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(402005168051793/6634900000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(178909986637973/3317450000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (66349/100000 : ℝ)) (alpha := (402005168051793/6634900000000000 : ℝ)) (beta := (178909986637973/3317450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (66349/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(402005168051793/6634900000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(178909986637973/3317450000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3401635511/10000000000 : ℝ)*X 0 0+(1648854667/5000000000 : ℝ)*X 0 1+(-3049459453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4121331657/10000000000 : ℝ)*X 0 0+(7127544613/10000000000 : ℝ)*X 0 1+(-946420053/10000000000 : ℝ)*X 0 2+(4121331657/10000000000 : ℝ)*X 1 0+(7127544613/10000000000 : ℝ)*X 1 1+(-946420053/10000000000 : ℝ)*X 1 2+(4121331657/10000000000 : ℝ)*X 2 0+(7127544613/10000000000 : ℝ)*X 2 1+(-946420053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-120100849/400000000 : ℝ)*X 0 0+(278456111/1000000000 : ℝ)*X 0 1+(-1365150921/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((3142291161/10000000000 : ℝ)*X 1 0+(-351513627/1250000000 : ℝ)*X 1 1+(-3347707453/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((5639421793/10000000000 : ℝ)*X 2 0+(5539570533/10000000000 : ℝ)*X 2 1+(635130557/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((985950077/2500000000 : ℝ)*X 0 0+(7655808039/10000000000 : ℝ)*X 0 1+(-6147/31250000 : ℝ)*X 0 2+(985950077/2500000000 : ℝ)*X 1 0+(7655808039/10000000000 : ℝ)*X 1 1+(-6147/31250000 : ℝ)*X 1 2+(985950077/2500000000 : ℝ)*X 2 0+(7655808039/10000000000 : ℝ)*X 2 1+(-6147/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1427188603/5000000000 : ℝ)*X 0 0+(586784821/2000000000 : ℝ)*X 0 1+(-682566769/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2914842859/10000000000 : ℝ)*X 1 0+(-3042090397/10000000000 : ℝ)*X 1 1+(-836916119/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((624131987/1000000000 : ℝ)*X 2 0+(5127328753/10000000000 : ℝ)*X 2 1+(926675609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1052534419/2500000000 : ℝ)*X 0 0+(3717488769/5000000000 : ℝ)*X 0 1+(-5014971/5000000000 : ℝ)*X 0 2+(1052534419/2500000000 : ℝ)*X 1 0+(3717488769/5000000000 : ℝ)*X 1 1+(-5014971/5000000000 : ℝ)*X 1 2+(1052534419/2500000000 : ℝ)*X 2 0+(3717488769/5000000000 : ℝ)*X 2 1+(-5014971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-823470553/2500000000 : ℝ)*X 0 0+(3219402153/10000000000 : ℝ)*X 0 1+(-6252206387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((13310663/39062500 : ℝ)*X 1 0+(-814186193/2500000000 : ℝ)*X 1 1+(-3063877803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((6856353469/10000000000 : ℝ)*X 2 0+(834569701/2000000000 : ℝ)*X 2 1+(1345672771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((517322639/2000000000 : ℝ)*X 0 0+(540479667/625000000 : ℝ)*X 0 1+(-26550921/2000000000 : ℝ)*X 0 2+(517322639/2000000000 : ℝ)*X 1 0+(540479667/625000000 : ℝ)*X 1 1+(-26550921/2000000000 : ℝ)*X 1 2+(517322639/2000000000 : ℝ)*X 2 0+(540479667/625000000 : ℝ)*X 2 1+(-26550921/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306058_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((7911/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7911/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3825442473540639/500000000000000000000 : ℝ) := by norm_num
    linear_combination (96617253/1600000000 : ℝ)*(base5) + (1217821/250000000000 : ℝ)*(base12) + (358481/200000000000 : ℝ)*(base59) + (392449825253/250000000000 : ℝ)*(base60) + (262924283109/31250000000 : ℝ)*(major_s2_0) + (262924283109/31250000000 : ℝ)*(major_s2_1) + (262924283109/31250000000 : ℝ)*(major_s2_2) + (5658151/1000000000000 : ℝ)*(sp_s2_6) + (11370375616043/1000000000000 : ℝ)*(sp_s2_7) + (227405834179/20000000000 : ℝ)*(sp_s2_8) + (2857691567613/250000000000 : ℝ)*(sp_s2_9) + (5396336708883/1000000000000 : ℝ)*(sp_s2_13) + (88778377/1000000000000 : ℝ)*(sp_s2_15) + (4293119/100000000000 : ℝ)*(sp_s2_27) + (5456771081349/1000000000000 : ℝ)*(f.failure) + (11370380487327/1000000000000 : ℝ)*(f.sum) + (6130354156739862629/42846525475000000000000000000000 : ℝ)*base63 + (857779886118813/1658725000000000000000000000 : ℝ)*base64 + (24207640693933/40360937500000000000000000 : ℝ)*base67 + (857820128650211/1658725000000000000000000000 : ℝ)*base68 + (28415937634091220171/285430080550000000000000000000000 : ℝ)*base71 + (2736696989114351/4301950000000000000000000000 : ℝ)*base73 + (220784387405863/258310000000000000000000000 : ℝ)*base74 + (161369788863693/215097500000000000000000000 : ℝ)*base76 + (2904868758566173767/22224734090000000000000000000000 : ℝ)*base78 + (38457/50000000000000000 : ℝ)*base87 + (38457/50000000000000000 : ℝ)*base89 + (38457/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13413/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13413/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (72137713887681380092060884300657/3686472205343525000000000000000000000 : ℝ) := by norm_num
    linear_combination (4056533384801/1000000000000 : ℝ)*(base5) + (329711/125000000000 : ℝ)*(base18) + (174259/50000000000 : ℝ)*(base49) + (1052299/200000000000 : ℝ)*(base53) + (1935185718887/500000000000 : ℝ)*(base60) + (7937760168579/1000000000000 : ℝ)*(major_s2_0) + (7937760168579/1000000000000 : ℝ)*(major_s2_1) + (1984438726771/250000000000 : ℝ)*(major_s2_2) + (9778211/100000000000 : ℝ)*(sp_s2_8) + (15723959/200000000000 : ℝ)*(sp_s2_13) + (268183418871/25000000000 : ℝ)*(sp_s2_14) + (5363618167521/500000000000 : ℝ)*(sp_s2_15) + (2956775080227/200000000000 : ℝ)*(sp_s2_16) + (1091559793479/1000000000000 : ℝ)*(sp_s2_20) + (2574085899037/500000000000 : ℝ)*(f.failure) + (2145468403267/200000000000 : ℝ)*(f.sum) + (13860014475344260863/42846525475000000000000000000000 : ℝ)*base62 + (1425124397671983/3317450000000000000000000000 : ℝ)*base64 + (457349878512743/1291550000000000000000000000 : ℝ)*base67 + (348471911359773/1658725000000000000000000000 : ℝ)*base68 + (157892584866775975347/285430080550000000000000000000000 : ℝ)*base70 + (1881678711246131/8603900000000000000000000000 : ℝ)*base73 + (32919042848999/129155000000000000000000000 : ℝ)*base75 + (18427622513571/430195000000000000000000000 : ℝ)*base76 + (7453248313405343777/44449468180000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (15559/25000000000000000 : ℝ)*base86 + (15559/25000000000000000 : ℝ)*base88 + (15559/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-26953/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-26953/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (60185073698666312370580811764719/7372944410687050000000000000000000000 : ℝ) := by norm_num
    linear_combination (2740251/1000000000000 : ℝ)*(base15) + (1559027/500000000000 : ℝ)*(base16) + (1571183507/500000000000 : ℝ)*(base49) + (114535500411/500000000000 : ℝ)*(base60) + (493768813657/125000000000 : ℝ)*(major_s2_0) + (493768813657/125000000000 : ℝ)*(major_s2_1) + (493768813657/125000000000 : ℝ)*(major_s2_2) + (48743413/500000000000 : ℝ)*(sp_s2_0) + (35513933/1000000000000 : ℝ)*(sp_s2_13) + (9623529/200000000000 : ℝ)*(sp_s2_16) + (5338262301841/1000000000000 : ℝ)*(sp_s2_21) + (5338353930361/1000000000000 : ℝ)*(sp_s2_22) + (2669155835511/500000000000 : ℝ)*(sp_s2_23) + (2561902994917/1000000000000 : ℝ)*(sp_s2_27) + (2561938508851/1000000000000 : ℝ)*(f.failure) + (5338359788667/1000000000000 : ℝ)*(f.sum) + (146095020468956118023/257079152850000000000000000000000 : ℝ)*base63 + (127729568103741/414681250000000000000000000 : ℝ)*base65 + (53604644160577/80721875000000000000000000 : ℝ)*base67 + (1629783650079681/3317450000000000000000000000 : ℝ)*base69 + (125770325154505916567/285430080550000000000000000000000 : ℝ)*base71 + (1210932555741177/4301950000000000000000000000 : ℝ)*base73 + (336829849166627/774930000000000000000000000 : ℝ)*base74 + (5070974569457/86039000000000000000000000 : ℝ)*base76 + (283905655085247739/11112367045000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (50143/50000000000000000 : ℝ)*base87 + (50143/50000000000000000 : ℝ)*base89 + (50143/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((86039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(77493/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(77493/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-66349/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-66349/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7911/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7911/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13413/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13413/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-26953/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-26953/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306058_s2 p hpa hpb X hX hprev1

#print axioms solution
