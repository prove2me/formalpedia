-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c304059_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:46:38.676635+00:00
-- url     : https://prove2.me/submissions/a967a279-f05c-4e2c-a6d5-2cfe284cbaca

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
theorem collision_support_c304059_s5_s5_1 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1693869113/5000000000 : ℝ)*x 0 + (-3365154411/10000000000 : ℝ)*x 1 + (6097290941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1693869113/5000000000 : ℝ)^133 ≤ (24041988738697/100000000000000 : ℝ)^101 := by
    have hnat : (1693869113 : ℕ)^133*100000000000000^101 ≤ 24041988738697^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1693869113 5000000000 24041988738697 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3365154411/10000000000 : ℝ)^133 ≤ (476623212337/2000000000000 : ℝ)^101 := by
    have hnat : (3365154411 : ℕ)^133*2000000000000^101 ≤ 476623212337^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3365154411 10000000000 476623212337 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6097290941/10000000000 : ℝ)^133 ≤ (26063425313427/50000000000000 : ℝ)^101 := by
    have hnat : (6097290941 : ℕ)^133*50000000000000^101 ≤ 26063425313427^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6097290941 10000000000 26063425313427 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1693869113/5000000000 : ℝ), (-3365154411/10000000000 : ℝ), (6097290941/10000000000 : ℝ)] ![(24041988738697/100000000000000 : ℝ), (476623212337/2000000000000 : ℝ), (26063425313427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1693869113/5000000000 : ℝ)|^133 ≤ (24041988738697/100000000000000 : ℝ)^101
        have hw : |(1693869113/5000000000 : ℝ)|=(1693869113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3365154411/10000000000 : ℝ)|^133 ≤ (476623212337/2000000000000 : ℝ)^101
        have hw : |(-3365154411/10000000000 : ℝ)|=(3365154411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6097290941/10000000000 : ℝ)|^133 ≤ (26063425313427/50000000000000 : ℝ)^101
        have hw : |(6097290941/10000000000 : ℝ)|=(6097290941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_2 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5857703769/10000000000 : ℝ)*x 0 + (1128319091/2000000000 : ℝ)*x 1 + (-97903689/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5857703769/10000000000 : ℝ)^133 ≤ (6180820068777/12500000000000 : ℝ)^101 := by
    have hnat : (5857703769 : ℕ)^133*12500000000000^101 ≤ 6180820068777^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5857703769 10000000000 6180820068777 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128319091/2000000000 : ℝ)^133 ≤ (47058512934009/100000000000000 : ℝ)^101 := by
    have hnat : (1128319091 : ℕ)^133*100000000000000^101 ≤ 47058512934009^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128319091 2000000000 47058512934009 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97903689/1250000000 : ℝ)^133 ≤ (3494926502617/100000000000000 : ℝ)^101 := by
    have hnat : (97903689 : ℕ)^133*100000000000000^101 ≤ 3494926502617^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97903689 1250000000 3494926502617 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5857703769/10000000000 : ℝ), (1128319091/2000000000 : ℝ), (-97903689/1250000000 : ℝ)] ![(6180820068777/12500000000000 : ℝ), (47058512934009/100000000000000 : ℝ), (3494926502617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5857703769/10000000000 : ℝ)|^133 ≤ (6180820068777/12500000000000 : ℝ)^101
        have hw : |(5857703769/10000000000 : ℝ)|=(5857703769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128319091/2000000000 : ℝ)|^133 ≤ (47058512934009/100000000000000 : ℝ)^101
        have hw : |(1128319091/2000000000 : ℝ)|=(1128319091/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97903689/1250000000 : ℝ)|^133 ≤ (3494926502617/100000000000000 : ℝ)^101
        have hw : |(-97903689/1250000000 : ℝ)|=(97903689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_6 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4358614711/10000000000 : ℝ)*x 0 + (978701989/2000000000 : ℝ)*x 1 + (3749387661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358614711/10000000000 : ℝ)^133 ≤ (33502919383537/100000000000000 : ℝ)^101 := by
    have hnat : (4358614711 : ℕ)^133*100000000000000^101 ≤ 33502919383537^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358614711 10000000000 33502919383537 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978701989/2000000000 : ℝ)^133 ≤ (39019563612971/100000000000000 : ℝ)^101 := by
    have hnat : (978701989 : ℕ)^133*100000000000000^101 ≤ 39019563612971^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978701989 2000000000 39019563612971 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3749387661/10000000000 : ℝ)^133 ≤ (68693792477/250000000000 : ℝ)^101 := by
    have hnat : (3749387661 : ℕ)^133*250000000000^101 ≤ 68693792477^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3749387661 10000000000 68693792477 250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358614711/10000000000 : ℝ), (978701989/2000000000 : ℝ), (3749387661/10000000000 : ℝ)] ![(33502919383537/100000000000000 : ℝ), (39019563612971/100000000000000 : ℝ), (68693792477/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358614711/10000000000 : ℝ)|^133 ≤ (33502919383537/100000000000000 : ℝ)^101
        have hw : |(4358614711/10000000000 : ℝ)|=(4358614711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(978701989/2000000000 : ℝ)|^133 ≤ (39019563612971/100000000000000 : ℝ)^101
        have hw : |(978701989/2000000000 : ℝ)|=(978701989/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3749387661/10000000000 : ℝ)|^133 ≤ (68693792477/250000000000 : ℝ)^101
        have hw : |(3749387661/10000000000 : ℝ)|=(3749387661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_7 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1552430131/5000000000 : ℝ)*x 0 + (2753799937/10000000000 : ℝ)*x 1 + (3403681943/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1552430131/5000000000 : ℝ)^133 ≤ (21434082085151/100000000000000 : ℝ)^101 := by
    have hnat : (1552430131 : ℕ)^133*100000000000000^101 ≤ 21434082085151^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1552430131 5000000000 21434082085151 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2753799937/10000000000 : ℝ)^133 ≤ (3660287648929/20000000000000 : ℝ)^101 := by
    have hnat : (2753799937 : ℕ)^133*20000000000000^101 ≤ 3660287648929^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753799937 10000000000 3660287648929 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3403681943/5000000000 : ℝ)^133 ≤ (30132239831009/50000000000000 : ℝ)^101 := by
    have hnat : (3403681943 : ℕ)^133*50000000000000^101 ≤ 30132239831009^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3403681943 5000000000 30132239831009 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1552430131/5000000000 : ℝ), (2753799937/10000000000 : ℝ), (3403681943/5000000000 : ℝ)] ![(21434082085151/100000000000000 : ℝ), (3660287648929/20000000000000 : ℝ), (30132239831009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1552430131/5000000000 : ℝ)|^133 ≤ (21434082085151/100000000000000 : ℝ)^101
        have hw : |(-1552430131/5000000000 : ℝ)|=(1552430131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2753799937/10000000000 : ℝ)|^133 ≤ (3660287648929/20000000000000 : ℝ)^101
        have hw : |(2753799937/10000000000 : ℝ)|=(2753799937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3403681943/5000000000 : ℝ)|^133 ≤ (30132239831009/50000000000000 : ℝ)^101
        have hw : |(3403681943/5000000000 : ℝ)|=(3403681943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_8 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (124407639/400000000 : ℝ)*x 0 + (-338444039/1250000000 : ℝ)*x 1 + (683781003/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (124407639/400000000 : ℝ)^133 ≤ (859302188041/4000000000000 : ℝ)^101 := by
    have hnat : (124407639 : ℕ)^133*4000000000000^101 ≤ 859302188041^101*400000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124407639 400000000 859302188041 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338444039/1250000000 : ℝ)^133 ≤ (357955650419/2000000000000 : ℝ)^101 := by
    have hnat : (338444039 : ℕ)^133*2000000000000^101 ≤ 357955650419^101*1250000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338444039 1250000000 357955650419 2000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683781003/1000000000 : ℝ)^133 ≤ (60619662762299/100000000000000 : ℝ)^101 := by
    have hnat : (683781003 : ℕ)^133*100000000000000^101 ≤ 60619662762299^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683781003 1000000000 60619662762299 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(124407639/400000000 : ℝ), (-338444039/1250000000 : ℝ), (683781003/1000000000 : ℝ)] ![(859302188041/4000000000000 : ℝ), (357955650419/2000000000000 : ℝ), (60619662762299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(124407639/400000000 : ℝ)|^133 ≤ (859302188041/4000000000000 : ℝ)^101
        have hw : |(124407639/400000000 : ℝ)|=(124407639/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-338444039/1250000000 : ℝ)|^133 ≤ (357955650419/2000000000000 : ℝ)^101
        have hw : |(-338444039/1250000000 : ℝ)|=(338444039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683781003/1000000000 : ℝ)|^133 ≤ (60619662762299/100000000000000 : ℝ)^101
        have hw : |(683781003/1000000000 : ℝ)|=(683781003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_9 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5500117153/10000000000 : ℝ)*x 0 + (628289733/1000000000 : ℝ)*x 1 + (-109801731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5500117153/10000000000 : ℝ)^133 ≤ (45510703086173/100000000000000 : ℝ)^101 := by
    have hnat : (5500117153 : ℕ)^133*100000000000000^101 ≤ 45510703086173^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500117153 10000000000 45510703086173 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628289733/1000000000 : ℝ)^133 ≤ (3389148992443/6250000000000 : ℝ)^101 := by
    have hnat : (628289733 : ℕ)^133*6250000000000^101 ≤ 3389148992443^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628289733 1000000000 3389148992443 6250000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109801731/10000000000 : ℝ)^133 ≤ (131456511079/50000000000000 : ℝ)^101 := by
    have hnat : (109801731 : ℕ)^133*50000000000000^101 ≤ 131456511079^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109801731 10000000000 131456511079 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5500117153/10000000000 : ℝ), (628289733/1000000000 : ℝ), (-109801731/10000000000 : ℝ)] ![(45510703086173/100000000000000 : ℝ), (3389148992443/6250000000000 : ℝ), (131456511079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5500117153/10000000000 : ℝ)|^133 ≤ (45510703086173/100000000000000 : ℝ)^101
        have hw : |(5500117153/10000000000 : ℝ)|=(5500117153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(628289733/1000000000 : ℝ)|^133 ≤ (3389148992443/6250000000000 : ℝ)^101
        have hw : |(628289733/1000000000 : ℝ)|=(628289733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109801731/10000000000 : ℝ)|^133 ≤ (131456511079/50000000000000 : ℝ)^101
        have hw : |(-109801731/10000000000 : ℝ)|=(109801731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_13 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3891474711/10000000000 : ℝ)*x 0 + (3226586431/5000000000 : ℝ)*x 1 + (2364482583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3891474711/10000000000 : ℝ)^133 ≤ (7214220582713/25000000000000 : ℝ)^101 := by
    have hnat : (3891474711 : ℕ)^133*25000000000000^101 ≤ 7214220582713^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3891474711 10000000000 7214220582713 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3226586431/5000000000 : ℝ)^133 ≤ (56169874408951/100000000000000 : ℝ)^101 := by
    have hnat : (3226586431 : ℕ)^133*100000000000000^101 ≤ 56169874408951^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3226586431 5000000000 56169874408951 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2364482583/10000000000 : ℝ)^133 ≤ (14973243244673/100000000000000 : ℝ)^101 := by
    have hnat : (2364482583 : ℕ)^133*100000000000000^101 ≤ 14973243244673^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2364482583 10000000000 14973243244673 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3891474711/10000000000 : ℝ), (3226586431/5000000000 : ℝ), (2364482583/10000000000 : ℝ)] ![(7214220582713/25000000000000 : ℝ), (56169874408951/100000000000000 : ℝ), (14973243244673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3891474711/10000000000 : ℝ)|^133 ≤ (7214220582713/25000000000000 : ℝ)^101
        have hw : |(3891474711/10000000000 : ℝ)|=(3891474711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3226586431/5000000000 : ℝ)|^133 ≤ (56169874408951/100000000000000 : ℝ)^101
        have hw : |(3226586431/5000000000 : ℝ)|=(3226586431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2364482583/10000000000 : ℝ)|^133 ≤ (14973243244673/100000000000000 : ℝ)^101
        have hw : |(2364482583/10000000000 : ℝ)|=(2364482583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_14 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1378242329/5000000000 : ℝ)*x 0 + (3101157767/10000000000 : ℝ)*x 1 + (6808234759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378242329/5000000000 : ℝ)^133 ≤ (18324937241079/100000000000000 : ℝ)^101 := by
    have hnat : (1378242329 : ℕ)^133*100000000000000^101 ≤ 18324937241079^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378242329 5000000000 18324937241079 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3101157767/10000000000 : ℝ)^133 ≤ (10700215250767/50000000000000 : ℝ)^101 := by
    have hnat : (3101157767 : ℕ)^133*50000000000000^101 ≤ 10700215250767^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3101157767 10000000000 10700215250767 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6808234759/10000000000 : ℝ)^133 ≤ (482197057921/800000000000 : ℝ)^101 := by
    have hnat : (6808234759 : ℕ)^133*800000000000^101 ≤ 482197057921^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6808234759 10000000000 482197057921 800000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1378242329/5000000000 : ℝ), (3101157767/10000000000 : ℝ), (6808234759/10000000000 : ℝ)] ![(18324937241079/100000000000000 : ℝ), (10700215250767/50000000000000 : ℝ), (482197057921/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1378242329/5000000000 : ℝ)|^133 ≤ (18324937241079/100000000000000 : ℝ)^101
        have hw : |(-1378242329/5000000000 : ℝ)|=(1378242329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3101157767/10000000000 : ℝ)|^133 ≤ (10700215250767/50000000000000 : ℝ)^101
        have hw : |(3101157767/10000000000 : ℝ)|=(3101157767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6808234759/10000000000 : ℝ)|^133 ≤ (482197057921/800000000000 : ℝ)^101
        have hw : |(6808234759/10000000000 : ℝ)|=(6808234759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_15 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1368873677/5000000000 : ℝ)*x 0 + (-616015507/2000000000 : ℝ)*x 1 + (6838681689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1368873677/5000000000 : ℝ)^133 ≤ (18161083771039/100000000000000 : ℝ)^101 := by
    have hnat : (1368873677 : ℕ)^133*100000000000000^101 ≤ 18161083771039^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368873677 5000000000 18161083771039 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (616015507/2000000000 : ℝ)^133 ≤ (5302269333119/25000000000000 : ℝ)^101 := by
    have hnat : (616015507 : ℕ)^133*25000000000000^101 ≤ 5302269333119^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616015507 2000000000 5302269333119 25000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6838681689/10000000000 : ℝ)^133 ≤ (60629838880451/100000000000000 : ℝ)^101 := by
    have hnat : (6838681689 : ℕ)^133*100000000000000^101 ≤ 60629838880451^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6838681689 10000000000 60629838880451 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1368873677/5000000000 : ℝ), (-616015507/2000000000 : ℝ), (6838681689/10000000000 : ℝ)] ![(18161083771039/100000000000000 : ℝ), (5302269333119/25000000000000 : ℝ), (60629838880451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1368873677/5000000000 : ℝ)|^133 ≤ (18161083771039/100000000000000 : ℝ)^101
        have hw : |(1368873677/5000000000 : ℝ)|=(1368873677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-616015507/2000000000 : ℝ)|^133 ≤ (5302269333119/25000000000000 : ℝ)^101
        have hw : |(-616015507/2000000000 : ℝ)|=(616015507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6838681689/10000000000 : ℝ)|^133 ≤ (60629838880451/100000000000000 : ℝ)^101
        have hw : |(6838681689/10000000000 : ℝ)|=(6838681689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_16 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3281858663/5000000000 : ℝ)*x 0 + (1040565201/2000000000 : ℝ)*x 1 + (-108930703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3281858663/5000000000 : ℝ)^133 ≤ (11488072042867/20000000000000 : ℝ)^101 := by
    have hnat : (3281858663 : ℕ)^133*20000000000000^101 ≤ 11488072042867^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3281858663 5000000000 11488072042867 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040565201/2000000000 : ℝ)^133 ≤ (1691978788269/4000000000000 : ℝ)^101 := by
    have hnat : (1040565201 : ℕ)^133*4000000000000^101 ≤ 1691978788269^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040565201 2000000000 1691978788269 4000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108930703/10000000000 : ℝ)^133 ≤ (260170070239/100000000000000 : ℝ)^101 := by
    have hnat : (108930703 : ℕ)^133*100000000000000^101 ≤ 260170070239^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108930703 10000000000 260170070239 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3281858663/5000000000 : ℝ), (1040565201/2000000000 : ℝ), (-108930703/10000000000 : ℝ)] ![(11488072042867/20000000000000 : ℝ), (1691978788269/4000000000000 : ℝ), (260170070239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3281858663/5000000000 : ℝ)|^133 ≤ (11488072042867/20000000000000 : ℝ)^101
        have hw : |(3281858663/5000000000 : ℝ)|=(3281858663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040565201/2000000000 : ℝ)|^133 ≤ (1691978788269/4000000000000 : ℝ)^101
        have hw : |(1040565201/2000000000 : ℝ)|=(1040565201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108930703/10000000000 : ℝ)|^133 ≤ (260170070239/100000000000000 : ℝ)^101
        have hw : |(-108930703/10000000000 : ℝ)|=(108930703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_20 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5815284343/10000000000 : ℝ)*x 0 + (921913943/2000000000 : ℝ)*x 1 + (9229341/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5815284343/10000000000 : ℝ)^133 ≤ (48975578444057/100000000000000 : ℝ)^101 := by
    have hnat : (5815284343 : ℕ)^133*100000000000000^101 ≤ 48975578444057^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5815284343 10000000000 48975578444057 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921913943/2000000000 : ℝ)^133 ≤ (18032973581729/50000000000000 : ℝ)^101 := by
    have hnat : (921913943 : ℕ)^133*50000000000000^101 ≤ 18032973581729^101*2000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921913943 2000000000 18032973581729 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9229341/39062500 : ℝ)^133 ≤ (14958474369761/100000000000000 : ℝ)^101 := by
    have hnat : (9229341 : ℕ)^133*100000000000000^101 ≤ 14958474369761^101*39062500^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9229341 39062500 14958474369761 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5815284343/10000000000 : ℝ), (921913943/2000000000 : ℝ), (9229341/39062500 : ℝ)] ![(48975578444057/100000000000000 : ℝ), (18032973581729/50000000000000 : ℝ), (14958474369761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5815284343/10000000000 : ℝ)|^133 ≤ (48975578444057/100000000000000 : ℝ)^101
        have hw : |(5815284343/10000000000 : ℝ)|=(5815284343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921913943/2000000000 : ℝ)|^133 ≤ (18032973581729/50000000000000 : ℝ)^101
        have hw : |(921913943/2000000000 : ℝ)|=(921913943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9229341/39062500 : ℝ)|^133 ≤ (14958474369761/100000000000000 : ℝ)^101
        have hw : |(9229341/39062500 : ℝ)|=(9229341/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_21 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-3431802963/10000000000 : ℝ)*x 0 + (1713330139/5000000000 : ℝ)*x 1 + (375583753/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3431802963/10000000000 : ℝ)^133 ≤ (24454630636073/100000000000000 : ℝ)^101 := by
    have hnat : (3431802963 : ℕ)^133*100000000000000^101 ≤ 24454630636073^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3431802963 10000000000 24454630636073 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1713330139/5000000000 : ℝ)^133 ≤ (12203192623777/50000000000000 : ℝ)^101 := by
    have hnat : (1713330139 : ℕ)^133*50000000000000^101 ≤ 12203192623777^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1713330139 5000000000 12203192623777 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (375583753/625000000 : ℝ)^133 ≤ (51138984106529/100000000000000 : ℝ)^101 := by
    have hnat : (375583753 : ℕ)^133*100000000000000^101 ≤ 51138984106529^101*625000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375583753 625000000 51138984106529 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3431802963/10000000000 : ℝ), (1713330139/5000000000 : ℝ), (375583753/625000000 : ℝ)] ![(24454630636073/100000000000000 : ℝ), (12203192623777/50000000000000 : ℝ), (51138984106529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3431802963/10000000000 : ℝ)|^133 ≤ (24454630636073/100000000000000 : ℝ)^101
        have hw : |(-3431802963/10000000000 : ℝ)|=(3431802963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1713330139/5000000000 : ℝ)|^133 ≤ (12203192623777/50000000000000 : ℝ)^101
        have hw : |(1713330139/5000000000 : ℝ)|=(1713330139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(375583753/625000000 : ℝ)|^133 ≤ (51138984106529/100000000000000 : ℝ)^101
        have hw : |(375583753/625000000 : ℝ)|=(375583753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_22 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3395952591/10000000000 : ℝ)*x 0 + (-3387990451/10000000000 : ℝ)*x 1 + (6071515599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3395952591/10000000000 : ℝ)^133 ≤ (602969587099/2500000000000 : ℝ)^101 := by
    have hnat : (3395952591 : ℕ)^133*2500000000000^101 ≤ 602969587099^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3395952591 10000000000 602969587099 2500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3387990451/10000000000 : ℝ)^133 ≤ (24044345871571/100000000000000 : ℝ)^101 := by
    have hnat : (3387990451 : ℕ)^133*100000000000000^101 ≤ 24044345871571^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3387990451 10000000000 24044345871571 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6071515599/10000000000 : ℝ)^133 ≤ (25918435309851/50000000000000 : ℝ)^101 := by
    have hnat : (6071515599 : ℕ)^133*50000000000000^101 ≤ 25918435309851^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6071515599 10000000000 25918435309851 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3395952591/10000000000 : ℝ), (-3387990451/10000000000 : ℝ), (6071515599/10000000000 : ℝ)] ![(602969587099/2500000000000 : ℝ), (24044345871571/100000000000000 : ℝ), (25918435309851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3395952591/10000000000 : ℝ)|^133 ≤ (602969587099/2500000000000 : ℝ)^101
        have hw : |(3395952591/10000000000 : ℝ)|=(3395952591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3387990451/10000000000 : ℝ)|^133 ≤ (24044345871571/100000000000000 : ℝ)^101
        have hw : |(-3387990451/10000000000 : ℝ)|=(3387990451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6071515599/10000000000 : ℝ)|^133 ≤ (25918435309851/50000000000000 : ℝ)^101
        have hw : |(6071515599/10000000000 : ℝ)|=(6071515599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_23 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (699733291/1000000000 : ℝ)*x 0 + (142569561/312500000 : ℝ)*x 1 + (-249693027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (699733291/1000000000 : ℝ)^133 ≤ (31244404784273/50000000000000 : ℝ)^101 := by
    have hnat : (699733291 : ℕ)^133*50000000000000^101 ≤ 31244404784273^101*1000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699733291 1000000000 31244404784273 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (142569561/312500000 : ℝ)^133 ≤ (4447369491947/12500000000000 : ℝ)^101 := by
    have hnat : (142569561 : ℕ)^133*12500000000000^101 ≤ 4447369491947^101*312500000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142569561 312500000 4447369491947 12500000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249693027/5000000000 : ℝ)^133 ≤ (966117238443/50000000000000 : ℝ)^101 := by
    have hnat : (249693027 : ℕ)^133*50000000000000^101 ≤ 966117238443^101*5000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249693027 5000000000 966117238443 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(699733291/1000000000 : ℝ), (142569561/312500000 : ℝ), (-249693027/5000000000 : ℝ)] ![(31244404784273/50000000000000 : ℝ), (4447369491947/12500000000000 : ℝ), (966117238443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(699733291/1000000000 : ℝ)|^133 ≤ (31244404784273/50000000000000 : ℝ)^101
        have hw : |(699733291/1000000000 : ℝ)|=(699733291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(142569561/312500000 : ℝ)|^133 ≤ (4447369491947/12500000000000 : ℝ)^101
        have hw : |(142569561/312500000 : ℝ)|=(142569561/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249693027/5000000000 : ℝ)|^133 ≤ (966117238443/50000000000000 : ℝ)^101
        have hw : |(-249693027/5000000000 : ℝ)|=(249693027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c304059_s5_s5_27 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2221912141/10000000000 : ℝ)*x 0 + (7200204183/10000000000 : ℝ)*x 1 + (773039987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2221912141/10000000000 : ℝ)^133 ≤ (2759175062271/20000000000000 : ℝ)^101 := by
    have hnat : (2221912141 : ℕ)^133*20000000000000^101 ≤ 2759175062271^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2221912141 10000000000 2759175062271 20000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7200204183/10000000000 : ℝ)^133 ≤ (32442710667079/50000000000000 : ℝ)^101 := by
    have hnat : (7200204183 : ℕ)^133*50000000000000^101 ≤ 32442710667079^101*10000000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7200204183 10000000000 32442710667079 50000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773039987/2500000000 : ℝ)^133 ≤ (21318703347773/100000000000000 : ℝ)^101 := by
    have hnat : (773039987 : ℕ)^133*100000000000000^101 ≤ 21318703347773^101*2500000000^133 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773039987 2500000000 21318703347773 100000000000000 133 101 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (133/32 : ℝ)) 133 101 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2221912141/10000000000 : ℝ), (7200204183/10000000000 : ℝ), (773039987/2500000000 : ℝ)] ![(2759175062271/20000000000000 : ℝ), (32442710667079/50000000000000 : ℝ), (21318703347773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2221912141/10000000000 : ℝ)|^133 ≤ (2759175062271/20000000000000 : ℝ)^101
        have hw : |(2221912141/10000000000 : ℝ)|=(2221912141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7200204183/10000000000 : ℝ)|^133 ≤ (32442710667079/50000000000000 : ℝ)^101
        have hw : |(7200204183/10000000000 : ℝ)|=(7200204183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773039987/2500000000 : ℝ)|^133 ≤ (21318703347773/100000000000000 : ℝ)^101
        have hw : |(773039987/2500000000 : ℝ)|=(773039987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c304059_s5 (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((74203/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74203/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14459/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14459/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5417/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5417/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2381/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2381/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11599/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11599/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18399/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18399/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76617/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76617/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76617/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (74203/100000 : ℝ) ^ (33/8 : ℝ) ≤ (7301776704626436533/25000000000000000000 : ℝ) := by
    have hpowers : (74203/100000 : ℝ)^33 ≤ (7301776704626436533/25000000000000000000 : ℝ)^8 := by
      have hnat : (74203 : ℕ)^33*25000000000000000000^8 ≤ 7301776704626436533^8*100000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74203 100000 7301776704626436533 25000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (74203/100000 : ℝ)) (X := (7301776704626436533/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0a : (32301776704626436533/25000000000000000000 : ℝ) ≤ (10640903916427727/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (32301776704626436533/25000000000000000000 : ℝ)^8 ≤ (10640903916427727/10000000000000000 : ℝ)^33 := by
      have hnat : (32301776704626436533 : ℕ)^8*10000000000000000^33 ≤ 10640903916427727^33*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32301776704626436533 25000000000000000000 10640903916427727 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10640903916427727/10000000000000000 : ℝ)) (X := (32301776704626436533/25000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner0b : (19801776704626436533/12500000000000000000 : ℝ) ≤ (1117982342826921/1000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (19801776704626436533/12500000000000000000 : ℝ)^8 ≤ (1117982342826921/1000000000000000 : ℝ)^33 := by
      have hnat : (19801776704626436533 : ℕ)^8*1000000000000000^33 ≤ 1117982342826921^33*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19801776704626436533 12500000000000000000 1117982342826921 1000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1117982342826921/1000000000000000 : ℝ)) (X := (19801776704626436533/12500000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(640903916427727/7420300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(538919511841483/7420300000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (74203/100000 : ℝ)) (alpha := (640903916427727/7420300000000000 : ℝ)) (beta := (538919511841483/7420300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (74203/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(640903916427727/7420300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(538919511841483/7420300000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (14459/20000 : ℝ) ^ (33/8 : ℝ) ≤ (819731459493746521/3125000000000000000 : ℝ) := by
    have hpowers : (14459/20000 : ℝ)^33 ≤ (819731459493746521/3125000000000000000 : ℝ)^8 := by
      have hnat : (14459 : ℕ)^33*3125000000000000000^8 ≤ 819731459493746521^8*20000^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14459 20000 819731459493746521 3125000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14459/20000 : ℝ)) (X := (819731459493746521/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1a : (3944731459493746521/3125000000000000000 : ℝ) ≤ (2645242211183699/2500000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (3944731459493746521/3125000000000000000 : ℝ)^8 ≤ (2645242211183699/2500000000000000 : ℝ)^33 := by
      have hnat : (3944731459493746521 : ℕ)^8*2500000000000000^33 ≤ 2645242211183699^33*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3944731459493746521 3125000000000000000 2645242211183699 2500000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2645242211183699/2500000000000000 : ℝ)) (X := (3944731459493746521/3125000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner1b : (2382231459493746521/1562500000000000000 : ℝ) ≤ (17307064128301/15625000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (2382231459493746521/1562500000000000000 : ℝ)^8 ≤ (17307064128301/15625000000000 : ℝ)^33 := by
      have hnat : (2382231459493746521 : ℕ)^8*15625000000000^33 ≤ 17307064128301^33*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2382231459493746521 1562500000000000000 17307064128301 15625000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (17307064128301/15625000000000 : ℝ)) (X := (2382231459493746521/1562500000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(145242211183699/1807375000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(123888049344461/1807375000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (14459/20000 : ℝ)) (alpha := (145242211183699/1807375000000000 : ℝ)) (beta := (123888049344461/1807375000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14459/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(145242211183699/1807375000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(123888049344461/1807375000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (5417/12500 : ℝ) ^ (33/8 : ℝ) ≤ (3176884261509614611/100000000000000000000 : ℝ) := by
    have hpowers : (5417/12500 : ℝ)^33 ≤ (3176884261509614611/100000000000000000000 : ℝ)^8 := by
      have hnat : (5417 : ℕ)^33*100000000000000000000^8 ≤ 3176884261509614611^8*12500^33 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5417 12500 3176884261509614611 100000000000000000000 33 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5417/12500 : ℝ)) (X := (3176884261509614611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2a : (103176884261509614611/100000000000000000000 : ℝ) ≤ (10076105479988217/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (103176884261509614611/100000000000000000000 : ℝ)^8 ≤ (10076105479988217/10000000000000000 : ℝ)^33 := by
      have hnat : (103176884261509614611 : ℕ)^8*10000000000000000^33 ≤ 10076105479988217^33*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103176884261509614611 100000000000000000000 10076105479988217 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10076105479988217/10000000000000000 : ℝ)) (X := (103176884261509614611/100000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have s5_corner2b : (53176884261509614611/50000000000000000000 : ℝ) ≤ (10150455870961439/10000000000000000 : ℝ) ^ (33/8 : ℝ) := by
    have hpowers : (53176884261509614611/50000000000000000000 : ℝ)^8 ≤ (10150455870961439/10000000000000000 : ℝ)^33 := by
      have hnat : (53176884261509614611 : ℕ)^8*10000000000000000^33 ≤ 10150455870961439^33*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53176884261509614611 50000000000000000000 10150455870961439 10000000000000000 8 33 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10150455870961439/10000000000000000 : ℝ)) (X := (53176884261509614611/50000000000000000000 : ℝ)) (by norm_num) 33 8 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(76105479988217/4333600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(37175195486611/2166800000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (33/8 : ℝ)) (rho := (5417/12500 : ℝ)) (alpha := (76105479988217/4333600000000000 : ℝ)) (beta := (37175195486611/2166800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (5417/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(76105479988217/4333600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(37175195486611/2166800000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_1 : ((1693869113/5000000000 : ℝ)*X 1 0+(-3365154411/10000000000 : ℝ)*X 1 1+(6097290941/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((5857703769/10000000000 : ℝ)*X 2 0+(1128319091/2000000000 : ℝ)*X 2 1+(-97903689/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((4358614711/10000000000 : ℝ)*X 0 0+(978701989/2000000000 : ℝ)*X 0 1+(3749387661/10000000000 : ℝ)*X 0 2+(4358614711/10000000000 : ℝ)*X 1 0+(978701989/2000000000 : ℝ)*X 1 1+(3749387661/10000000000 : ℝ)*X 1 2+(4358614711/10000000000 : ℝ)*X 2 0+(978701989/2000000000 : ℝ)*X 2 1+(3749387661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-1552430131/5000000000 : ℝ)*X 0 0+(2753799937/10000000000 : ℝ)*X 0 1+(3403681943/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((124407639/400000000 : ℝ)*X 1 0+(-338444039/1250000000 : ℝ)*X 1 1+(683781003/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((5500117153/10000000000 : ℝ)*X 2 0+(628289733/1000000000 : ℝ)*X 2 1+(-109801731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((3891474711/10000000000 : ℝ)*X 0 0+(3226586431/5000000000 : ℝ)*X 0 1+(2364482583/10000000000 : ℝ)*X 0 2+(3891474711/10000000000 : ℝ)*X 1 0+(3226586431/5000000000 : ℝ)*X 1 1+(2364482583/10000000000 : ℝ)*X 1 2+(3891474711/10000000000 : ℝ)*X 2 0+(3226586431/5000000000 : ℝ)*X 2 1+(2364482583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-1378242329/5000000000 : ℝ)*X 0 0+(3101157767/10000000000 : ℝ)*X 0 1+(6808234759/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((1368873677/5000000000 : ℝ)*X 1 0+(-616015507/2000000000 : ℝ)*X 1 1+(6838681689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((3281858663/5000000000 : ℝ)*X 2 0+(1040565201/2000000000 : ℝ)*X 2 1+(-108930703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((5815284343/10000000000 : ℝ)*X 0 0+(921913943/2000000000 : ℝ)*X 0 1+(9229341/39062500 : ℝ)*X 0 2+(5815284343/10000000000 : ℝ)*X 1 0+(921913943/2000000000 : ℝ)*X 1 1+(9229341/39062500 : ℝ)*X 1 2+(5815284343/10000000000 : ℝ)*X 2 0+(921913943/2000000000 : ℝ)*X 2 1+(9229341/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-3431802963/10000000000 : ℝ)*X 0 0+(1713330139/5000000000 : ℝ)*X 0 1+(375583753/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((3395952591/10000000000 : ℝ)*X 1 0+(-3387990451/10000000000 : ℝ)*X 1 1+(6071515599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((699733291/1000000000 : ℝ)*X 2 0+(142569561/312500000 : ℝ)*X 2 1+(-249693027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((2221912141/10000000000 : ℝ)*X 0 0+(7200204183/10000000000 : ℝ)*X 0 1+(773039987/2500000000 : ℝ)*X 0 2+(2221912141/10000000000 : ℝ)*X 1 0+(7200204183/10000000000 : ℝ)*X 1 1+(773039987/2500000000 : ℝ)*X 1 2+(2221912141/10000000000 : ℝ)*X 2 0+(7200204183/10000000000 : ℝ)*X 2 1+(773039987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c304059_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((2381/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2381/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9227001773860276907902420953279/1162381135161800000000000000000000000 : ℝ) := by norm_num
    linear_combination (111249/1000000000000 : ℝ)*(base19) + (63649/1000000000000 : ℝ)*(base49) + (35147/7812500000 : ℝ)*(base59) + (38321633751/31250000000 : ℝ)*(base60) + (2755821714323/500000000000 : ℝ)*(major_s5_0) + (2755821714323/500000000000 : ℝ)*(major_s5_1) + (2755821714323/500000000000 : ℝ)*(major_s5_2) + (4905759/200000000000 : ℝ)*(sp_s5_2) + (3694680692641/500000000000 : ℝ)*(sp_s5_7) + (59114265103/8000000000 : ℝ)*(sp_s5_8) + (7389336856487/1000000000000 : ℝ)*(sp_s5_9) + (1816948699139/500000000000 : ℝ)*(sp_s5_13) + (78136157/1000000000000 : ℝ)*(sp_s5_15) + (12713859/500000000000 : ℝ)*(sp_s5_27) + (3633922825997/1000000000000 : ℝ)*(f.failure) + (3694680692641/500000000000 : ℝ)*(f.sum) + (16890748182594282243/156648806000000000000000000000000 : ℝ)*base63 + (886155811807593/1083400000000000000000000000 : ℝ)*base65 + (1036275782144681/1807375000000000000000000000 : ℝ)*base67 + (1044728247036589/2166800000000000000000000000 : ℝ)*base69 + (36314543789777838387/80391530200000000000000000000000 : ℝ)*base71 + (1985782682118797/1855075000000000000000000000 : ℝ)*base73 + (772921654132079/1807375000000000000000000000 : ℝ)*base75 + (1105356460490923/1855075000000000000000000000 : ℝ)*base77 + (63734890384990591483/134112647125000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (2123/12500000000000000 : ℝ)*base87 + (2123/12500000000000000 : ℝ)*base89 + (2123/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11599/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11599/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (87641065684596553033994181/9790550375000000000000000000000 : ℝ) := by norm_num
    linear_combination (10311/1000000000000 : ℝ)*(base13) + (1326924211/12500000000 : ℝ)*(base59) + (633703115989/500000000000 : ℝ)*(base60) + (1365845995969/250000000000 : ℝ)*(major_s5_0) + (1365845995969/250000000000 : ℝ)*(major_s5_1) + (1365845995969/250000000000 : ℝ)*(major_s5_2) + (799097/125000000000 : ℝ)*(sp_s5_1) + (7831773/500000000000 : ℝ)*(sp_s5_6) + (84285727/1000000000000 : ℝ)*(sp_s5_7) + (915572019637/125000000000 : ℝ)*(sp_s5_14) + (7324654060359/1000000000000 : ℝ)*(sp_s5_15) + (7324609110983/1000000000000 : ℝ)*(sp_s5_16) + (1801044433601/500000000000 : ℝ)*(sp_s5_20) + (6417769/125000000000 : ℝ)*(sp_s5_23) + (900526132687/250000000000 : ℝ)*(f.failure) + (1464932090627/200000000000 : ℝ)*(f.sum) + (1418208960460833671/78324403000000000000000000000000 : ℝ)*base62 + (270528283237789/541700000000000000000000000 : ℝ)*base65 + (647180647230693/903687500000000000000000000 : ℝ)*base67 + (168020678226367/1083400000000000000000000000 : ℝ)*base69 + (14083855803871951771/40195765100000000000000000000000 : ℝ)*base71 + (295093055274921/3710150000000000000000000000 : ℝ)*base72 + (281317853299301/1807375000000000000000000000 : ℝ)*base74 + (297061693294359/3710150000000000000000000000 : ℝ)*base76 + (6792247631791834921/268225294250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (333/3125000000000000 : ℝ)*base87 + (333/3125000000000000 : ℝ)*base89 + (333/3125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18399/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18399/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (32125872624196930796342367069807/5811905675809000000000000000000000000 : ℝ) := by norm_num
    linear_combination (558207/1000000000000 : ℝ)*(base8) + (426211/200000000000 : ℝ)*(base11) + (14294439429/1000000000000 : ℝ)*(base50) + (139486342971/500000000000 : ℝ)*(base60) + (3359945846547/1000000000000 : ℝ)*(major_s5_0) + (3359945846547/1000000000000 : ℝ)*(major_s5_1) + (3359945846547/1000000000000 : ℝ)*(major_s5_2) + (34187/2500000000 : ℝ)*(sp_s5_2) + (34541803/1000000000000 : ℝ)*(sp_s5_13) + (30039571/1000000000000 : ℝ)*(sp_s5_16) + (2252308075561/500000000000 : ℝ)*(sp_s5_21) + (70384669381/15625000000 : ℝ)*(sp_s5_22) + (4504575126013/1000000000000 : ℝ)*(sp_s5_23) + (2215236468369/1000000000000 : ℝ)*(sp_s5_27) + (2215271010171/1000000000000 : ℝ)*(f.failure) + (70384669381/15625000000 : ℝ)*(f.sum) + (61878238404850733027/313297612000000000000000000000000 : ℝ)*base63 + (977883056129503/2166800000000000000000000000 : ℝ)*base64 + (2138145688597741/3614750000000000000000000000 : ℝ)*base66 + (1440211993320859/4333600000000000000000000000 : ℝ)*base68 + (76187065067176867217/160783060400000000000000000000000 : ℝ)*base70 + (1528698162584109/7420300000000000000000000000 : ℝ)*base72 + (136618266872789/903687500000000000000000000 : ℝ)*base75 + (3074291207587651/7420300000000000000000000000 : ℝ)*base76 + (338036856992254361201/536450588500000000000000000000000 : ℝ)*base78 + (5511/12500000000000000 : ℝ)*base86 + (5511/12500000000000000 : ℝ)*base88 + (5511/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (33/8 : ℝ) ≤ p) (hpb : p ≤ (133/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (18959/12500 : ℝ) (187821/100000 : ℝ) (76617/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((74203/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(74203/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14459/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14459/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(5417/12500 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(5417/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2381/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2381/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11599/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(11599/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(18399/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(18399/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c304059_s5 p hpa hpb X hX hprev4

#print axioms solution
