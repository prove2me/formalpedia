-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305062_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:14.17999+00:00
-- url     : https://prove2.me/submissions/a41325e3-566a-4d9e-ae1e-f23fd0316106

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
theorem collision_support_c305062_s2_s2_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-234552911/2000000000 : ℝ)*x 0 + (5010688427/10000000000 : ℝ)*x 1 + (-6227102519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234552911/2000000000 : ℝ)^67 ≤ (5986852294161/100000000000000 : ℝ)^51 := by
    have hnat : (234552911 : ℕ)^67*100000000000000^51 ≤ 5986852294161^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234552911 2000000000 5986852294161 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5010688427/10000000000 : ℝ)^67 ≤ (2017054194107/5000000000000 : ℝ)^51 := by
    have hnat : (5010688427 : ℕ)^67*5000000000000^51 ≤ 2017054194107^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010688427 10000000000 2017054194107 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6227102519/10000000000 : ℝ)^67 ≤ (268360319033/500000000000 : ℝ)^51 := by
    have hnat : (6227102519 : ℕ)^67*500000000000^51 ≤ 268360319033^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6227102519 10000000000 268360319033 500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-234552911/2000000000 : ℝ), (5010688427/10000000000 : ℝ), (-6227102519/10000000000 : ℝ)] ![(5986852294161/100000000000000 : ℝ), (2017054194107/5000000000000 : ℝ), (268360319033/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-234552911/2000000000 : ℝ)|^67 ≤ (5986852294161/100000000000000 : ℝ)^51
        have hw : |(-234552911/2000000000 : ℝ)|=(234552911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5010688427/10000000000 : ℝ)|^67 ≤ (2017054194107/5000000000000 : ℝ)^51
        have hw : |(5010688427/10000000000 : ℝ)|=(5010688427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6227102519/10000000000 : ℝ)|^67 ≤ (268360319033/500000000000 : ℝ)^51
        have hw : |(-6227102519/10000000000 : ℝ)|=(6227102519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (156873387/312500000 : ℝ)*x 0 + (-1168950041/10000000000 : ℝ)*x 1 + (-1244141493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (156873387/312500000 : ℝ)^67 ≤ (4043905308773/10000000000000 : ℝ)^51 := by
    have hnat : (156873387 : ℕ)^67*10000000000000^51 ≤ 4043905308773^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156873387 312500000 4043905308773 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1168950041/10000000000 : ℝ)^67 ≤ (2980641764659/50000000000000 : ℝ)^51 := by
    have hnat : (1168950041 : ℕ)^67*50000000000000^51 ≤ 2980641764659^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168950041 10000000000 2980641764659 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244141493/2000000000 : ℝ)^67 ≤ (26799831688933/50000000000000 : ℝ)^51 := by
    have hnat : (1244141493 : ℕ)^67*50000000000000^51 ≤ 26799831688933^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244141493 2000000000 26799831688933 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(156873387/312500000 : ℝ), (-1168950041/10000000000 : ℝ), (-1244141493/2000000000 : ℝ)] ![(4043905308773/10000000000000 : ℝ), (2980641764659/50000000000000 : ℝ), (26799831688933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(156873387/312500000 : ℝ)|^67 ≤ (4043905308773/10000000000000 : ℝ)^51
        have hw : |(156873387/312500000 : ℝ)|=(156873387/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1168950041/10000000000 : ℝ)|^67 ≤ (2980641764659/50000000000000 : ℝ)^51
        have hw : |(-1168950041/10000000000 : ℝ)|=(1168950041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1244141493/2000000000 : ℝ)|^67 ≤ (26799831688933/50000000000000 : ℝ)^51
        have hw : |(-1244141493/2000000000 : ℝ)|=(1244141493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1561510007/10000000000 : ℝ)*x 0 + (1209802711/5000000000 : ℝ)*x 1 + (-8096616611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1561510007/10000000000 : ℝ)^67 ≤ (348818251903/4000000000000 : ℝ)^51 := by
    have hnat : (1561510007 : ℕ)^67*4000000000000^51 ≤ 348818251903^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561510007 10000000000 348818251903 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1209802711/5000000000 : ℝ)^67 ≤ (15502777200893/100000000000000 : ℝ)^51 := by
    have hnat : (1209802711 : ℕ)^67*100000000000000^51 ≤ 15502777200893^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209802711 5000000000 15502777200893 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8096616611/10000000000 : ℝ)^67 ≤ (75776766489467/100000000000000 : ℝ)^51 := by
    have hnat : (8096616611 : ℕ)^67*100000000000000^51 ≤ 75776766489467^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8096616611 10000000000 75776766489467 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1561510007/10000000000 : ℝ), (1209802711/5000000000 : ℝ), (-8096616611/10000000000 : ℝ)] ![(348818251903/4000000000000 : ℝ), (15502777200893/100000000000000 : ℝ), (75776766489467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1561510007/10000000000 : ℝ)|^67 ≤ (348818251903/4000000000000 : ℝ)^51
        have hw : |(-1561510007/10000000000 : ℝ)|=(1561510007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1209802711/5000000000 : ℝ)|^67 ≤ (15502777200893/100000000000000 : ℝ)^51
        have hw : |(1209802711/5000000000 : ℝ)|=(1209802711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8096616611/10000000000 : ℝ)|^67 ≤ (75776766489467/100000000000000 : ℝ)^51
        have hw : |(-8096616611/10000000000 : ℝ)|=(8096616611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (280513571/1000000000 : ℝ)*x 0 + (-1098792437/10000000000 : ℝ)*x 1 + (-1617717221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280513571/1000000000 : ℝ)^67 ≤ (18826211626189/100000000000000 : ℝ)^51 := by
    have hnat : (280513571 : ℕ)^67*100000000000000^51 ≤ 18826211626189^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280513571 1000000000 18826211626189 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098792437/10000000000 : ℝ)^67 ≤ (549574352973/10000000000000 : ℝ)^51 := by
    have hnat : (1098792437 : ℕ)^67*10000000000000^51 ≤ 549574352973^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098792437 10000000000 549574352973 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1617717221/2000000000 : ℝ)^67 ≤ (75678044830983/100000000000000 : ℝ)^51 := by
    have hnat : (1617717221 : ℕ)^67*100000000000000^51 ≤ 75678044830983^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617717221 2000000000 75678044830983 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280513571/1000000000 : ℝ), (-1098792437/10000000000 : ℝ), (-1617717221/2000000000 : ℝ)] ![(18826211626189/100000000000000 : ℝ), (549574352973/10000000000000 : ℝ), (75678044830983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280513571/1000000000 : ℝ)|^67 ≤ (18826211626189/100000000000000 : ℝ)^51
        have hw : |(280513571/1000000000 : ℝ)|=(280513571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098792437/10000000000 : ℝ)|^67 ≤ (549574352973/10000000000000 : ℝ)^51
        have hw : |(-1098792437/10000000000 : ℝ)|=(1098792437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1617717221/2000000000 : ℝ)|^67 ≤ (75678044830983/100000000000000 : ℝ)^51
        have hw : |(-1617717221/2000000000 : ℝ)|=(1617717221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (102786941/312500000 : ℝ)*x 0 + (7277071121/10000000000 : ℝ)*x 1 + (1854482449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (102786941/312500000 : ℝ)^67 ≤ (11602620698257/50000000000000 : ℝ)^51 := by
    have hnat : (102786941 : ℕ)^67*50000000000000^51 ≤ 11602620698257^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102786941 312500000 11602620698257 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7277071121/10000000000 : ℝ)^67 ≤ (16466029944497/25000000000000 : ℝ)^51 := by
    have hnat : (7277071121 : ℕ)^67*25000000000000^51 ≤ 16466029944497^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7277071121 10000000000 16466029944497 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1854482449/10000000000 : ℝ)^67 ≤ (546531940689/5000000000000 : ℝ)^51 := by
    have hnat : (1854482449 : ℕ)^67*5000000000000^51 ≤ 546531940689^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854482449 10000000000 546531940689 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(102786941/312500000 : ℝ), (7277071121/10000000000 : ℝ), (1854482449/10000000000 : ℝ)] ![(11602620698257/50000000000000 : ℝ), (16466029944497/25000000000000 : ℝ), (546531940689/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(102786941/312500000 : ℝ)|^67 ≤ (11602620698257/50000000000000 : ℝ)^51
        have hw : |(102786941/312500000 : ℝ)|=(102786941/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7277071121/10000000000 : ℝ)|^67 ≤ (16466029944497/25000000000000 : ℝ)^51
        have hw : |(7277071121/10000000000 : ℝ)|=(7277071121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1854482449/10000000000 : ℝ)|^67 ≤ (546531940689/5000000000000 : ℝ)^51
        have hw : |(1854482449/10000000000 : ℝ)|=(1854482449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1914820817/5000000000 : ℝ)*x 0 + (7759652479/10000000000 : ℝ)*x 1 + (-7/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914820817/5000000000 : ℝ)^67 ≤ (28338980201891/100000000000000 : ℝ)^51 := by
    have hnat : (1914820817 : ℕ)^67*100000000000000^51 ≤ 28338980201891^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914820817 5000000000 28338980201891 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7759652479/10000000000 : ℝ)^67 ≤ (7166101978453/10000000000000 : ℝ)^51 := by
    have hnat : (7759652479 : ℕ)^67*10000000000000^51 ≤ 7166101978453^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7759652479 10000000000 7166101978453 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7/2500000000 : ℝ)^67 ≤ (581/100000000000000 : ℝ)^51 := by
    have hnat : (7 : ℕ)^67*100000000000000^51 ≤ 581^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7 2500000000 581 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1914820817/5000000000 : ℝ), (7759652479/10000000000 : ℝ), (-7/2500000000 : ℝ)] ![(28338980201891/100000000000000 : ℝ), (7166101978453/10000000000000 : ℝ), (581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1914820817/5000000000 : ℝ)|^67 ≤ (28338980201891/100000000000000 : ℝ)^51
        have hw : |(1914820817/5000000000 : ℝ)|=(1914820817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7759652479/10000000000 : ℝ)|^67 ≤ (7166101978453/10000000000000 : ℝ)^51
        have hw : |(7759652479/10000000000 : ℝ)|=(7759652479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7/2500000000 : ℝ)|^67 ≤ (581/100000000000000 : ℝ)^51
        have hw : |(-7/2500000000 : ℝ)|=(7/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-108711069/1000000000 : ℝ)*x 0 + (1383102787/5000000000 : ℝ)*x 1 + (-812266231/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108711069/1000000000 : ℝ)^67 ≤ (5419113926181/100000000000000 : ℝ)^51 := by
    have hnat : (108711069 : ℕ)^67*100000000000000^51 ≤ 5419113926181^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108711069 1000000000 5419113926181 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383102787/5000000000 : ℝ)^67 ≤ (9241859941597/50000000000000 : ℝ)^51 := by
    have hnat : (1383102787 : ℕ)^67*50000000000000^51 ≤ 9241859941597^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383102787 5000000000 9241859941597 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (812266231/1000000000 : ℝ)^67 ≤ (76097166166273/100000000000000 : ℝ)^51 := by
    have hnat : (812266231 : ℕ)^67*100000000000000^51 ≤ 76097166166273^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812266231 1000000000 76097166166273 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108711069/1000000000 : ℝ), (1383102787/5000000000 : ℝ), (-812266231/1000000000 : ℝ)] ![(5419113926181/100000000000000 : ℝ), (9241859941597/50000000000000 : ℝ), (76097166166273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108711069/1000000000 : ℝ)|^67 ≤ (5419113926181/100000000000000 : ℝ)^51
        have hw : |(-108711069/1000000000 : ℝ)|=(108711069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1383102787/5000000000 : ℝ)|^67 ≤ (9241859941597/50000000000000 : ℝ)^51
        have hw : |(1383102787/5000000000 : ℝ)|=(1383102787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-812266231/1000000000 : ℝ)|^67 ≤ (76097166166273/100000000000000 : ℝ)^51
        have hw : |(-812266231/1000000000 : ℝ)|=(812266231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2399723769/10000000000 : ℝ)*x 0 + (-1554122393/10000000000 : ℝ)*x 1 + (-8114608581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2399723769/10000000000 : ℝ)^67 ≤ (3067128942341/20000000000000 : ℝ)^51 := by
    have hnat : (2399723769 : ℕ)^67*20000000000000^51 ≤ 3067128942341^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2399723769 10000000000 3067128942341 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1554122393/10000000000 : ℝ)^67 ≤ (8666296068993/100000000000000 : ℝ)^51 := by
    have hnat : (1554122393 : ℕ)^67*100000000000000^51 ≤ 8666296068993^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554122393 10000000000 8666296068993 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8114608581/10000000000 : ℝ)^67 ≤ (18999514801431/25000000000000 : ℝ)^51 := by
    have hnat : (8114608581 : ℕ)^67*25000000000000^51 ≤ 18999514801431^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8114608581 10000000000 18999514801431 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2399723769/10000000000 : ℝ), (-1554122393/10000000000 : ℝ), (-8114608581/10000000000 : ℝ)] ![(3067128942341/20000000000000 : ℝ), (8666296068993/100000000000000 : ℝ), (18999514801431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2399723769/10000000000 : ℝ)|^67 ≤ (3067128942341/20000000000000 : ℝ)^51
        have hw : |(2399723769/10000000000 : ℝ)|=(2399723769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1554122393/10000000000 : ℝ)|^67 ≤ (8666296068993/100000000000000 : ℝ)^51
        have hw : |(-1554122393/10000000000 : ℝ)|=(1554122393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8114608581/10000000000 : ℝ)|^67 ≤ (18999514801431/25000000000000 : ℝ)^51
        have hw : |(-8114608581/10000000000 : ℝ)|=(8114608581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7194442051/10000000000 : ℝ)*x 0 + (33895311/100000000 : ℝ)*x 1 + (1860452123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7194442051/10000000000 : ℝ)^67 ≤ (16220845154751/25000000000000 : ℝ)^51 := by
    have hnat : (7194442051 : ℕ)^67*25000000000000^51 ≤ 16220845154751^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7194442051 10000000000 16220845154751 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33895311/100000000 : ℝ)^67 ≤ (12069866048079/50000000000000 : ℝ)^51 := by
    have hnat : (33895311 : ℕ)^67*50000000000000^51 ≤ 12069866048079^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33895311 100000000 12069866048079 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1860452123/10000000000 : ℝ)^67 ≤ (1097688725913/10000000000000 : ℝ)^51 := by
    have hnat : (1860452123 : ℕ)^67*10000000000000^51 ≤ 1097688725913^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1860452123 10000000000 1097688725913 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7194442051/10000000000 : ℝ), (33895311/100000000 : ℝ), (1860452123/10000000000 : ℝ)] ![(16220845154751/25000000000000 : ℝ), (12069866048079/50000000000000 : ℝ), (1097688725913/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7194442051/10000000000 : ℝ)|^67 ≤ (16220845154751/25000000000000 : ℝ)^51
        have hw : |(7194442051/10000000000 : ℝ)|=(7194442051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33895311/100000000 : ℝ)|^67 ≤ (12069866048079/50000000000000 : ℝ)^51
        have hw : |(33895311/100000000 : ℝ)|=(33895311/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1860452123/10000000000 : ℝ)|^67 ≤ (1097688725913/10000000000000 : ℝ)^51
        have hw : |(1860452123/10000000000 : ℝ)|=(1860452123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3937618289/5000000000 : ℝ)*x 0 + (368418243/1000000000 : ℝ)*x 1 + (-2787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3937618289/5000000000 : ℝ)^67 ≤ (1461331866389/2000000000000 : ℝ)^51 := by
    have hnat : (3937618289 : ℕ)^67*2000000000000^51 ≤ 1461331866389^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3937618289 5000000000 1461331866389 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368418243/1000000000 : ℝ)^67 ≤ (13466703210133/50000000000000 : ℝ)^51 := by
    have hnat : (368418243 : ℕ)^67*50000000000000^51 ≤ 13466703210133^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368418243 1000000000 13466703210133 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2787/10000000000 : ℝ)^67 ≤ (244743/100000000000000 : ℝ)^51 := by
    have hnat : (2787 : ℕ)^67*100000000000000^51 ≤ 244743^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787 10000000000 244743 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3937618289/5000000000 : ℝ), (368418243/1000000000 : ℝ), (-2787/10000000000 : ℝ)] ![(1461331866389/2000000000000 : ℝ), (13466703210133/50000000000000 : ℝ), (244743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3937618289/5000000000 : ℝ)|^67 ≤ (1461331866389/2000000000000 : ℝ)^51
        have hw : |(3937618289/5000000000 : ℝ)|=(3937618289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(368418243/1000000000 : ℝ)|^67 ≤ (13466703210133/50000000000000 : ℝ)^51
        have hw : |(368418243/1000000000 : ℝ)|=(368418243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2787/10000000000 : ℝ)|^67 ≤ (244743/100000000000000 : ℝ)^51
        have hw : |(-2787/10000000000 : ℝ)|=(2787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4012783/100000000 : ℝ)*x 0 + (3393645737/5000000000 : ℝ)*x 1 + (-4829330659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4012783/100000000 : ℝ)^67 ≤ (1463224568889/100000000000000 : ℝ)^51 := by
    have hnat : (4012783 : ℕ)^67*100000000000000^51 ≤ 1463224568889^51*100000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012783 100000000 1463224568889 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3393645737/5000000000 : ℝ)^67 ≤ (60102896464147/100000000000000 : ℝ)^51 := by
    have hnat : (3393645737 : ℕ)^67*100000000000000^51 ≤ 60102896464147^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3393645737 5000000000 60102896464147 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4829330659/10000000000 : ℝ)^67 ≤ (1537355158241/4000000000000 : ℝ)^51 := by
    have hnat : (4829330659 : ℕ)^67*4000000000000^51 ≤ 1537355158241^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4829330659 10000000000 1537355158241 4000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4012783/100000000 : ℝ), (3393645737/5000000000 : ℝ), (-4829330659/10000000000 : ℝ)] ![(1463224568889/100000000000000 : ℝ), (60102896464147/100000000000000 : ℝ), (1537355158241/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4012783/100000000 : ℝ)|^67 ≤ (1463224568889/100000000000000 : ℝ)^51
        have hw : |(-4012783/100000000 : ℝ)|=(4012783/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3393645737/5000000000 : ℝ)|^67 ≤ (60102896464147/100000000000000 : ℝ)^51
        have hw : |(3393645737/5000000000 : ℝ)|=(3393645737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4829330659/10000000000 : ℝ)|^67 ≤ (1537355158241/4000000000000 : ℝ)^51
        have hw : |(-4829330659/10000000000 : ℝ)|=(4829330659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3470234159/5000000000 : ℝ)*x 0 + (-538950303/10000000000 : ℝ)*x 1 + (-1147543493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3470234159/5000000000 : ℝ)^67 ≤ (30945563578711/50000000000000 : ℝ)^51 := by
    have hnat : (3470234159 : ℕ)^67*50000000000000^51 ≤ 30945563578711^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3470234159 5000000000 30945563578711 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538950303/10000000000 : ℝ)^67 ≤ (33683968067/1562500000000 : ℝ)^51 := by
    have hnat : (538950303 : ℕ)^67*1562500000000^51 ≤ 33683968067^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538950303 10000000000 33683968067 1562500000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147543493/2500000000 : ℝ)^67 ≤ (3595309887381/10000000000000 : ℝ)^51 := by
    have hnat : (1147543493 : ℕ)^67*10000000000000^51 ≤ 3595309887381^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147543493 2500000000 3595309887381 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3470234159/5000000000 : ℝ), (-538950303/10000000000 : ℝ), (-1147543493/2500000000 : ℝ)] ![(30945563578711/50000000000000 : ℝ), (33683968067/1562500000000 : ℝ), (3595309887381/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3470234159/5000000000 : ℝ)|^67 ≤ (30945563578711/50000000000000 : ℝ)^51
        have hw : |(3470234159/5000000000 : ℝ)|=(3470234159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538950303/10000000000 : ℝ)|^67 ≤ (33683968067/1562500000000 : ℝ)^51
        have hw : |(-538950303/10000000000 : ℝ)|=(538950303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1147543493/2500000000 : ℝ)|^67 ≤ (3595309887381/10000000000000 : ℝ)^51
        have hw : |(-1147543493/2500000000 : ℝ)|=(1147543493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3051956167/10000000000 : ℝ)*x 0 + (3668939171/5000000000 : ℝ)*x 1 + (509713533/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3051956167/10000000000 : ℝ)^67 ≤ (21031844582549/100000000000000 : ℝ)^51 := by
    have hnat : (3051956167 : ℕ)^67*100000000000000^51 ≤ 21031844582549^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3051956167 10000000000 21031844582549 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3668939171/5000000000 : ℝ)^67 ≤ (66588088575847/100000000000000 : ℝ)^51 := by
    have hnat : (3668939171 : ℕ)^67*100000000000000^51 ≤ 66588088575847^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3668939171 5000000000 66588088575847 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509713533/2500000000 : ℝ)^67 ≤ (12380066822477/100000000000000 : ℝ)^51 := by
    have hnat : (509713533 : ℕ)^67*100000000000000^51 ≤ 12380066822477^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509713533 2500000000 12380066822477 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3051956167/10000000000 : ℝ), (3668939171/5000000000 : ℝ), (509713533/2500000000 : ℝ)] ![(21031844582549/100000000000000 : ℝ), (66588088575847/100000000000000 : ℝ), (12380066822477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3051956167/10000000000 : ℝ)|^67 ≤ (21031844582549/100000000000000 : ℝ)^51
        have hw : |(3051956167/10000000000 : ℝ)|=(3051956167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3668939171/5000000000 : ℝ)|^67 ≤ (66588088575847/100000000000000 : ℝ)^51
        have hw : |(3668939171/5000000000 : ℝ)|=(3668939171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(509713533/2500000000 : ℝ)|^67 ≤ (12380066822477/100000000000000 : ℝ)^51
        have hw : |(509713533/2500000000 : ℝ)|=(509713533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305062_s2_s2_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8381646099/10000000000 : ℝ)*x 0 + (46858127/156250000 : ℝ)*x 1 + (-34806517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8381646099/10000000000 : ℝ)^67 ≤ (39650236040643/50000000000000 : ℝ)^51 := by
    have hnat : (8381646099 : ℕ)^67*50000000000000^51 ≤ 39650236040643^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8381646099 10000000000 39650236040643 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46858127/156250000 : ℝ)^67 ≤ (20553011047231/100000000000000 : ℝ)^51 := by
    have hnat : (46858127 : ℕ)^67*100000000000000^51 ≤ 20553011047231^51*156250000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46858127 156250000 20553011047231 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34806517/5000000000 : ℝ)^67 ≤ (366292149/250000000000 : ℝ)^51 := by
    have hnat : (34806517 : ℕ)^67*250000000000^51 ≤ 366292149^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34806517 5000000000 366292149 250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8381646099/10000000000 : ℝ), (46858127/156250000 : ℝ), (-34806517/5000000000 : ℝ)] ![(39650236040643/50000000000000 : ℝ), (20553011047231/100000000000000 : ℝ), (366292149/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8381646099/10000000000 : ℝ)|^67 ≤ (39650236040643/50000000000000 : ℝ)^51
        have hw : |(8381646099/10000000000 : ℝ)|=(8381646099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46858127/156250000 : ℝ)|^67 ≤ (20553011047231/100000000000000 : ℝ)^51
        have hw : |(46858127/156250000 : ℝ)|=(46858127/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34806517/5000000000 : ℝ)|^67 ≤ (366292149/250000000000 : ℝ)^51
        have hw : |(-34806517/5000000000 : ℝ)|=(34806517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305062_s2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((11213/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11213/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44617/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44617/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37073/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37073/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20091/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20091/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20069/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20069/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31811/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31811/50000 : ℝ)*X 1 2) := by
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
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (93447/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (11213/12500 : ℝ) ^ (133/32 : ℝ) ≤ (31830545839413490777/50000000000000000000 : ℝ) := by
    have hpowers : (11213/12500 : ℝ)^133 ≤ (31830545839413490777/50000000000000000000 : ℝ)^32 := by
      have hnat : (11213 : ℕ)^133*50000000000000000000^32 ≤ 31830545839413490777^32*12500^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11213 12500 31830545839413490777 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11213/12500 : ℝ)) (X := (31830545839413490777/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (81830545839413490777/50000000000000000000 : ℝ) ≤ (2814593006065247/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (81830545839413490777/50000000000000000000 : ℝ)^32 ≤ (2814593006065247/2500000000000000 : ℝ)^133 := by
      have hnat : (81830545839413490777 : ℕ)^32*2500000000000000^133 ≤ 2814593006065247^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        81830545839413490777 50000000000000000000 2814593006065247 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2814593006065247/2500000000000000 : ℝ)) (X := (81830545839413490777/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (56830545839413490777/25000000000000000000 : ℝ) ≤ (3046130930882799/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (56830545839413490777/25000000000000000000 : ℝ)^32 ≤ (3046130930882799/2500000000000000 : ℝ)^133 := by
      have hnat : (56830545839413490777 : ℕ)^32*2500000000000000^133 ≤ 3046130930882799^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56830545839413490777 25000000000000000000 3046130930882799 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3046130930882799/2500000000000000 : ℝ)) (X := (56830545839413490777/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(314593006065247/2242600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(14471120301097/140162500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (11213/12500 : ℝ)) (alpha := (314593006065247/2242600000000000 : ℝ)) (beta := (14471120301097/140162500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11213/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(314593006065247/2242600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(14471120301097/140162500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (44617/50000 : ℝ) ^ (133/32 : ℝ) ≤ (7785774593808459117/12500000000000000000 : ℝ) := by
    have hpowers : (44617/50000 : ℝ)^133 ≤ (7785774593808459117/12500000000000000000 : ℝ)^32 := by
      have hnat : (44617 : ℕ)^133*12500000000000000000^32 ≤ 7785774593808459117^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44617 50000 7785774593808459117 12500000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44617/50000 : ℝ)) (X := (7785774593808459117/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (20285774593808459117/12500000000000000000 : ℝ) ≤ (5617771484192387/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (20285774593808459117/12500000000000000000 : ℝ)^32 ≤ (5617771484192387/5000000000000000 : ℝ)^133 := by
      have hnat : (20285774593808459117 : ℕ)^32*5000000000000000^133 ≤ 5617771484192387^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20285774593808459117 12500000000000000000 5617771484192387 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5617771484192387/5000000000000000 : ℝ)) (X := (20285774593808459117/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (14035774593808459117/6250000000000000000 : ℝ) ≤ (3037224392423751/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (14035774593808459117/6250000000000000000 : ℝ)^32 ≤ (3037224392423751/2500000000000000 : ℝ)^133 := by
      have hnat : (14035774593808459117 : ℕ)^32*2500000000000000^133 ≤ 3037224392423751^133*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14035774593808459117 6250000000000000000 3037224392423751 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3037224392423751/2500000000000000 : ℝ)) (X := (14035774593808459117/6250000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(617771484192387/4461700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(91335460131023/892340000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (44617/50000 : ℝ)) (alpha := (617771484192387/4461700000000000 : ℝ)) (beta := (91335460131023/892340000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (44617/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(617771484192387/4461700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(91335460131023/892340000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (37073/50000 : ℝ) ^ (133/32 : ℝ) ≤ (7210944008517384087/25000000000000000000 : ℝ) := by
    have hpowers : (37073/50000 : ℝ)^133 ≤ (7210944008517384087/25000000000000000000 : ℝ)^32 := by
      have hnat : (37073 : ℕ)^133*25000000000000000000^32 ≤ 7210944008517384087^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37073 50000 7210944008517384087 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37073/50000 : ℝ)) (X := (7210944008517384087/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (32210944008517384087/25000000000000000000 : ℝ) ≤ (1062873135375549/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (32210944008517384087/25000000000000000000 : ℝ)^32 ≤ (1062873135375549/1000000000000000 : ℝ)^133 := by
      have hnat : (32210944008517384087 : ℕ)^32*1000000000000000^133 ≤ 1062873135375549^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32210944008517384087 25000000000000000000 1062873135375549 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1062873135375549/1000000000000000 : ℝ)) (X := (32210944008517384087/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (19710944008517384087/12500000000000000000 : ℝ) ≤ (5579051352811699/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (19710944008517384087/12500000000000000000 : ℝ)^32 ≤ (5579051352811699/5000000000000000 : ℝ)^133 := by
      have hnat : (19710944008517384087 : ℕ)^32*5000000000000000^133 ≤ 5579051352811699^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19710944008517384087 12500000000000000000 5579051352811699 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5579051352811699/5000000000000000 : ℝ)) (X := (19710944008517384087/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(62873135375549/741460000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(132342837966977/1853650000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (37073/50000 : ℝ)) (alpha := (62873135375549/741460000000000 : ℝ)) (beta := (132342837966977/1853650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37073/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(62873135375549/741460000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(132342837966977/1853650000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-234552911/2000000000 : ℝ)*X 0 0+(5010688427/10000000000 : ℝ)*X 0 1+(-6227102519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((156873387/312500000 : ℝ)*X 1 0+(-1168950041/10000000000 : ℝ)*X 1 1+(-1244141493/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1561510007/10000000000 : ℝ)*X 0 0+(1209802711/5000000000 : ℝ)*X 0 1+(-8096616611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((280513571/1000000000 : ℝ)*X 1 0+(-1098792437/10000000000 : ℝ)*X 1 1+(-1617717221/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((102786941/312500000 : ℝ)*X 2 0+(7277071121/10000000000 : ℝ)*X 2 1+(1854482449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1914820817/5000000000 : ℝ)*X 0 0+(7759652479/10000000000 : ℝ)*X 0 1+(-7/2500000000 : ℝ)*X 0 2+(1914820817/5000000000 : ℝ)*X 1 0+(7759652479/10000000000 : ℝ)*X 1 1+(-7/2500000000 : ℝ)*X 1 2+(1914820817/5000000000 : ℝ)*X 2 0+(7759652479/10000000000 : ℝ)*X 2 1+(-7/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-108711069/1000000000 : ℝ)*X 0 0+(1383102787/5000000000 : ℝ)*X 0 1+(-812266231/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2399723769/10000000000 : ℝ)*X 1 0+(-1554122393/10000000000 : ℝ)*X 1 1+(-8114608581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((7194442051/10000000000 : ℝ)*X 2 0+(33895311/100000000 : ℝ)*X 2 1+(1860452123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3937618289/5000000000 : ℝ)*X 0 0+(368418243/1000000000 : ℝ)*X 0 1+(-2787/10000000000 : ℝ)*X 0 2+(3937618289/5000000000 : ℝ)*X 1 0+(368418243/1000000000 : ℝ)*X 1 1+(-2787/10000000000 : ℝ)*X 1 2+(3937618289/5000000000 : ℝ)*X 2 0+(368418243/1000000000 : ℝ)*X 2 1+(-2787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-4012783/100000000 : ℝ)*X 0 0+(3393645737/5000000000 : ℝ)*X 0 1+(-4829330659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3470234159/5000000000 : ℝ)*X 1 0+(-538950303/10000000000 : ℝ)*X 1 1+(-1147543493/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3051956167/10000000000 : ℝ)*X 2 0+(3668939171/5000000000 : ℝ)*X 2 1+(509713533/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((8381646099/10000000000 : ℝ)*X 0 0+(46858127/156250000 : ℝ)*X 0 1+(-34806517/5000000000 : ℝ)*X 0 2+(8381646099/10000000000 : ℝ)*X 1 0+(46858127/156250000 : ℝ)*X 1 1+(-34806517/5000000000 : ℝ)*X 1 2+(8381646099/10000000000 : ℝ)*X 2 0+(46858127/156250000 : ℝ)*X 2 1+(-34806517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305062_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((20091/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20091/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20770101816342617358432361835277/1854726677773300000000000000000000000 : ℝ) := by norm_num
    linear_combination (202875606477/250000000000 : ℝ)*(base7) + (56639/250000000000 : ℝ)*(base49) + (1038901/1000000000000 : ℝ)*(base60) + (2129272571077/1000000000000 : ℝ)*(major_s2_0) + (2129272571077/1000000000000 : ℝ)*(major_s2_1) + (2129272571077/1000000000000 : ℝ)*(major_s2_2) + (235477/31250000000 : ℝ)*(sp_s2_0) + (159423/31250000000 : ℝ)*(sp_s2_1) + (147535367083/62500000000 : ℝ)*(sp_s2_7) + (236064926631/100000000000 : ℝ)*(sp_s2_8) + (590163747947/250000000000 : ℝ)*(sp_s2_9) + (2203839062153/1000000000000 : ℝ)*(sp_s2_13) + (16316639/200000000000 : ℝ)*(sp_s2_14) + (311971/500000000000 : ℝ)*(sp_s2_15) + (278467327249/200000000000 : ℝ)*(f.failure) + (590163747947/250000000000 : ℝ)*(f.sum) + (7229722864037553193/41352151025000000000000000000000 : ℝ)*base63 + (191156052182183/231706250000000000000000000 : ℝ)*base65 + (141706979211257/892340000000000000000000000 : ℝ)*base66 + (293991665534969/741460000000000000000000000 : ℝ)*base69 + (6754718140336572839/16627981960000000000000000000000 : ℝ)*base71 + (25273262685329/140162500000000000000000000 : ℝ)*base73 + (1298077255098939/4461700000000000000000000000 : ℝ)*base75 + (641282815595919/2242600000000000000000000000 : ℝ)*base77 + (20721709540762547219/50029042100000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (77/312500000000000 : ℝ)*base86 + (77/312500000000000 : ℝ)*base88 + (77/312500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20069/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20069/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (210064529348258611996442487/20676075512500000000000000000000 : ℝ) := by norm_num
    linear_combination (812311822793/1000000000000 : ℝ)*(base7) + (1340651/1000000000000 : ℝ)*(base12) + (49359/1000000000000 : ℝ)*(base40) + (49583/200000000000 : ℝ)*(base59) + (262492825461/125000000000 : ℝ)*(major_s2_0) + (262492825461/125000000000 : ℝ)*(major_s2_1) + (262492825461/125000000000 : ℝ)*(major_s2_2) + (433379/1000000000000 : ℝ)*(sp_s2_1) + (79310737/1000000000000 : ℝ)*(sp_s2_8) + (2320668763227/1000000000000 : ℝ)*(sp_s2_14) + (2320590359761/1000000000000 : ℝ)*(sp_s2_15) + (2320670103877/1000000000000 : ℝ)*(sp_s2_16) + (2185446480633/1000000000000 : ℝ)*(sp_s2_20) + (1439981/62500000000 : ℝ)*(sp_s2_27) + (670487157/488281250 : ℝ)*(f.failure) + (2320670103877/1000000000000 : ℝ)*(f.sum) + (335247682706853059/20676075512500000000000000000000 : ℝ)*base62 + (80663079368867/231706250000000000000000000 : ℝ)*base65 + (262043931984897/446170000000000000000000000 : ℝ)*base67 + (51521546715467/370730000000000000000000000 : ℝ)*base69 + (957049164720373061/4156995490000000000000000000000 : ℝ)*base71 + (7430617023079/140162500000000000000000000 : ℝ)*base72 + (470970296168703/2230850000000000000000000000 : ℝ)*base75 + (15565423267209/140162500000000000000000000 : ℝ)*base76 + (352512912705420653/1563407565625000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (57/390625000000000 : ℝ)*base86 + (57/390625000000000 : ℝ)*base88 + (57/390625000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31811/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31811/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1336064849216388080380041206547/185472667777330000000000000000000000 : ℝ) := by norm_num
    linear_combination (67916205349/125000000000 : ℝ)*(base7) + (761899/500000000000 : ℝ)*(base34) + (53282032759/1000000000000 : ℝ)*(base39) + (336299/62500000000 : ℝ)*(base43) + (419092647/50000000000 : ℝ)*(base59) + (1960891325647/1000000000000 : ℝ)*(major_s2_0) + (1960887468661/1000000000000 : ℝ)*(major_s2_1) + (392178569889/200000000000 : ℝ)*(major_s2_2) + (35276893/200000000000 : ℝ)*(sp_s2_9) + (410393/25000000000 : ℝ)*(sp_s2_20) + (460212035051/200000000000 : ℝ)*(sp_s2_21) + (2301067079837/1000000000000 : ℝ)*(sp_s2_22) + (575221328647/250000000000 : ℝ)*(sp_s2_23) + (456386105067/250000000000 : ℝ)*(sp_s2_27) + (641116358497/500000000000 : ℝ)*(f.failure) + (2301067079837/1000000000000 : ℝ)*(f.sum) + (10134419498351194779/41352151025000000000000000000000 : ℝ)*base63 + (21532316544051/370730000000000000000000000 : ℝ)*base65 + (13211808007701/892340000000000000000000000 : ℝ)*base67 + (214493953179037/741460000000000000000000000 : ℝ)*base69 + (15197662206821092303/83139909800000000000000000000000 : ℝ)*base70 + (846731325661/35040625000000000000000000 : ℝ)*base73 + (563528281411247/4461700000000000000000000000 : ℝ)*base75 + (521420278140909/2242600000000000000000000000 : ℝ)*base77 + (4012519289706267329/50029042100000000000000000000000 : ℝ)*base79 + (1299/3125000000000000 : ℝ)*base86 + (1299/3125000000000000 : ℝ)*base88 + (1299/3125000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((11213/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11213/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44617/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(44617/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37073/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37073/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((20091/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20091/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20069/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20069/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-31811/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-31811/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305062_s2 p hpa hpb X hX hprev1

#print axioms solution
