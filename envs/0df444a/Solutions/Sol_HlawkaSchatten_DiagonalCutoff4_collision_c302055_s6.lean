-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c302055_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:22:51.714833+00:00
-- url     : https://prove2.me/submissions/4e371b1d-f529-44c4-9014-c91ed3d9a65d

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
theorem collision_support_c302055_s6_s6_0 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1117102353/5000000000 : ℝ)*x 0 + (1435001517/2500000000 : ℝ)*x 1 + (4838475023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117102353/5000000000 : ℝ)^131 ≤ (13763803545801/100000000000000 : ℝ)^99 := by
    have hnat : (1117102353 : ℕ)^131*100000000000000^99 ≤ 13763803545801^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117102353 5000000000 13763803545801 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1435001517/2500000000 : ℝ)^131 ≤ (9594338270419/20000000000000 : ℝ)^99 := by
    have hnat : (1435001517 : ℕ)^131*20000000000000^99 ≤ 9594338270419^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1435001517 2500000000 9594338270419 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4838475023/10000000000 : ℝ)^131 ≤ (38264505090791/100000000000000 : ℝ)^99 := by
    have hnat : (4838475023 : ℕ)^131*100000000000000^99 ≤ 38264505090791^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4838475023 10000000000 38264505090791 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1117102353/5000000000 : ℝ), (1435001517/2500000000 : ℝ), (4838475023/10000000000 : ℝ)] ![(13763803545801/100000000000000 : ℝ), (9594338270419/20000000000000 : ℝ), (38264505090791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1117102353/5000000000 : ℝ)|^131 ≤ (13763803545801/100000000000000 : ℝ)^99
        have hw : |(-1117102353/5000000000 : ℝ)|=(1117102353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1435001517/2500000000 : ℝ)|^131 ≤ (9594338270419/20000000000000 : ℝ)^99
        have hw : |(1435001517/2500000000 : ℝ)|=(1435001517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4838475023/10000000000 : ℝ)|^131 ≤ (38264505090791/100000000000000 : ℝ)^99
        have hw : |(4838475023/10000000000 : ℝ)|=(4838475023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_2 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (962513541/2000000000 : ℝ)*x 0 + (5739516961/10000000000 : ℝ)*x 1 + (-1134007441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962513541/2000000000 : ℝ)^131 ≤ (18996814799371/50000000000000 : ℝ)^99 := by
    have hnat : (962513541 : ℕ)^131*50000000000000^99 ≤ 18996814799371^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962513541 2000000000 18996814799371 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5739516961/10000000000 : ℝ)^131 ≤ (47966282480423/100000000000000 : ℝ)^99 := by
    have hnat : (5739516961 : ℕ)^131*100000000000000^99 ≤ 47966282480423^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5739516961 10000000000 47966282480423 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134007441/5000000000 : ℝ)^131 ≤ (14040087913567/100000000000000 : ℝ)^99 := by
    have hnat : (1134007441 : ℕ)^131*100000000000000^99 ≤ 14040087913567^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134007441 5000000000 14040087913567 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(962513541/2000000000 : ℝ), (5739516961/10000000000 : ℝ), (-1134007441/5000000000 : ℝ)] ![(18996814799371/50000000000000 : ℝ), (47966282480423/100000000000000 : ℝ), (14040087913567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(962513541/2000000000 : ℝ)|^131 ≤ (18996814799371/50000000000000 : ℝ)^99
        have hw : |(962513541/2000000000 : ℝ)|=(962513541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5739516961/10000000000 : ℝ)|^131 ≤ (47966282480423/100000000000000 : ℝ)^99
        have hw : |(5739516961/10000000000 : ℝ)|=(5739516961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134007441/5000000000 : ℝ)|^131 ≤ (14040087913567/100000000000000 : ℝ)^99
        have hw : |(-1134007441/5000000000 : ℝ)|=(1134007441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5970721087/10000000000 : ℝ)*x 0 + (4092862347/10000000000 : ℝ)*x 1 + (706886101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5970721087/10000000000 : ℝ)^131 ≤ (50539553574551/100000000000000 : ℝ)^99 := by
    have hnat : (5970721087 : ℕ)^131*100000000000000^99 ≤ 50539553574551^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5970721087 10000000000 50539553574551 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4092862347/10000000000 : ℝ)^131 ≤ (30663503138031/100000000000000 : ℝ)^99 := by
    have hnat : (4092862347 : ℕ)^131*100000000000000^99 ≤ 30663503138031^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4092862347 10000000000 30663503138031 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706886101/2500000000 : ℝ)^131 ≤ (469923581689/2500000000000 : ℝ)^99 := by
    have hnat : (706886101 : ℕ)^131*2500000000000^99 ≤ 469923581689^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706886101 2500000000 469923581689 2500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5970721087/10000000000 : ℝ), (4092862347/10000000000 : ℝ), (706886101/2500000000 : ℝ)] ![(50539553574551/100000000000000 : ℝ), (30663503138031/100000000000000 : ℝ), (469923581689/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5970721087/10000000000 : ℝ)|^131 ≤ (50539553574551/100000000000000 : ℝ)^99
        have hw : |(5970721087/10000000000 : ℝ)|=(5970721087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4092862347/10000000000 : ℝ)|^131 ≤ (30663503138031/100000000000000 : ℝ)^99
        have hw : |(4092862347/10000000000 : ℝ)|=(4092862347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706886101/2500000000 : ℝ)|^131 ≤ (469923581689/2500000000000 : ℝ)^99
        have hw : |(706886101/2500000000 : ℝ)|=(706886101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_7 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-929697611/5000000000 : ℝ)*x 0 + (490269737/1000000000 : ℝ)*x 1 + (5946400933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929697611/5000000000 : ℝ)^131 ≤ (10794661574859/100000000000000 : ℝ)^99 := by
    have hnat : (929697611 : ℕ)^131*100000000000000^99 ≤ 10794661574859^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929697611 5000000000 10794661574859 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (490269737/1000000000 : ℝ)^131 ≤ (3893800531077/10000000000000 : ℝ)^99 := by
    have hnat : (490269737 : ℕ)^131*10000000000000^99 ≤ 3893800531077^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490269737 1000000000 3893800531077 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5946400933/10000000000 : ℝ)^131 ≤ (1570854159409/3125000000000 : ℝ)^99 := by
    have hnat : (5946400933 : ℕ)^131*3125000000000^99 ≤ 1570854159409^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5946400933 10000000000 1570854159409 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-929697611/5000000000 : ℝ), (490269737/1000000000 : ℝ), (5946400933/10000000000 : ℝ)] ![(10794661574859/100000000000000 : ℝ), (3893800531077/10000000000000 : ℝ), (1570854159409/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-929697611/5000000000 : ℝ)|^131 ≤ (10794661574859/100000000000000 : ℝ)^99
        have hw : |(-929697611/5000000000 : ℝ)|=(929697611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(490269737/1000000000 : ℝ)|^131 ≤ (3893800531077/10000000000000 : ℝ)^99
        have hw : |(490269737/1000000000 : ℝ)|=(490269737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5946400933/10000000000 : ℝ)|^131 ≤ (1570854159409/3125000000000 : ℝ)^99
        have hw : |(5946400933/10000000000 : ℝ)|=(5946400933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_8 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4532963787/10000000000 : ℝ)*x 0 + (-236950539/5000000000 : ℝ)*x 1 + (706378773/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4532963787/10000000000 : ℝ)^131 ≤ (17550273553479/50000000000000 : ℝ)^99 := by
    have hnat : (4532963787 : ℕ)^131*50000000000000^99 ≤ 17550273553479^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532963787 10000000000 17550273553479 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (236950539/5000000000 : ℝ)^131 ≤ (1768589955229/100000000000000 : ℝ)^99 := by
    have hnat : (236950539 : ℕ)^131*100000000000000^99 ≤ 1768589955229^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236950539 5000000000 1768589955229 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (706378773/1000000000 : ℝ)^131 ≤ (6313086292779/10000000000000 : ℝ)^99 := by
    have hnat : (706378773 : ℕ)^131*10000000000000^99 ≤ 6313086292779^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      706378773 1000000000 6313086292779 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4532963787/10000000000 : ℝ), (-236950539/5000000000 : ℝ), (706378773/1000000000 : ℝ)] ![(17550273553479/50000000000000 : ℝ), (1768589955229/100000000000000 : ℝ), (6313086292779/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4532963787/10000000000 : ℝ)|^131 ≤ (17550273553479/50000000000000 : ℝ)^99
        have hw : |(4532963787/10000000000 : ℝ)|=(4532963787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-236950539/5000000000 : ℝ)|^131 ≤ (1768589955229/100000000000000 : ℝ)^99
        have hw : |(-236950539/5000000000 : ℝ)|=(236950539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(706378773/1000000000 : ℝ)|^131 ≤ (6313086292779/10000000000000 : ℝ)^99
        have hw : |(706378773/1000000000 : ℝ)|=(706378773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_9 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4507852587/10000000000 : ℝ)*x 0 + (1673301827/2500000000 : ℝ)*x 1 + (-1248207263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4507852587/10000000000 : ℝ)^131 ≤ (34843480469073/100000000000000 : ℝ)^99 := by
    have hnat : (4507852587 : ℕ)^131*100000000000000^99 ≤ 34843480469073^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507852587 10000000000 34843480469073 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1673301827/2500000000 : ℝ)^131 ≤ (29392981616511/50000000000000 : ℝ)^99 := by
    have hnat : (1673301827 : ℕ)^131*50000000000000^99 ≤ 29392981616511^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1673301827 2500000000 29392981616511 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1248207263/10000000000 : ℝ)^131 ≤ (6370556290681/100000000000000 : ℝ)^99 := by
    have hnat : (1248207263 : ℕ)^131*100000000000000^99 ≤ 6370556290681^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1248207263 10000000000 6370556290681 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4507852587/10000000000 : ℝ), (1673301827/2500000000 : ℝ), (-1248207263/10000000000 : ℝ)] ![(34843480469073/100000000000000 : ℝ), (29392981616511/50000000000000 : ℝ), (6370556290681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4507852587/10000000000 : ℝ)|^131 ≤ (34843480469073/100000000000000 : ℝ)^99
        have hw : |(4507852587/10000000000 : ℝ)|=(4507852587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1673301827/2500000000 : ℝ)|^131 ≤ (29392981616511/50000000000000 : ℝ)^99
        have hw : |(1673301827/2500000000 : ℝ)|=(1673301827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1248207263/10000000000 : ℝ)|^131 ≤ (6370556290681/100000000000000 : ℝ)^99
        have hw : |(-1248207263/10000000000 : ℝ)|=(1248207263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_13 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5172379331/10000000000 : ℝ)*x 0 + (2947369587/5000000000 : ℝ)*x 1 + (776950763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172379331/10000000000 : ℝ)^131 ≤ (2089853506739/5000000000000 : ℝ)^99 := by
    have hnat : (5172379331 : ℕ)^131*5000000000000^99 ≤ 2089853506739^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172379331 10000000000 2089853506739 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2947369587/5000000000 : ℝ)^131 ≤ (49690267054771/100000000000000 : ℝ)^99 := by
    have hnat : (2947369587 : ℕ)^131*100000000000000^99 ≤ 49690267054771^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2947369587 5000000000 49690267054771 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (776950763/5000000000 : ℝ)^131 ≤ (425633139737/5000000000000 : ℝ)^99 := by
    have hnat : (776950763 : ℕ)^131*5000000000000^99 ≤ 425633139737^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776950763 5000000000 425633139737 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172379331/10000000000 : ℝ), (2947369587/5000000000 : ℝ), (776950763/5000000000 : ℝ)] ![(2089853506739/5000000000000 : ℝ), (49690267054771/100000000000000 : ℝ), (425633139737/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172379331/10000000000 : ℝ)|^131 ≤ (2089853506739/5000000000000 : ℝ)^99
        have hw : |(5172379331/10000000000 : ℝ)|=(5172379331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2947369587/5000000000 : ℝ)|^131 ≤ (49690267054771/100000000000000 : ℝ)^99
        have hw : |(2947369587/5000000000 : ℝ)|=(2947369587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(776950763/5000000000 : ℝ)|^131 ≤ (425633139737/5000000000000 : ℝ)^99
        have hw : |(776950763/5000000000 : ℝ)|=(776950763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_14 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1097048251/10000000000 : ℝ)*x 0 + (1323428253/2500000000 : ℝ)*x 1 + (3029486293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097048251/10000000000 : ℝ)^131 ≤ (537026432331/10000000000000 : ℝ)^99 := by
    have hnat : (1097048251 : ℕ)^131*10000000000000^99 ≤ 537026432331^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097048251 10000000000 537026432331 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1323428253/2500000000 : ℝ)^131 ≤ (43099360211917/100000000000000 : ℝ)^99 := by
    have hnat : (1323428253 : ℕ)^131*100000000000000^99 ≤ 43099360211917^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323428253 2500000000 43099360211917 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3029486293/5000000000 : ℝ)^131 ≤ (51530375447929/100000000000000 : ℝ)^99 := by
    have hnat : (3029486293 : ℕ)^131*100000000000000^99 ≤ 51530375447929^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3029486293 5000000000 51530375447929 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1097048251/10000000000 : ℝ), (1323428253/2500000000 : ℝ), (3029486293/5000000000 : ℝ)] ![(537026432331/10000000000000 : ℝ), (43099360211917/100000000000000 : ℝ), (51530375447929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1097048251/10000000000 : ℝ)|^131 ≤ (537026432331/10000000000000 : ℝ)^99
        have hw : |(-1097048251/10000000000 : ℝ)|=(1097048251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1323428253/2500000000 : ℝ)|^131 ≤ (43099360211917/100000000000000 : ℝ)^99
        have hw : |(1323428253/2500000000 : ℝ)|=(1323428253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3029486293/5000000000 : ℝ)|^131 ≤ (51530375447929/100000000000000 : ℝ)^99
        have hw : |(3029486293/5000000000 : ℝ)|=(3029486293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_15 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2100760383/5000000000 : ℝ)*x 0 + (-529156307/5000000000 : ℝ)*x 1 + (7064045343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100760383/5000000000 : ℝ)^131 ≤ (31745292069503/100000000000000 : ℝ)^99 := by
    have hnat : (2100760383 : ℕ)^131*100000000000000^99 ≤ 31745292069503^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100760383 5000000000 31745292069503 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529156307/5000000000 : ℝ)^131 ≤ (2560399213521/50000000000000 : ℝ)^99 := by
    have hnat : (529156307 : ℕ)^131*50000000000000^99 ≤ 2560399213521^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529156307 5000000000 2560399213521 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7064045343/10000000000 : ℝ)^131 ≤ (7891738686663/12500000000000 : ℝ)^99 := by
    have hnat : (7064045343 : ℕ)^131*12500000000000^99 ≤ 7891738686663^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7064045343 10000000000 7891738686663 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100760383/5000000000 : ℝ), (-529156307/5000000000 : ℝ), (7064045343/10000000000 : ℝ)] ![(31745292069503/100000000000000 : ℝ), (2560399213521/50000000000000 : ℝ), (7891738686663/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100760383/5000000000 : ℝ)|^131 ≤ (31745292069503/100000000000000 : ℝ)^99
        have hw : |(2100760383/5000000000 : ℝ)|=(2100760383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-529156307/5000000000 : ℝ)|^131 ≤ (2560399213521/50000000000000 : ℝ)^99
        have hw : |(-529156307/5000000000 : ℝ)|=(529156307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7064045343/10000000000 : ℝ)|^131 ≤ (7891738686663/12500000000000 : ℝ)^99
        have hw : |(7064045343/10000000000 : ℝ)|=(7064045343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_16 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (754637633/1250000000 : ℝ)*x 0 + (5293217083/10000000000 : ℝ)*x 1 + (-567816189/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (754637633/1250000000 : ℝ)^131 ≤ (51284380731661/100000000000000 : ℝ)^99 := by
    have hnat : (754637633 : ℕ)^131*100000000000000^99 ≤ 51284380731661^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754637633 1250000000 51284380731661 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5293217083/10000000000 : ℝ)^131 ≤ (43094017528257/100000000000000 : ℝ)^99 := by
    have hnat : (5293217083 : ℕ)^131*100000000000000^99 ≤ 43094017528257^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293217083 10000000000 43094017528257 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567816189/5000000000 : ℝ)^131 ≤ (44972813869/800000000000 : ℝ)^99 := by
    have hnat : (567816189 : ℕ)^131*800000000000^99 ≤ 44972813869^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567816189 5000000000 44972813869 800000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(754637633/1250000000 : ℝ), (5293217083/10000000000 : ℝ), (-567816189/5000000000 : ℝ)] ![(51284380731661/100000000000000 : ℝ), (43094017528257/100000000000000 : ℝ), (44972813869/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(754637633/1250000000 : ℝ)|^131 ≤ (51284380731661/100000000000000 : ℝ)^99
        have hw : |(754637633/1250000000 : ℝ)|=(754637633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5293217083/10000000000 : ℝ)|^131 ≤ (43094017528257/100000000000000 : ℝ)^99
        have hw : |(5293217083/10000000000 : ℝ)|=(5293217083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567816189/5000000000 : ℝ)|^131 ≤ (44972813869/800000000000 : ℝ)^99
        have hw : |(-567816189/5000000000 : ℝ)|=(567816189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_20 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (7350838731/10000000000 : ℝ)*x 0 + (700316631/2000000000 : ℝ)*x 1 + (1553388067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7350838731/10000000000 : ℝ)^131 ≤ (33273820029571/50000000000000 : ℝ)^99 := by
    have hnat : (7350838731 : ℕ)^131*50000000000000^99 ≤ 33273820029571^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7350838731 10000000000 33273820029571 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (700316631/2000000000 : ℝ)^131 ≤ (3117927374023/12500000000000 : ℝ)^99 := by
    have hnat : (700316631 : ℕ)^131*12500000000000^99 ≤ 3117927374023^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      700316631 2000000000 3117927374023 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1553388067/10000000000 : ℝ)^131 ≤ (8508940929761/100000000000000 : ℝ)^99 := by
    have hnat : (1553388067 : ℕ)^131*100000000000000^99 ≤ 8508940929761^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553388067 10000000000 8508940929761 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7350838731/10000000000 : ℝ), (700316631/2000000000 : ℝ), (1553388067/10000000000 : ℝ)] ![(33273820029571/50000000000000 : ℝ), (3117927374023/12500000000000 : ℝ), (8508940929761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7350838731/10000000000 : ℝ)|^131 ≤ (33273820029571/50000000000000 : ℝ)^99
        have hw : |(7350838731/10000000000 : ℝ)|=(7350838731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(700316631/2000000000 : ℝ)|^131 ≤ (3117927374023/12500000000000 : ℝ)^99
        have hw : |(700316631/2000000000 : ℝ)|=(700316631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1553388067/10000000000 : ℝ)|^131 ≤ (8508940929761/100000000000000 : ℝ)^99
        have hw : |(1553388067/10000000000 : ℝ)|=(1553388067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_21 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-208982833/2000000000 : ℝ)*x 0 + (1617371181/2500000000 : ℝ)*x 1 + (4886204067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208982833/2000000000 : ℝ)^131 ≤ (5035188867427/100000000000000 : ℝ)^99 := by
    have hnat : (208982833 : ℕ)^131*100000000000000^99 ≤ 5035188867427^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208982833 2000000000 5035188867427 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1617371181/2500000000 : ℝ)^131 ≤ (14050011233187/25000000000000 : ℝ)^99 := by
    have hnat : (1617371181 : ℕ)^131*25000000000000^99 ≤ 14050011233187^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1617371181 2500000000 14050011233187 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4886204067/10000000000 : ℝ)^131 ≤ (38764766184889/100000000000000 : ℝ)^99 := by
    have hnat : (4886204067 : ℕ)^131*100000000000000^99 ≤ 38764766184889^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886204067 10000000000 38764766184889 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208982833/2000000000 : ℝ), (1617371181/2500000000 : ℝ), (4886204067/10000000000 : ℝ)] ![(5035188867427/100000000000000 : ℝ), (14050011233187/25000000000000 : ℝ), (38764766184889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208982833/2000000000 : ℝ)|^131 ≤ (5035188867427/100000000000000 : ℝ)^99
        have hw : |(-208982833/2000000000 : ℝ)|=(208982833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1617371181/2500000000 : ℝ)|^131 ≤ (14050011233187/25000000000000 : ℝ)^99
        have hw : |(1617371181/2500000000 : ℝ)|=(1617371181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4886204067/10000000000 : ℝ)|^131 ≤ (38764766184889/100000000000000 : ℝ)^99
        have hw : |(4886204067/10000000000 : ℝ)|=(4886204067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_22 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3057173281/5000000000 : ℝ)*x 0 + (-18436159/400000000 : ℝ)*x 1 + (43544269/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3057173281/5000000000 : ℝ)^131 ≤ (26077231707287/50000000000000 : ℝ)^99 := by
    have hnat : (3057173281 : ℕ)^131*50000000000000^99 ≤ 26077231707287^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3057173281 5000000000 26077231707287 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18436159/400000000 : ℝ)^131 ≤ (426173228443/25000000000000 : ℝ)^99 := by
    have hnat : (18436159 : ℕ)^131*25000000000000^99 ≤ 426173228443^99*400000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18436159 400000000 426173228443 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43544269/78125000 : ℝ)^131 ≤ (5767605457357/12500000000000 : ℝ)^99 := by
    have hnat : (43544269 : ℕ)^131*12500000000000^99 ≤ 5767605457357^99*78125000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43544269 78125000 5767605457357 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3057173281/5000000000 : ℝ), (-18436159/400000000 : ℝ), (43544269/78125000 : ℝ)] ![(26077231707287/50000000000000 : ℝ), (426173228443/25000000000000 : ℝ), (5767605457357/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3057173281/5000000000 : ℝ)|^131 ≤ (26077231707287/50000000000000 : ℝ)^99
        have hw : |(3057173281/5000000000 : ℝ)|=(3057173281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18436159/400000000 : ℝ)|^131 ≤ (426173228443/25000000000000 : ℝ)^99
        have hw : |(-18436159/400000000 : ℝ)|=(18436159/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43544269/78125000 : ℝ)|^131 ≤ (5767605457357/12500000000000 : ℝ)^99
        have hw : |(43544269/78125000 : ℝ)|=(43544269/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_23 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4171186297/10000000000 : ℝ)*x 0 + (6706205601/10000000000 : ℝ)*x 1 + (-1704428861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4171186297/10000000000 : ℝ)^131 ≤ (31442365455811/100000000000000 : ℝ)^99 := by
    have hnat : (4171186297 : ℕ)^131*100000000000000^99 ≤ 31442365455811^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171186297 10000000000 31442365455811 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6706205601/10000000000 : ℝ)^131 ≤ (58937074905549/100000000000000 : ℝ)^99 := by
    have hnat : (6706205601 : ℕ)^131*100000000000000^99 ≤ 58937074905549^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6706205601 10000000000 58937074905549 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1704428861/10000000000 : ℝ)^131 ≤ (4810279811591/50000000000000 : ℝ)^99 := by
    have hnat : (1704428861 : ℕ)^131*50000000000000^99 ≤ 4810279811591^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704428861 10000000000 4810279811591 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4171186297/10000000000 : ℝ), (6706205601/10000000000 : ℝ), (-1704428861/10000000000 : ℝ)] ![(31442365455811/100000000000000 : ℝ), (58937074905549/100000000000000 : ℝ), (4810279811591/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4171186297/10000000000 : ℝ)|^131 ≤ (31442365455811/100000000000000 : ℝ)^99
        have hw : |(4171186297/10000000000 : ℝ)|=(4171186297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6706205601/10000000000 : ℝ)|^131 ≤ (58937074905549/100000000000000 : ℝ)^99
        have hw : |(6706205601/10000000000 : ℝ)|=(6706205601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1704428861/10000000000 : ℝ)|^131 ≤ (4810279811591/50000000000000 : ℝ)^99
        have hw : |(-1704428861/10000000000 : ℝ)|=(1704428861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c302055_s6_s6_27 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1840297691/2500000000 : ℝ)*x 0 + (43549593/156250000 : ℝ)*x 1 + (2370502453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1840297691/2500000000 : ℝ)^131 ≤ (8333959813119/12500000000000 : ℝ)^99 := by
    have hnat : (1840297691 : ℕ)^131*12500000000000^99 ≤ 8333959813119^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840297691 2500000000 8333959813119 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43549593/156250000 : ℝ)^131 ≤ (9221321708597/50000000000000 : ℝ)^99 := by
    have hnat : (43549593 : ℕ)^131*50000000000000^99 ≤ 9221321708597^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43549593 156250000 9221321708597 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2370502453/10000000000 : ℝ)^131 ≤ (465177439419/3125000000000 : ℝ)^99 := by
    have hnat : (2370502453 : ℕ)^131*3125000000000^99 ≤ 465177439419^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370502453 10000000000 465177439419 3125000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1840297691/2500000000 : ℝ), (43549593/156250000 : ℝ), (2370502453/10000000000 : ℝ)] ![(8333959813119/12500000000000 : ℝ), (9221321708597/50000000000000 : ℝ), (465177439419/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1840297691/2500000000 : ℝ)|^131 ≤ (8333959813119/12500000000000 : ℝ)^99
        have hw : |(1840297691/2500000000 : ℝ)|=(1840297691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43549593/156250000 : ℝ)|^131 ≤ (9221321708597/50000000000000 : ℝ)^99
        have hw : |(43549593/156250000 : ℝ)|=(43549593/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2370502453/10000000000 : ℝ)|^131 ≤ (465177439419/3125000000000 : ℝ)^99
        have hw : |(2370502453/10000000000 : ℝ)|=(2370502453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c302055_s6 (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((29519/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29519/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14879/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14879/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60917/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(60917/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2141/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2141/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43833/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43857/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43857/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4769/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4769/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4769/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (29519/50000 : ℝ) ^ (65/16 : ℝ) ≤ (5877495136146789399/50000000000000000000 : ℝ) := by
    have hpowers : (29519/50000 : ℝ)^65 ≤ (5877495136146789399/50000000000000000000 : ℝ)^16 := by
      have hnat : (29519 : ℕ)^65*50000000000000000000^16 ≤ 5877495136146789399^16*50000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29519 50000 5877495136146789399 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29519/50000 : ℝ)) (X := (5877495136146789399/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0a : (55877495136146789399/50000000000000000000 : ℝ) ≤ (1284668579524581/1250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (55877495136146789399/50000000000000000000 : ℝ)^16 ≤ (1284668579524581/1250000000000000 : ℝ)^65 := by
      have hnat : (55877495136146789399 : ℕ)^16*1250000000000000^65 ≤ 1284668579524581^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55877495136146789399 50000000000000000000 1284668579524581 1250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1284668579524581/1250000000000000 : ℝ)) (X := (55877495136146789399/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner0b : (30877495136146789399/25000000000000000000 : ℝ) ≤ (263337568839193/250000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (30877495136146789399/25000000000000000000 : ℝ)^16 ≤ (263337568839193/250000000000000 : ℝ)^65 := by
      have hnat : (30877495136146789399 : ℕ)^16*250000000000000^65 ≤ 263337568839193^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30877495136146789399 25000000000000000000 263337568839193 250000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (263337568839193/250000000000000 : ℝ)) (X := (30877495136146789399/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(34668579524581/737975000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(4002408083923/92246875000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (29519/50000 : ℝ)) (alpha := (34668579524581/737975000000000 : ℝ)) (beta := (4002408083923/92246875000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (29519/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(34668579524581/737975000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(4002408083923/92246875000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (14879/25000 : ℝ) ^ (65/16 : ℝ) ≤ (12146455092372549667/100000000000000000000 : ℝ) := by
    have hpowers : (14879/25000 : ℝ)^65 ≤ (12146455092372549667/100000000000000000000 : ℝ)^16 := by
      have hnat : (14879 : ℕ)^65*100000000000000000000^16 ≤ 12146455092372549667^16*25000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14879 25000 12146455092372549667 100000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14879/25000 : ℝ)) (X := (12146455092372549667/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1a : (112146455092372549667/100000000000000000000 : ℝ) ≤ (2571549647056781/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (112146455092372549667/100000000000000000000 : ℝ)^16 ≤ (2571549647056781/2500000000000000 : ℝ)^65 := by
      have hnat : (112146455092372549667 : ℕ)^16*2500000000000000^65 ≤ 2571549647056781^65*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112146455092372549667 100000000000000000000 2571549647056781 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2571549647056781/2500000000000000 : ℝ)) (X := (112146455092372549667/100000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner1b : (62146455092372549667/50000000000000000000 : ℝ) ≤ (10549899778260607/10000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (62146455092372549667/50000000000000000000 : ℝ)^16 ≤ (10549899778260607/10000000000000000 : ℝ)^65 := by
      have hnat : (62146455092372549667 : ℕ)^16*10000000000000000^65 ≤ 10549899778260607^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62146455092372549667 50000000000000000000 10549899778260607 10000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10549899778260607/10000000000000000 : ℝ)) (X := (62146455092372549667/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(71549647056781/1487900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(263701190033483/5951600000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (14879/25000 : ℝ)) (alpha := (71549647056781/1487900000000000 : ℝ)) (beta := (263701190033483/5951600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (14879/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(71549647056781/1487900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(263701190033483/5951600000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (60917/100000 : ℝ) ^ (65/16 : ℝ) ≤ (6675290808024743879/50000000000000000000 : ℝ) := by
    have hpowers : (60917/100000 : ℝ)^65 ≤ (6675290808024743879/50000000000000000000 : ℝ)^16 := by
      have hnat : (60917 : ℕ)^65*50000000000000000000^16 ≤ 6675290808024743879^16*100000^65 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60917 100000 6675290808024743879 50000000000000000000 65 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60917/100000 : ℝ)) (X := (6675290808024743879/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2a : (56675290808024743879/50000000000000000000 : ℝ) ≤ (5156637712245869/5000000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (56675290808024743879/50000000000000000000 : ℝ)^16 ≤ (5156637712245869/5000000000000000 : ℝ)^65 := by
      have hnat : (56675290808024743879 : ℕ)^16*5000000000000000^65 ≤ 5156637712245869^65*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56675290808024743879 50000000000000000000 5156637712245869 5000000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5156637712245869/5000000000000000 : ℝ)) (X := (56675290808024743879/50000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have s6_corner2b : (31675290808024743879/25000000000000000000 : ℝ) ≤ (2649963238175463/2500000000000000 : ℝ) ^ (65/16 : ℝ) := by
    have hpowers : (31675290808024743879/25000000000000000000 : ℝ)^16 ≤ (2649963238175463/2500000000000000 : ℝ)^65 := by
      have hnat : (31675290808024743879 : ℕ)^16*2500000000000000^65 ≤ 2649963238175463^65*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31675290808024743879 25000000000000000000 2649963238175463 2500000000000000 16 65 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2649963238175463/2500000000000000 : ℝ)) (X := (31675290808024743879/25000000000000000000 : ℝ)) (by norm_num) 65 16 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(156637712245869/3045850000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(143288764105057/3045850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (65/16 : ℝ)) (rho := (60917/100000 : ℝ)) (alpha := (156637712245869/3045850000000000 : ℝ)) (beta := (143288764105057/3045850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (60917/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(156637712245869/3045850000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(143288764105057/3045850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-1117102353/5000000000 : ℝ)*X 0 0+(1435001517/2500000000 : ℝ)*X 0 1+(4838475023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((962513541/2000000000 : ℝ)*X 2 0+(5739516961/10000000000 : ℝ)*X 2 1+(-1134007441/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((5970721087/10000000000 : ℝ)*X 0 0+(4092862347/10000000000 : ℝ)*X 0 1+(706886101/2500000000 : ℝ)*X 0 2+(5970721087/10000000000 : ℝ)*X 1 0+(4092862347/10000000000 : ℝ)*X 1 1+(706886101/2500000000 : ℝ)*X 1 2+(5970721087/10000000000 : ℝ)*X 2 0+(4092862347/10000000000 : ℝ)*X 2 1+(706886101/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-929697611/5000000000 : ℝ)*X 0 0+(490269737/1000000000 : ℝ)*X 0 1+(5946400933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((4532963787/10000000000 : ℝ)*X 1 0+(-236950539/5000000000 : ℝ)*X 1 1+(706378773/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((4507852587/10000000000 : ℝ)*X 2 0+(1673301827/2500000000 : ℝ)*X 2 1+(-1248207263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((5172379331/10000000000 : ℝ)*X 0 0+(2947369587/5000000000 : ℝ)*X 0 1+(776950763/5000000000 : ℝ)*X 0 2+(5172379331/10000000000 : ℝ)*X 1 0+(2947369587/5000000000 : ℝ)*X 1 1+(776950763/5000000000 : ℝ)*X 1 2+(5172379331/10000000000 : ℝ)*X 2 0+(2947369587/5000000000 : ℝ)*X 2 1+(776950763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-1097048251/10000000000 : ℝ)*X 0 0+(1323428253/2500000000 : ℝ)*X 0 1+(3029486293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((2100760383/5000000000 : ℝ)*X 1 0+(-529156307/5000000000 : ℝ)*X 1 1+(7064045343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((754637633/1250000000 : ℝ)*X 2 0+(5293217083/10000000000 : ℝ)*X 2 1+(-567816189/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((7350838731/10000000000 : ℝ)*X 0 0+(700316631/2000000000 : ℝ)*X 0 1+(1553388067/10000000000 : ℝ)*X 0 2+(7350838731/10000000000 : ℝ)*X 1 0+(700316631/2000000000 : ℝ)*X 1 1+(1553388067/10000000000 : ℝ)*X 1 2+(7350838731/10000000000 : ℝ)*X 2 0+(700316631/2000000000 : ℝ)*X 2 1+(1553388067/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-208982833/2000000000 : ℝ)*X 0 0+(1617371181/2500000000 : ℝ)*X 0 1+(4886204067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((3057173281/5000000000 : ℝ)*X 1 0+(-18436159/400000000 : ℝ)*X 1 1+(43544269/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((4171186297/10000000000 : ℝ)*X 2 0+(6706205601/10000000000 : ℝ)*X 2 1+(-1704428861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((1840297691/2500000000 : ℝ)*X 0 0+(43549593/156250000 : ℝ)*X 0 1+(2370502453/10000000000 : ℝ)*X 0 2+(1840297691/2500000000 : ℝ)*X 1 0+(43549593/156250000 : ℝ)*X 1 1+(2370502453/10000000000 : ℝ)*X 1 2+(1840297691/2500000000 : ℝ)*X 2 0+(43549593/156250000 : ℝ)*X 2 1+(2370502453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c302055_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((2141/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2141/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5892532017497464619321709679563/1070222022612680000000000000000000000 : ℝ) := by norm_num
    linear_combination (1463807/500000000000 : ℝ)*(base19) + (255635457087/1000000000000 : ℝ)*(base49) + (839857651051/200000000000 : ℝ)*(major_s6_0) + (839857651051/200000000000 : ℝ)*(major_s6_1) + (839857651051/200000000000 : ℝ)*(major_s6_2) + (36440131/1000000000000 : ℝ)*(sp_s6_0) + (2589547/500000000000 : ℝ)*(sp_s6_6) + (5583429442281/1000000000000 : ℝ)*(sp_s6_7) + (279171626617/50000000000 : ℝ)*(sp_s6_8) + (5583386032857/1000000000000 : ℝ)*(sp_s6_9) + (4504155559/1600000000 : ℝ)*(sp_s6_13) + (255573/40000000000 : ℝ)*(sp_s6_14) + (4601473/125000000000 : ℝ)*(sp_s6_15) + (86238881/1000000000000 : ℝ)*(sp_s6_23) + (2815102403469/1000000000000 : ℝ)*(f.failure) + (2791736135869/500000000000 : ℝ)*(f.sum) + (803566357181212869/18127680860000000000000000000000 : ℝ)*base63 + (7757422085141/24366800000000000000000000 : ℝ)*base65 + (79978059178217/1190320000000000000000000000 : ℝ)*base66 + (1273853644881/15229250000000000000000000 : ℝ)*base68 + (1907362478457390831/17982089230000000000000000000000 : ℝ)*base71 + (48360643076127/147595000000000000000000000 : ℝ)*base72 + (36397492092571/297580000000000000000000000 : ℝ)*base74 + (71892103123033/295190000000000000000000000 : ℝ)*base76 + (10105274226341836903/35137056080000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (2927/10000000000000000 : ℝ)*base86 + (2927/10000000000000000 : ℝ)*base88 + (2927/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43833/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1249011333085157965849755783/90638404300000000000000000000000 : ℝ) := by norm_num
    linear_combination (187603/62500000000 : ℝ)*(base39) + (37138412821/200000000000 : ℝ)*(base49) + (1581409/1000000000000 : ℝ)*(base60) + (2021006968971/500000000000 : ℝ)*(major_s6_0) + (2021006968971/500000000000 : ℝ)*(major_s6_1) + (2021006968971/500000000000 : ℝ)*(major_s6_2) + (4704963/500000000000 : ℝ)*(sp_s6_2) + (28980653/1000000000000 : ℝ)*(sp_s6_7) + (16782711/250000000000 : ℝ)*(sp_s6_8) + (5374324838853/1000000000000 : ℝ)*(sp_s6_14) + (5374286688661/1000000000000 : ℝ)*(sp_s6_15) + (268717220479/50000000000 : ℝ)*(sp_s6_16) + (27095820393/10000000000 : ℝ)*(sp_s6_20) + (8742369/100000000000 : ℝ)*(sp_s6_27) + (270966946299/100000000000 : ℝ)*(f.failure) + (2687176909753/500000000000 : ℝ)*(f.sum) + (3002469386950389139/11329800537500000000000000000000 : ℝ)*base62 + (19660418154121/761462500000000000000000000 : ℝ)*base65 + (694390074935653/2975800000000000000000000000 : ℝ)*base66 + (266425009103/47591406250000000000000000 : ℝ)*base68 + (2761602252888860811/22477611537500000000000000000000 : ℝ)*base71 + (228004828607221/1475950000000000000000000000 : ℝ)*base73 + (215370478559599/743950000000000000000000000 : ℝ)*base74 + (150242375299483/737975000000000000000000000 : ℝ)*base76 + (21854183503210336031/87842640200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (183/1000000000000000 : ℝ)*base87 + (183/1000000000000000 : ℝ)*base89 + (183/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43857/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43857/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (931936469022679762115724145089/167222191033231250000000000000000000 : ℝ) := by norm_num
    linear_combination (30919591993/250000000000 : ℝ)*(base40) + (138229707709/1000000000000 : ℝ)*(base49) + (1208373/500000000000 : ℝ)*(base59) + (3921140299253/1000000000000 : ℝ)*(major_s6_0) + (3921140299253/1000000000000 : ℝ)*(major_s6_1) + (3921140299253/1000000000000 : ℝ)*(major_s6_2) + (1951381/250000000000 : ℝ)*(sp_s6_0) + (950669/100000000000 : ℝ)*(sp_s6_2) + (5971927/250000000000 : ℝ)*(sp_s6_9) + (37403303/500000000000 : ℝ)*(sp_s6_20) + (10427264537/2000000000 : ℝ)*(sp_s6_21) + (208545602961/40000000000 : ℝ)*(sp_s6_22) + (5213606679627/1000000000000 : ℝ)*(sp_s6_23) + (525712772037/200000000000 : ℝ)*(sp_s6_27) + (2628638666791/1000000000000 : ℝ)*(f.failure) + (208545602961/40000000000 : ℝ)*(f.sum) + (18419429614782255127/90638404300000000000000000000000 : ℝ)*base63 + (3823298755335451/3045850000000000000000000000 : ℝ)*base65 + (1925982540153361/5951600000000000000000000000 : ℝ)*base67 + (1265534970111897/3045850000000000000000000000 : ℝ)*base69 + (4443014983514834317/11238805768750000000000000000000 : ℝ)*base71 + (578190161665139/1475950000000000000000000000 : ℝ)*base73 + (652456452209703/1487900000000000000000000000 : ℝ)*base75 + (167458177265541/1475950000000000000000000000 : ℝ)*base77 + (21304759221064255593/175685280400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (8653/10000000000000000 : ℝ)*base86 + (8653/10000000000000000 : ℝ)*base88 + (8653/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (65/16 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (14917/10000 : ℝ) (36753/20000 : ℝ) (4769/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((29519/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29519/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14879/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14879/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60917/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(60917/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2141/5000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2141/5000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43833/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(43833/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(43857/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(43857/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c302055_s6 p hpa hpb X hX hprev5

#print axioms solution
