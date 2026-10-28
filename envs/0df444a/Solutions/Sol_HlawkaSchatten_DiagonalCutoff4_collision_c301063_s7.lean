-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301063_s7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:41:00.418904+00:00
-- url     : https://prove2.me/submissions/0d842d00-edd4-4b49-8195-7c84ca8f6750

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
theorem collision_support_c301063_s7_s7_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-856305233/5000000000 : ℝ)*x 0 + (1367370317/2500000000 : ℝ)*x 1 + (1103930601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856305233/5000000000 : ℝ)^65 ≤ (9625530293211/100000000000000 : ℝ)^49 := by
    have hnat : (856305233 : ℕ)^65*100000000000000^49 ≤ 9625530293211^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856305233 5000000000 9625530293211 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367370317/2500000000 : ℝ)^65 ≤ (44913565340583/100000000000000 : ℝ)^49 := by
    have hnat : (1367370317 : ℕ)^65*100000000000000^49 ≤ 44913565340583^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367370317 2500000000 44913565340583 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103930601/2000000000 : ℝ)^65 ≤ (45460904351747/100000000000000 : ℝ)^49 := by
    have hnat : (1103930601 : ℕ)^65*100000000000000^49 ≤ 45460904351747^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103930601 2000000000 45460904351747 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-856305233/5000000000 : ℝ), (1367370317/2500000000 : ℝ), (1103930601/2000000000 : ℝ)] ![(9625530293211/100000000000000 : ℝ), (44913565340583/100000000000000 : ℝ), (45460904351747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-856305233/5000000000 : ℝ)|^65 ≤ (9625530293211/100000000000000 : ℝ)^49
        have hw : |(-856305233/5000000000 : ℝ)|=(856305233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367370317/2500000000 : ℝ)|^65 ≤ (44913565340583/100000000000000 : ℝ)^49
        have hw : |(1367370317/2500000000 : ℝ)|=(1367370317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103930601/2000000000 : ℝ)|^65 ≤ (45460904351747/100000000000000 : ℝ)^49
        have hw : |(1103930601/2000000000 : ℝ)|=(1103930601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (683868867/1250000000 : ℝ)*x 0 + (-1726346071/10000000000 : ℝ)*x 1 + (5508798717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683868867/1250000000 : ℝ)^65 ≤ (2808098448709/6250000000000 : ℝ)^49 := by
    have hnat : (683868867 : ℕ)^65*6250000000000^49 ≤ 2808098448709^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683868867 1250000000 2808098448709 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1726346071/10000000000 : ℝ)^65 ≤ (4864035750601/50000000000000 : ℝ)^49 := by
    have hnat : (1726346071 : ℕ)^65*50000000000000^49 ≤ 4864035750601^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726346071 10000000000 4864035750601 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508798717/10000000000 : ℝ)^65 ≤ (11335588326183/25000000000000 : ℝ)^49 := by
    have hnat : (5508798717 : ℕ)^65*25000000000000^49 ≤ 11335588326183^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508798717 10000000000 11335588326183 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(683868867/1250000000 : ℝ), (-1726346071/10000000000 : ℝ), (5508798717/10000000000 : ℝ)] ![(2808098448709/6250000000000 : ℝ), (4864035750601/50000000000000 : ℝ), (11335588326183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(683868867/1250000000 : ℝ)|^65 ≤ (2808098448709/6250000000000 : ℝ)^49
        have hw : |(683868867/1250000000 : ℝ)|=(683868867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1726346071/10000000000 : ℝ)|^65 ≤ (4864035750601/50000000000000 : ℝ)^49
        have hw : |(-1726346071/10000000000 : ℝ)|=(1726346071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508798717/10000000000 : ℝ)|^65 ≤ (11335588326183/25000000000000 : ℝ)^49
        have hw : |(5508798717/10000000000 : ℝ)|=(5508798717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (344010011/625000000 : ℝ)*x 0 + (5501032999/10000000000 : ℝ)*x 1 + (-844554299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344010011/625000000 : ℝ)^65 ≤ (45291714189463/100000000000000 : ℝ)^49 := by
    have hnat : (344010011 : ℕ)^65*100000000000000^49 ≤ 45291714189463^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344010011 625000000 45291714189463 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501032999/10000000000 : ℝ)^65 ≤ (11314395637637/25000000000000 : ℝ)^49 := by
    have hnat : (5501032999 : ℕ)^65*25000000000000^49 ≤ 11314395637637^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501032999 10000000000 11314395637637 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (844554299/5000000000 : ℝ)^65 ≤ (9450703256299/100000000000000 : ℝ)^49 := by
    have hnat : (844554299 : ℕ)^65*100000000000000^49 ≤ 9450703256299^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844554299 5000000000 9450703256299 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344010011/625000000 : ℝ), (5501032999/10000000000 : ℝ), (-844554299/5000000000 : ℝ)] ![(45291714189463/100000000000000 : ℝ), (11314395637637/25000000000000 : ℝ), (9450703256299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344010011/625000000 : ℝ)|^65 ≤ (45291714189463/100000000000000 : ℝ)^49
        have hw : |(344010011/625000000 : ℝ)|=(344010011/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501032999/10000000000 : ℝ)|^65 ≤ (11314395637637/25000000000000 : ℝ)^49
        have hw : |(5501032999/10000000000 : ℝ)|=(5501032999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-844554299/5000000000 : ℝ)|^65 ≤ (9450703256299/100000000000000 : ℝ)^49
        have hw : |(-844554299/5000000000 : ℝ)|=(844554299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_6 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2197125823/5000000000 : ℝ)*x 0 + (1093991081/2500000000 : ℝ)*x 1 + (4334962729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2197125823/5000000000 : ℝ)^65 ≤ (6719019714329/20000000000000 : ℝ)^49 := by
    have hnat : (2197125823 : ℕ)^65*20000000000000^49 ≤ 6719019714329^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197125823 5000000000 6719019714329 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093991081/2500000000 : ℝ)^65 ≤ (16704880615947/50000000000000 : ℝ)^49 := by
    have hnat : (1093991081 : ℕ)^65*50000000000000^49 ≤ 16704880615947^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093991081 2500000000 16704880615947 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4334962729/10000000000 : ℝ)^65 ≤ (2062196261139/6250000000000 : ℝ)^49 := by
    have hnat : (4334962729 : ℕ)^65*6250000000000^49 ≤ 2062196261139^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334962729 10000000000 2062196261139 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2197125823/5000000000 : ℝ), (1093991081/2500000000 : ℝ), (4334962729/10000000000 : ℝ)] ![(6719019714329/20000000000000 : ℝ), (16704880615947/50000000000000 : ℝ), (2062196261139/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2197125823/5000000000 : ℝ)|^65 ≤ (6719019714329/20000000000000 : ℝ)^49
        have hw : |(2197125823/5000000000 : ℝ)|=(2197125823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093991081/2500000000 : ℝ)|^65 ≤ (16704880615947/50000000000000 : ℝ)^49
        have hw : |(1093991081/2500000000 : ℝ)|=(1093991081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4334962729/10000000000 : ℝ)|^65 ≤ (2062196261139/6250000000000 : ℝ)^49
        have hw : |(4334962729/10000000000 : ℝ)|=(4334962729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1529269131/10000000000 : ℝ)*x 0 + (225675171/500000000 : ℝ)*x 1 + (6537820219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1529269131/10000000000 : ℝ)^65 ≤ (331324040791/4000000000000 : ℝ)^49 := by
    have hnat : (1529269131 : ℕ)^65*4000000000000^49 ≤ 331324040791^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1529269131 10000000000 331324040791 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225675171/500000000 : ℝ)^65 ≤ (34809833626947/100000000000000 : ℝ)^49 := by
    have hnat : (225675171 : ℕ)^65*100000000000000^49 ≤ 34809833626947^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225675171 500000000 34809833626947 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6537820219/10000000000 : ℝ)^65 ≤ (56907065337199/100000000000000 : ℝ)^49 := by
    have hnat : (6537820219 : ℕ)^65*100000000000000^49 ≤ 56907065337199^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6537820219 10000000000 56907065337199 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1529269131/10000000000 : ℝ), (225675171/500000000 : ℝ), (6537820219/10000000000 : ℝ)] ![(331324040791/4000000000000 : ℝ), (34809833626947/100000000000000 : ℝ), (56907065337199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1529269131/10000000000 : ℝ)|^65 ≤ (331324040791/4000000000000 : ℝ)^49
        have hw : |(-1529269131/10000000000 : ℝ)|=(1529269131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225675171/500000000 : ℝ)|^65 ≤ (34809833626947/100000000000000 : ℝ)^49
        have hw : |(225675171/500000000 : ℝ)|=(225675171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6537820219/10000000000 : ℝ)|^65 ≤ (56907065337199/100000000000000 : ℝ)^49
        have hw : |(6537820219/10000000000 : ℝ)|=(6537820219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4970393609/10000000000 : ℝ)*x 0 + (-413132747/5000000000 : ℝ)*x 1 + (407925313/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4970393609/10000000000 : ℝ)^65 ≤ (7911941620131/20000000000000 : ℝ)^49 := by
    have hnat : (4970393609 : ℕ)^65*20000000000000^49 ≤ 7911941620131^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970393609 10000000000 7911941620131 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413132747/5000000000 : ℝ)^65 ≤ (1830189359473/50000000000000 : ℝ)^49 := by
    have hnat : (413132747 : ℕ)^65*50000000000000^49 ≤ 1830189359473^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413132747 5000000000 1830189359473 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407925313/625000000 : ℝ)^65 ≤ (28389956581997/50000000000000 : ℝ)^49 := by
    have hnat : (407925313 : ℕ)^65*50000000000000^49 ≤ 28389956581997^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407925313 625000000 28389956581997 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4970393609/10000000000 : ℝ), (-413132747/5000000000 : ℝ), (407925313/625000000 : ℝ)] ![(7911941620131/20000000000000 : ℝ), (1830189359473/50000000000000 : ℝ), (28389956581997/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4970393609/10000000000 : ℝ)|^65 ≤ (7911941620131/20000000000000 : ℝ)^49
        have hw : |(4970393609/10000000000 : ℝ)|=(4970393609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413132747/5000000000 : ℝ)|^65 ≤ (1830189359473/50000000000000 : ℝ)^49
        have hw : |(-413132747/5000000000 : ℝ)|=(413132747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(407925313/625000000 : ℝ)|^65 ≤ (28389956581997/50000000000000 : ℝ)^49
        have hw : |(407925313/625000000 : ℝ)|=(407925313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4756750513/10000000000 : ℝ)*x 0 + (6747918833/10000000000 : ℝ)*x 1 + (-192537799/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4756750513/10000000000 : ℝ)^65 ≤ (37320059926721/100000000000000 : ℝ)^49 := by
    have hnat : (4756750513 : ℕ)^65*100000000000000^49 ≤ 37320059926721^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4756750513 10000000000 37320059926721 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6747918833/10000000000 : ℝ)^65 ≤ (29672803523871/50000000000000 : ℝ)^49 := by
    have hnat : (6747918833 : ℕ)^65*50000000000000^49 ≤ 29672803523871^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6747918833 10000000000 29672803523871 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192537799/2500000000 : ℝ)^65 ≤ (83358325233/2500000000000 : ℝ)^49 := by
    have hnat : (192537799 : ℕ)^65*2500000000000^49 ≤ 83358325233^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192537799 2500000000 83358325233 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4756750513/10000000000 : ℝ), (6747918833/10000000000 : ℝ), (-192537799/2500000000 : ℝ)] ![(37320059926721/100000000000000 : ℝ), (29672803523871/50000000000000 : ℝ), (83358325233/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4756750513/10000000000 : ℝ)|^65 ≤ (37320059926721/100000000000000 : ℝ)^49
        have hw : |(4756750513/10000000000 : ℝ)|=(4756750513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6747918833/10000000000 : ℝ)|^65 ≤ (29672803523871/50000000000000 : ℝ)^49
        have hw : |(6747918833/10000000000 : ℝ)|=(6747918833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-192537799/2500000000 : ℝ)|^65 ≤ (83358325233/2500000000000 : ℝ)^49
        have hw : |(-192537799/2500000000 : ℝ)|=(192537799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4368554/9765625 : ℝ)*x 0 + (1477825009/2500000000 : ℝ)*x 1 + (1244837353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368554/9765625 : ℝ)^65 ≤ (34400136665133/100000000000000 : ℝ)^49 := by
    have hnat : (4368554 : ℕ)^65*100000000000000^49 ≤ 34400136665133^49*9765625^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368554 9765625 34400136665133 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1477825009/2500000000 : ℝ)^65 ≤ (24894334379003/50000000000000 : ℝ)^49 := by
    have hnat : (1477825009 : ℕ)^65*50000000000000^49 ≤ 24894334379003^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477825009 2500000000 24894334379003 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1244837353/5000000000 : ℝ)^65 ≤ (15811194563151/100000000000000 : ℝ)^49 := by
    have hnat : (1244837353 : ℕ)^65*100000000000000^49 ≤ 15811194563151^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244837353 5000000000 15811194563151 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368554/9765625 : ℝ), (1477825009/2500000000 : ℝ), (1244837353/5000000000 : ℝ)] ![(34400136665133/100000000000000 : ℝ), (24894334379003/50000000000000 : ℝ), (15811194563151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368554/9765625 : ℝ)|^65 ≤ (34400136665133/100000000000000 : ℝ)^49
        have hw : |(4368554/9765625 : ℝ)|=(4368554/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1477825009/2500000000 : ℝ)|^65 ≤ (24894334379003/50000000000000 : ℝ)^49
        have hw : |(1477825009/2500000000 : ℝ)|=(1477825009/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1244837353/5000000000 : ℝ)|^65 ≤ (15811194563151/100000000000000 : ℝ)^49
        have hw : |(1244837353/5000000000 : ℝ)|=(1244837353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-201662767/2500000000 : ℝ)*x 0 + (4981895031/10000000000 : ℝ)*x 1 + (6526227803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (201662767/2500000000 : ℝ)^65 ≤ (3545562371863/100000000000000 : ℝ)^49 := by
    have hnat : (201662767 : ℕ)^65*100000000000000^49 ≤ 3545562371863^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201662767 2500000000 3545562371863 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4981895031/10000000000 : ℝ)^65 ≤ (7936237076683/20000000000000 : ℝ)^49 := by
    have hnat : (4981895031 : ℕ)^65*20000000000000^49 ≤ 7936237076683^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981895031 10000000000 7936237076683 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6526227803/10000000000 : ℝ)^65 ≤ (14193313057323/25000000000000 : ℝ)^49 := by
    have hnat : (6526227803 : ℕ)^65*25000000000000^49 ≤ 14193313057323^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6526227803 10000000000 14193313057323 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-201662767/2500000000 : ℝ), (4981895031/10000000000 : ℝ), (6526227803/10000000000 : ℝ)] ![(3545562371863/100000000000000 : ℝ), (7936237076683/20000000000000 : ℝ), (14193313057323/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-201662767/2500000000 : ℝ)|^65 ≤ (3545562371863/100000000000000 : ℝ)^49
        have hw : |(-201662767/2500000000 : ℝ)|=(201662767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4981895031/10000000000 : ℝ)|^65 ≤ (7936237076683/20000000000000 : ℝ)^49
        have hw : |(4981895031/10000000000 : ℝ)|=(4981895031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6526227803/10000000000 : ℝ)|^65 ≤ (14193313057323/25000000000000 : ℝ)^49
        have hw : |(6526227803/10000000000 : ℝ)|=(6526227803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4539913587/10000000000 : ℝ)*x 0 + (-1527936771/10000000000 : ℝ)*x 1 + (6515213533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4539913587/10000000000 : ℝ)^65 ≤ (17540142984611/50000000000000 : ℝ)^49 := by
    have hnat : (4539913587 : ℕ)^65*50000000000000^49 ≤ 17540142984611^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539913587 10000000000 17540142984611 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1527936771/10000000000 : ℝ)^65 ≤ (2068382346319/25000000000000 : ℝ)^49 := by
    have hnat : (1527936771 : ℕ)^65*25000000000000^49 ≤ 2068382346319^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1527936771 10000000000 2068382346319 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6515213533/10000000000 : ℝ)^65 ≤ (5664618463401/10000000000000 : ℝ)^49 := by
    have hnat : (6515213533 : ℕ)^65*10000000000000^49 ≤ 5664618463401^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6515213533 10000000000 5664618463401 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4539913587/10000000000 : ℝ), (-1527936771/10000000000 : ℝ), (6515213533/10000000000 : ℝ)] ![(17540142984611/50000000000000 : ℝ), (2068382346319/25000000000000 : ℝ), (5664618463401/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4539913587/10000000000 : ℝ)|^65 ≤ (17540142984611/50000000000000 : ℝ)^49
        have hw : |(4539913587/10000000000 : ℝ)|=(4539913587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1527936771/10000000000 : ℝ)|^65 ≤ (2068382346319/25000000000000 : ℝ)^49
        have hw : |(-1527936771/10000000000 : ℝ)|=(1527936771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6515213533/10000000000 : ℝ)|^65 ≤ (5664618463401/10000000000000 : ℝ)^49
        have hw : |(6515213533/10000000000 : ℝ)|=(6515213533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6509425487/10000000000 : ℝ)*x 0 + (5013881601/10000000000 : ℝ)*x 1 + (-1563481/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6509425487/10000000000 : ℝ)^65 ≤ (56579438171807/100000000000000 : ℝ)^49 := by
    have hnat : (6509425487 : ℕ)^65*100000000000000^49 ≤ 56579438171807^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6509425487 10000000000 56579438171807 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5013881601/10000000000 : ℝ)^65 ≤ (20009753354011/50000000000000 : ℝ)^49 := by
    have hnat : (5013881601 : ℕ)^65*50000000000000^49 ≤ 20009753354011^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5013881601 10000000000 20009753354011 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1563481/20000000 : ℝ)^65 ≤ (1700527555349/50000000000000 : ℝ)^49 := by
    have hnat : (1563481 : ℕ)^65*50000000000000^49 ≤ 1700527555349^49*20000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1563481 20000000 1700527555349 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6509425487/10000000000 : ℝ), (5013881601/10000000000 : ℝ), (-1563481/20000000 : ℝ)] ![(56579438171807/100000000000000 : ℝ), (20009753354011/50000000000000 : ℝ), (1700527555349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6509425487/10000000000 : ℝ)|^65 ≤ (56579438171807/100000000000000 : ℝ)^49
        have hw : |(6509425487/10000000000 : ℝ)|=(6509425487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5013881601/10000000000 : ℝ)|^65 ≤ (20009753354011/50000000000000 : ℝ)^49
        have hw : |(5013881601/10000000000 : ℝ)|=(5013881601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1563481/20000000 : ℝ)|^65 ≤ (1700527555349/50000000000000 : ℝ)^49
        have hw : |(-1563481/20000000 : ℝ)|=(1563481/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3182539993/5000000000 : ℝ)*x 0 + (3940841223/10000000000 : ℝ)*x 1 + (2512374617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3182539993/5000000000 : ℝ)^65 ≤ (54921175194113/100000000000000 : ℝ)^49 := by
    have hnat : (3182539993 : ℕ)^65*100000000000000^49 ≤ 54921175194113^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3182539993 5000000000 54921175194113 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3940841223/10000000000 : ℝ)^65 ≤ (7269028209343/25000000000000 : ℝ)^49 := by
    have hnat : (3940841223 : ℕ)^65*25000000000000^49 ≤ 7269028209343^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3940841223 10000000000 7269028209343 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512374617/10000000000 : ℝ)^65 ≤ (320054238907/2000000000000 : ℝ)^49 := by
    have hnat : (2512374617 : ℕ)^65*2000000000000^49 ≤ 320054238907^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512374617 10000000000 320054238907 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3182539993/5000000000 : ℝ), (3940841223/10000000000 : ℝ), (2512374617/10000000000 : ℝ)] ![(54921175194113/100000000000000 : ℝ), (7269028209343/25000000000000 : ℝ), (320054238907/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3182539993/5000000000 : ℝ)|^65 ≤ (54921175194113/100000000000000 : ℝ)^49
        have hw : |(3182539993/5000000000 : ℝ)|=(3182539993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3940841223/10000000000 : ℝ)|^65 ≤ (7269028209343/25000000000000 : ℝ)^49
        have hw : |(3940841223/10000000000 : ℝ)|=(3940841223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2512374617/10000000000 : ℝ)|^65 ≤ (320054238907/2000000000000 : ℝ)^49
        have hw : |(2512374617/10000000000 : ℝ)|=(2512374617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-748267609/10000000000 : ℝ)*x 0 + (6109619377/10000000000 : ℝ)*x 1 + (5456686887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (748267609/10000000000 : ℝ)^65 ≤ (1604619536197/50000000000000 : ℝ)^49 := by
    have hnat : (748267609 : ℕ)^65*50000000000000^49 ≤ 1604619536197^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748267609 10000000000 1604619536197 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6109619377/10000000000 : ℝ)^65 ≤ (52016511886919/100000000000000 : ℝ)^49 := by
    have hnat : (6109619377 : ℕ)^65*100000000000000^49 ≤ 52016511886919^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6109619377 10000000000 52016511886919 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456686887/10000000000 : ℝ)^65 ≤ (11193562257427/25000000000000 : ℝ)^49 := by
    have hnat : (5456686887 : ℕ)^65*25000000000000^49 ≤ 11193562257427^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456686887 10000000000 11193562257427 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-748267609/10000000000 : ℝ), (6109619377/10000000000 : ℝ), (5456686887/10000000000 : ℝ)] ![(1604619536197/50000000000000 : ℝ), (52016511886919/100000000000000 : ℝ), (11193562257427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-748267609/10000000000 : ℝ)|^65 ≤ (1604619536197/50000000000000 : ℝ)^49
        have hw : |(-748267609/10000000000 : ℝ)|=(748267609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6109619377/10000000000 : ℝ)|^65 ≤ (52016511886919/100000000000000 : ℝ)^49
        have hw : |(6109619377/10000000000 : ℝ)|=(6109619377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456686887/10000000000 : ℝ)|^65 ≤ (11193562257427/25000000000000 : ℝ)^49
        have hw : |(5456686887/10000000000 : ℝ)|=(5456686887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (326706429/500000000 : ℝ)*x 0 + (-372961889/5000000000 : ℝ)*x 1 + (2503168561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326706429/500000000 : ℝ)^65 ≤ (2274577749783/4000000000000 : ℝ)^49 := by
    have hnat : (326706429 : ℕ)^65*4000000000000^49 ≤ 2274577749783^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326706429 500000000 2274577749783 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (372961889/5000000000 : ℝ)^65 ≤ (159795551473/5000000000000 : ℝ)^49 := by
    have hnat : (372961889 : ℕ)^65*5000000000000^49 ≤ 159795551473^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372961889 5000000000 159795551473 5000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2503168561/5000000000 : ℝ)^65 ≤ (39939645211169/100000000000000 : ℝ)^49 := by
    have hnat : (2503168561 : ℕ)^65*100000000000000^49 ≤ 39939645211169^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503168561 5000000000 39939645211169 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(326706429/500000000 : ℝ), (-372961889/5000000000 : ℝ), (2503168561/5000000000 : ℝ)] ![(2274577749783/4000000000000 : ℝ), (159795551473/5000000000000 : ℝ), (39939645211169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(326706429/500000000 : ℝ)|^65 ≤ (2274577749783/4000000000000 : ℝ)^49
        have hw : |(326706429/500000000 : ℝ)|=(326706429/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-372961889/5000000000 : ℝ)|^65 ≤ (159795551473/5000000000000 : ℝ)^49
        have hw : |(-372961889/5000000000 : ℝ)|=(372961889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2503168561/5000000000 : ℝ)|^65 ≤ (39939645211169/100000000000000 : ℝ)^49
        have hw : |(2503168561/5000000000 : ℝ)|=(2503168561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2246625103/5000000000 : ℝ)*x 0 + (6580941323/10000000000 : ℝ)*x 1 + (-744268431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246625103/5000000000 : ℝ)^65 ≤ (34602780977277/100000000000000 : ℝ)^49 := by
    have hnat : (2246625103 : ℕ)^65*100000000000000^49 ≤ 34602780977277^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246625103 5000000000 34602780977277 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6580941323/10000000000 : ℝ)^65 ≤ (57405498680977/100000000000000 : ℝ)^49 := by
    have hnat : (6580941323 : ℕ)^65*100000000000000^49 ≤ 57405498680977^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6580941323 10000000000 57405498680977 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (744268431/5000000000 : ℝ)^65 ≤ (1997930083987/25000000000000 : ℝ)^49 := by
    have hnat : (744268431 : ℕ)^65*25000000000000^49 ≤ 1997930083987^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744268431 5000000000 1997930083987 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246625103/5000000000 : ℝ), (6580941323/10000000000 : ℝ), (-744268431/5000000000 : ℝ)] ![(34602780977277/100000000000000 : ℝ), (57405498680977/100000000000000 : ℝ), (1997930083987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246625103/5000000000 : ℝ)|^65 ≤ (34602780977277/100000000000000 : ℝ)^49
        have hw : |(2246625103/5000000000 : ℝ)|=(2246625103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6580941323/10000000000 : ℝ)|^65 ≤ (57405498680977/100000000000000 : ℝ)^49
        have hw : |(6580941323/10000000000 : ℝ)|=(6580941323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-744268431/5000000000 : ℝ)|^65 ≤ (1997930083987/25000000000000 : ℝ)^49
        have hw : |(-744268431/5000000000 : ℝ)|=(744268431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301063_s7_s7_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3261216033/5000000000 : ℝ)*x 0 + (653942751/2000000000 : ℝ)*x 1 + (3036191971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3261216033/5000000000 : ℝ)^65 ≤ (28364727144491/50000000000000 : ℝ)^49 := by
    have hnat : (3261216033 : ℕ)^65*50000000000000^49 ≤ 28364727144491^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3261216033 5000000000 28364727144491 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653942751/2000000000 : ℝ)^65 ≤ (11348861733997/50000000000000 : ℝ)^49 := by
    have hnat : (653942751 : ℕ)^65*50000000000000^49 ≤ 11348861733997^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653942751 2000000000 11348861733997 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3036191971/10000000000 : ℝ)^65 ≤ (20572822221279/100000000000000 : ℝ)^49 := by
    have hnat : (3036191971 : ℕ)^65*100000000000000^49 ≤ 20572822221279^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3036191971 10000000000 20572822221279 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3261216033/5000000000 : ℝ), (653942751/2000000000 : ℝ), (3036191971/10000000000 : ℝ)] ![(28364727144491/50000000000000 : ℝ), (11348861733997/50000000000000 : ℝ), (20572822221279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3261216033/5000000000 : ℝ)|^65 ≤ (28364727144491/50000000000000 : ℝ)^49
        have hw : |(3261216033/5000000000 : ℝ)|=(3261216033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653942751/2000000000 : ℝ)|^65 ≤ (11348861733997/50000000000000 : ℝ)^49
        have hw : |(653942751/2000000000 : ℝ)|=(653942751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3036191971/10000000000 : ℝ)|^65 ≤ (20572822221279/100000000000000 : ℝ)^49
        have hw : |(3036191971/10000000000 : ℝ)|=(3036191971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301063_s7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((13117/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13117/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53323/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53323/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12739/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12739/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10009/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10009/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38663/100000 : ℝ)*X 1 2) := by
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
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev6 with ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩
  have s7_pow0 : (13117/25000 : ℝ) ^ (129/32 : ℝ) ≤ (7427193572212326857/100000000000000000000 : ℝ) := by
    have hpowers : (13117/25000 : ℝ)^129 ≤ (7427193572212326857/100000000000000000000 : ℝ)^32 := by
      have hnat : (13117 : ℕ)^129*100000000000000000000^32 ≤ 7427193572212326857^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13117 25000 7427193572212326857 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13117/25000 : ℝ)) (X := (7427193572212326857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner0a : (107427193572212326857/100000000000000000000 : ℝ) ≤ (5089654040848147/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (107427193572212326857/100000000000000000000 : ℝ)^32 ≤ (5089654040848147/5000000000000000 : ℝ)^129 := by
      have hnat : (107427193572212326857 : ℕ)^32*5000000000000000^129 ≤ 5089654040848147^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107427193572212326857 100000000000000000000 5089654040848147 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5089654040848147/5000000000000000 : ℝ)) (X := (107427193572212326857/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner0b : (57427193572212326857/50000000000000000000 : ℝ) ≤ (10349522954287873/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (57427193572212326857/50000000000000000000 : ℝ)^32 ≤ (10349522954287873/10000000000000000 : ℝ)^129 := by
      have hnat : (57427193572212326857 : ℕ)^32*10000000000000000^129 ≤ 10349522954287873^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57427193572212326857 50000000000000000000 10349522954287873 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10349522954287873/10000000000000000 : ℝ)) (X := (57427193572212326857/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s7_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(88854351683/2600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(170214872591579/5246800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (13117/25000 : ℝ)) (alpha := (88854351683/2600000000000 : ℝ)) (beta := (170214872591579/5246800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow0,s7_corner0a]) (by linarith only [s7_pow0,s7_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (13117/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(88854351683/2600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(170214872591579/5246800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow1 : (53323/100000 : ℝ) ^ (129/32 : ℝ) ≤ (7927283343587593939/100000000000000000000 : ℝ) := by
    have hpowers : (53323/100000 : ℝ)^129 ≤ (7927283343587593939/100000000000000000000 : ℝ)^32 := by
      have hnat : (53323 : ℕ)^129*100000000000000000000^32 ≤ 7927283343587593939^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53323 100000 7927283343587593939 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (53323/100000 : ℝ)) (X := (7927283343587593939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner1a : (107927283343587593939/100000000000000000000 : ℝ) ≤ (2547760570967953/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (107927283343587593939/100000000000000000000 : ℝ)^32 ≤ (2547760570967953/2500000000000000 : ℝ)^129 := by
      have hnat : (107927283343587593939 : ℕ)^32*2500000000000000^129 ≤ 2547760570967953^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107927283343587593939 100000000000000000000 2547760570967953 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2547760570967953/2500000000000000 : ℝ)) (X := (107927283343587593939/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner1b : (57927283343587593939/50000000000000000000 : ℝ) ≤ (10371806996122569/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (57927283343587593939/50000000000000000000 : ℝ)^32 ≤ (10371806996122569/10000000000000000 : ℝ)^129 := by
      have hnat : (57927283343587593939 : ℕ)^32*10000000000000000^129 ≤ 10371806996122569^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57927283343587593939 50000000000000000000 10371806996122569 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10371806996122569/10000000000000000 : ℝ)) (X := (57927283343587593939/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s7_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(47760570967953/1333075000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(180764712250757/5332300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (53323/100000 : ℝ)) (alpha := (47760570967953/1333075000000000 : ℝ)) (beta := (180764712250757/5332300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow1,s7_corner1a]) (by linarith only [s7_pow1,s7_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (53323/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(47760570967953/1333075000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(180764712250757/5332300000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s7_pow2 : (12739/25000 : ℝ) ^ (129/32 : ℝ) ≤ (825165729677393251/12500000000000000000 : ℝ) := by
    have hpowers : (12739/25000 : ℝ)^129 ≤ (825165729677393251/12500000000000000000 : ℝ)^32 := by
      have hnat : (12739 : ℕ)^129*12500000000000000000^32 ≤ 825165729677393251^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12739 25000 825165729677393251 12500000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12739/25000 : ℝ)) (X := (825165729677393251/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner2a : (13325165729677393251/12500000000000000000 : ℝ) ≤ (5079919759479393/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (13325165729677393251/12500000000000000000 : ℝ)^32 ≤ (5079919759479393/5000000000000000 : ℝ)^129 := by
      have hnat : (13325165729677393251 : ℕ)^32*5000000000000000^129 ≤ 5079919759479393^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13325165729677393251 12500000000000000000 5079919759479393 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5079919759479393/5000000000000000 : ℝ)) (X := (13325165729677393251/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s7_corner2b : (7075165729677393251/6250000000000000000 : ℝ) ≤ (5156200315024541/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (7075165729677393251/6250000000000000000 : ℝ)^32 ≤ (5156200315024541/5000000000000000 : ℝ)^129 := by
      have hnat : (7075165729677393251 : ℕ)^32*5000000000000000^129 ≤ 5156200315024541^129*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7075165729677393251 6250000000000000000 5156200315024541 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5156200315024541/5000000000000000 : ℝ)) (X := (7075165729677393251/6250000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s7_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(79919759479393/2547800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(19070138886287/636950000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (12739/25000 : ℝ)) (alpha := (79919759479393/2547800000000000 : ℝ)) (beta := (19070138886287/636950000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s7_pow2,s7_corner2a]) (by linarith only [s7_pow2,s7_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (12739/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s6_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(79919759479393/2547800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(19070138886287/636950000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s7_0 : ((-856305233/5000000000 : ℝ)*X 0 0+(1367370317/2500000000 : ℝ)*X 0 1+(1103930601/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_1 : ((683868867/1250000000 : ℝ)*X 1 0+(-1726346071/10000000000 : ℝ)*X 1 1+(5508798717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_2 : ((344010011/625000000 : ℝ)*X 2 0+(5501032999/10000000000 : ℝ)*X 2 1+(-844554299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_6 : ((2197125823/5000000000 : ℝ)*X 0 0+(1093991081/2500000000 : ℝ)*X 0 1+(4334962729/10000000000 : ℝ)*X 0 2+(2197125823/5000000000 : ℝ)*X 1 0+(1093991081/2500000000 : ℝ)*X 1 1+(4334962729/10000000000 : ℝ)*X 1 2+(2197125823/5000000000 : ℝ)*X 2 0+(1093991081/2500000000 : ℝ)*X 2 1+(4334962729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_7 : ((-1529269131/10000000000 : ℝ)*X 0 0+(225675171/500000000 : ℝ)*X 0 1+(6537820219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_8 : ((4970393609/10000000000 : ℝ)*X 1 0+(-413132747/5000000000 : ℝ)*X 1 1+(407925313/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_9 : ((4756750513/10000000000 : ℝ)*X 2 0+(6747918833/10000000000 : ℝ)*X 2 1+(-192537799/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_13 : ((4368554/9765625 : ℝ)*X 0 0+(1477825009/2500000000 : ℝ)*X 0 1+(1244837353/5000000000 : ℝ)*X 0 2+(4368554/9765625 : ℝ)*X 1 0+(1477825009/2500000000 : ℝ)*X 1 1+(1244837353/5000000000 : ℝ)*X 1 2+(4368554/9765625 : ℝ)*X 2 0+(1477825009/2500000000 : ℝ)*X 2 1+(1244837353/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_14 : ((-201662767/2500000000 : ℝ)*X 0 0+(4981895031/10000000000 : ℝ)*X 0 1+(6526227803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_15 : ((4539913587/10000000000 : ℝ)*X 1 0+(-1527936771/10000000000 : ℝ)*X 1 1+(6515213533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_16 : ((6509425487/10000000000 : ℝ)*X 2 0+(5013881601/10000000000 : ℝ)*X 2 1+(-1563481/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_20 : ((3182539993/5000000000 : ℝ)*X 0 0+(3940841223/10000000000 : ℝ)*X 0 1+(2512374617/10000000000 : ℝ)*X 0 2+(3182539993/5000000000 : ℝ)*X 1 0+(3940841223/10000000000 : ℝ)*X 1 1+(2512374617/10000000000 : ℝ)*X 1 2+(3182539993/5000000000 : ℝ)*X 2 0+(3940841223/10000000000 : ℝ)*X 2 1+(2512374617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_21 : ((-748267609/10000000000 : ℝ)*X 0 0+(6109619377/10000000000 : ℝ)*X 0 1+(5456686887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_22 : ((326706429/500000000 : ℝ)*X 1 0+(-372961889/5000000000 : ℝ)*X 1 1+(2503168561/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_23 : ((2246625103/5000000000 : ℝ)*X 2 0+(6580941323/10000000000 : ℝ)*X 2 1+(-744268431/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s7_27 : ((3261216033/5000000000 : ℝ)*X 0 0+(653942751/2000000000 : ℝ)*X 0 1+(3036191971/10000000000 : ℝ)*X 0 2+(3261216033/5000000000 : ℝ)*X 1 0+(653942751/2000000000 : ℝ)*X 1 1+(3036191971/10000000000 : ℝ)*X 1 2+(3261216033/5000000000 : ℝ)*X 2 0+(653942751/2000000000 : ℝ)*X 2 1+(3036191971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301063_s7_s7_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s7_0 : (0 : ℝ) ≤ ((10009/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10009/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1343606651243337645360594129/139887558200000000000000000000000 : ℝ) := by norm_num
    linear_combination (1242881/1000000000000 : ℝ)*(base50) + (126501146399/1000000000000 : ℝ)*(base60) + (3863232243771/1000000000000 : ℝ)*(major_s7_0) + (3863232243771/1000000000000 : ℝ)*(major_s7_1) + (3863232243771/1000000000000 : ℝ)*(major_s7_2) + (16119309/1000000000000 : ℝ)*(sp_s7_0) + (9117129/1000000000000 : ℝ)*(sp_s7_6) + (2557394134999/500000000000 : ℝ)*(sp_s7_7) + (1022952589857/200000000000 : ℝ)*(sp_s7_8) + (2557396678651/500000000000 : ℝ)*(sp_s7_9) + (652906012099/250000000000 : ℝ)*(sp_s7_13) + (185399/7812500000 : ℝ)*(sp_s7_14) + (32585547/500000000000 : ℝ)*(sp_s7_15) + (17381539/500000000000 : ℝ)*(sp_s7_23) + (104465326621/40000000000 : ℝ)*(f.failure) + (5114828120379/1000000000000 : ℝ)*(f.sum) + (9884823087858959829/27171267880000000000000000000000 : ℝ)*base63 + (3177751097643/636950000000000000000000000 : ℝ)*base64 + (2191524673879553/5332300000000000000000000000 : ℝ)*base66 + (80822248199537/2547800000000000000000000000 : ℝ)*base68 + (125488671942311/33121400000000000000000000000 : ℝ)*base71 + (84436211550911/5246800000000000000000000000 : ℝ)*base72 + (153776762021017/1333075000000000000000000000 : ℝ)*base74 + (1518732974527/2600000000000000000000000 : ℝ)*base76 + (112317697840111220057/279775116400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (201/1000000000000000 : ℝ)*base87 + (201/1000000000000000 : ℝ)*base89 + (201/1000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s7_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20277/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2682531053672764843653519500733/356405520781960000000000000000000000 : ℝ) := by norm_num
    linear_combination (1347647/1000000000000 : ℝ)*(base39) + (240197/200000000000 : ℝ)*(base49) + (1090437/1000000000000 : ℝ)*(base60) + (780337693703/200000000000 : ℝ)*(major_s7_0) + (780337693703/200000000000 : ℝ)*(major_s7_1) + (780337693703/200000000000 : ℝ)*(major_s7_2) + (3000833/500000000000 : ℝ)*(sp_s7_2) + (19545191/1000000000000 : ℝ)*(sp_s7_7) + (6523809/200000000000 : ℝ)*(sp_s7_8) + (5165724431837/1000000000000 : ℝ)*(sp_s7_14) + (5165711357983/1000000000000 : ℝ)*(sp_s7_15) + (5165737975363/1000000000000 : ℝ)*(sp_s7_16) + (2637574682079/1000000000000 : ℝ)*(sp_s7_20) + (55769041/1000000000000 : ℝ)*(sp_s7_27) + (32970380639/12500000000 : ℝ)*(f.failure) + (5165743977029/1000000000000 : ℝ)*(f.sum) + (3147427801637220281/27171267880000000000000000000000 : ℝ)*base63 + (237641119079/796187500000000000000000 : ℝ)*base65 + (670251431806047/1066460000000000000000000000 : ℝ)*base67 + (247931222709423/509560000000000000000000000 : ℝ)*base69 + (585143518264489/6624280000000000000000000000 : ℝ)*base70 + (418755155032629/1049360000000000000000000000 : ℝ)*base73 + (72303165220913/533230000000000000000000000 : ℝ)*base74 + (51782899439/520000000000000000000000 : ℝ)*base76 + (9175102424032284171/55955023280000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (157/625000000000000 : ℝ)*base86 + (157/625000000000000 : ℝ)*base88 + (157/625000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s7_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38663/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1491688610755503474541595046579/356405520781960000000000000000000000 : ℝ) := by norm_num
    linear_combination (3016751/1000000000000 : ℝ)*(base15) + (105886988577/500000000000 : ℝ)*(base40) + (728156577063/200000000000 : ℝ)*(major_s7_0) + (728156577063/200000000000 : ℝ)*(major_s7_1) + (728156577063/200000000000 : ℝ)*(major_s7_2) + (321099/15625000000 : ℝ)*(sp_s7_0) + (19087021/1000000000000 : ℝ)*(sp_s7_1) + (1534977/200000000000 : ℝ)*(sp_s7_2) + (14144011/1000000000000 : ℝ)*(sp_s7_9) + (16144893/500000000000 : ℝ)*(sp_s7_20) + (1205072875703/250000000000 : ℝ)*(sp_s7_21) + (4820289949377/1000000000000 : ℝ)*(sp_s7_22) + (1205072558563/250000000000 : ℝ)*(sp_s7_23) + (1230610016283/500000000000 : ℝ)*(sp_s7_27) + (2461252322351/1000000000000 : ℝ)*(f.failure) + (1205078013287/250000000000 : ℝ)*(f.sum) + (11969636606054850459/27171267880000000000000000000000 : ℝ)*base62 + (32743191794339/127390000000000000000000000 : ℝ)*base64 + (184103277800221/1066460000000000000000000000 : ℝ)*base66 + (546081626755849/509560000000000000000000000 : ℝ)*base68 + (190162763767693/1324856000000000000000000000 : ℝ)*base70 + (620236705608187/1049360000000000000000000000 : ℝ)*base72 + (211772479623363/533230000000000000000000000 : ℝ)*base74 + (23707204727/104000000000000000000000 : ℝ)*base76 + (1919453671948170641/11191004656000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (12669/25000000000000000 : ℝ)*base86 + (12669/25000000000000000 : ℝ)*base88 + (12669/25000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s7_0,ratio_s7_1,ratio_s7_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev6 : (0 : ℝ) ≤ ((13117/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(13117/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53323/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53323/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12739/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12739/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((10009/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10009/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20277/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20277/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38663/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38663/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301063_s7 p hpa hpb X hX hprev6

#print axioms solution
