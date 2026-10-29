-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306063_s6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:59:05.078138+00:00
-- url     : https://prove2.me/submissions/1f2a4f5f-2f97-4c57-ac39-8fbb715743a2

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
theorem collision_support_c306063_s6_s6_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-45678207/250000000 : ℝ)*x 0 + (5390674367/10000000000 : ℝ)*x 1 + (2706583327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (45678207/250000000 : ℝ)^135 ≤ (1346870201329/12500000000000 : ℝ)^103 := by
    have hnat : (45678207 : ℕ)^135*12500000000000^103 ≤ 1346870201329^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45678207 250000000 1346870201329 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390674367/10000000000 : ℝ)^135 ≤ (44490786204741/100000000000000 : ℝ)^103 := by
    have hnat : (5390674367 : ℕ)^135*100000000000000^103 ≤ 44490786204741^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390674367 10000000000 44490786204741 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706583327/5000000000 : ℝ)^135 ≤ (559178152193/1250000000000 : ℝ)^103 := by
    have hnat : (2706583327 : ℕ)^135*1250000000000^103 ≤ 559178152193^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706583327 5000000000 559178152193 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-45678207/250000000 : ℝ), (5390674367/10000000000 : ℝ), (2706583327/5000000000 : ℝ)] ![(1346870201329/12500000000000 : ℝ), (44490786204741/100000000000000 : ℝ), (559178152193/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-45678207/250000000 : ℝ)|^135 ≤ (1346870201329/12500000000000 : ℝ)^103
        have hw : |(-45678207/250000000 : ℝ)|=(45678207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390674367/10000000000 : ℝ)|^135 ≤ (44490786204741/100000000000000 : ℝ)^103
        have hw : |(5390674367/10000000000 : ℝ)|=(5390674367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706583327/5000000000 : ℝ)|^135 ≤ (559178152193/1250000000000 : ℝ)^103
        have hw : |(2706583327/5000000000 : ℝ)|=(2706583327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_1 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2695743911/5000000000 : ℝ)*x 0 + (-916949041/5000000000 : ℝ)*x 1 + (5407519573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695743911/5000000000 : ℝ)^135 ≤ (22249792946009/50000000000000 : ℝ)^103 := by
    have hnat : (2695743911 : ℕ)^135*50000000000000^103 ≤ 22249792946009^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695743911 5000000000 22249792946009 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (916949041/5000000000 : ℝ)^135 ≤ (2706829475631/25000000000000 : ℝ)^103 := by
    have hnat : (916949041 : ℕ)^135*25000000000000^103 ≤ 2706829475631^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916949041 5000000000 2706829475631 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407519573/10000000000 : ℝ)^135 ≤ (22336548096751/50000000000000 : ℝ)^103 := by
    have hnat : (5407519573 : ℕ)^135*50000000000000^103 ≤ 22336548096751^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407519573 10000000000 22336548096751 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695743911/5000000000 : ℝ), (-916949041/5000000000 : ℝ), (5407519573/10000000000 : ℝ)] ![(22249792946009/50000000000000 : ℝ), (2706829475631/25000000000000 : ℝ), (22336548096751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695743911/5000000000 : ℝ)|^135 ≤ (22249792946009/50000000000000 : ℝ)^103
        have hw : |(2695743911/5000000000 : ℝ)|=(2695743911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-916949041/5000000000 : ℝ)|^135 ≤ (2706829475631/25000000000000 : ℝ)^103
        have hw : |(-916949041/5000000000 : ℝ)|=(916949041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407519573/10000000000 : ℝ)|^135 ≤ (22336548096751/50000000000000 : ℝ)^103
        have hw : |(5407519573/10000000000 : ℝ)|=(5407519573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (135221889/250000000 : ℝ)*x 0 + (5404284827/10000000000 : ℝ)*x 1 + (-1814070651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135221889/250000000 : ℝ)^135 ≤ (698246551029/1562500000000 : ℝ)^103 := by
    have hnat : (135221889 : ℕ)^135*1562500000000^103 ≤ 698246551029^103*250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135221889 250000000 698246551029 1562500000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5404284827/10000000000 : ℝ)^135 ≤ (44638073921377/100000000000000 : ℝ)^103 := by
    have hnat : (5404284827 : ℕ)^135*100000000000000^103 ≤ 44638073921377^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404284827 10000000000 44638073921377 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1814070651/10000000000 : ℝ)^135 ≤ (533707339637/5000000000000 : ℝ)^103 := by
    have hnat : (1814070651 : ℕ)^135*5000000000000^103 ≤ 533707339637^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1814070651 10000000000 533707339637 5000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135221889/250000000 : ℝ), (5404284827/10000000000 : ℝ), (-1814070651/10000000000 : ℝ)] ![(698246551029/1562500000000 : ℝ), (44638073921377/100000000000000 : ℝ), (533707339637/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135221889/250000000 : ℝ)|^135 ≤ (698246551029/1562500000000 : ℝ)^103
        have hw : |(135221889/250000000 : ℝ)|=(135221889/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5404284827/10000000000 : ℝ)|^135 ≤ (44638073921377/100000000000000 : ℝ)^103
        have hw : |(5404284827/10000000000 : ℝ)|=(5404284827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1814070651/10000000000 : ℝ)|^135 ≤ (533707339637/5000000000000 : ℝ)^103
        have hw : |(-1814070651/10000000000 : ℝ)|=(1814070651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4330916849/10000000000 : ℝ)*x 0 + (4328053921/10000000000 : ℝ)*x 1 + (539458407/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330916849/10000000000 : ℝ)^135 ≤ (33394320670811/100000000000000 : ℝ)^103 := by
    have hnat : (4330916849 : ℕ)^135*100000000000000^103 ≤ 33394320670811^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330916849 10000000000 33394320670811 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4328053921/10000000000 : ℝ)^135 ≤ (33365390224593/100000000000000 : ℝ)^103 := by
    have hnat : (4328053921 : ℕ)^135*100000000000000^103 ≤ 33365390224593^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328053921 10000000000 33365390224593 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539458407/1250000000 : ℝ)^135 ≤ (1038759034181/3125000000000 : ℝ)^103 := by
    have hnat : (539458407 : ℕ)^135*3125000000000^103 ≤ 1038759034181^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539458407 1250000000 1038759034181 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330916849/10000000000 : ℝ), (4328053921/10000000000 : ℝ), (539458407/1250000000 : ℝ)] ![(33394320670811/100000000000000 : ℝ), (33365390224593/100000000000000 : ℝ), (1038759034181/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330916849/10000000000 : ℝ)|^135 ≤ (33394320670811/100000000000000 : ℝ)^103
        have hw : |(4330916849/10000000000 : ℝ)|=(4330916849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4328053921/10000000000 : ℝ)|^135 ≤ (33365390224593/100000000000000 : ℝ)^103
        have hw : |(4328053921/10000000000 : ℝ)|=(4328053921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539458407/1250000000 : ℝ)|^135 ≤ (1038759034181/3125000000000 : ℝ)^103
        have hw : |(539458407/1250000000 : ℝ)|=(539458407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160023/12500000 : ℝ)*x 0 + (1163573717/2500000000 : ℝ)*x 1 + (1546495451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160023/12500000 : ℝ)^135 ≤ (5007721733963/50000000000000 : ℝ)^103 := by
    have hnat : (2160023 : ℕ)^135*50000000000000^103 ≤ 5007721733963^103*12500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160023 12500000 5007721733963 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163573717/2500000000 : ℝ)^135 ≤ (36699730147453/100000000000000 : ℝ)^103 := by
    have hnat : (1163573717 : ℕ)^135*100000000000000^103 ≤ 36699730147453^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163573717 2500000000 36699730147453 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1546495451/2500000000 : ℝ)^135 ≤ (532848263653/1000000000000 : ℝ)^103 := by
    have hnat : (1546495451 : ℕ)^135*1000000000000^103 ≤ 532848263653^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546495451 2500000000 532848263653 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160023/12500000 : ℝ), (1163573717/2500000000 : ℝ), (1546495451/2500000000 : ℝ)] ![(5007721733963/50000000000000 : ℝ), (36699730147453/100000000000000 : ℝ), (532848263653/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160023/12500000 : ℝ)|^135 ≤ (5007721733963/50000000000000 : ℝ)^103
        have hw : |(-2160023/12500000 : ℝ)|=(2160023/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1163573717/2500000000 : ℝ)|^135 ≤ (36699730147453/100000000000000 : ℝ)^103
        have hw : |(1163573717/2500000000 : ℝ)|=(1163573717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1546495451/2500000000 : ℝ)|^135 ≤ (532848263653/1000000000000 : ℝ)^103
        have hw : |(1546495451/2500000000 : ℝ)|=(1546495451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1268131069/2500000000 : ℝ)*x 0 + (-561879283/5000000000 : ℝ)*x 1 + (6180292229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1268131069/2500000000 : ℝ)^135 ≤ (41081215284229/100000000000000 : ℝ)^103 := by
    have hnat : (1268131069 : ℕ)^135*100000000000000^103 ≤ 41081215284229^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268131069 2500000000 41081215284229 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561879283/5000000000 : ℝ)^135 ≤ (5698184096213/100000000000000 : ℝ)^103 := by
    have hnat : (561879283 : ℕ)^135*100000000000000^103 ≤ 5698184096213^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561879283 5000000000 5698184096213 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6180292229/10000000000 : ℝ)^135 ≤ (26610300305013/50000000000000 : ℝ)^103 := by
    have hnat : (6180292229 : ℕ)^135*50000000000000^103 ≤ 26610300305013^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6180292229 10000000000 26610300305013 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1268131069/2500000000 : ℝ), (-561879283/5000000000 : ℝ), (6180292229/10000000000 : ℝ)] ![(41081215284229/100000000000000 : ℝ), (5698184096213/100000000000000 : ℝ), (26610300305013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1268131069/2500000000 : ℝ)|^135 ≤ (41081215284229/100000000000000 : ℝ)^103
        have hw : |(1268131069/2500000000 : ℝ)|=(1268131069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561879283/5000000000 : ℝ)|^135 ≤ (5698184096213/100000000000000 : ℝ)^103
        have hw : |(-561879283/5000000000 : ℝ)|=(561879283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6180292229/10000000000 : ℝ)|^135 ≤ (26610300305013/50000000000000 : ℝ)^103
        have hw : |(6180292229/10000000000 : ℝ)|=(6180292229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (612271317/1250000000 : ℝ)*x 0 + (3179847737/5000000000 : ℝ)*x 1 + (-547288233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612271317/1250000000 : ℝ)^135 ≤ (39240429702381/100000000000000 : ℝ)^103 := by
    have hnat : (612271317 : ℕ)^135*100000000000000^103 ≤ 39240429702381^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612271317 1250000000 39240429702381 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3179847737/5000000000 : ℝ)^135 ≤ (27627271601683/50000000000000 : ℝ)^103 := by
    have hnat : (3179847737 : ℕ)^135*50000000000000^103 ≤ 27627271601683^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3179847737 5000000000 27627271601683 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547288233/5000000000 : ℝ)^135 ≤ (1101005416231/20000000000000 : ℝ)^103 := by
    have hnat : (547288233 : ℕ)^135*20000000000000^103 ≤ 1101005416231^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547288233 5000000000 1101005416231 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(612271317/1250000000 : ℝ), (3179847737/5000000000 : ℝ), (-547288233/5000000000 : ℝ)] ![(39240429702381/100000000000000 : ℝ), (27627271601683/50000000000000 : ℝ), (1101005416231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(612271317/1250000000 : ℝ)|^135 ≤ (39240429702381/100000000000000 : ℝ)^103
        have hw : |(612271317/1250000000 : ℝ)|=(612271317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3179847737/5000000000 : ℝ)|^135 ≤ (27627271601683/50000000000000 : ℝ)^103
        have hw : |(3179847737/5000000000 : ℝ)|=(3179847737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547288233/5000000000 : ℝ)|^135 ≤ (1101005416231/20000000000000 : ℝ)^103
        have hw : |(-547288233/5000000000 : ℝ)|=(547288233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2248059299/5000000000 : ℝ)*x 0 + (5545529033/10000000000 : ℝ)*x 1 + (2788555441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2248059299/5000000000 : ℝ)^135 ≤ (35073695569361/100000000000000 : ℝ)^103 := by
    have hnat : (2248059299 : ℕ)^135*100000000000000^103 ≤ 35073695569361^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248059299 5000000000 35073695569361 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5545529033/10000000000 : ℝ)^135 ≤ (11543334946167/25000000000000 : ℝ)^103 := by
    have hnat : (5545529033 : ℕ)^135*25000000000000^103 ≤ 11543334946167^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5545529033 10000000000 11543334946167 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2788555441/10000000000 : ℝ)^135 ≤ (18752964631831/100000000000000 : ℝ)^103 := by
    have hnat : (2788555441 : ℕ)^135*100000000000000^103 ≤ 18752964631831^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2788555441 10000000000 18752964631831 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2248059299/5000000000 : ℝ), (5545529033/10000000000 : ℝ), (2788555441/10000000000 : ℝ)] ![(35073695569361/100000000000000 : ℝ), (11543334946167/25000000000000 : ℝ), (18752964631831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2248059299/5000000000 : ℝ)|^135 ≤ (35073695569361/100000000000000 : ℝ)^103
        have hw : |(2248059299/5000000000 : ℝ)|=(2248059299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5545529033/10000000000 : ℝ)|^135 ≤ (11543334946167/25000000000000 : ℝ)^103
        have hw : |(5545529033/10000000000 : ℝ)|=(5545529033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2788555441/10000000000 : ℝ)|^135 ≤ (18752964631831/100000000000000 : ℝ)^103
        have hw : |(2788555441/10000000000 : ℝ)|=(2788555441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1117674029/10000000000 : ℝ)*x 0 + (5080269657/10000000000 : ℝ)*x 1 + (1544146391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1117674029/10000000000 : ℝ)^135 ≤ (565778034807/10000000000000 : ℝ)^103 := by
    have hnat : (1117674029 : ℕ)^135*10000000000000^103 ≤ 565778034807^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117674029 10000000000 565778034807 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080269657/10000000000 : ℝ)^135 ≤ (20581725591311/50000000000000 : ℝ)^103 := by
    have hnat : (5080269657 : ℕ)^135*50000000000000^103 ≤ 20581725591311^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080269657 10000000000 20581725591311 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1544146391/2500000000 : ℝ)^135 ≤ (103864782151/195312500000 : ℝ)^103 := by
    have hnat : (1544146391 : ℕ)^135*195312500000^103 ≤ 103864782151^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1544146391 2500000000 103864782151 195312500000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1117674029/10000000000 : ℝ), (5080269657/10000000000 : ℝ), (1544146391/2500000000 : ℝ)] ![(565778034807/10000000000000 : ℝ), (20581725591311/50000000000000 : ℝ), (103864782151/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1117674029/10000000000 : ℝ)|^135 ≤ (565778034807/10000000000000 : ℝ)^103
        have hw : |(-1117674029/10000000000 : ℝ)|=(1117674029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080269657/10000000000 : ℝ)|^135 ≤ (20581725591311/50000000000000 : ℝ)^103
        have hw : |(5080269657/10000000000 : ℝ)|=(5080269657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1544146391/2500000000 : ℝ)|^135 ≤ (103864782151/195312500000 : ℝ)^103
        have hw : |(1544146391/2500000000 : ℝ)|=(1544146391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4671789187/10000000000 : ℝ)*x 0 + (-863308223/5000000000 : ℝ)*x 1 + (1542723883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4671789187/10000000000 : ℝ)^135 ≤ (36880637345289/100000000000000 : ℝ)^103 := by
    have hnat : (4671789187 : ℕ)^135*100000000000000^103 ≤ 36880637345289^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671789187 10000000000 36880637345289 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (863308223/5000000000 : ℝ)^135 ≤ (10004794748553/100000000000000 : ℝ)^103 := by
    have hnat : (863308223 : ℕ)^135*100000000000000^103 ≤ 10004794748553^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      863308223 5000000000 10004794748553 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1542723883/2500000000 : ℝ)^135 ≤ (53114567889/100000000000 : ℝ)^103 := by
    have hnat : (1542723883 : ℕ)^135*100000000000^103 ≤ 53114567889^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542723883 2500000000 53114567889 100000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4671789187/10000000000 : ℝ), (-863308223/5000000000 : ℝ), (1542723883/2500000000 : ℝ)] ![(36880637345289/100000000000000 : ℝ), (10004794748553/100000000000000 : ℝ), (53114567889/100000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4671789187/10000000000 : ℝ)|^135 ≤ (36880637345289/100000000000000 : ℝ)^103
        have hw : |(4671789187/10000000000 : ℝ)|=(4671789187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-863308223/5000000000 : ℝ)|^135 ≤ (10004794748553/100000000000000 : ℝ)^103
        have hw : |(-863308223/5000000000 : ℝ)|=(863308223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1542723883/2500000000 : ℝ)|^135 ≤ (53114567889/100000000000 : ℝ)^103
        have hw : |(1542723883/2500000000 : ℝ)|=(1542723883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1542935871/2500000000 : ℝ)*x 0 + (509395169/1000000000 : ℝ)*x 1 + (-137996649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1542935871/2500000000 : ℝ)^135 ≤ (26562067078471/50000000000000 : ℝ)^103 := by
    have hnat : (1542935871 : ℕ)^135*50000000000000^103 ≤ 26562067078471^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542935871 2500000000 26562067078471 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509395169/1000000000 : ℝ)^135 ≤ (2581800883361/6250000000000 : ℝ)^103 := by
    have hnat : (509395169 : ℕ)^135*6250000000000^103 ≤ 2581800883361^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509395169 1000000000 2581800883361 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137996649/1250000000 : ℝ)^135 ≤ (556705169893/10000000000000 : ℝ)^103 := by
    have hnat : (137996649 : ℕ)^135*10000000000000^103 ≤ 556705169893^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137996649 1250000000 556705169893 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1542935871/2500000000 : ℝ), (509395169/1000000000 : ℝ), (-137996649/1250000000 : ℝ)] ![(26562067078471/50000000000000 : ℝ), (2581800883361/6250000000000 : ℝ), (556705169893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1542935871/2500000000 : ℝ)|^135 ≤ (26562067078471/50000000000000 : ℝ)^103
        have hw : |(1542935871/2500000000 : ℝ)|=(1542935871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(509395169/1000000000 : ℝ)|^135 ≤ (2581800883361/6250000000000 : ℝ)^103
        have hw : |(509395169/1000000000 : ℝ)|=(509395169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137996649/1250000000 : ℝ)|^135 ≤ (556705169893/10000000000000 : ℝ)^103
        have hw : |(-137996649/1250000000 : ℝ)|=(137996649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5913394623/10000000000 : ℝ)*x 0 + (1019093097/2500000000 : ℝ)*x 1 + (2808135331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5913394623/10000000000 : ℝ)^135 ≤ (10045723551853/20000000000000 : ℝ)^103 := by
    have hnat : (5913394623 : ℕ)^135*20000000000000^103 ≤ 10045723551853^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5913394623 10000000000 10045723551853 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1019093097/2500000000 : ℝ)^135 ≤ (6169129377409/20000000000000 : ℝ)^103 := by
    have hnat : (1019093097 : ℕ)^135*20000000000000^103 ≤ 6169129377409^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019093097 2500000000 6169129377409 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2808135331/10000000000 : ℝ)^135 ≤ (18925735341603/100000000000000 : ℝ)^103 := by
    have hnat : (2808135331 : ℕ)^135*100000000000000^103 ≤ 18925735341603^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808135331 10000000000 18925735341603 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5913394623/10000000000 : ℝ), (1019093097/2500000000 : ℝ), (2808135331/10000000000 : ℝ)] ![(10045723551853/20000000000000 : ℝ), (6169129377409/20000000000000 : ℝ), (18925735341603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5913394623/10000000000 : ℝ)|^135 ≤ (10045723551853/20000000000000 : ℝ)^103
        have hw : |(5913394623/10000000000 : ℝ)|=(5913394623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1019093097/2500000000 : ℝ)|^135 ≤ (6169129377409/20000000000000 : ℝ)^103
        have hw : |(1019093097/2500000000 : ℝ)|=(1019093097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2808135331/10000000000 : ℝ)|^135 ≤ (18925735341603/100000000000000 : ℝ)^103
        have hw : |(2808135331/10000000000 : ℝ)|=(2808135331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-106398081/1000000000 : ℝ)*x 0 + (292365323/500000000 : ℝ)*x 1 + (5456263979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106398081/1000000000 : ℝ)^135 ≤ (5304225321091/100000000000000 : ℝ)^103 := by
    have hnat : (106398081 : ℕ)^135*100000000000000^103 ≤ 5304225321091^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106398081 1000000000 5304225321091 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292365323/500000000 : ℝ)^135 ≤ (9898828214479/20000000000000 : ℝ)^103 := by
    have hnat : (292365323 : ℕ)^135*20000000000000^103 ≤ 9898828214479^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292365323 500000000 9898828214479 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456263979/10000000000 : ℝ)^135 ≤ (45201633597781/100000000000000 : ℝ)^103 := by
    have hnat : (5456263979 : ℕ)^135*100000000000000^103 ≤ 45201633597781^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456263979 10000000000 45201633597781 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106398081/1000000000 : ℝ), (292365323/500000000 : ℝ), (5456263979/10000000000 : ℝ)] ![(5304225321091/100000000000000 : ℝ), (9898828214479/20000000000000 : ℝ), (45201633597781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106398081/1000000000 : ℝ)|^135 ≤ (5304225321091/100000000000000 : ℝ)^103
        have hw : |(-106398081/1000000000 : ℝ)|=(106398081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(292365323/500000000 : ℝ)|^135 ≤ (9898828214479/20000000000000 : ℝ)^103
        have hw : |(292365323/500000000 : ℝ)|=(292365323/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456263979/10000000000 : ℝ)|^135 ≤ (45201633597781/100000000000000 : ℝ)^103
        have hw : |(5456263979/10000000000 : ℝ)|=(5456263979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3103945753/5000000000 : ℝ)*x 0 + (-1061678967/10000000000 : ℝ)*x 1 + (1016337111/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3103945753/5000000000 : ℝ)^135 ≤ (10706464294163/20000000000000 : ℝ)^103 := by
    have hnat : (3103945753 : ℕ)^135*20000000000000^103 ≤ 10706464294163^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3103945753 5000000000 10706464294163 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061678967/10000000000 : ℝ)^135 ≤ (1322297485669/25000000000000 : ℝ)^103 := by
    have hnat : (1061678967 : ℕ)^135*25000000000000^103 ≤ 1322297485669^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061678967 10000000000 1322297485669 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016337111/2000000000 : ℝ)^135 ≤ (1286827767747/3125000000000 : ℝ)^103 := by
    have hnat : (1016337111 : ℕ)^135*3125000000000^103 ≤ 1286827767747^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016337111 2000000000 1286827767747 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3103945753/5000000000 : ℝ), (-1061678967/10000000000 : ℝ), (1016337111/2000000000 : ℝ)] ![(10706464294163/20000000000000 : ℝ), (1322297485669/25000000000000 : ℝ), (1286827767747/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3103945753/5000000000 : ℝ)|^135 ≤ (10706464294163/20000000000000 : ℝ)^103
        have hw : |(3103945753/5000000000 : ℝ)|=(3103945753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061678967/10000000000 : ℝ)|^135 ≤ (1322297485669/25000000000000 : ℝ)^103
        have hw : |(-1061678967/10000000000 : ℝ)|=(1061678967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1016337111/2000000000 : ℝ)|^135 ≤ (1286827767747/3125000000000 : ℝ)^103
        have hw : |(1016337111/2000000000 : ℝ)|=(1016337111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (924447743/2000000000 : ℝ)*x 0 + (6229876131/10000000000 : ℝ)*x 1 + (-85311661/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924447743/2000000000 : ℝ)^135 ≤ (9092197151139/25000000000000 : ℝ)^103 := by
    have hnat : (924447743 : ℕ)^135*25000000000000^103 ≤ 9092197151139^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924447743 2000000000 9092197151139 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6229876131/10000000000 : ℝ)^135 ≤ (53780935836273/100000000000000 : ℝ)^103 := by
    have hnat : (6229876131 : ℕ)^135*100000000000000^103 ≤ 53780935836273^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6229876131 10000000000 53780935836273 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85311661/500000000 : ℝ)^135 ≤ (2462568887779/25000000000000 : ℝ)^103 := by
    have hnat : (85311661 : ℕ)^135*25000000000000^103 ≤ 2462568887779^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85311661 500000000 2462568887779 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(924447743/2000000000 : ℝ), (6229876131/10000000000 : ℝ), (-85311661/500000000 : ℝ)] ![(9092197151139/25000000000000 : ℝ), (53780935836273/100000000000000 : ℝ), (2462568887779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(924447743/2000000000 : ℝ)|^135 ≤ (9092197151139/25000000000000 : ℝ)^103
        have hw : |(924447743/2000000000 : ℝ)|=(924447743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6229876131/10000000000 : ℝ)|^135 ≤ (53780935836273/100000000000000 : ℝ)^103
        have hw : |(6229876131/10000000000 : ℝ)|=(6229876131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85311661/500000000 : ℝ)|^135 ≤ (2462568887779/25000000000000 : ℝ)^103
        have hw : |(-85311661/500000000 : ℝ)|=(85311661/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s6_s6_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1513300931/2500000000 : ℝ)*x 0 + (3459488633/10000000000 : ℝ)*x 1 + (3294415169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1513300931/2500000000 : ℝ)^135 ≤ (51790793538697/100000000000000 : ℝ)^103 := by
    have hnat : (1513300931 : ℕ)^135*100000000000000^103 ≤ 51790793538697^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1513300931 2500000000 51790793538697 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3459488633/10000000000 : ℝ)^135 ≤ (12438336760137/50000000000000 : ℝ)^103 := by
    have hnat : (3459488633 : ℕ)^135*50000000000000^103 ≤ 12438336760137^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3459488633 10000000000 12438336760137 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3294415169/10000000000 : ℝ)^135 ≤ (11666266466321/50000000000000 : ℝ)^103 := by
    have hnat : (3294415169 : ℕ)^135*50000000000000^103 ≤ 11666266466321^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3294415169 10000000000 11666266466321 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1513300931/2500000000 : ℝ), (3459488633/10000000000 : ℝ), (3294415169/10000000000 : ℝ)] ![(51790793538697/100000000000000 : ℝ), (12438336760137/50000000000000 : ℝ), (11666266466321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1513300931/2500000000 : ℝ)|^135 ≤ (51790793538697/100000000000000 : ℝ)^103
        have hw : |(1513300931/2500000000 : ℝ)|=(1513300931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3459488633/10000000000 : ℝ)|^135 ≤ (12438336760137/50000000000000 : ℝ)^103
        have hw : |(3459488633/10000000000 : ℝ)|=(3459488633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3294415169/10000000000 : ℝ)|^135 ≤ (11666266466321/50000000000000 : ℝ)^103
        have hw : |(3294415169/10000000000 : ℝ)|=(3294415169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306063_s6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((867/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(867/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2201/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2201/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41997/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41997/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15713/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15713/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7943/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7943/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15187/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15187/50000 : ℝ)*X 1 2) := by
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
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev5 with ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩
  have s6_pow0 : (867/2000 : ℝ) ^ (67/16 : ℝ) ≤ (1509599934018392213/50000000000000000000 : ℝ) := by
    have hpowers : (867/2000 : ℝ)^67 ≤ (1509599934018392213/50000000000000000000 : ℝ)^16 := by
      have hnat : (867 : ℕ)^67*50000000000000000000^16 ≤ 1509599934018392213^16*2000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        867 2000 1509599934018392213 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (867/2000 : ℝ)) (X := (1509599934018392213/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner0a : (51509599934018392213/50000000000000000000 : ℝ) ≤ (1258910772205551/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (51509599934018392213/50000000000000000000 : ℝ)^16 ≤ (1258910772205551/1250000000000000 : ℝ)^67 := by
      have hnat : (51509599934018392213 : ℕ)^16*1250000000000000^67 ≤ 1258910772205551^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51509599934018392213 50000000000000000000 1258910772205551 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1258910772205551/1250000000000000 : ℝ)) (X := (51509599934018392213/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner0b : (26509599934018392213/25000000000000000000 : ℝ) ≤ (10140999372067277/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (26509599934018392213/25000000000000000000 : ℝ)^16 ≤ (10140999372067277/10000000000000000 : ℝ)^67 := by
      have hnat : (26509599934018392213 : ℕ)^16*10000000000000000^67 ≤ 10140999372067277^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26509599934018392213 25000000000000000000 10140999372067277 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10140999372067277/10000000000000000 : ℝ)) (X := (26509599934018392213/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s6_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(8910772205551/541875000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(69713194422869/4335000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (867/2000 : ℝ)) (alpha := (8910772205551/541875000000000 : ℝ)) (beta := (69713194422869/4335000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow0,s6_corner0a]) (by linarith only [s6_pow0,s6_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (867/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(8910772205551/541875000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(69713194422869/4335000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow1 : (2201/5000 : ℝ) ^ (67/16 : ℝ) ≤ (1609735565160485117/50000000000000000000 : ℝ) := by
    have hpowers : (2201/5000 : ℝ)^67 ≤ (1609735565160485117/50000000000000000000 : ℝ)^16 := by
      have hnat : (2201 : ℕ)^67*50000000000000000000^16 ≤ 1609735565160485117^16*5000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 5000 1609735565160485117 50000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/5000 : ℝ)) (X := (1609735565160485117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner1a : (51609735565160485117/50000000000000000000 : ℝ) ≤ (5037979124665021/5000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (51609735565160485117/50000000000000000000 : ℝ)^16 ≤ (5037979124665021/5000000000000000 : ℝ)^67 := by
      have hnat : (51609735565160485117 : ℕ)^16*5000000000000000^67 ≤ 5037979124665021^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51609735565160485117 50000000000000000000 5037979124665021 5000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5037979124665021/5000000000000000 : ℝ)) (X := (51609735565160485117/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner1b : (26609735565160485117/25000000000000000000 : ℝ) ≤ (2030026787853591/2000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (26609735565160485117/25000000000000000000 : ℝ)^16 ≤ (2030026787853591/2000000000000000 : ℝ)^67 := by
      have hnat : (26609735565160485117 : ℕ)^16*2000000000000000^67 ≤ 2030026787853591^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26609735565160485117 25000000000000000000 2030026787853591 2000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2030026787853591/2000000000000000 : ℝ)) (X := (26609735565160485117/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s6_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(37979124665021/2201000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(74175689937913/4402000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (2201/5000 : ℝ)) (alpha := (37979124665021/2201000000000000 : ℝ)) (beta := (74175689937913/4402000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow1,s6_corner1a]) (by linarith only [s6_pow1,s6_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (2201/5000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(37979124665021/2201000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(74175689937913/4402000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s6_pow2 : (41997/100000 : ℝ) ^ (67/16 : ℝ) ≤ (2643787216558984073/100000000000000000000 : ℝ) := by
    have hpowers : (41997/100000 : ℝ)^67 ≤ (2643787216558984073/100000000000000000000 : ℝ)^16 := by
      have hnat : (41997 : ℕ)^67*100000000000000000000^16 ≤ 2643787216558984073^16*100000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        41997 100000 2643787216558984073 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (41997/100000 : ℝ)) (X := (2643787216558984073/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner2a : (102643787216558984073/100000000000000000000 : ℝ) ≤ (1006250962303389/1000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (102643787216558984073/100000000000000000000 : ℝ)^16 ≤ (1006250962303389/1000000000000000 : ℝ)^67 := by
      have hnat : (102643787216558984073 : ℕ)^16*1000000000000000^67 ≤ 1006250962303389^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102643787216558984073 100000000000000000000 1006250962303389 1000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006250962303389/1000000000000000 : ℝ)) (X := (102643787216558984073/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s6_corner2b : (52643787216558984073/50000000000000000000 : ℝ) ≤ (632737839648911/625000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (52643787216558984073/50000000000000000000 : ℝ)^16 ≤ (632737839648911/625000000000000 : ℝ)^67 := by
      have hnat : (52643787216558984073 : ℕ)^16*625000000000000^67 ≤ 632737839648911^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52643787216558984073 50000000000000000000 632737839648911 625000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632737839648911/625000000000000 : ℝ)) (X := (52643787216558984073/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s6_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(6250962303389/419970000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(30647905674343/2099850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (41997/100000 : ℝ)) (alpha := (6250962303389/419970000000000 : ℝ)) (beta := (30647905674343/2099850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s6_pow2,s6_corner2a]) (by linarith only [s6_pow2,s6_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (41997/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s5_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(6250962303389/419970000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(30647905674343/2099850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s6_0 : ((-45678207/250000000 : ℝ)*X 0 0+(5390674367/10000000000 : ℝ)*X 0 1+(2706583327/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_1 : ((2695743911/5000000000 : ℝ)*X 1 0+(-916949041/5000000000 : ℝ)*X 1 1+(5407519573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_2 : ((135221889/250000000 : ℝ)*X 2 0+(5404284827/10000000000 : ℝ)*X 2 1+(-1814070651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_6 : ((4330916849/10000000000 : ℝ)*X 0 0+(4328053921/10000000000 : ℝ)*X 0 1+(539458407/1250000000 : ℝ)*X 0 2+(4330916849/10000000000 : ℝ)*X 1 0+(4328053921/10000000000 : ℝ)*X 1 1+(539458407/1250000000 : ℝ)*X 1 2+(4330916849/10000000000 : ℝ)*X 2 0+(4328053921/10000000000 : ℝ)*X 2 1+(539458407/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_7 : ((-2160023/12500000 : ℝ)*X 0 0+(1163573717/2500000000 : ℝ)*X 0 1+(1546495451/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_8 : ((1268131069/2500000000 : ℝ)*X 1 0+(-561879283/5000000000 : ℝ)*X 1 1+(6180292229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_9 : ((612271317/1250000000 : ℝ)*X 2 0+(3179847737/5000000000 : ℝ)*X 2 1+(-547288233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_13 : ((2248059299/5000000000 : ℝ)*X 0 0+(5545529033/10000000000 : ℝ)*X 0 1+(2788555441/10000000000 : ℝ)*X 0 2+(2248059299/5000000000 : ℝ)*X 1 0+(5545529033/10000000000 : ℝ)*X 1 1+(2788555441/10000000000 : ℝ)*X 1 2+(2248059299/5000000000 : ℝ)*X 2 0+(5545529033/10000000000 : ℝ)*X 2 1+(2788555441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_14 : ((-1117674029/10000000000 : ℝ)*X 0 0+(5080269657/10000000000 : ℝ)*X 0 1+(1544146391/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_15 : ((4671789187/10000000000 : ℝ)*X 1 0+(-863308223/5000000000 : ℝ)*X 1 1+(1542723883/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_16 : ((1542935871/2500000000 : ℝ)*X 2 0+(509395169/1000000000 : ℝ)*X 2 1+(-137996649/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_20 : ((5913394623/10000000000 : ℝ)*X 0 0+(1019093097/2500000000 : ℝ)*X 0 1+(2808135331/10000000000 : ℝ)*X 0 2+(5913394623/10000000000 : ℝ)*X 1 0+(1019093097/2500000000 : ℝ)*X 1 1+(2808135331/10000000000 : ℝ)*X 1 2+(5913394623/10000000000 : ℝ)*X 2 0+(1019093097/2500000000 : ℝ)*X 2 1+(2808135331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_21 : ((-106398081/1000000000 : ℝ)*X 0 0+(292365323/500000000 : ℝ)*X 0 1+(5456263979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_22 : ((3103945753/5000000000 : ℝ)*X 1 0+(-1061678967/10000000000 : ℝ)*X 1 1+(1016337111/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_23 : ((924447743/2000000000 : ℝ)*X 2 0+(6229876131/10000000000 : ℝ)*X 2 1+(-85311661/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s6_27 : ((1513300931/2500000000 : ℝ)*X 0 0+(3459488633/10000000000 : ℝ)*X 0 1+(3294415169/10000000000 : ℝ)*X 0 2+(1513300931/2500000000 : ℝ)*X 1 0+(3459488633/10000000000 : ℝ)*X 1 1+(3294415169/10000000000 : ℝ)*X 1 2+(1513300931/2500000000 : ℝ)*X 2 0+(3459488633/10000000000 : ℝ)*X 2 1+(3294415169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s6_s6_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s6_0 : (0 : ℝ) ≤ ((15713/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15713/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (25865428933169515314975953/7702949750000000000000000000000 : ℝ) := by norm_num
    linear_combination (293407/500000000000 : ℝ)*(base50) + (127948126453/1000000000000 : ℝ)*(base60) + (2466817957919/500000000000 : ℝ)*(major_s6_0) + (2466817957919/500000000000 : ℝ)*(major_s6_1) + (2466817957919/500000000000 : ℝ)*(major_s6_2) + (422181/125000000000 : ℝ)*(sp_s6_0) + (4428867/1000000000000 : ℝ)*(sp_s6_6) + (6667460886799/1000000000000 : ℝ)*(sp_s6_7) + (416715428713/62500000000 : ℝ)*(sp_s6_8) + (3333725599447/500000000000 : ℝ)*(sp_s6_9) + (3199790569277/1000000000000 : ℝ)*(sp_s6_13) + (2289999/200000000000 : ℝ)*(sp_s6_14) + (14427417/500000000000 : ℝ)*(sp_s6_15) + (6128837/250000000000 : ℝ)*(sp_s6_23) + (24998398423/7812500000 : ℝ)*(f.failure) + (3333737857121/500000000000 : ℝ)*(f.sum) + (15443924242295181697/46217698500000000000000000000000 : ℝ)*base62 + (338175816145901/2099850000000000000000000000 : ℝ)*base64 + (554224088424653/2201000000000000000000000000 : ℝ)*base66 + (251698333428133/419970000000000000000000000 : ℝ)*base68 + (665682449856153779/2528569375000000000000000000000 : ℝ)*base71 + (768782233636139/2167500000000000000000000000 : ℝ)*base72 + (527389675315351/1100500000000000000000000000 : ℝ)*base74 + (104343826293631/270937500000000000000000000 : ℝ)*base76 + (1017178456567138867/9541335000000000000000000000000 : ℝ)*base79 + (481/1562500000000000 : ℝ)*base87 + (481/1562500000000000 : ℝ)*base89 + (481/1562500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7943/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7943/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8743026543980755452904859021/2782690597187500000000000000000000 : ℝ) := by norm_num
    linear_combination (871419/1000000000000 : ℝ)*(base60) + (623947766801/125000000000 : ℝ)*(major_s6_0) + (623947766801/125000000000 : ℝ)*(major_s6_1) + (623947766801/125000000000 : ℝ)*(major_s6_2) + (1430689/200000000000 : ℝ)*(sp_s6_0) + (1525397/200000000000 : ℝ)*(sp_s6_1) + (9760223/500000000000 : ℝ)*(sp_s6_2) + (408839/31250000000 : ℝ)*(sp_s6_7) + (11246701/1000000000000 : ℝ)*(sp_s6_8) + (6745765963681/1000000000000 : ℝ)*(sp_s6_14) + (6745767326289/1000000000000 : ℝ)*(sp_s6_15) + (6745766679529/1000000000000 : ℝ)*(sp_s6_16) + (1618675779437/500000000000 : ℝ)*(sp_s6_20) + (25462651/1000000000000 : ℝ)*(sp_s6_27) + (129495080861/40000000000 : ℝ)*(f.failure) + (3372893099987/500000000000 : ℝ)*(f.sum) + (12525889335966539351/23108849250000000000000000000000 : ℝ)*base62 + (721129994678809/2099850000000000000000000000 : ℝ)*base65 + (41078610887919/275125000000000000000000000 : ℝ)*base67 + (346898196199243/419970000000000000000000000 : ℝ)*base68 + (1257487099973459553/5057138750000000000000000000000 : ℝ)*base71 + (477808530838987/1083750000000000000000000000 : ℝ)*base72 + (75527272953727/137562500000000000000000000 : ℝ)*base74 + (497166139696009/1083750000000000000000000000 : ℝ)*base76 + (2942361907784629/298166718750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1073/2000000000000000 : ℝ)*base87 + (1073/2000000000000000 : ℝ)*base89 + (1073/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s6_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15187/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15187/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (116700348846588717599154237/30811799000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46019217181/200000000000 : ℝ)*(base40) + (237021/200000000000 : ℝ)*(base50) + (4615515372209/1000000000000 : ℝ)*(major_s6_0) + (4615515372209/1000000000000 : ℝ)*(major_s6_1) + (4615515372209/1000000000000 : ℝ)*(major_s6_2) + (35062633/1000000000000 : ℝ)*(sp_s6_0) + (35377089/1000000000000 : ℝ)*(sp_s6_1) + (18345427/1000000000000 : ℝ)*(sp_s6_2) + (1135131/50000000000 : ℝ)*(sp_s6_9) + (41733099/1000000000000 : ℝ)*(sp_s6_20) + (3118761003947/500000000000 : ℝ)*(sp_s6_21) + (6237521693439/1000000000000 : ℝ)*(sp_s6_22) + (6237516022481/1000000000000 : ℝ)*(sp_s6_23) + (74835766957/25000000000 : ℝ)*(sp_s6_27) + (2993472411379/1000000000000 : ℝ)*(f.failure) + (97461829227/15625000000 : ℝ)*(f.sum) + (21430268667727590967/92435397000000000000000000000000 : ℝ)*base62 + (282486520045433/524962500000000000000000000 : ℝ)*base65 + (2807909016920417/4402000000000000000000000000 : ℝ)*base67 + (1312155429977/26248125000000000000000000 : ℝ)*base68 + (6084850197218071/79017792968750000000000000000 : ℝ)*base71 + (124014221240879/4335000000000000000000000000 : ℝ)*base72 + (313461353813811/2201000000000000000000000000 : ℝ)*base74 + (45860195481841/541875000000000000000000000 : ℝ)*base76 + (3676343181303810337/19082670000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (8753/50000000000000000 : ℝ)*base86 + (8753/50000000000000000 : ℝ)*base88 + (8753/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s6_0,ratio_s6_1,ratio_s6_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev5 : (0 : ℝ) ≤ ((867/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(867/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2201/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(2201/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(41997/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(41997/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15713/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15713/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7943/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7943/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15187/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15187/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306063_s6 p hpa hpb X hX hprev5

#print axioms solution
