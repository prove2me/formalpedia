-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309061_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:04:41.602559+00:00
-- url     : https://prove2.me/submissions/a1b21ffe-ee4b-4494-93b9-d55f4d173f45

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
theorem collision_support_c309061_s5_s5_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-51359223/200000000 : ℝ)*x 0 + (4514765019/10000000000 : ℝ)*x 1 + (140009599/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (51359223/200000000 : ℝ)^35 ≤ (17165311670041/100000000000000 : ℝ)^27 := by
    have hnat : (51359223 : ℕ)^35*100000000000000^27 ≤ 17165311670041^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51359223 200000000 17165311670041 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4514765019/10000000000 : ℝ)^35 ≤ (35670140987601/100000000000000 : ℝ)^27 := by
    have hnat : (4514765019 : ℕ)^35*100000000000000^27 ≤ 35670140987601^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4514765019 10000000000 35670140987601 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (140009599/250000000 : ℝ)^35 ≤ (5895568417297/12500000000000 : ℝ)^27 := by
    have hnat : (140009599 : ℕ)^35*12500000000000^27 ≤ 5895568417297^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140009599 250000000 5895568417297 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-51359223/200000000 : ℝ), (4514765019/10000000000 : ℝ), (140009599/250000000 : ℝ)] ![(17165311670041/100000000000000 : ℝ), (35670140987601/100000000000000 : ℝ), (5895568417297/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-51359223/200000000 : ℝ)|^35 ≤ (17165311670041/100000000000000 : ℝ)^27
        have hw : |(-51359223/200000000 : ℝ)|=(51359223/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4514765019/10000000000 : ℝ)|^35 ≤ (35670140987601/100000000000000 : ℝ)^27
        have hw : |(4514765019/10000000000 : ℝ)|=(4514765019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(140009599/250000000 : ℝ)|^35 ≤ (5895568417297/12500000000000 : ℝ)^27
        have hw : |(140009599/250000000 : ℝ)|=(140009599/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2338731571/5000000000 : ℝ)*x 0 + (-1295716073/5000000000 : ℝ)*x 1 + (5427489739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2338731571/5000000000 : ℝ)^35 ≤ (37345275702567/100000000000000 : ℝ)^27 := by
    have hnat : (2338731571 : ℕ)^35*100000000000000^27 ≤ 37345275702567^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338731571 5000000000 37345275702567 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295716073/5000000000 : ℝ)^35 ≤ (17368962157759/100000000000000 : ℝ)^27 := by
    have hnat : (1295716073 : ℕ)^35*100000000000000^27 ≤ 17368962157759^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295716073 5000000000 17368962157759 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427489739/10000000000 : ℝ)^35 ≤ (11321440531931/25000000000000 : ℝ)^27 := by
    have hnat : (5427489739 : ℕ)^35*25000000000000^27 ≤ 11321440531931^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427489739 10000000000 11321440531931 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2338731571/5000000000 : ℝ), (-1295716073/5000000000 : ℝ), (5427489739/10000000000 : ℝ)] ![(37345275702567/100000000000000 : ℝ), (17368962157759/100000000000000 : ℝ), (11321440531931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2338731571/5000000000 : ℝ)|^35 ≤ (37345275702567/100000000000000 : ℝ)^27
        have hw : |(2338731571/5000000000 : ℝ)|=(2338731571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1295716073/5000000000 : ℝ)|^35 ≤ (17368962157759/100000000000000 : ℝ)^27
        have hw : |(-1295716073/5000000000 : ℝ)|=(1295716073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427489739/10000000000 : ℝ)|^35 ≤ (11321440531931/25000000000000 : ℝ)^27
        have hw : |(5427489739/10000000000 : ℝ)|=(5427489739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (73227573/156250000 : ℝ)*x 0 + (3000741969/5000000000 : ℝ)*x 1 + (-90908041/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73227573/156250000 : ℝ)^35 ≤ (3743950134351/10000000000000 : ℝ)^27 := by
    have hnat : (73227573 : ℕ)^35*10000000000000^27 ≤ 3743950134351^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73227573 156250000 3743950134351 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3000741969/5000000000 : ℝ)^35 ≤ (51589047184809/100000000000000 : ℝ)^27 := by
    have hnat : (3000741969 : ℕ)^35*100000000000000^27 ≤ 51589047184809^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3000741969 5000000000 51589047184809 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90908041/500000000 : ℝ)^35 ≤ (2194290291111/20000000000000 : ℝ)^27 := by
    have hnat : (90908041 : ℕ)^35*20000000000000^27 ≤ 2194290291111^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90908041 500000000 2194290291111 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(73227573/156250000 : ℝ), (3000741969/5000000000 : ℝ), (-90908041/500000000 : ℝ)] ![(3743950134351/10000000000000 : ℝ), (51589047184809/100000000000000 : ℝ), (2194290291111/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(73227573/156250000 : ℝ)|^35 ≤ (3743950134351/10000000000000 : ℝ)^27
        have hw : |(73227573/156250000 : ℝ)|=(73227573/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3000741969/5000000000 : ℝ)|^35 ≤ (51589047184809/100000000000000 : ℝ)^27
        have hw : |(3000741969/5000000000 : ℝ)|=(3000741969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90908041/500000000 : ℝ)|^35 ≤ (2194290291111/20000000000000 : ℝ)^27
        have hw : |(-90908041/500000000 : ℝ)|=(90908041/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5766314593/10000000000 : ℝ)*x 0 + (3196274107/10000000000 : ℝ)*x 1 + (75364509/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5766314593/10000000000 : ℝ)^35 ≤ (48983903855139/100000000000000 : ℝ)^27 := by
    have hnat : (5766314593 : ℕ)^35*100000000000000^27 ≤ 48983903855139^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5766314593 10000000000 48983903855139 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3196274107/10000000000 : ℝ)^35 ≤ (22796694190229/100000000000000 : ℝ)^27 := by
    have hnat : (3196274107 : ℕ)^35*100000000000000^27 ≤ 22796694190229^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3196274107 10000000000 22796694190229 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75364509/200000000 : ℝ)^35 ≤ (28219401934503/100000000000000 : ℝ)^27 := by
    have hnat : (75364509 : ℕ)^35*100000000000000^27 ≤ 28219401934503^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75364509 200000000 28219401934503 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5766314593/10000000000 : ℝ), (3196274107/10000000000 : ℝ), (75364509/200000000 : ℝ)] ![(48983903855139/100000000000000 : ℝ), (22796694190229/100000000000000 : ℝ), (28219401934503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5766314593/10000000000 : ℝ)|^35 ≤ (48983903855139/100000000000000 : ℝ)^27
        have hw : |(5766314593/10000000000 : ℝ)|=(5766314593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3196274107/10000000000 : ℝ)|^35 ≤ (22796694190229/100000000000000 : ℝ)^27
        have hw : |(3196274107/10000000000 : ℝ)|=(3196274107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75364509/200000000 : ℝ)|^35 ≤ (28219401934503/100000000000000 : ℝ)^27
        have hw : |(75364509/200000000 : ℝ)|=(75364509/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2572691639/10000000000 : ℝ)*x 0 + (4424456301/10000000000 : ℝ)*x 1 + (2840464003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2572691639/10000000000 : ℝ)^35 ≤ (1720631244031/10000000000000 : ℝ)^27 := by
    have hnat : (2572691639 : ℕ)^35*10000000000000^27 ≤ 1720631244031^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572691639 10000000000 1720631244031 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4424456301/10000000000 : ℝ)^35 ≤ (1737398800677/5000000000000 : ℝ)^27 := by
    have hnat : (4424456301 : ℕ)^35*5000000000000^27 ≤ 1737398800677^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4424456301 10000000000 1737398800677 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840464003/5000000000 : ℝ)^35 ≤ (48045711526097/100000000000000 : ℝ)^27 := by
    have hnat : (2840464003 : ℕ)^35*100000000000000^27 ≤ 48045711526097^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840464003 5000000000 48045711526097 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2572691639/10000000000 : ℝ), (4424456301/10000000000 : ℝ), (2840464003/5000000000 : ℝ)] ![(1720631244031/10000000000000 : ℝ), (1737398800677/5000000000000 : ℝ), (48045711526097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2572691639/10000000000 : ℝ)|^35 ≤ (1720631244031/10000000000000 : ℝ)^27
        have hw : |(-2572691639/10000000000 : ℝ)|=(2572691639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4424456301/10000000000 : ℝ)|^35 ≤ (1737398800677/5000000000000 : ℝ)^27
        have hw : |(4424456301/10000000000 : ℝ)|=(4424456301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840464003/5000000000 : ℝ)|^35 ≤ (48045711526097/100000000000000 : ℝ)^27
        have hw : |(2840464003/5000000000 : ℝ)|=(2840464003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (575232227/1250000000 : ℝ)*x 0 + (-2382206083/10000000000 : ℝ)*x 1 + (5664167341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (575232227/1250000000 : ℝ)^35 ≤ (18282330465471/50000000000000 : ℝ)^27 := by
    have hnat : (575232227 : ℕ)^35*50000000000000^27 ≤ 18282330465471^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      575232227 1250000000 18282330465471 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2382206083/10000000000 : ℝ)^35 ≤ (1557329864539/10000000000000 : ℝ)^27 := by
    have hnat : (2382206083 : ℕ)^35*10000000000000^27 ≤ 1557329864539^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2382206083 10000000000 1557329864539 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664167341/10000000000 : ℝ)^35 ≤ (23931020203493/50000000000000 : ℝ)^27 := by
    have hnat : (5664167341 : ℕ)^35*50000000000000^27 ≤ 23931020203493^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664167341 10000000000 23931020203493 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(575232227/1250000000 : ℝ), (-2382206083/10000000000 : ℝ), (5664167341/10000000000 : ℝ)] ![(18282330465471/50000000000000 : ℝ), (1557329864539/10000000000000 : ℝ), (23931020203493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(575232227/1250000000 : ℝ)|^35 ≤ (18282330465471/50000000000000 : ℝ)^27
        have hw : |(575232227/1250000000 : ℝ)|=(575232227/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2382206083/10000000000 : ℝ)|^35 ≤ (1557329864539/10000000000000 : ℝ)^27
        have hw : |(-2382206083/10000000000 : ℝ)|=(2382206083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664167341/10000000000 : ℝ)|^35 ≤ (23931020203493/50000000000000 : ℝ)^27
        have hw : |(5664167341/10000000000 : ℝ)|=(5664167341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4610963157/10000000000 : ℝ)*x 0 + (124616077/200000000 : ℝ)*x 1 + (-99058173/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4610963157/10000000000 : ℝ)^35 ≤ (36658472430119/100000000000000 : ℝ)^27 := by
    have hnat : (4610963157 : ℕ)^35*100000000000000^27 ≤ 36658472430119^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610963157 10000000000 36658472430119 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124616077/200000000 : ℝ)^35 ≤ (54158702507369/100000000000000 : ℝ)^27 := by
    have hnat : (124616077 : ℕ)^35*100000000000000^27 ≤ 54158702507369^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124616077 200000000 54158702507369 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99058173/625000000 : ℝ)^35 ≤ (286963282709/3125000000000 : ℝ)^27 := by
    have hnat : (99058173 : ℕ)^35*3125000000000^27 ≤ 286963282709^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99058173 625000000 286963282709 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4610963157/10000000000 : ℝ), (124616077/200000000 : ℝ), (-99058173/625000000 : ℝ)] ![(36658472430119/100000000000000 : ℝ), (54158702507369/100000000000000 : ℝ), (286963282709/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4610963157/10000000000 : ℝ)|^35 ≤ (36658472430119/100000000000000 : ℝ)^27
        have hw : |(4610963157/10000000000 : ℝ)|=(4610963157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(124616077/200000000 : ℝ)|^35 ≤ (54158702507369/100000000000000 : ℝ)^27
        have hw : |(124616077/200000000 : ℝ)|=(124616077/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99058173/625000000 : ℝ)|^35 ≤ (286963282709/3125000000000 : ℝ)^27
        have hw : |(-99058173/625000000 : ℝ)|=(99058173/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5773980961/10000000000 : ℝ)*x 0 + (3363318949/10000000000 : ℝ)*x 1 + (719613443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5773980961/10000000000 : ℝ)^35 ≤ (49068341188539/100000000000000 : ℝ)^27 := by
    have hnat : (5773980961 : ℕ)^35*100000000000000^27 ≤ 49068341188539^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5773980961 10000000000 49068341188539 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3363318949/10000000000 : ℝ)^35 ≤ (24352927803919/100000000000000 : ℝ)^27 := by
    have hnat : (3363318949 : ℕ)^35*100000000000000^27 ≤ 24352927803919^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3363318949 10000000000 24352927803919 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719613443/2000000000 : ℝ)^35 ≤ (26578730990823/100000000000000 : ℝ)^27 := by
    have hnat : (719613443 : ℕ)^35*100000000000000^27 ≤ 26578730990823^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719613443 2000000000 26578730990823 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5773980961/10000000000 : ℝ), (3363318949/10000000000 : ℝ), (719613443/2000000000 : ℝ)] ![(49068341188539/100000000000000 : ℝ), (24352927803919/100000000000000 : ℝ), (26578730990823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5773980961/10000000000 : ℝ)|^35 ≤ (49068341188539/100000000000000 : ℝ)^27
        have hw : |(5773980961/10000000000 : ℝ)|=(5773980961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3363318949/10000000000 : ℝ)|^35 ≤ (24352927803919/100000000000000 : ℝ)^27
        have hw : |(3363318949/10000000000 : ℝ)|=(3363318949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(719613443/2000000000 : ℝ)|^35 ≤ (26578730990823/100000000000000 : ℝ)^27
        have hw : |(719613443/2000000000 : ℝ)|=(719613443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-91316651/400000000 : ℝ)*x 0 + (1157890583/2500000000 : ℝ)*x 1 + (2856242471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (91316651/400000000 : ℝ)^35 ≤ (14737130948097/100000000000000 : ℝ)^27 := by
    have hnat : (91316651 : ℕ)^35*100000000000000^27 ≤ 14737130948097^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91316651 400000000 14737130948097 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157890583/2500000000 : ℝ)^35 ≤ (7374181269517/20000000000000 : ℝ)^27 := by
    have hnat : (1157890583 : ℕ)^35*20000000000000^27 ≤ 7374181269517^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157890583 2500000000 7374181269517 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2856242471/5000000000 : ℝ)^35 ≤ (24195981345493/50000000000000 : ℝ)^27 := by
    have hnat : (2856242471 : ℕ)^35*50000000000000^27 ≤ 24195981345493^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856242471 5000000000 24195981345493 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-91316651/400000000 : ℝ), (1157890583/2500000000 : ℝ), (2856242471/5000000000 : ℝ)] ![(14737130948097/100000000000000 : ℝ), (7374181269517/20000000000000 : ℝ), (24195981345493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-91316651/400000000 : ℝ)|^35 ≤ (14737130948097/100000000000000 : ℝ)^27
        have hw : |(-91316651/400000000 : ℝ)|=(91316651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1157890583/2500000000 : ℝ)|^35 ≤ (7374181269517/20000000000000 : ℝ)^27
        have hw : |(1157890583/2500000000 : ℝ)|=(1157890583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2856242471/5000000000 : ℝ)|^35 ≤ (24195981345493/50000000000000 : ℝ)^27
        have hw : |(2856242471/5000000000 : ℝ)|=(2856242471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (141185257/312500000 : ℝ)*x 0 + (-624826533/2500000000 : ℝ)*x 1 + (5651622207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141185257/312500000 : ℝ)^35 ≤ (35702541088467/100000000000000 : ℝ)^27 := by
    have hnat : (141185257 : ℕ)^35*100000000000000^27 ≤ 35702541088467^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141185257 312500000 35702541088467 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (624826533/2500000000 : ℝ)^35 ≤ (4143197139119/25000000000000 : ℝ)^27 := by
    have hnat : (624826533 : ℕ)^35*25000000000000^27 ≤ 4143197139119^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624826533 2500000000 4143197139119 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5651622207/10000000000 : ℝ)^35 ≤ (47724670337117/100000000000000 : ℝ)^27 := by
    have hnat : (5651622207 : ℕ)^35*100000000000000^27 ≤ 47724670337117^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5651622207 10000000000 47724670337117 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(141185257/312500000 : ℝ), (-624826533/2500000000 : ℝ), (5651622207/10000000000 : ℝ)] ![(35702541088467/100000000000000 : ℝ), (4143197139119/25000000000000 : ℝ), (47724670337117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(141185257/312500000 : ℝ)|^35 ≤ (35702541088467/100000000000000 : ℝ)^27
        have hw : |(141185257/312500000 : ℝ)|=(141185257/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-624826533/2500000000 : ℝ)|^35 ≤ (4143197139119/25000000000000 : ℝ)^27
        have hw : |(-624826533/2500000000 : ℝ)|=(624826533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5651622207/10000000000 : ℝ)|^35 ≤ (47724670337117/100000000000000 : ℝ)^27
        have hw : |(5651622207/10000000000 : ℝ)|=(5651622207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4975062283/10000000000 : ℝ)*x 0 + (5882659187/10000000000 : ℝ)*x 1 + (-39936903/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4975062283/10000000000 : ℝ)^35 ≤ (20226980298791/50000000000000 : ℝ)^27 := by
    have hnat : (4975062283 : ℕ)^35*50000000000000^27 ≤ 20226980298791^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975062283 10000000000 20226980298791 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5882659187/10000000000 : ℝ)^35 ≤ (6283610235059/12500000000000 : ℝ)^27 := by
    have hnat : (5882659187 : ℕ)^35*12500000000000^27 ≤ 6283610235059^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5882659187 10000000000 6283610235059 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39936903/250000000 : ℝ)^35 ≤ (9277157511329/100000000000000 : ℝ)^27 := by
    have hnat : (39936903 : ℕ)^35*100000000000000^27 ≤ 9277157511329^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39936903 250000000 9277157511329 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4975062283/10000000000 : ℝ), (5882659187/10000000000 : ℝ), (-39936903/250000000 : ℝ)] ![(20226980298791/50000000000000 : ℝ), (6283610235059/12500000000000 : ℝ), (9277157511329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4975062283/10000000000 : ℝ)|^35 ≤ (20226980298791/50000000000000 : ℝ)^27
        have hw : |(4975062283/10000000000 : ℝ)|=(4975062283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5882659187/10000000000 : ℝ)|^35 ≤ (6283610235059/12500000000000 : ℝ)^27
        have hw : |(5882659187/10000000000 : ℝ)|=(5882659187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-39936903/250000000 : ℝ)|^35 ≤ (9277157511329/100000000000000 : ℝ)^27
        have hw : |(-39936903/250000000 : ℝ)|=(39936903/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3059875863/5000000000 : ℝ)*x 0 + (47167653/156250000 : ℝ)*x 1 + (3529117261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3059875863/5000000000 : ℝ)^35 ≤ (52910738025287/100000000000000 : ℝ)^27 := by
    have hnat : (3059875863 : ℕ)^35*100000000000000^27 ≤ 52910738025287^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3059875863 5000000000 52910738025287 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47167653/156250000 : ℝ)^35 ≤ (10584445092449/50000000000000 : ℝ)^27 := by
    have hnat : (47167653 : ℕ)^35*50000000000000^27 ≤ 10584445092449^27*156250000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47167653 156250000 10584445092449 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3529117261/10000000000 : ℝ)^35 ≤ (41472594829/160000000000 : ℝ)^27 := by
    have hnat : (3529117261 : ℕ)^35*160000000000^27 ≤ 41472594829^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3529117261 10000000000 41472594829 160000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3059875863/5000000000 : ℝ), (47167653/156250000 : ℝ), (3529117261/10000000000 : ℝ)] ![(52910738025287/100000000000000 : ℝ), (10584445092449/50000000000000 : ℝ), (41472594829/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3059875863/5000000000 : ℝ)|^35 ≤ (52910738025287/100000000000000 : ℝ)^27
        have hw : |(3059875863/5000000000 : ℝ)|=(3059875863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(47167653/156250000 : ℝ)|^35 ≤ (10584445092449/50000000000000 : ℝ)^27
        have hw : |(47167653/156250000 : ℝ)|=(47167653/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3529117261/10000000000 : ℝ)|^35 ≤ (41472594829/160000000000 : ℝ)^27
        have hw : |(3529117261/10000000000 : ℝ)|=(3529117261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2301774779/10000000000 : ℝ)*x 0 + (1169783287/2500000000 : ℝ)*x 1 + (5653233179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2301774779/10000000000 : ℝ)^35 ≤ (7447566844359/50000000000000 : ℝ)^27 := by
    have hnat : (2301774779 : ℕ)^35*50000000000000^27 ≤ 7447566844359^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2301774779 10000000000 7447566844359 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1169783287/2500000000 : ℝ)^35 ≤ (9340640187509/25000000000000 : ℝ)^27 := by
    have hnat : (1169783287 : ℕ)^35*25000000000000^27 ≤ 9340640187509^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1169783287 2500000000 9340640187509 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5653233179/10000000000 : ℝ)^35 ≤ (47742305538553/100000000000000 : ℝ)^27 := by
    have hnat : (5653233179 : ℕ)^35*100000000000000^27 ≤ 47742305538553^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653233179 10000000000 47742305538553 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2301774779/10000000000 : ℝ), (1169783287/2500000000 : ℝ), (5653233179/10000000000 : ℝ)] ![(7447566844359/50000000000000 : ℝ), (9340640187509/25000000000000 : ℝ), (47742305538553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2301774779/10000000000 : ℝ)|^35 ≤ (7447566844359/50000000000000 : ℝ)^27
        have hw : |(-2301774779/10000000000 : ℝ)|=(2301774779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1169783287/2500000000 : ℝ)|^35 ≤ (9340640187509/25000000000000 : ℝ)^27
        have hw : |(1169783287/2500000000 : ℝ)|=(1169783287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5653233179/10000000000 : ℝ)|^35 ≤ (47742305538553/100000000000000 : ℝ)^27
        have hw : |(5653233179/10000000000 : ℝ)|=(5653233179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (989419273/2000000000 : ℝ)*x 0 + (-1163372967/5000000000 : ℝ)*x 1 + (134413903/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989419273/2000000000 : ℝ)^35 ≤ (8031885570213/20000000000000 : ℝ)^27 := by
    have hnat : (989419273 : ℕ)^35*20000000000000^27 ≤ 8031885570213^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989419273 2000000000 8031885570213 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163372967/5000000000 : ℝ)^35 ≤ (7552470390497/50000000000000 : ℝ)^27 := by
    have hnat : (1163372967 : ℕ)^35*50000000000000^27 ≤ 7552470390497^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163372967 5000000000 7552470390497 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134413903/250000000 : ℝ)^35 ≤ (44735631354967/100000000000000 : ℝ)^27 := by
    have hnat : (134413903 : ℕ)^35*100000000000000^27 ≤ 44735631354967^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134413903 250000000 44735631354967 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(989419273/2000000000 : ℝ), (-1163372967/5000000000 : ℝ), (134413903/250000000 : ℝ)] ![(8031885570213/20000000000000 : ℝ), (7552470390497/50000000000000 : ℝ), (44735631354967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(989419273/2000000000 : ℝ)|^35 ≤ (8031885570213/20000000000000 : ℝ)^27
        have hw : |(989419273/2000000000 : ℝ)|=(989419273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1163372967/5000000000 : ℝ)|^35 ≤ (7552470390497/50000000000000 : ℝ)^27
        have hw : |(-1163372967/5000000000 : ℝ)|=(1163372967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134413903/250000000 : ℝ)|^35 ≤ (44735631354967/100000000000000 : ℝ)^27
        have hw : |(134413903/250000000 : ℝ)|=(134413903/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4503867301/10000000000 : ℝ)*x 0 + (6190904331/10000000000 : ℝ)*x 1 + (-893727887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4503867301/10000000000 : ℝ)^35 ≤ (35558569274617/100000000000000 : ℝ)^27 := by
    have hnat : (4503867301 : ℕ)^35*100000000000000^27 ≤ 35558569274617^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503867301 10000000000 35558569274617 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6190904331/10000000000 : ℝ)^35 ≤ (10741912180011/20000000000000 : ℝ)^27 := by
    have hnat : (6190904331 : ℕ)^35*20000000000000^27 ≤ 10741912180011^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6190904331 10000000000 10741912180011 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893727887/5000000000 : ℝ)^35 ≤ (2682967452311/25000000000000 : ℝ)^27 := by
    have hnat : (893727887 : ℕ)^35*25000000000000^27 ≤ 2682967452311^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893727887 5000000000 2682967452311 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4503867301/10000000000 : ℝ), (6190904331/10000000000 : ℝ), (-893727887/5000000000 : ℝ)] ![(35558569274617/100000000000000 : ℝ), (10741912180011/20000000000000 : ℝ), (2682967452311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4503867301/10000000000 : ℝ)|^35 ≤ (35558569274617/100000000000000 : ℝ)^27
        have hw : |(4503867301/10000000000 : ℝ)|=(4503867301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6190904331/10000000000 : ℝ)|^35 ≤ (10741912180011/20000000000000 : ℝ)^27
        have hw : |(6190904331/10000000000 : ℝ)|=(6190904331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893727887/5000000000 : ℝ)|^35 ≤ (2682967452311/25000000000000 : ℝ)^27
        have hw : |(-893727887/5000000000 : ℝ)|=(893727887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s5_s5_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6170370453/10000000000 : ℝ)*x 0 + (1507611187/5000000000 : ℝ)*x 1 + (3472672079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6170370453/10000000000 : ℝ)^35 ≤ (6684843561879/12500000000000 : ℝ)^27 := by
    have hnat : (6170370453 : ℕ)^35*12500000000000^27 ≤ 6684843561879^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6170370453 10000000000 6684843561879 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1507611187/5000000000 : ℝ)^35 ≤ (10568506099531/50000000000000 : ℝ)^27 := by
    have hnat : (1507611187 : ℕ)^35*50000000000000^27 ≤ 10568506099531^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507611187 5000000000 10568506099531 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3472672079/10000000000 : ℝ)^35 ≤ (25384239290943/100000000000000 : ℝ)^27 := by
    have hnat : (3472672079 : ℕ)^35*100000000000000^27 ≤ 25384239290943^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3472672079 10000000000 25384239290943 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6170370453/10000000000 : ℝ), (1507611187/5000000000 : ℝ), (3472672079/10000000000 : ℝ)] ![(6684843561879/12500000000000 : ℝ), (10568506099531/50000000000000 : ℝ), (25384239290943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6170370453/10000000000 : ℝ)|^35 ≤ (6684843561879/12500000000000 : ℝ)^27
        have hw : |(6170370453/10000000000 : ℝ)|=(6170370453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1507611187/5000000000 : ℝ)|^35 ≤ (10568506099531/50000000000000 : ℝ)^27
        have hw : |(1507611187/5000000000 : ℝ)|=(1507611187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3472672079/10000000000 : ℝ)|^35 ≤ (25384239290943/100000000000000 : ℝ)^27
        have hw : |(3472672079/10000000000 : ℝ)|=(3472672079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309061_s5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((5439/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5439/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32209/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32209/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29753/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4047/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4047/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20273/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20273/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18811/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18811/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s5_pow0 : (5439/20000 : ℝ) ^ (69/16 : ℝ) ≤ (364111239299035251/100000000000000000000 : ℝ) := by
    have hpowers : (5439/20000 : ℝ)^69 ≤ (364111239299035251/100000000000000000000 : ℝ)^16 := by
      have hnat : (5439 : ℕ)^69*100000000000000000000^16 ≤ 364111239299035251^16*20000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5439 20000 364111239299035251 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5439/20000 : ℝ)) (X := (364111239299035251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner0a : (100364111239299035251/100000000000000000000 : ℝ) ≤ (10008431377546821/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (100364111239299035251/100000000000000000000 : ℝ)^16 ≤ (10008431377546821/10000000000000000 : ℝ)^69 := by
      have hnat : (100364111239299035251 : ℕ)^16*10000000000000000^69 ≤ 10008431377546821^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100364111239299035251 100000000000000000000 10008431377546821 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008431377546821/10000000000000000 : ℝ)) (X := (100364111239299035251/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner0b : (50364111239299035251/50000000000000000000 : ℝ) ≤ (2504209823107679/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50364111239299035251/50000000000000000000 : ℝ)^16 ≤ (2504209823107679/2500000000000000 : ℝ)^69 := by
      have hnat : (50364111239299035251 : ℕ)^16*2500000000000000^69 ≤ 2504209823107679^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50364111239299035251 50000000000000000000 2504209823107679 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504209823107679/2500000000000000 : ℝ)) (X := (50364111239299035251/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(227875068833/73500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1681582976779/543900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (5439/20000 : ℝ)) (alpha := (227875068833/73500000000000 : ℝ)) (beta := (1681582976779/543900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5439/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(227875068833/73500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1681582976779/543900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (32209/100000 : ℝ) ^ (69/16 : ℝ) ≤ (188839074015086319/25000000000000000000 : ℝ) := by
    have hpowers : (32209/100000 : ℝ)^69 ≤ (188839074015086319/25000000000000000000 : ℝ)^16 := by
      have hnat : (32209 : ℕ)^69*25000000000000000000^16 ≤ 188839074015086319^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32209 100000 188839074015086319 25000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (32209/100000 : ℝ)) (X := (188839074015086319/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner1a : (25188839074015086319/25000000000000000000 : ℝ) ≤ (10017464920753303/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25188839074015086319/25000000000000000000 : ℝ)^16 ≤ (10017464920753303/10000000000000000 : ℝ)^69 := by
      have hnat : (25188839074015086319 : ℕ)^16*10000000000000000^69 ≤ 10017464920753303^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25188839074015086319 25000000000000000000 10017464920753303 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017464920753303/10000000000000000 : ℝ)) (X := (25188839074015086319/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner1b : (12688839074015086319/12500000000000000000 : ℝ) ≤ (1254353694652841/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (12688839074015086319/12500000000000000000 : ℝ)^16 ≤ (1254353694652841/1250000000000000 : ℝ)^69 := by
      have hnat : (12688839074015086319 : ℕ)^16*1250000000000000^69 ≤ 1254353694652841^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12688839074015086319 12500000000000000000 1254353694652841 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1254353694652841/1250000000000000 : ℝ)) (X := (12688839074015086319/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(17464920753303/3220900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(694585458777/128836000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (32209/100000 : ℝ)) (alpha := (17464920753303/3220900000000000 : ℝ)) (beta := (694585458777/128836000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (32209/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(17464920753303/3220900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(694585458777/128836000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (29753/100000 : ℝ) ^ (69/16 : ℝ) ≤ (268269572117130751/50000000000000000000 : ℝ) := by
    have hpowers : (29753/100000 : ℝ)^69 ≤ (268269572117130751/50000000000000000000 : ℝ)^16 := by
      have hnat : (29753 : ℕ)^69*50000000000000000000^16 ≤ 268269572117130751^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29753 100000 268269572117130751 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29753/100000 : ℝ)) (X := (268269572117130751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner2a : (50268269572117130751/50000000000000000000 : ℝ) ≤ (500620796548919/500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50268269572117130751/50000000000000000000 : ℝ)^16 ≤ (500620796548919/500000000000000 : ℝ)^69 := by
      have hnat : (50268269572117130751 : ℕ)^16*500000000000000^69 ≤ 500620796548919^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50268269572117130751 50000000000000000000 500620796548919 500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500620796548919/500000000000000 : ℝ)) (X := (50268269572117130751/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s5_corner2b : (25268269572117130751/25000000000000000000 : ℝ) ≤ (2004956213962193/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25268269572117130751/25000000000000000000 : ℝ)^16 ≤ (2004956213962193/2000000000000000 : ℝ)^69 := by
      have hnat : (25268269572117130751 : ℕ)^16*2000000000000000^69 ≤ 2004956213962193^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25268269572117130751 25000000000000000000 2004956213962193 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004956213962193/2000000000000000 : ℝ)) (X := (25268269572117130751/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(620796548919/148765000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2473027766517/595060000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (29753/100000 : ℝ)) (alpha := (620796548919/148765000000000 : ℝ)) (beta := (2473027766517/595060000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29753/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(620796548919/148765000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2473027766517/595060000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-51359223/200000000 : ℝ)*X 0 0+(4514765019/10000000000 : ℝ)*X 0 1+(140009599/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((2338731571/5000000000 : ℝ)*X 1 0+(-1295716073/5000000000 : ℝ)*X 1 1+(5427489739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((73227573/156250000 : ℝ)*X 2 0+(3000741969/5000000000 : ℝ)*X 2 1+(-90908041/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((5766314593/10000000000 : ℝ)*X 0 0+(3196274107/10000000000 : ℝ)*X 0 1+(75364509/200000000 : ℝ)*X 0 2+(5766314593/10000000000 : ℝ)*X 1 0+(3196274107/10000000000 : ℝ)*X 1 1+(75364509/200000000 : ℝ)*X 1 2+(5766314593/10000000000 : ℝ)*X 2 0+(3196274107/10000000000 : ℝ)*X 2 1+(75364509/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-2572691639/10000000000 : ℝ)*X 0 0+(4424456301/10000000000 : ℝ)*X 0 1+(2840464003/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((575232227/1250000000 : ℝ)*X 1 0+(-2382206083/10000000000 : ℝ)*X 1 1+(5664167341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((4610963157/10000000000 : ℝ)*X 2 0+(124616077/200000000 : ℝ)*X 2 1+(-99058173/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((5773980961/10000000000 : ℝ)*X 0 0+(3363318949/10000000000 : ℝ)*X 0 1+(719613443/2000000000 : ℝ)*X 0 2+(5773980961/10000000000 : ℝ)*X 1 0+(3363318949/10000000000 : ℝ)*X 1 1+(719613443/2000000000 : ℝ)*X 1 2+(5773980961/10000000000 : ℝ)*X 2 0+(3363318949/10000000000 : ℝ)*X 2 1+(719613443/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-91316651/400000000 : ℝ)*X 0 0+(1157890583/2500000000 : ℝ)*X 0 1+(2856242471/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((141185257/312500000 : ℝ)*X 1 0+(-624826533/2500000000 : ℝ)*X 1 1+(5651622207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((4975062283/10000000000 : ℝ)*X 2 0+(5882659187/10000000000 : ℝ)*X 2 1+(-39936903/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((3059875863/5000000000 : ℝ)*X 0 0+(47167653/156250000 : ℝ)*X 0 1+(3529117261/10000000000 : ℝ)*X 0 2+(3059875863/5000000000 : ℝ)*X 1 0+(47167653/156250000 : ℝ)*X 1 1+(3529117261/10000000000 : ℝ)*X 1 2+(3059875863/5000000000 : ℝ)*X 2 0+(47167653/156250000 : ℝ)*X 2 1+(3529117261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-2301774779/10000000000 : ℝ)*X 0 0+(1169783287/2500000000 : ℝ)*X 0 1+(5653233179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((989419273/2000000000 : ℝ)*X 1 0+(-1163372967/5000000000 : ℝ)*X 1 1+(134413903/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((4503867301/10000000000 : ℝ)*X 2 0+(6190904331/10000000000 : ℝ)*X 2 1+(-893727887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((6170370453/10000000000 : ℝ)*X 0 0+(1507611187/5000000000 : ℝ)*X 0 1+(3472672079/10000000000 : ℝ)*X 0 2+(6170370453/10000000000 : ℝ)*X 1 0+(1507611187/5000000000 : ℝ)*X 1 1+(3472672079/10000000000 : ℝ)*X 1 2+(6170370453/10000000000 : ℝ)*X 2 0+(1507611187/5000000000 : ℝ)*X 2 1+(3472672079/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((4047/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4047/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (496475899629194437813356762243/86871198275050000000000000000000000 : ℝ) := by norm_num
    linear_combination (8147/62500000000 : ℝ)*(base50) + (563816049271/200000000000 : ℝ)*(base59) + (495461/500000000000 : ℝ)*(base60) + (15874304817051/1000000000000 : ℝ)*(major_s5_0) + (15874304817051/1000000000000 : ℝ)*(major_s5_1) + (15874304817051/1000000000000 : ℝ)*(major_s5_2) + (141611583/500000000000 : ℝ)*(sp_s5_0) + (177434333/1000000000000 : ℝ)*(sp_s5_6) + (10889985214437/500000000000 : ℝ)*(sp_s5_7) + (5444995621749/250000000000 : ℝ)*(sp_s5_8) + (680627393581/31250000000 : ℝ)*(sp_s5_9) + (9968176642699/1000000000000 : ℝ)*(sp_s5_13) + (67791261/250000000000 : ℝ)*(sp_s5_15) + (22132181/125000000000 : ℝ)*(sp_s5_23) + (1246044259629/125000000000 : ℝ)*(f.failure) + (544506341301/25000000000 : ℝ)*(f.sum) + (80923892351645721411/95831437700000000000000000000000 : ℝ)*base62 + (77800561681627/595060000000000000000000000 : ℝ)*base64 + (339548771128233/644180000000000000000000000 : ℝ)*base67 + (29866278263831/148765000000000000000000000 : ℝ)*base68 + (181820634965528721/364474250000000000000000000000 : ℝ)*base70 + (45699988939973/181300000000000000000000000 : ℝ)*base73 + (317407674730547/3220900000000000000000000000 : ℝ)*base74 + (6530353955661/24500000000000000000000000 : ℝ)*base77 + (243068609740550743/1459872925000000000000000000000 : ℝ)*base79 + (1863/12500000000000000 : ℝ)*base87 + (1863/12500000000000000 : ℝ)*base89 + (1863/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20273/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20273/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9678044381561296070652097/729936462500000000000000000000 : ℝ) := by norm_num
    linear_combination (532723/250000000000 : ℝ)*(base39) + (98453394289/1000000000000 : ℝ)*(base40) + (515213592391/200000000000 : ℝ)*(base59) + (16268236368557/1000000000000 : ℝ)*(major_s5_0) + (16268236368557/1000000000000 : ℝ)*(major_s5_1) + (16268236368557/1000000000000 : ℝ)*(major_s5_2) + (115925637/200000000000 : ℝ)*(sp_s5_1) + (31693989/40000000000 : ℝ)*(sp_s5_2) + (205855841/1000000000000 : ℝ)*(sp_s5_6) + (847890133/1000000000000 : ℝ)*(sp_s5_7) + (22319894938967/1000000000000 : ℝ)*(sp_s5_14) + (4464032640183/200000000000 : ℝ)*(sp_s5_15) + (35711920767/1600000000 : ℝ)*(sp_s5_16) + (10215519632587/1000000000000 : ℝ)*(sp_s5_20) + (2553931372107/250000000000 : ℝ)*(f.failure) + (223207428291/10000000000 : ℝ)*(f.sum) + (11637375972129571007/95831437700000000000000000000000 : ℝ)*base62 + (284552874438223/595060000000000000000000000 : ℝ)*base65 + (242295085937703/644180000000000000000000000 : ℝ)*base67 + (101066877010701/297530000000000000000000000 : ℝ)*base69 + (142594145191809733/546711375000000000000000000000 : ℝ)*base70 + (293602519976873/543900000000000000000000000 : ℝ)*base73 + (1124931000685771/3220900000000000000000000000 : ℝ)*base75 + (9290575298881/73500000000000000000000000 : ℝ)*base77 + (333307468283028233/4379618775000000000000000000000 : ℝ)*base79 + (1571/25000000000000000 : ℝ)*base86 + (1571/25000000000000000 : ℝ)*base88 + (1571/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18811/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18811/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (854906981996655127185800532321/86871198275050000000000000000000000 : ℝ) := by norm_num
    linear_combination (530847/250000000000 : ℝ)*(base39) + (143654818449/250000000000 : ℝ)*(base40) + (427527/250000000000 : ℝ)*(base50) + (2650678343749/1000000000000 : ℝ)*(base59) + (3222622162237/200000000000 : ℝ)*(major_s5_0) + (3222622162237/200000000000 : ℝ)*(major_s5_1) + (3222622162237/200000000000 : ℝ)*(major_s5_2) + (91610481/125000000000 : ℝ)*(sp_s5_0) + (315197181/500000000000 : ℝ)*(sp_s5_1) + (28109589/200000000000 : ℝ)*(sp_s5_2) + (22107171887923/1000000000000 : ℝ)*(sp_s5_21) + (2210727437741/100000000000 : ℝ)*(sp_s5_22) + (11053882111913/500000000000 : ℝ)*(sp_s5_23) + (10118313570231/1000000000000 : ℝ)*(sp_s5_27) + (10118313570231/1000000000000 : ℝ)*(f.failure) + (22107904771771/1000000000000 : ℝ)*(f.sum) + (843335415551201019/19166287540000000000000000000000 : ℝ)*base63 + (13925068892739/119012000000000000000000000 : ℝ)*base65 + (314784719058503/644180000000000000000000000 : ℝ)*base66 + (225843409531811/297530000000000000000000000 : ℝ)*base68 + (147114262675039559/218684550000000000000000000000 : ℝ)*base71 + (104592085264403/108780000000000000000000000 : ℝ)*base72 + (30328179967649/644180000000000000000000000 : ℝ)*base75 + (2820691330721/14700000000000000000000000 : ℝ)*base77 + (674528191384838267/875923755000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (76057/100000000000000000 : ℝ)*base87 + (76057/100000000000000000 : ℝ)*base89 + (76057/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((5439/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5439/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32209/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32209/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29753/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4047/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4047/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20273/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20273/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18811/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(18811/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309061_s5 p hpa hpb X hX hprev4

#print axioms solution
