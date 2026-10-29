-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:18:44.371172+00:00
-- url     : https://prove2.me/submissions/797692a5-3528-4610-b7b9-b9607f4e90e3

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
theorem collision_support_c312053_s2_s2_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-535743091/2500000000 : ℝ)*x 0 + (2574983609/5000000000 : ℝ)*x 1 + (5206200149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535743091/2500000000 : ℝ)^73 ≤ (13906945350141/100000000000000 : ℝ)^57 := by
    have hnat : (535743091 : ℕ)^73*100000000000000^57 ≤ 13906945350141^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535743091 2500000000 13906945350141 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2574983609/5000000000 : ℝ)^73 ≤ (42747180219667/100000000000000 : ℝ)^57 := by
    have hnat : (2574983609 : ℕ)^73*100000000000000^57 ≤ 42747180219667^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574983609 5000000000 42747180219667 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206200149/10000000000 : ℝ)^73 ≤ (5418234302177/12500000000000 : ℝ)^57 := by
    have hnat : (5206200149 : ℕ)^73*12500000000000^57 ≤ 5418234302177^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206200149 10000000000 5418234302177 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535743091/2500000000 : ℝ), (2574983609/5000000000 : ℝ), (5206200149/10000000000 : ℝ)] ![(13906945350141/100000000000000 : ℝ), (42747180219667/100000000000000 : ℝ), (5418234302177/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535743091/2500000000 : ℝ)|^73 ≤ (13906945350141/100000000000000 : ℝ)^57
        have hw : |(-535743091/2500000000 : ℝ)|=(535743091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2574983609/5000000000 : ℝ)|^73 ≤ (42747180219667/100000000000000 : ℝ)^57
        have hw : |(2574983609/5000000000 : ℝ)|=(2574983609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206200149/10000000000 : ℝ)|^73 ≤ (5418234302177/12500000000000 : ℝ)^57
        have hw : |(5206200149/10000000000 : ℝ)|=(5206200149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (282249777/625000000 : ℝ)*x 0 + (-793509909/5000000000 : ℝ)*x 1 + (3108534037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (282249777/625000000 : ℝ)^73 ≤ (9031966661169/25000000000000 : ℝ)^57 := by
    have hnat : (282249777 : ℕ)^73*25000000000000^57 ≤ 9031966661169^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282249777 625000000 9031966661169 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (793509909/5000000000 : ℝ)^73 ≤ (1893278089409/20000000000000 : ℝ)^57 := by
    have hnat : (793509909 : ℕ)^73*20000000000000^57 ≤ 1893278089409^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793509909 5000000000 1893278089409 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3108534037/5000000000 : ℝ)^73 ≤ (10881148579949/20000000000000 : ℝ)^57 := by
    have hnat : (3108534037 : ℕ)^73*20000000000000^57 ≤ 10881148579949^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3108534037 5000000000 10881148579949 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(282249777/625000000 : ℝ), (-793509909/5000000000 : ℝ), (3108534037/5000000000 : ℝ)] ![(9031966661169/25000000000000 : ℝ), (1893278089409/20000000000000 : ℝ), (10881148579949/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(282249777/625000000 : ℝ)|^73 ≤ (9031966661169/25000000000000 : ℝ)^57
        have hw : |(282249777/625000000 : ℝ)|=(282249777/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-793509909/5000000000 : ℝ)|^73 ≤ (1893278089409/20000000000000 : ℝ)^57
        have hw : |(-793509909/5000000000 : ℝ)|=(793509909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3108534037/5000000000 : ℝ)|^73 ≤ (10881148579949/20000000000000 : ℝ)^57
        have hw : |(3108534037/5000000000 : ℝ)|=(3108534037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1134635537/2500000000 : ℝ)*x 0 + (6214717347/10000000000 : ℝ)*x 1 + (-780072617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134635537/2500000000 : ℝ)^73 ≤ (4544877792571/12500000000000 : ℝ)^57 := by
    have hnat : (1134635537 : ℕ)^73*12500000000000^57 ≤ 4544877792571^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134635537 2500000000 4544877792571 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6214717347/10000000000 : ℝ)^73 ≤ (54379398623459/100000000000000 : ℝ)^57 := by
    have hnat : (6214717347 : ℕ)^73*100000000000000^57 ≤ 54379398623459^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6214717347 10000000000 54379398623459 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (780072617/5000000000 : ℝ)^73 ≤ (370463161063/4000000000000 : ℝ)^57 := by
    have hnat : (780072617 : ℕ)^73*4000000000000^57 ≤ 370463161063^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      780072617 5000000000 370463161063 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1134635537/2500000000 : ℝ), (6214717347/10000000000 : ℝ), (-780072617/5000000000 : ℝ)] ![(4544877792571/12500000000000 : ℝ), (54379398623459/100000000000000 : ℝ), (370463161063/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1134635537/2500000000 : ℝ)|^73 ≤ (4544877792571/12500000000000 : ℝ)^57
        have hw : |(1134635537/2500000000 : ℝ)|=(1134635537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6214717347/10000000000 : ℝ)|^73 ≤ (54379398623459/100000000000000 : ℝ)^57
        have hw : |(6214717347/10000000000 : ℝ)|=(6214717347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-780072617/5000000000 : ℝ)|^73 ≤ (370463161063/4000000000000 : ℝ)^57
        have hw : |(-780072617/5000000000 : ℝ)|=(780072617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3452926589/5000000000 : ℝ)*x 0 + (2758024383/10000000000 : ℝ)*x 1 + (1341524567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3452926589/5000000000 : ℝ)^73 ≤ (62242261846693/100000000000000 : ℝ)^57 := by
    have hnat : (3452926589 : ℕ)^73*100000000000000^57 ≤ 62242261846693^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3452926589 5000000000 62242261846693 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2758024383/10000000000 : ℝ)^73 ≤ (19212018978633/100000000000000 : ℝ)^57 := by
    have hnat : (2758024383 : ℕ)^73*100000000000000^57 ≤ 19212018978633^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758024383 10000000000 19212018978633 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1341524567/5000000000 : ℝ)^73 ≤ (4636429788089/25000000000000 : ℝ)^57 := by
    have hnat : (1341524567 : ℕ)^73*25000000000000^57 ≤ 4636429788089^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341524567 5000000000 4636429788089 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3452926589/5000000000 : ℝ), (2758024383/10000000000 : ℝ), (1341524567/5000000000 : ℝ)] ![(62242261846693/100000000000000 : ℝ), (19212018978633/100000000000000 : ℝ), (4636429788089/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3452926589/5000000000 : ℝ)|^73 ≤ (62242261846693/100000000000000 : ℝ)^57
        have hw : |(3452926589/5000000000 : ℝ)|=(3452926589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2758024383/10000000000 : ℝ)|^73 ≤ (19212018978633/100000000000000 : ℝ)^57
        have hw : |(2758024383/10000000000 : ℝ)|=(2758024383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1341524567/5000000000 : ℝ)|^73 ≤ (4636429788089/25000000000000 : ℝ)^57
        have hw : |(1341524567/5000000000 : ℝ)|=(1341524567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-405309533/2000000000 : ℝ)*x 0 + (2058363297/5000000000 : ℝ)*x 1 + (1566710589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405309533/2000000000 : ℝ)^73 ≤ (6473397134683/50000000000000 : ℝ)^57 := by
    have hnat : (405309533 : ℕ)^73*50000000000000^57 ≤ 6473397134683^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405309533 2000000000 6473397134683 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2058363297/5000000000 : ℝ)^73 ≤ (32088994007633/100000000000000 : ℝ)^57 := by
    have hnat : (2058363297 : ℕ)^73*100000000000000^57 ≤ 32088994007633^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058363297 5000000000 32088994007633 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1566710589/2500000000 : ℝ)^73 ≤ (5496421170957/10000000000000 : ℝ)^57 := by
    have hnat : (1566710589 : ℕ)^73*10000000000000^57 ≤ 5496421170957^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566710589 2500000000 5496421170957 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405309533/2000000000 : ℝ), (2058363297/5000000000 : ℝ), (1566710589/2500000000 : ℝ)] ![(6473397134683/50000000000000 : ℝ), (32088994007633/100000000000000 : ℝ), (5496421170957/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405309533/2000000000 : ℝ)|^73 ≤ (6473397134683/50000000000000 : ℝ)^57
        have hw : |(-405309533/2000000000 : ℝ)|=(405309533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2058363297/5000000000 : ℝ)|^73 ≤ (32088994007633/100000000000000 : ℝ)^57
        have hw : |(2058363297/5000000000 : ℝ)|=(2058363297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1566710589/2500000000 : ℝ)|^73 ≤ (5496421170957/10000000000000 : ℝ)^57
        have hw : |(1566710589/2500000000 : ℝ)|=(1566710589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1019557349/2500000000 : ℝ)*x 0 + (-43806939/400000000 : ℝ)*x 1 + (6920226107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019557349/2500000000 : ℝ)^73 ≤ (6341037993703/20000000000000 : ℝ)^57 := by
    have hnat : (1019557349 : ℕ)^73*20000000000000^57 ≤ 6341037993703^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019557349 2500000000 6341037993703 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43806939/400000000 : ℝ)^73 ≤ (2943297019249/50000000000000 : ℝ)^57 := by
    have hnat : (43806939 : ℕ)^73*50000000000000^57 ≤ 2943297019249^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43806939 400000000 2943297019249 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6920226107/10000000000 : ℝ)^73 ≤ (2496328639439/4000000000000 : ℝ)^57 := by
    have hnat : (6920226107 : ℕ)^73*4000000000000^57 ≤ 2496328639439^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6920226107 10000000000 2496328639439 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019557349/2500000000 : ℝ), (-43806939/400000000 : ℝ), (6920226107/10000000000 : ℝ)] ![(6341037993703/20000000000000 : ℝ), (2943297019249/50000000000000 : ℝ), (2496328639439/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019557349/2500000000 : ℝ)|^73 ≤ (6341037993703/20000000000000 : ℝ)^57
        have hw : |(1019557349/2500000000 : ℝ)|=(1019557349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-43806939/400000000 : ℝ)|^73 ≤ (2943297019249/50000000000000 : ℝ)^57
        have hw : |(-43806939/400000000 : ℝ)|=(43806939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6920226107/10000000000 : ℝ)|^73 ≤ (2496328639439/4000000000000 : ℝ)^57
        have hw : |(6920226107/10000000000 : ℝ)|=(6920226107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2050514467/5000000000 : ℝ)*x 0 + (7185250727/10000000000 : ℝ)*x 1 + (-115099099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050514467/5000000000 : ℝ)^73 ≤ (31932371454189/100000000000000 : ℝ)^57 := by
    have hnat : (2050514467 : ℕ)^73*100000000000000^57 ≤ 31932371454189^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050514467 5000000000 31932371454189 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7185250727/10000000000 : ℝ)^73 ≤ (16371366579171/25000000000000 : ℝ)^57 := by
    have hnat : (7185250727 : ℕ)^73*25000000000000^57 ≤ 16371366579171^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7185250727 10000000000 16371366579171 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115099099/2000000000 : ℝ)^73 ≤ (2582162217671/100000000000000 : ℝ)^57 := by
    have hnat : (115099099 : ℕ)^73*100000000000000^57 ≤ 2582162217671^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115099099 2000000000 2582162217671 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2050514467/5000000000 : ℝ), (7185250727/10000000000 : ℝ), (-115099099/2000000000 : ℝ)] ![(31932371454189/100000000000000 : ℝ), (16371366579171/25000000000000 : ℝ), (2582162217671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2050514467/5000000000 : ℝ)|^73 ≤ (31932371454189/100000000000000 : ℝ)^57
        have hw : |(2050514467/5000000000 : ℝ)|=(2050514467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7185250727/10000000000 : ℝ)|^73 ≤ (16371366579171/25000000000000 : ℝ)^57
        have hw : |(7185250727/10000000000 : ℝ)|=(7185250727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-115099099/2000000000 : ℝ)|^73 ≤ (2582162217671/100000000000000 : ℝ)^57
        have hw : |(-115099099/2000000000 : ℝ)|=(115099099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6577344713/10000000000 : ℝ)*x 0 + (4394836893/10000000000 : ℝ)*x 1 + (1202148041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6577344713/10000000000 : ℝ)^73 ≤ (58475923414697/100000000000000 : ℝ)^57 := by
    have hnat : (6577344713 : ℕ)^73*100000000000000^57 ≤ 58475923414697^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6577344713 10000000000 58475923414697 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394836893/10000000000 : ℝ)^73 ≤ (34891221059447/100000000000000 : ℝ)^57 := by
    have hnat : (4394836893 : ℕ)^73*100000000000000^57 ≤ 34891221059447^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394836893 10000000000 34891221059447 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1202148041/10000000000 : ℝ)^73 ≤ (26531422017/400000000000 : ℝ)^57 := by
    have hnat : (1202148041 : ℕ)^73*400000000000^57 ≤ 26531422017^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202148041 10000000000 26531422017 400000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6577344713/10000000000 : ℝ), (4394836893/10000000000 : ℝ), (1202148041/10000000000 : ℝ)] ![(58475923414697/100000000000000 : ℝ), (34891221059447/100000000000000 : ℝ), (26531422017/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6577344713/10000000000 : ℝ)|^73 ≤ (58475923414697/100000000000000 : ℝ)^57
        have hw : |(6577344713/10000000000 : ℝ)|=(6577344713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394836893/10000000000 : ℝ)|^73 ≤ (34891221059447/100000000000000 : ℝ)^57
        have hw : |(4394836893/10000000000 : ℝ)|=(4394836893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1202148041/10000000000 : ℝ)|^73 ≤ (26531422017/400000000000 : ℝ)^57
        have hw : |(1202148041/10000000000 : ℝ)|=(1202148041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-25237279/250000000 : ℝ)*x 0 + (305934613/625000000 : ℝ)*x 1 + (311903707/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (25237279/250000000 : ℝ)^73 ≤ (5303375164073/100000000000000 : ℝ)^57 := by
    have hnat : (25237279 : ℕ)^73*100000000000000^57 ≤ 5303375164073^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25237279 250000000 5303375164073 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (305934613/625000000 : ℝ)^73 ≤ (20027672882253/50000000000000 : ℝ)^57 := by
    have hnat : (305934613 : ℕ)^73*50000000000000^57 ≤ 20027672882253^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305934613 625000000 20027672882253 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (311903707/500000000 : ℝ)^73 ≤ (54641279057057/100000000000000 : ℝ)^57 := by
    have hnat : (311903707 : ℕ)^73*100000000000000^57 ≤ 54641279057057^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311903707 500000000 54641279057057 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-25237279/250000000 : ℝ), (305934613/625000000 : ℝ), (311903707/500000000 : ℝ)] ![(5303375164073/100000000000000 : ℝ), (20027672882253/50000000000000 : ℝ), (54641279057057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-25237279/250000000 : ℝ)|^73 ≤ (5303375164073/100000000000000 : ℝ)^57
        have hw : |(-25237279/250000000 : ℝ)|=(25237279/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(305934613/625000000 : ℝ)|^73 ≤ (20027672882253/50000000000000 : ℝ)^57
        have hw : |(305934613/625000000 : ℝ)|=(305934613/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(311903707/500000000 : ℝ)|^73 ≤ (54641279057057/100000000000000 : ℝ)^57
        have hw : |(311903707/500000000 : ℝ)|=(311903707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (811254151/2000000000 : ℝ)*x 0 + (-1155684253/10000000000 : ℝ)*x 1 + (3451396837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811254151/2000000000 : ℝ)^73 ≤ (31486724184893/100000000000000 : ℝ)^57 := by
    have hnat : (811254151 : ℕ)^73*100000000000000^57 ≤ 31486724184893^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811254151 2000000000 31486724184893 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155684253/10000000000 : ℝ)^73 ≤ (788290924967/12500000000000 : ℝ)^57 := by
    have hnat : (1155684253 : ℕ)^73*12500000000000^57 ≤ 788290924967^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155684253 10000000000 788290924967 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3451396837/5000000000 : ℝ)^73 ≤ (62206948404941/100000000000000 : ℝ)^57 := by
    have hnat : (3451396837 : ℕ)^73*100000000000000^57 ≤ 62206948404941^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3451396837 5000000000 62206948404941 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(811254151/2000000000 : ℝ), (-1155684253/10000000000 : ℝ), (3451396837/5000000000 : ℝ)] ![(31486724184893/100000000000000 : ℝ), (788290924967/12500000000000 : ℝ), (62206948404941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(811254151/2000000000 : ℝ)|^73 ≤ (31486724184893/100000000000000 : ℝ)^57
        have hw : |(811254151/2000000000 : ℝ)|=(811254151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1155684253/10000000000 : ℝ)|^73 ≤ (788290924967/12500000000000 : ℝ)^57
        have hw : |(-1155684253/10000000000 : ℝ)|=(1155684253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3451396837/5000000000 : ℝ)|^73 ≤ (62206948404941/100000000000000 : ℝ)^57
        have hw : |(3451396837/5000000000 : ℝ)|=(3451396837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2873531401/5000000000 : ℝ)*x 0 + (5642914101/10000000000 : ℝ)*x 1 + (-151065833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2873531401/5000000000 : ℝ)^73 ≤ (12298779232267/25000000000000 : ℝ)^57 := by
    have hnat : (2873531401 : ℕ)^73*25000000000000^57 ≤ 12298779232267^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2873531401 5000000000 12298779232267 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5642914101/10000000000 : ℝ)^73 ≤ (24028132773151/50000000000000 : ℝ)^57 := by
    have hnat : (5642914101 : ℕ)^73*50000000000000^57 ≤ 24028132773151^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5642914101 10000000000 24028132773151 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151065833/2500000000 : ℝ)^73 ≤ (1374308754927/50000000000000 : ℝ)^57 := by
    have hnat : (151065833 : ℕ)^73*50000000000000^57 ≤ 1374308754927^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151065833 2500000000 1374308754927 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2873531401/5000000000 : ℝ), (5642914101/10000000000 : ℝ), (-151065833/2500000000 : ℝ)] ![(12298779232267/25000000000000 : ℝ), (24028132773151/50000000000000 : ℝ), (1374308754927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2873531401/5000000000 : ℝ)|^73 ≤ (12298779232267/25000000000000 : ℝ)^57
        have hw : |(2873531401/5000000000 : ℝ)|=(2873531401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5642914101/10000000000 : ℝ)|^73 ≤ (24028132773151/50000000000000 : ℝ)^57
        have hw : |(5642914101/10000000000 : ℝ)|=(5642914101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151065833/2500000000 : ℝ)|^73 ≤ (1374308754927/50000000000000 : ℝ)^57
        have hw : |(-151065833/2500000000 : ℝ)|=(151065833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1619880859/2000000000 : ℝ)*x 0 + (1238234979/5000000000 : ℝ)*x 1 + (1242909847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1619880859/2000000000 : ℝ)^73 ≤ (76340622403087/100000000000000 : ℝ)^57 := by
    have hnat : (1619880859 : ℕ)^73*100000000000000^57 ≤ 76340622403087^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619880859 2000000000 76340622403087 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1238234979/5000000000 : ℝ)^73 ≤ (16737128155959/100000000000000 : ℝ)^57 := by
    have hnat : (1238234979 : ℕ)^73*100000000000000^57 ≤ 16737128155959^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1238234979 5000000000 16737128155959 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1242909847/10000000000 : ℝ)^73 ≤ (3461124711993/50000000000000 : ℝ)^57 := by
    have hnat : (1242909847 : ℕ)^73*50000000000000^57 ≤ 3461124711993^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242909847 10000000000 3461124711993 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1619880859/2000000000 : ℝ), (1238234979/5000000000 : ℝ), (1242909847/10000000000 : ℝ)] ![(76340622403087/100000000000000 : ℝ), (16737128155959/100000000000000 : ℝ), (3461124711993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1619880859/2000000000 : ℝ)|^73 ≤ (76340622403087/100000000000000 : ℝ)^57
        have hw : |(1619880859/2000000000 : ℝ)|=(1619880859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1238234979/5000000000 : ℝ)|^73 ≤ (16737128155959/100000000000000 : ℝ)^57
        have hw : |(1238234979/5000000000 : ℝ)|=(1238234979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1242909847/10000000000 : ℝ)|^73 ≤ (3461124711993/50000000000000 : ℝ)^57
        have hw : |(1242909847/10000000000 : ℝ)|=(1242909847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1005537511/10000000000 : ℝ)*x 0 + (1465955101/2500000000 : ℝ)*x 1 + (2645141461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1005537511/10000000000 : ℝ)^73 ≤ (5276788923423/100000000000000 : ℝ)^57 := by
    have hnat : (1005537511 : ℕ)^73*100000000000000^57 ≤ 5276788923423^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005537511 10000000000 5276788923423 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1465955101/2500000000 : ℝ)^73 ≤ (2019149874583/4000000000000 : ℝ)^57 := by
    have hnat : (1465955101 : ℕ)^73*4000000000000^57 ≤ 2019149874583^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1465955101 2500000000 2019149874583 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2645141461/5000000000 : ℝ)^73 ≤ (4424446420601/10000000000000 : ℝ)^57 := by
    have hnat : (2645141461 : ℕ)^73*10000000000000^57 ≤ 4424446420601^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645141461 5000000000 4424446420601 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1005537511/10000000000 : ℝ), (1465955101/2500000000 : ℝ), (2645141461/5000000000 : ℝ)] ![(5276788923423/100000000000000 : ℝ), (2019149874583/4000000000000 : ℝ), (4424446420601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1005537511/10000000000 : ℝ)|^73 ≤ (5276788923423/100000000000000 : ℝ)^57
        have hw : |(-1005537511/10000000000 : ℝ)|=(1005537511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1465955101/2500000000 : ℝ)|^73 ≤ (2019149874583/4000000000000 : ℝ)^57
        have hw : |(1465955101/2500000000 : ℝ)|=(1465955101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2645141461/5000000000 : ℝ)|^73 ≤ (4424446420601/10000000000000 : ℝ)^57
        have hw : |(2645141461/5000000000 : ℝ)|=(2645141461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2864108203/5000000000 : ℝ)*x 0 + (-129006627/2000000000 : ℝ)*x 1 + (176245921/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2864108203/5000000000 : ℝ)^73 ≤ (4898860160571/10000000000000 : ℝ)^57 := by
    have hnat : (2864108203 : ℕ)^73*10000000000000^57 ≤ 4898860160571^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2864108203 5000000000 4898860160571 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129006627/2000000000 : ℝ)^73 ≤ (1494168632453/50000000000000 : ℝ)^57 := by
    have hnat : (129006627 : ℕ)^73*50000000000000^57 ≤ 1494168632453^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129006627 2000000000 1494168632453 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (176245921/312500000 : ℝ)^73 ≤ (48023061113147/100000000000000 : ℝ)^57 := by
    have hnat : (176245921 : ℕ)^73*100000000000000^57 ≤ 48023061113147^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      176245921 312500000 48023061113147 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2864108203/5000000000 : ℝ), (-129006627/2000000000 : ℝ), (176245921/312500000 : ℝ)] ![(4898860160571/10000000000000 : ℝ), (1494168632453/50000000000000 : ℝ), (48023061113147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2864108203/5000000000 : ℝ)|^73 ≤ (4898860160571/10000000000000 : ℝ)^57
        have hw : |(2864108203/5000000000 : ℝ)|=(2864108203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129006627/2000000000 : ℝ)|^73 ≤ (1494168632453/50000000000000 : ℝ)^57
        have hw : |(-129006627/2000000000 : ℝ)|=(129006627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(176245921/312500000 : ℝ)|^73 ≤ (48023061113147/100000000000000 : ℝ)^57
        have hw : |(176245921/312500000 : ℝ)|=(176245921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3981542693/10000000000 : ℝ)*x 0 + (7013839391/10000000000 : ℝ)*x 1 + (-1077146159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3981542693/10000000000 : ℝ)^73 ≤ (30745750369589/100000000000000 : ℝ)^57 := by
    have hnat : (3981542693 : ℕ)^73*100000000000000^57 ≤ 30745750369589^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3981542693 10000000000 30745750369589 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7013839391/10000000000 : ℝ)^73 ≤ (12698292890181/20000000000000 : ℝ)^57 := by
    have hnat : (7013839391 : ℕ)^73*20000000000000^57 ≤ 12698292890181^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7013839391 10000000000 12698292890181 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077146159/10000000000 : ℝ)^73 ≤ (5762785171699/100000000000000 : ℝ)^57 := by
    have hnat : (1077146159 : ℕ)^73*100000000000000^57 ≤ 5762785171699^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077146159 10000000000 5762785171699 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3981542693/10000000000 : ℝ), (7013839391/10000000000 : ℝ), (-1077146159/10000000000 : ℝ)] ![(30745750369589/100000000000000 : ℝ), (12698292890181/20000000000000 : ℝ), (5762785171699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3981542693/10000000000 : ℝ)|^73 ≤ (30745750369589/100000000000000 : ℝ)^57
        have hw : |(3981542693/10000000000 : ℝ)|=(3981542693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7013839391/10000000000 : ℝ)|^73 ≤ (12698292890181/20000000000000 : ℝ)^57
        have hw : |(7013839391/10000000000 : ℝ)|=(7013839391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1077146159/10000000000 : ℝ)|^73 ≤ (5762785171699/100000000000000 : ℝ)^57
        have hw : |(-1077146159/10000000000 : ℝ)|=(1077146159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312053_s2_s2_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2081862027/2500000000 : ℝ)*x 0 + (1763026029/10000000000 : ℝ)*x 1 + (832390681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081862027/2500000000 : ℝ)^73 ≤ (9888023931023/12500000000000 : ℝ)^57 := by
    have hnat : (2081862027 : ℕ)^73*12500000000000^57 ≤ 9888023931023^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081862027 2500000000 9888023931023 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1763026029/10000000000 : ℝ)^73 ≤ (10831340922741/100000000000000 : ℝ)^57 := by
    have hnat : (1763026029 : ℕ)^73*100000000000000^57 ≤ 10831340922741^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763026029 10000000000 10831340922741 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832390681/5000000000 : ℝ)^73 ≤ (10064467610071/100000000000000 : ℝ)^57 := by
    have hnat : (832390681 : ℕ)^73*100000000000000^57 ≤ 10064467610071^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832390681 5000000000 10064467610071 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2081862027/2500000000 : ℝ), (1763026029/10000000000 : ℝ), (832390681/5000000000 : ℝ)] ![(9888023931023/12500000000000 : ℝ), (10831340922741/100000000000000 : ℝ), (10064467610071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2081862027/2500000000 : ℝ)|^73 ≤ (9888023931023/12500000000000 : ℝ)^57
        have hw : |(2081862027/2500000000 : ℝ)|=(2081862027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1763026029/10000000000 : ℝ)|^73 ≤ (10831340922741/100000000000000 : ℝ)^57
        have hw : |(1763026029/10000000000 : ℝ)|=(1763026029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(832390681/5000000000 : ℝ)|^73 ≤ (10064467610071/100000000000000 : ℝ)^57
        have hw : |(832390681/5000000000 : ℝ)|=(832390681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312053_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((16139/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16139/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13803/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13803/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8473/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8473/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((39293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9137/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9137/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44009/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (16139/25000 : ℝ) ^ (9/2 : ℝ) ≤ (6977257681455416207/50000000000000000000 : ℝ) := by
    have hpowers : (16139/25000 : ℝ)^9 ≤ (6977257681455416207/50000000000000000000 : ℝ)^2 := by
      have hnat : (16139 : ℕ)^9*50000000000000000000^2 ≤ 6977257681455416207^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16139 25000 6977257681455416207 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16139/25000 : ℝ)) (X := (6977257681455416207/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0a : (56977257681455416207/50000000000000000000 : ℝ) ≤ (10294541496211321/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (56977257681455416207/50000000000000000000 : ℝ)^2 ≤ (10294541496211321/10000000000000000 : ℝ)^9 := by
      have hnat : (56977257681455416207 : ℕ)^2*10000000000000000^9 ≤ 10294541496211321^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56977257681455416207 50000000000000000000 10294541496211321 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10294541496211321/10000000000000000 : ℝ)) (X := (56977257681455416207/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0b : (31977257681455416207/25000000000000000000 : ℝ) ≤ (10562234953138423/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (31977257681455416207/25000000000000000000 : ℝ)^2 ≤ (10562234953138423/10000000000000000 : ℝ)^9 := by
      have hnat : (31977257681455416207 : ℕ)^2*10000000000000000^9 ≤ 10562234953138423^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31977257681455416207 25000000000000000000 10562234953138423 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10562234953138423/10000000000000000 : ℝ)) (X := (31977257681455416207/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(294541496211321/6455600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(133846728463551/3227800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (16139/25000 : ℝ)) (alpha := (294541496211321/6455600000000000 : ℝ)) (beta := (133846728463551/3227800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16139/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(294541496211321/6455600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(133846728463551/3227800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (13803/20000 : ℝ) ^ (9/2 : ℝ) ≤ (4711787808398091177/25000000000000000000 : ℝ) := by
    have hpowers : (13803/20000 : ℝ)^9 ≤ (4711787808398091177/25000000000000000000 : ℝ)^2 := by
      have hnat : (13803 : ℕ)^9*25000000000000000000^2 ≤ 4711787808398091177^2*20000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13803 20000 4711787808398091177 25000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13803/20000 : ℝ)) (X := (4711787808398091177/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1a : (29711787808398091177/25000000000000000000 : ℝ) ≤ (2078232672174589/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (29711787808398091177/25000000000000000000 : ℝ)^2 ≤ (2078232672174589/2000000000000000 : ℝ)^9 := by
      have hnat : (29711787808398091177 : ℕ)^2*2000000000000000^9 ≤ 2078232672174589^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29711787808398091177 25000000000000000000 2078232672174589 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2078232672174589/2000000000000000 : ℝ)) (X := (29711787808398091177/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1b : (17211787808398091177/12500000000000000000 : ℝ) ≤ (10736685097740269/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (17211787808398091177/12500000000000000000 : ℝ)^2 ≤ (10736685097740269/10000000000000000 : ℝ)^9 := by
      have hnat : (17211787808398091177 : ℕ)^2*10000000000000000^9 ≤ 10736685097740269^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17211787808398091177 12500000000000000000 10736685097740269 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10736685097740269/10000000000000000 : ℝ)) (X := (17211787808398091177/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(78232672174589/1380300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(28793478072277/575125000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (13803/20000 : ℝ)) (alpha := (78232672174589/1380300000000000 : ℝ)) (beta := (28793478072277/575125000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13803/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(78232672174589/1380300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(28793478072277/575125000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (8473/12500 : ℝ) ^ (9/2 : ℝ) ≤ (17380904378571093237/100000000000000000000 : ℝ) := by
    have hpowers : (8473/12500 : ℝ)^9 ≤ (17380904378571093237/100000000000000000000 : ℝ)^2 := by
      have hnat : (8473 : ℕ)^9*100000000000000000000^2 ≤ 17380904378571093237^2*12500^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8473 12500 17380904378571093237 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8473/12500 : ℝ)) (X := (17380904378571093237/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2a : (117380904378571093237/100000000000000000000 : ℝ) ≤ (5181268572185687/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (117380904378571093237/100000000000000000000 : ℝ)^2 ≤ (5181268572185687/5000000000000000 : ℝ)^9 := by
      have hnat : (117380904378571093237 : ℕ)^2*5000000000000000^9 ≤ 5181268572185687^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117380904378571093237 100000000000000000000 5181268572185687 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5181268572185687/5000000000000000 : ℝ)) (X := (117380904378571093237/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2b : (67380904378571093237/50000000000000000000 : ℝ) ≤ (2671361348049763/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (67380904378571093237/50000000000000000000 : ℝ)^2 ≤ (2671361348049763/2500000000000000 : ℝ)^9 := by
      have hnat : (67380904378571093237 : ℕ)^2*2500000000000000^9 ≤ 2671361348049763^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67380904378571093237 50000000000000000000 2671361348049763 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2671361348049763/2500000000000000 : ℝ)) (X := (67380904378571093237/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(181268572185687/3389200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(161454123913839/3389200000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (8473/12500 : ℝ)) (alpha := (181268572185687/3389200000000000 : ℝ)) (beta := (161454123913839/3389200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8473/12500 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(181268572185687/3389200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(161454123913839/3389200000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-535743091/2500000000 : ℝ)*X 0 0+(2574983609/5000000000 : ℝ)*X 0 1+(5206200149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((282249777/625000000 : ℝ)*X 1 0+(-793509909/5000000000 : ℝ)*X 1 1+(3108534037/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1134635537/2500000000 : ℝ)*X 2 0+(6214717347/10000000000 : ℝ)*X 2 1+(-780072617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3452926589/5000000000 : ℝ)*X 0 0+(2758024383/10000000000 : ℝ)*X 0 1+(1341524567/5000000000 : ℝ)*X 0 2+(3452926589/5000000000 : ℝ)*X 1 0+(2758024383/10000000000 : ℝ)*X 1 1+(1341524567/5000000000 : ℝ)*X 1 2+(3452926589/5000000000 : ℝ)*X 2 0+(2758024383/10000000000 : ℝ)*X 2 1+(1341524567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-405309533/2000000000 : ℝ)*X 0 0+(2058363297/5000000000 : ℝ)*X 0 1+(1566710589/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1019557349/2500000000 : ℝ)*X 1 0+(-43806939/400000000 : ℝ)*X 1 1+(6920226107/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2050514467/5000000000 : ℝ)*X 2 0+(7185250727/10000000000 : ℝ)*X 2 1+(-115099099/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((6577344713/10000000000 : ℝ)*X 0 0+(4394836893/10000000000 : ℝ)*X 0 1+(1202148041/10000000000 : ℝ)*X 0 2+(6577344713/10000000000 : ℝ)*X 1 0+(4394836893/10000000000 : ℝ)*X 1 1+(1202148041/10000000000 : ℝ)*X 1 2+(6577344713/10000000000 : ℝ)*X 2 0+(4394836893/10000000000 : ℝ)*X 2 1+(1202148041/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-25237279/250000000 : ℝ)*X 0 0+(305934613/625000000 : ℝ)*X 0 1+(311903707/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((811254151/2000000000 : ℝ)*X 1 0+(-1155684253/10000000000 : ℝ)*X 1 1+(3451396837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2873531401/5000000000 : ℝ)*X 2 0+(5642914101/10000000000 : ℝ)*X 2 1+(-151065833/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1619880859/2000000000 : ℝ)*X 0 0+(1238234979/5000000000 : ℝ)*X 0 1+(1242909847/10000000000 : ℝ)*X 0 2+(1619880859/2000000000 : ℝ)*X 1 0+(1238234979/5000000000 : ℝ)*X 1 1+(1242909847/10000000000 : ℝ)*X 1 2+(1619880859/2000000000 : ℝ)*X 2 0+(1238234979/5000000000 : ℝ)*X 2 1+(1242909847/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-1005537511/10000000000 : ℝ)*X 0 0+(1465955101/2500000000 : ℝ)*X 0 1+(2645141461/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2864108203/5000000000 : ℝ)*X 1 0+(-129006627/2000000000 : ℝ)*X 1 1+(176245921/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((3981542693/10000000000 : ℝ)*X 2 0+(7013839391/10000000000 : ℝ)*X 2 1+(-1077146159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((2081862027/2500000000 : ℝ)*X 0 0+(1763026029/10000000000 : ℝ)*X 0 1+(832390681/5000000000 : ℝ)*X 0 2+(2081862027/2500000000 : ℝ)*X 1 0+(1763026029/10000000000 : ℝ)*X 1 1+(832390681/5000000000 : ℝ)*X 1 2+(2081862027/2500000000 : ℝ)*X 2 0+(1763026029/10000000000 : ℝ)*X 2 1+(832390681/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((39293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2780756316301927685059747602959/629167181947000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3145797/1000000000000 : ℝ)*(base49) + (125258281139/250000000000 : ℝ)*(base59) + (4459393934293/1000000000000 : ℝ)*(major_s2_0) + (4459393934293/1000000000000 : ℝ)*(major_s2_1) + (4459393934293/1000000000000 : ℝ)*(major_s2_2) + (17702313/500000000000 : ℝ)*(sp_s2_0) + (9845843/1000000000000 : ℝ)*(sp_s2_6) + (24402589957/3906250000 : ℝ)*(sp_s2_7) + (390426521573/62500000000 : ℝ)*(sp_s2_8) + (156175187609/25000000000 : ℝ)*(sp_s2_9) + (2671677760451/1000000000000 : ℝ)*(sp_s2_13) + (11107/31250000000 : ℝ)*(sp_s2_14) + (137221937/500000000000 : ℝ)*(sp_s2_15) + (45642341/500000000000 : ℝ)*(sp_s2_23) + (1335843803147/500000000000 : ℝ)*(f.failure) + (3123549394521/500000000000 : ℝ)*(f.sum) + (12768942030288028723/46781127600000000000000000000000 : ℝ)*base62 + (1666440696892773/3389200000000000000000000000 : ℝ)*base65 + (300311122931297/1150250000000000000000000000 : ℝ)*base66 + (276177384179509/3389200000000000000000000000 : ℝ)*base68 + (4583240956735796979/13674574700000000000000000000000 : ℝ)*base71 + (432121127050543/3227800000000000000000000000 : ℝ)*base73 + (117694388337913/1380300000000000000000000000 : ℝ)*base74 + (972792252884413/6455600000000000000000000000 : ℝ)*base77 + (37918222831142894317/74255539000000000000000000000000 : ℝ)*base78 + (25211/50000000000000000 : ℝ)*base87 + (25211/50000000000000000 : ℝ)*base89 + (25211/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9137/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9137/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (753460550314525764674625703681/78645897743375000000000000000000000 : ℝ) := by norm_num
    linear_combination (379383/1000000000000 : ℝ)*(base39) + (3397633531/500000000000 : ℝ)*(base49) + (9858562863/200000000000 : ℝ)*(base59) + (1069902682849/250000000000 : ℝ)*(major_s2_0) + (1069902682849/250000000000 : ℝ)*(major_s2_1) + (1069902682849/250000000000 : ℝ)*(major_s2_2) + (952883/1000000000000 : ℝ)*(sp_s2_1) + (2268349/125000000000 : ℝ)*(sp_s2_2) + (42000917/1000000000000 : ℝ)*(sp_s2_7) + (5995199387387/1000000000000 : ℝ)*(sp_s2_14) + (5995240435421/1000000000000 : ℝ)*(sp_s2_15) + (749402905189/125000000000 : ℝ)*(sp_s2_16) + (1281958241949/500000000000 : ℝ)*(sp_s2_20) + (6039711/100000000000 : ℝ)*(sp_s2_27) + (160248555063/62500000000 : ℝ)*(f.failure) + (374702586769/62500000000 : ℝ)*(f.sum) + (1783155759416660749/11695281900000000000000000000000 : ℝ)*base62 + (727994153732951/847300000000000000000000000 : ℝ)*base64 + (540447288444417/575125000000000000000000000 : ℝ)*base66 + (769414326655467/847300000000000000000000000 : ℝ)*base68 + (948717410912331751/6837287350000000000000000000000 : ℝ)*base70 + (996148248030991/806950000000000000000000000 : ℝ)*base72 + (79235872832041/86268750000000000000000000 : ℝ)*base74 + (1385593856140371/1613900000000000000000000000 : ℝ)*base76 + (10072055251142085531/18563884750000000000000000000000 : ℝ)*base78 + (5519/6250000000000000 : ℝ)*base87 + (5519/6250000000000000 : ℝ)*base89 + (5519/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44009/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10060910510460789977737560302979/629167181947000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34339058917/200000000000 : ℝ)*(base40) + (365869/62500000000 : ℝ)*(base49) + (20396494333/200000000000 : ℝ)*(base59) + (4034199963147/1000000000000 : ℝ)*(major_s2_0) + (4034199963147/1000000000000 : ℝ)*(major_s2_1) + (4034199963147/1000000000000 : ℝ)*(major_s2_2) + (37328661/1000000000000 : ℝ)*(sp_s2_0) + (536553/10000000000 : ℝ)*(sp_s2_2) + (14117669/500000000000 : ℝ)*(sp_s2_16) + (51902553/200000000000 : ℝ)*(sp_s2_20) + (28257047691/5000000000 : ℝ)*(sp_s2_21) + (5651446866861/1000000000000 : ℝ)*(sp_s2_22) + (176605155507/31250000000 : ℝ)*(sp_s2_23) + (120834410819/50000000000 : ℝ)*(sp_s2_27) + (302118466143/125000000000 : ℝ)*(f.failure) + (5651446866861/1000000000000 : ℝ)*(f.sum) + (6816485015143864719/15593709200000000000000000000000 : ℝ)*base62 + (116083599480293/3389200000000000000000000000 : ℝ)*base64 + (98293214426731/575125000000000000000000000 : ℝ)*base67 + (1294898489879531/3389200000000000000000000000 : ℝ)*base68 + (3537513138900469809/13674574700000000000000000000000 : ℝ)*base70 + (497109799053537/3227800000000000000000000000 : ℝ)*base73 + (378168016308369/460100000000000000000000000 : ℝ)*base74 + (4771413284331533/6455600000000000000000000000 : ℝ)*base76 + (20553332464489940757/74255539000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (10941/12500000000000000 : ℝ)*base86 + (10941/12500000000000000 : ℝ)*base88 + (10941/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((16139/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16139/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13803/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13803/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8473/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(8473/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((39293/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39293/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9137/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(9137/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44009/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44009/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312053_s2 p hpa hpb X hX hprev1

#print axioms solution
