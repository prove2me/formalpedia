-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310053_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:26:22.942187+00:00
-- url     : https://prove2.me/submissions/f01d97d8-7b0d-4c9d-a46d-24278f5c6f89

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
theorem collision_support_c310053_s3_s3_0 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2395847719/10000000000 : ℝ)*x 0 + (2551877293/5000000000 : ℝ)*x 1 + (5127754183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2395847719/10000000000 : ℝ)^71 ≤ (15810232398287/100000000000000 : ℝ)^55 := by
    have hnat : (2395847719 : ℕ)^71*100000000000000^55 ≤ 15810232398287^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2395847719 10000000000 15810232398287 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2551877293/5000000000 : ℝ)^71 ≤ (20983709725209/50000000000000 : ℝ)^55 := by
    have hnat : (2551877293 : ℕ)^71*50000000000000^55 ≤ 20983709725209^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2551877293 5000000000 20983709725209 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127754183/10000000000 : ℝ)^71 ≤ (42222348136339/100000000000000 : ℝ)^55 := by
    have hnat : (5127754183 : ℕ)^71*100000000000000^55 ≤ 42222348136339^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127754183 10000000000 42222348136339 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2395847719/10000000000 : ℝ), (2551877293/5000000000 : ℝ), (5127754183/10000000000 : ℝ)] ![(15810232398287/100000000000000 : ℝ), (20983709725209/50000000000000 : ℝ), (42222348136339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2395847719/10000000000 : ℝ)|^71 ≤ (15810232398287/100000000000000 : ℝ)^55
        have hw : |(-2395847719/10000000000 : ℝ)|=(2395847719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2551877293/5000000000 : ℝ)|^71 ≤ (20983709725209/50000000000000 : ℝ)^55
        have hw : |(2551877293/5000000000 : ℝ)|=(2551877293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127754183/10000000000 : ℝ)|^71 ≤ (42222348136339/100000000000000 : ℝ)^55
        have hw : |(5127754183/10000000000 : ℝ)|=(5127754183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (90272071/200000000 : ℝ)*x 0 + (-956270553/5000000000 : ℝ)*x 1 + (6058675897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90272071/200000000 : ℝ)^71 ≤ (4476423250373/12500000000000 : ℝ)^55 := by
    have hnat : (90272071 : ℕ)^71*12500000000000^55 ≤ 4476423250373^55*200000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90272071 200000000 4476423250373 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (956270553/5000000000 : ℝ)^71 ≤ (5910099969599/50000000000000 : ℝ)^55 := by
    have hnat : (956270553 : ℕ)^71*50000000000000^55 ≤ 5910099969599^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956270553 5000000000 5910099969599 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6058675897/10000000000 : ℝ)^71 ≤ (52368414035169/100000000000000 : ℝ)^55 := by
    have hnat : (6058675897 : ℕ)^71*100000000000000^55 ≤ 52368414035169^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6058675897 10000000000 52368414035169 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(90272071/200000000 : ℝ), (-956270553/5000000000 : ℝ), (6058675897/10000000000 : ℝ)] ![(4476423250373/12500000000000 : ℝ), (5910099969599/50000000000000 : ℝ), (52368414035169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(90272071/200000000 : ℝ)|^71 ≤ (4476423250373/12500000000000 : ℝ)^55
        have hw : |(90272071/200000000 : ℝ)|=(90272071/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-956270553/5000000000 : ℝ)|^71 ≤ (5910099969599/50000000000000 : ℝ)^55
        have hw : |(-956270553/5000000000 : ℝ)|=(956270553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6058675897/10000000000 : ℝ)|^71 ≤ (52368414035169/100000000000000 : ℝ)^55
        have hw : |(6058675897/10000000000 : ℝ)|=(6058675897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1134020489/2500000000 : ℝ)*x 0 + (3025012019/5000000000 : ℝ)*x 1 + (-94786969/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134020489/2500000000 : ℝ)^71 ≤ (18020890489039/50000000000000 : ℝ)^55 := by
    have hnat : (1134020489 : ℕ)^71*50000000000000^55 ≤ 18020890489039^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134020489 2500000000 18020890489039 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3025012019/5000000000 : ℝ)^71 ≤ (26135948214113/50000000000000 : ℝ)^55 := by
    have hnat : (3025012019 : ℕ)^71*50000000000000^55 ≤ 26135948214113^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3025012019 5000000000 26135948214113 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94786969/500000000 : ℝ)^71 ≤ (11686322579821/100000000000000 : ℝ)^55 := by
    have hnat : (94786969 : ℕ)^71*100000000000000^55 ≤ 11686322579821^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94786969 500000000 11686322579821 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1134020489/2500000000 : ℝ), (3025012019/5000000000 : ℝ), (-94786969/500000000 : ℝ)] ![(18020890489039/50000000000000 : ℝ), (26135948214113/50000000000000 : ℝ), (11686322579821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1134020489/2500000000 : ℝ)|^71 ≤ (18020890489039/50000000000000 : ℝ)^55
        have hw : |(1134020489/2500000000 : ℝ)|=(1134020489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3025012019/5000000000 : ℝ)|^71 ≤ (26135948214113/50000000000000 : ℝ)^55
        have hw : |(3025012019/5000000000 : ℝ)|=(3025012019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94786969/500000000 : ℝ)|^71 ≤ (11686322579821/100000000000000 : ℝ)^55
        have hw : |(-94786969/500000000 : ℝ)|=(94786969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6613413139/10000000000 : ℝ)*x 0 + (370958929/1250000000 : ℝ)*x 1 + (1466009823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6613413139/10000000000 : ℝ)^71 ≤ (58638903949539/100000000000000 : ℝ)^55 := by
    have hnat : (6613413139 : ℕ)^71*100000000000000^55 ≤ 58638903949539^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6613413139 10000000000 58638903949539 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (370958929/1250000000 : ℝ)^71 ≤ (20841874703271/100000000000000 : ℝ)^55 := by
    have hnat : (370958929 : ℕ)^71*100000000000000^55 ≤ 20841874703271^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      370958929 1250000000 20841874703271 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1466009823/5000000000 : ℝ)^71 ≤ (2564902667699/12500000000000 : ℝ)^55 := by
    have hnat : (1466009823 : ℕ)^71*12500000000000^55 ≤ 2564902667699^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1466009823 5000000000 2564902667699 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6613413139/10000000000 : ℝ), (370958929/1250000000 : ℝ), (1466009823/5000000000 : ℝ)] ![(58638903949539/100000000000000 : ℝ), (20841874703271/100000000000000 : ℝ), (2564902667699/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6613413139/10000000000 : ℝ)|^71 ≤ (58638903949539/100000000000000 : ℝ)^55
        have hw : |(6613413139/10000000000 : ℝ)|=(6613413139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(370958929/1250000000 : ℝ)|^71 ≤ (20841874703271/100000000000000 : ℝ)^55
        have hw : |(370958929/1250000000 : ℝ)|=(370958929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1466009823/5000000000 : ℝ)|^71 ≤ (2564902667699/12500000000000 : ℝ)^55
        have hw : |(1466009823/5000000000 : ℝ)|=(1466009823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-36116063/156250000 : ℝ)*x 0 + (526420541/1250000000 : ℝ)*x 1 + (6039878433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36116063/156250000 : ℝ)^71 ≤ (7547400541933/50000000000000 : ℝ)^55 := by
    have hnat : (36116063 : ℕ)^71*50000000000000^55 ≤ 7547400541933^55*156250000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36116063 156250000 7547400541933 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526420541/1250000000 : ℝ)^71 ≤ (16373216361903/50000000000000 : ℝ)^55 := by
    have hnat : (526420541 : ℕ)^71*50000000000000^55 ≤ 16373216361903^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526420541 1250000000 16373216361903 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6039878433/10000000000 : ℝ)^71 ≤ (52158766170299/100000000000000 : ℝ)^55 := by
    have hnat : (6039878433 : ℕ)^71*100000000000000^55 ≤ 52158766170299^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6039878433 10000000000 52158766170299 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36116063/156250000 : ℝ), (526420541/1250000000 : ℝ), (6039878433/10000000000 : ℝ)] ![(7547400541933/50000000000000 : ℝ), (16373216361903/50000000000000 : ℝ), (52158766170299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36116063/156250000 : ℝ)|^71 ≤ (7547400541933/50000000000000 : ℝ)^55
        have hw : |(-36116063/156250000 : ℝ)|=(36116063/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526420541/1250000000 : ℝ)|^71 ≤ (16373216361903/50000000000000 : ℝ)^55
        have hw : |(526420541/1250000000 : ℝ)|=(526420541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6039878433/10000000000 : ℝ)|^71 ≤ (52158766170299/100000000000000 : ℝ)^55
        have hw : |(6039878433/10000000000 : ℝ)|=(6039878433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4234821769/10000000000 : ℝ)*x 0 + (-765448597/5000000000 : ℝ)*x 1 + (3285313639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4234821769/10000000000 : ℝ)^71 ≤ (8245520855329/25000000000000 : ℝ)^55 := by
    have hnat : (4234821769 : ℕ)^71*25000000000000^55 ≤ 8245520855329^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234821769 10000000000 8245520855329 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765448597/5000000000 : ℝ)^71 ≤ (4434140204033/50000000000000 : ℝ)^55 := by
    have hnat : (765448597 : ℕ)^71*50000000000000^55 ≤ 4434140204033^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765448597 5000000000 4434140204033 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3285313639/5000000000 : ℝ)^71 ≤ (58149636162643/100000000000000 : ℝ)^55 := by
    have hnat : (3285313639 : ℕ)^71*100000000000000^55 ≤ 58149636162643^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3285313639 5000000000 58149636162643 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4234821769/10000000000 : ℝ), (-765448597/5000000000 : ℝ), (3285313639/5000000000 : ℝ)] ![(8245520855329/25000000000000 : ℝ), (4434140204033/50000000000000 : ℝ), (58149636162643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4234821769/10000000000 : ℝ)|^71 ≤ (8245520855329/25000000000000 : ℝ)^55
        have hw : |(4234821769/10000000000 : ℝ)|=(4234821769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-765448597/5000000000 : ℝ)|^71 ≤ (4434140204033/50000000000000 : ℝ)^55
        have hw : |(-765448597/5000000000 : ℝ)|=(765448597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3285313639/5000000000 : ℝ)|^71 ≤ (58149636162643/100000000000000 : ℝ)^55
        have hw : |(3285313639/5000000000 : ℝ)|=(3285313639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (532179497/1250000000 : ℝ)*x 0 + (1715502977/2500000000 : ℝ)*x 1 + (-1026039903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532179497/1250000000 : ℝ)^71 ≤ (830240572361/2500000000000 : ℝ)^55 := by
    have hnat : (532179497 : ℕ)^71*2500000000000^55 ≤ 830240572361^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532179497 1250000000 830240572361 2500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1715502977/2500000000 : ℝ)^71 ≤ (61499801273797/100000000000000 : ℝ)^55 := by
    have hnat : (1715502977 : ℕ)^71*100000000000000^55 ≤ 61499801273797^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715502977 2500000000 61499801273797 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1026039903/10000000000 : ℝ)^71 ≤ (2645287906513/50000000000000 : ℝ)^55 := by
    have hnat : (1026039903 : ℕ)^71*50000000000000^55 ≤ 2645287906513^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026039903 10000000000 2645287906513 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(532179497/1250000000 : ℝ), (1715502977/2500000000 : ℝ), (-1026039903/10000000000 : ℝ)] ![(830240572361/2500000000000 : ℝ), (61499801273797/100000000000000 : ℝ), (2645287906513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(532179497/1250000000 : ℝ)|^71 ≤ (830240572361/2500000000000 : ℝ)^55
        have hw : |(532179497/1250000000 : ℝ)|=(532179497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1715502977/2500000000 : ℝ)|^71 ≤ (61499801273797/100000000000000 : ℝ)^55
        have hw : |(1715502977/2500000000 : ℝ)|=(1715502977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1026039903/10000000000 : ℝ)|^71 ≤ (2645287906513/50000000000000 : ℝ)^55
        have hw : |(-1026039903/10000000000 : ℝ)|=(1026039903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (399519143/625000000 : ℝ)*x 0 + (4177207881/10000000000 : ℝ)*x 1 + (934596819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399519143/625000000 : ℝ)^71 ≤ (56120508595913/100000000000000 : ℝ)^55 := by
    have hnat : (399519143 : ℕ)^71*100000000000000^55 ≤ 56120508595913^55*625000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399519143 625000000 56120508595913 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4177207881/10000000000 : ℝ)^71 ≤ (16201991864019/50000000000000 : ℝ)^55 := by
    have hnat : (4177207881 : ℕ)^71*50000000000000^55 ≤ 16201991864019^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177207881 10000000000 16201991864019 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934596819/5000000000 : ℝ)^71 ≤ (2295101531167/20000000000000 : ℝ)^55 := by
    have hnat : (934596819 : ℕ)^71*20000000000000^55 ≤ 2295101531167^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934596819 5000000000 2295101531167 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(399519143/625000000 : ℝ), (4177207881/10000000000 : ℝ), (934596819/5000000000 : ℝ)] ![(56120508595913/100000000000000 : ℝ), (16201991864019/50000000000000 : ℝ), (2295101531167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(399519143/625000000 : ℝ)|^71 ≤ (56120508595913/100000000000000 : ℝ)^55
        have hw : |(399519143/625000000 : ℝ)|=(399519143/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4177207881/10000000000 : ℝ)|^71 ≤ (16201991864019/50000000000000 : ℝ)^55
        have hw : |(4177207881/10000000000 : ℝ)|=(4177207881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934596819/5000000000 : ℝ)|^71 ≤ (2295101531167/20000000000000 : ℝ)^55
        have hw : |(934596819/5000000000 : ℝ)|=(934596819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1501692259/10000000000 : ℝ)*x 0 + (1231379131/2500000000 : ℝ)*x 1 + (1191898801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1501692259/10000000000 : ℝ)^71 ≤ (8650492869081/100000000000000 : ℝ)^55 := by
    have hnat : (1501692259 : ℕ)^71*100000000000000^55 ≤ 8650492869081^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501692259 10000000000 8650492869081 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1231379131/2500000000 : ℝ)^71 ≤ (20042560892211/50000000000000 : ℝ)^55 := by
    have hnat : (1231379131 : ℕ)^71*50000000000000^55 ≤ 20042560892211^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1231379131 2500000000 20042560892211 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1191898801/2000000000 : ℝ)^71 ≤ (2050575413001/4000000000000 : ℝ)^55 := by
    have hnat : (1191898801 : ℕ)^71*4000000000000^55 ≤ 2050575413001^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191898801 2000000000 2050575413001 4000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1501692259/10000000000 : ℝ), (1231379131/2500000000 : ℝ), (1191898801/2000000000 : ℝ)] ![(8650492869081/100000000000000 : ℝ), (20042560892211/50000000000000 : ℝ), (2050575413001/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1501692259/10000000000 : ℝ)|^71 ≤ (8650492869081/100000000000000 : ℝ)^55
        have hw : |(-1501692259/10000000000 : ℝ)|=(1501692259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1231379131/2500000000 : ℝ)|^71 ≤ (20042560892211/50000000000000 : ℝ)^55
        have hw : |(1231379131/2500000000 : ℝ)|=(1231379131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1191898801/2000000000 : ℝ)|^71 ≤ (2050575413001/4000000000000 : ℝ)^55
        have hw : |(1191898801/2000000000 : ℝ)|=(1191898801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4106079531/10000000000 : ℝ)*x 0 + (-1648355969/10000000000 : ℝ)*x 1 + (1321133291/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4106079531/10000000000 : ℝ)^71 ≤ (7923368773059/25000000000000 : ℝ)^55 := by
    have hnat : (4106079531 : ℕ)^71*25000000000000^55 ≤ 7923368773059^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4106079531 10000000000 7923368773059 25000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1648355969/10000000000 : ℝ)^71 ≤ (4878137404547/50000000000000 : ℝ)^55 := by
    have hnat : (1648355969 : ℕ)^71*50000000000000^55 ≤ 4878137404547^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648355969 10000000000 4878137404547 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1321133291/2000000000 : ℝ)^71 ≤ (29275125042841/50000000000000 : ℝ)^55 := by
    have hnat : (1321133291 : ℕ)^71*50000000000000^55 ≤ 29275125042841^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321133291 2000000000 29275125042841 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4106079531/10000000000 : ℝ), (-1648355969/10000000000 : ℝ), (1321133291/2000000000 : ℝ)] ![(7923368773059/25000000000000 : ℝ), (4878137404547/50000000000000 : ℝ), (29275125042841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4106079531/10000000000 : ℝ)|^71 ≤ (7923368773059/25000000000000 : ℝ)^55
        have hw : |(4106079531/10000000000 : ℝ)|=(4106079531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1648355969/10000000000 : ℝ)|^71 ≤ (4878137404547/50000000000000 : ℝ)^55
        have hw : |(-1648355969/10000000000 : ℝ)|=(1648355969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1321133291/2000000000 : ℝ)|^71 ≤ (29275125042841/50000000000000 : ℝ)^55
        have hw : |(1321133291/2000000000 : ℝ)|=(1321133291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_16 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5472108943/10000000000 : ℝ)*x 0 + (2843121993/5000000000 : ℝ)*x 1 + (-55321211/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5472108943/10000000000 : ℝ)^71 ≤ (22958926167613/50000000000000 : ℝ)^55 := by
    have hnat : (5472108943 : ℕ)^71*50000000000000^55 ≤ 22958926167613^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472108943 10000000000 22958926167613 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2843121993/5000000000 : ℝ)^71 ≤ (48250519856397/100000000000000 : ℝ)^55 := by
    have hnat : (2843121993 : ℕ)^71*100000000000000^55 ≤ 48250519856397^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843121993 5000000000 48250519856397 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55321211/500000000 : ℝ)^71 ≤ (5831627797317/100000000000000 : ℝ)^55 := by
    have hnat : (55321211 : ℕ)^71*100000000000000^55 ≤ 5831627797317^55*500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55321211 500000000 5831627797317 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5472108943/10000000000 : ℝ), (2843121993/5000000000 : ℝ), (-55321211/500000000 : ℝ)] ![(22958926167613/50000000000000 : ℝ), (48250519856397/100000000000000 : ℝ), (5831627797317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5472108943/10000000000 : ℝ)|^71 ≤ (22958926167613/50000000000000 : ℝ)^55
        have hw : |(5472108943/10000000000 : ℝ)|=(5472108943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2843121993/5000000000 : ℝ)|^71 ≤ (48250519856397/100000000000000 : ℝ)^55
        have hw : |(2843121993/5000000000 : ℝ)|=(2843121993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55321211/500000000 : ℝ)|^71 ≤ (5831627797317/100000000000000 : ℝ)^55
        have hw : |(-55321211/500000000 : ℝ)|=(55321211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1896384467/2500000000 : ℝ)*x 0 + (694696633/2500000000 : ℝ)*x 1 + (1790850769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1896384467/2500000000 : ℝ)^71 ≤ (34998008493583/50000000000000 : ℝ)^55 := by
    have hnat : (1896384467 : ℕ)^71*50000000000000^55 ≤ 34998008493583^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896384467 2500000000 34998008493583 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (694696633/2500000000 : ℝ)^71 ≤ (19145539237929/100000000000000 : ℝ)^55 := by
    have hnat : (694696633 : ℕ)^71*100000000000000^55 ≤ 19145539237929^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694696633 2500000000 19145539237929 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1790850769/10000000000 : ℝ)^71 ≤ (10858443756543/100000000000000 : ℝ)^55 := by
    have hnat : (1790850769 : ℕ)^71*100000000000000^55 ≤ 10858443756543^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1790850769 10000000000 10858443756543 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1896384467/2500000000 : ℝ), (694696633/2500000000 : ℝ), (1790850769/10000000000 : ℝ)] ![(34998008493583/50000000000000 : ℝ), (19145539237929/100000000000000 : ℝ), (10858443756543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1896384467/2500000000 : ℝ)|^71 ≤ (34998008493583/50000000000000 : ℝ)^55
        have hw : |(1896384467/2500000000 : ℝ)|=(1896384467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(694696633/2500000000 : ℝ)|^71 ≤ (19145539237929/100000000000000 : ℝ)^55
        have hw : |(694696633/2500000000 : ℝ)|=(694696633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1790850769/10000000000 : ℝ)|^71 ≤ (10858443756543/100000000000000 : ℝ)^55
        have hw : |(1790850769/10000000000 : ℝ)|=(1790850769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-351752381/2500000000 : ℝ)*x 0 + (688601079/1250000000 : ℝ)*x 1 + (5454875087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (351752381/2500000000 : ℝ)^71 ≤ (159059238231/2000000000000 : ℝ)^55 := by
    have hnat : (351752381 : ℕ)^71*2000000000000^55 ≤ 159059238231^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351752381 2500000000 159059238231 2000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688601079/1250000000 : ℝ)^71 ≤ (46315783232741/100000000000000 : ℝ)^55 := by
    have hnat : (688601079 : ℕ)^71*100000000000000^55 ≤ 46315783232741^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688601079 1250000000 46315783232741 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5454875087/10000000000 : ℝ)^71 ≤ (22865627420111/50000000000000 : ℝ)^55 := by
    have hnat : (5454875087 : ℕ)^71*50000000000000^55 ≤ 22865627420111^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454875087 10000000000 22865627420111 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-351752381/2500000000 : ℝ), (688601079/1250000000 : ℝ), (5454875087/10000000000 : ℝ)] ![(159059238231/2000000000000 : ℝ), (46315783232741/100000000000000 : ℝ), (22865627420111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-351752381/2500000000 : ℝ)|^71 ≤ (159059238231/2000000000000 : ℝ)^55
        have hw : |(-351752381/2500000000 : ℝ)|=(351752381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688601079/1250000000 : ℝ)|^71 ≤ (46315783232741/100000000000000 : ℝ)^55
        have hw : |(688601079/1250000000 : ℝ)|=(688601079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5454875087/10000000000 : ℝ)|^71 ≤ (22865627420111/50000000000000 : ℝ)^55
        have hw : |(5454875087/10000000000 : ℝ)|=(5454875087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2772088817/5000000000 : ℝ)*x 0 + (-240930843/2000000000 : ℝ)*x 1 + (5552593133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2772088817/5000000000 : ℝ)^71 ≤ (46700016151009/100000000000000 : ℝ)^55 := by
    have hnat : (2772088817 : ℕ)^71*100000000000000^55 ≤ 46700016151009^55*5000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2772088817 5000000000 46700016151009 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (240930843/2000000000 : ℝ)^71 ≤ (813555031251/12500000000000 : ℝ)^55 := by
    have hnat : (240930843 : ℕ)^71*12500000000000^55 ≤ 813555031251^55*2000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240930843 2000000000 813555031251 12500000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5552593133/10000000000 : ℝ)^71 ≤ (2924471473801/6250000000000 : ℝ)^55 := by
    have hnat : (5552593133 : ℕ)^71*6250000000000^55 ≤ 2924471473801^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5552593133 10000000000 2924471473801 6250000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2772088817/5000000000 : ℝ), (-240930843/2000000000 : ℝ), (5552593133/10000000000 : ℝ)] ![(46700016151009/100000000000000 : ℝ), (813555031251/12500000000000 : ℝ), (2924471473801/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2772088817/5000000000 : ℝ)|^71 ≤ (46700016151009/100000000000000 : ℝ)^55
        have hw : |(2772088817/5000000000 : ℝ)|=(2772088817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-240930843/2000000000 : ℝ)|^71 ≤ (813555031251/12500000000000 : ℝ)^55
        have hw : |(-240930843/2000000000 : ℝ)|=(240930843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5552593133/10000000000 : ℝ)|^71 ≤ (2924471473801/6250000000000 : ℝ)^55
        have hw : |(5552593133/10000000000 : ℝ)|=(5552593133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_23 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4085804707/10000000000 : ℝ)*x 0 + (270304419/400000000 : ℝ)*x 1 + (-360656539/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4085804707/10000000000 : ℝ)^71 ≤ (6298319988649/20000000000000 : ℝ)^55 := by
    have hnat : (4085804707 : ℕ)^71*20000000000000^55 ≤ 6298319988649^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4085804707 10000000000 6298319988649 20000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270304419/400000000 : ℝ)^71 ≤ (30147301200533/50000000000000 : ℝ)^55 := by
    have hnat : (270304419 : ℕ)^71*50000000000000^55 ≤ 30147301200533^55*400000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270304419 400000000 30147301200533 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360656539/2500000000 : ℝ)^71 ≤ (4106898818933/50000000000000 : ℝ)^55 := by
    have hnat : (360656539 : ℕ)^71*50000000000000^55 ≤ 4106898818933^55*2500000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360656539 2500000000 4106898818933 50000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4085804707/10000000000 : ℝ), (270304419/400000000 : ℝ), (-360656539/2500000000 : ℝ)] ![(6298319988649/20000000000000 : ℝ), (30147301200533/50000000000000 : ℝ), (4106898818933/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4085804707/10000000000 : ℝ)|^71 ≤ (6298319988649/20000000000000 : ℝ)^55
        have hw : |(4085804707/10000000000 : ℝ)|=(4085804707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270304419/400000000 : ℝ)|^71 ≤ (30147301200533/50000000000000 : ℝ)^55
        have hw : |(270304419/400000000 : ℝ)|=(270304419/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-360656539/2500000000 : ℝ)|^71 ≤ (4106898818933/50000000000000 : ℝ)^55
        have hw : |(-360656539/2500000000 : ℝ)|=(360656539/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310053_s3_s3_27 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ)) (x : Fin 3 → ℝ) :
    (960178903/1250000000 : ℝ)*x 0 + (2239167921/10000000000 : ℝ)*x 1 + (2225121009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (960178903/1250000000 : ℝ)^71 ≤ (71140387327909/100000000000000 : ℝ)^55 := by
    have hnat : (960178903 : ℕ)^71*100000000000000^55 ≤ 71140387327909^55*1250000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960178903 1250000000 71140387327909 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2239167921/10000000000 : ℝ)^71 ≤ (1448841795561/10000000000000 : ℝ)^55 := by
    have hnat : (2239167921 : ℕ)^71*10000000000000^55 ≤ 1448841795561^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2239167921 10000000000 1448841795561 10000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2225121009/10000000000 : ℝ)^71 ≤ (14371194702601/100000000000000 : ℝ)^55 := by
    have hnat : (2225121009 : ℕ)^71*100000000000000^55 ≤ 14371194702601^55*10000000000^71 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225121009 10000000000 14371194702601 100000000000000 71 55 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (71/16 : ℝ)) 71 55 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(960178903/1250000000 : ℝ), (2239167921/10000000000 : ℝ), (2225121009/10000000000 : ℝ)] ![(71140387327909/100000000000000 : ℝ), (1448841795561/10000000000000 : ℝ), (14371194702601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(960178903/1250000000 : ℝ)|^71 ≤ (71140387327909/100000000000000 : ℝ)^55
        have hw : |(960178903/1250000000 : ℝ)|=(960178903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2239167921/10000000000 : ℝ)|^71 ≤ (1448841795561/10000000000000 : ℝ)^55
        have hw : |(2239167921/10000000000 : ℝ)|=(2239167921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2225121009/10000000000 : ℝ)|^71 ≤ (14371194702601/100000000000000 : ℝ)^55
        have hw : |(2225121009/10000000000 : ℝ)|=(2225121009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310053_s3 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((10391/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10391/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60103/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60103/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29289/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29289/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30761/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30761/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4511/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4511/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17341/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (10391/20000 : ℝ) ^ (35/8 : ℝ) ≤ (5699931711031001837/100000000000000000000 : ℝ) := by
    have hpowers : (10391/20000 : ℝ)^35 ≤ (5699931711031001837/100000000000000000000 : ℝ)^8 := by
      have hnat : (10391 : ℕ)^35*100000000000000000000^8 ≤ 5699931711031001837^8*20000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10391 20000 5699931711031001837 100000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10391/20000 : ℝ)) (X := (5699931711031001837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0a : (105699931711031001837/100000000000000000000 : ℝ) ≤ (10127512551761487/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (105699931711031001837/100000000000000000000 : ℝ)^8 ≤ (10127512551761487/10000000000000000 : ℝ)^35 := by
      have hnat : (105699931711031001837 : ℕ)^8*10000000000000000^35 ≤ 10127512551761487^35*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105699931711031001837 100000000000000000000 10127512551761487 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10127512551761487/10000000000000000 : ℝ)) (X := (105699931711031001837/100000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner0b : (55699931711031001837/50000000000000000000 : ℝ) ≤ (640614125634131/625000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (55699931711031001837/50000000000000000000 : ℝ)^8 ≤ (640614125634131/625000000000000 : ℝ)^35 := by
      have hnat : (55699931711031001837 : ℕ)^8*625000000000000^35 ≤ 640614125634131^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55699931711031001837 50000000000000000000 640614125634131 625000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (640614125634131/625000000000000 : ℝ)) (X := (55699931711031001837/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(127512551761487/5195500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(122313458384609/5195500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (10391/20000 : ℝ)) (alpha := (127512551761487/5195500000000000 : ℝ)) (beta := (122313458384609/5195500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10391/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(127512551761487/5195500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(122313458384609/5195500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (60103/100000 : ℝ) ^ (35/8 : ℝ) ≤ (336915256988492157/3125000000000000000 : ℝ) := by
    have hpowers : (60103/100000 : ℝ)^35 ≤ (336915256988492157/3125000000000000000 : ℝ)^8 := by
      have hnat : (60103 : ℕ)^35*3125000000000000000^8 ≤ 336915256988492157^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60103 100000 336915256988492157 3125000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60103/100000 : ℝ)) (X := (336915256988492157/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1a : (3461915256988492157/3125000000000000000 : ℝ) ≤ (10236788985050413/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (3461915256988492157/3125000000000000000 : ℝ)^8 ≤ (10236788985050413/10000000000000000 : ℝ)^35 := by
      have hnat : (3461915256988492157 : ℕ)^8*10000000000000000^35 ≤ 10236788985050413^35*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3461915256988492157 3125000000000000000 10236788985050413 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10236788985050413/10000000000000000 : ℝ)) (X := (3461915256988492157/3125000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner1b : (1899415256988492157/1562500000000000000 : ℝ) ≤ (10456415528829207/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (1899415256988492157/1562500000000000000 : ℝ)^8 ≤ (10456415528829207/10000000000000000 : ℝ)^35 := by
      have hnat : (1899415256988492157 : ℕ)^8*10000000000000000^35 ≤ 10456415528829207^35*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1899415256988492157 1562500000000000000 10456415528829207 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10456415528829207/10000000000000000 : ℝ)) (X := (1899415256988492157/1562500000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(236788985050413/6010300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(109813271889397/3005150000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (60103/100000 : ℝ)) (alpha := (236788985050413/6010300000000000 : ℝ)) (beta := (109813271889397/3005150000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (60103/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(236788985050413/6010300000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(109813271889397/3005150000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (29289/50000 : ℝ) ^ (35/8 : ℝ) ≤ (2408677300474548171/25000000000000000000 : ℝ) := by
    have hpowers : (29289/50000 : ℝ)^35 ≤ (2408677300474548171/25000000000000000000 : ℝ)^8 := by
      have hnat : (29289 : ℕ)^35*25000000000000000000^8 ≤ 2408677300474548171^8*50000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29289 50000 2408677300474548171 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (29289/50000 : ℝ)) (X := (2408677300474548171/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2a : (27408677300474548171/25000000000000000000 : ℝ) ≤ (10212474548668453/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (27408677300474548171/25000000000000000000 : ℝ)^8 ≤ (10212474548668453/10000000000000000 : ℝ)^35 := by
      have hnat : (27408677300474548171 : ℕ)^8*10000000000000000^35 ≤ 10212474548668453^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27408677300474548171 25000000000000000000 10212474548668453 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10212474548668453/10000000000000000 : ℝ)) (X := (27408677300474548171/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s3_corner2b : (14908677300474548171/12500000000000000000 : ℝ) ≤ (1301374759018143/1250000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (14908677300474548171/12500000000000000000 : ℝ)^8 ≤ (1301374759018143/1250000000000000 : ℝ)^35 := by
      have hnat : (14908677300474548171 : ℕ)^8*1250000000000000^35 ≤ 1301374759018143^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14908677300474548171 12500000000000000000 1301374759018143 1250000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1301374759018143/1250000000000000 : ℝ)) (X := (14908677300474548171/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(70824849556151/1952600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(198523523476691/5857800000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (29289/50000 : ℝ)) (alpha := (70824849556151/1952600000000000 : ℝ)) (beta := (198523523476691/5857800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (29289/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(70824849556151/1952600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(198523523476691/5857800000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2395847719/10000000000 : ℝ)*X 0 0+(2551877293/5000000000 : ℝ)*X 0 1+(5127754183/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((90272071/200000000 : ℝ)*X 1 0+(-956270553/5000000000 : ℝ)*X 1 1+(6058675897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((1134020489/2500000000 : ℝ)*X 2 0+(3025012019/5000000000 : ℝ)*X 2 1+(-94786969/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((6613413139/10000000000 : ℝ)*X 0 0+(370958929/1250000000 : ℝ)*X 0 1+(1466009823/5000000000 : ℝ)*X 0 2+(6613413139/10000000000 : ℝ)*X 1 0+(370958929/1250000000 : ℝ)*X 1 1+(1466009823/5000000000 : ℝ)*X 1 2+(6613413139/10000000000 : ℝ)*X 2 0+(370958929/1250000000 : ℝ)*X 2 1+(1466009823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-36116063/156250000 : ℝ)*X 0 0+(526420541/1250000000 : ℝ)*X 0 1+(6039878433/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4234821769/10000000000 : ℝ)*X 1 0+(-765448597/5000000000 : ℝ)*X 1 1+(3285313639/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((532179497/1250000000 : ℝ)*X 2 0+(1715502977/2500000000 : ℝ)*X 2 1+(-1026039903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((399519143/625000000 : ℝ)*X 0 0+(4177207881/10000000000 : ℝ)*X 0 1+(934596819/5000000000 : ℝ)*X 0 2+(399519143/625000000 : ℝ)*X 1 0+(4177207881/10000000000 : ℝ)*X 1 1+(934596819/5000000000 : ℝ)*X 1 2+(399519143/625000000 : ℝ)*X 2 0+(4177207881/10000000000 : ℝ)*X 2 1+(934596819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1501692259/10000000000 : ℝ)*X 0 0+(1231379131/2500000000 : ℝ)*X 0 1+(1191898801/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4106079531/10000000000 : ℝ)*X 1 0+(-1648355969/10000000000 : ℝ)*X 1 1+(1321133291/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5472108943/10000000000 : ℝ)*X 2 0+(2843121993/5000000000 : ℝ)*X 2 1+(-55321211/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((1896384467/2500000000 : ℝ)*X 0 0+(694696633/2500000000 : ℝ)*X 0 1+(1790850769/10000000000 : ℝ)*X 0 2+(1896384467/2500000000 : ℝ)*X 1 0+(694696633/2500000000 : ℝ)*X 1 1+(1790850769/10000000000 : ℝ)*X 1 2+(1896384467/2500000000 : ℝ)*X 2 0+(694696633/2500000000 : ℝ)*X 2 1+(1790850769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-351752381/2500000000 : ℝ)*X 0 0+(688601079/1250000000 : ℝ)*X 0 1+(5454875087/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((2772088817/5000000000 : ℝ)*X 1 0+(-240930843/2000000000 : ℝ)*X 1 1+(5552593133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4085804707/10000000000 : ℝ)*X 2 0+(270304419/400000000 : ℝ)*X 2 1+(-360656539/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((960178903/1250000000 : ℝ)*X 0 0+(2239167921/10000000000 : ℝ)*X 0 1+(2225121009/10000000000 : ℝ)*X 0 2+(960178903/1250000000 : ℝ)*X 1 0+(2239167921/10000000000 : ℝ)*X 1 1+(2225121009/10000000000 : ℝ)*X 1 2+(960178903/1250000000 : ℝ)*X 2 0+(2239167921/10000000000 : ℝ)*X 2 1+(2225121009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310053_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((30761/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30761/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5945987275148631844410709/916852482812500000000000000000 : ℝ) := by norm_num
    linear_combination (72903714523/1000000000000 : ℝ)*(base49) + (692330907277/1000000000000 : ℝ)*(base59) + (126243/200000000000 : ℝ)*(base60) + (2748489415991/500000000000 : ℝ)*(major_s3_0) + (2748489415991/500000000000 : ℝ)*(major_s3_1) + (2748489415991/500000000000 : ℝ)*(major_s3_2) + (11305091/250000000000 : ℝ)*(sp_s3_0) + (8498767/1000000000000 : ℝ)*(sp_s3_6) + (7596372173297/1000000000000 : ℝ)*(sp_s3_7) + (3798142526813/500000000000 : ℝ)*(sp_s3_8) + (379814231513/50000000000 : ℝ)*(sp_s3_9) + (3397529609793/1000000000000 : ℝ)*(sp_s3_13) + (26468007/200000000000 : ℝ)*(sp_s3_15) + (132763401/1000000000000 : ℝ)*(sp_s3_23) + (42469226357/12500000000 : ℝ)*(f.failure) + (7596417393661/1000000000000 : ℝ)*(f.sum) + (42414304873953080649/58678558900000000000000000000000 : ℝ)*base62 + (1623796673800111/2928900000000000000000000000 : ℝ)*base64 + (986261800703789/3005150000000000000000000000 : ℝ)*base66 + (579171496026239/976300000000000000000000000 : ℝ)*base68 + (101203046303496314329/152170999500000000000000000000000 : ℝ)*base70 + (12209597284409/162359375000000000000000000 : ℝ)*base73 + (323532817081677/3005150000000000000000000000 : ℝ)*base74 + (30182921938317/2597750000000000000000000000 : ℝ)*base77 + (73844738469354546113/156132568250000000000000000000000 : ℝ)*base78 + (601/1250000000000000 : ℝ)*base87 + (601/1250000000000000 : ℝ)*base89 + (601/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4511/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4511/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12799103180816246359789996291283/1524322263824750000000000000000000000 : ℝ) := by norm_num
    linear_combination (23257/62500000000 : ℝ)*(base39) + (157350682881/1000000000000 : ℝ)*(base49) + (251517942453/1000000000000 : ℝ)*(base59) + (2693245208597/500000000000 : ℝ)*(major_s3_0) + (2693245208597/500000000000 : ℝ)*(major_s3_1) + (2693245208597/500000000000 : ℝ)*(major_s3_2) + (2364411/200000000000 : ℝ)*(sp_s3_1) + (1944351/125000000000 : ℝ)*(sp_s3_2) + (42477833/1000000000000 : ℝ)*(sp_s3_7) + (7443687433733/1000000000000 : ℝ)*(sp_s3_14) + (7443718089511/1000000000000 : ℝ)*(sp_s3_15) + (3721857178379/500000000000 : ℝ)*(sp_s3_16) + (1664590978633/500000000000 : ℝ)*(sp_s3_20) + (66166691/1000000000000 : ℝ)*(sp_s3_27) + (3329248123957/1000000000000 : ℝ)*(f.failure) + (3721864955783/500000000000 : ℝ)*(f.sum) + (5725035028950743817/58678558900000000000000000000000 : ℝ)*base63 + (818059322653237/2928900000000000000000000000 : ℝ)*base64 + (366011844182423/3005150000000000000000000000 : ℝ)*base66 + (159099297863457/976300000000000000000000000 : ℝ)*base69 + (57701761030278170443/152170999500000000000000000000000 : ℝ)*base70 + (478912377395749/1298875000000000000000000000 : ℝ)*base73 + (406123066244851/3005150000000000000000000000 : ℝ)*base75 + (132613188966057/1298875000000000000000000000 : ℝ)*base77 + (1060644154440456513/19516571031250000000000000000000 : ℝ)*base79 + (25099/100000000000000000 : ℝ)*base86 + (25099/100000000000000000 : ℝ)*base88 + (25099/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17341/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9419095574812601341344012147327/1524322263824750000000000000000000000 : ℝ) := by norm_num
    linear_combination (116549847727/500000000000 : ℝ)*(base40) + (1100884693/200000000000 : ℝ)*(base49) + (162304869173/500000000000 : ℝ)*(base59) + (2443063745457/500000000000 : ℝ)*(major_s3_0) + (2443063745457/500000000000 : ℝ)*(major_s3_1) + (2443063745457/500000000000 : ℝ)*(major_s3_2) + (2638939/200000000000 : ℝ)*(sp_s3_0) + (7330291/250000000000 : ℝ)*(sp_s3_2) + (4563883/1000000000000 : ℝ)*(sp_s3_16) + (49047383/500000000000 : ℝ)*(sp_s3_20) + (6752252774367/1000000000000 : ℝ)*(sp_s3_21) + (3376132984531/500000000000 : ℝ)*(sp_s3_22) + (1350446416803/200000000000 : ℝ)*(sp_s3_23) + (3019888858263/1000000000000 : ℝ)*(sp_s3_27) + (3019986953029/1000000000000 : ℝ)*(f.failure) + (3376132984531/500000000000 : ℝ)*(f.sum) + (1153270700379970057/58678558900000000000000000000000 : ℝ)*base63 + (81043710198201/976300000000000000000000000 : ℝ)*base65 + (1224912189354383/3005150000000000000000000000 : ℝ)*base66 + (422096985948033/976300000000000000000000000 : ℝ)*base68 + (27313255141055519589/50723666500000000000000000000000 : ℝ)*base71 + (286277570468403/649437500000000000000000000 : ℝ)*base72 + (1252002440863129/3005150000000000000000000000 : ℝ)*base74 + (938300999746191/2597750000000000000000000000 : ℝ)*base76 + (166358182542884119/39033142062500000000000000000000 : ℝ)*base78 + (20997/100000000000000000 : ℝ)*base87 + (20997/100000000000000000 : ℝ)*base89 + (20997/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (71/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((10391/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10391/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60103/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60103/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29289/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29289/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30761/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30761/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4511/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(4511/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17341/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17341/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310053_s3 p hpa hpb X hX hprev2

#print axioms solution
