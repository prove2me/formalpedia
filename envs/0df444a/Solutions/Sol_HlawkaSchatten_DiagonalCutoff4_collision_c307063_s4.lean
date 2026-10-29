-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307063_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:16:23.087411+00:00
-- url     : https://prove2.me/submissions/ffe7cb7f-6e01-4464-9517-e22ba5ef2c43

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
theorem collision_support_c307063_s4_s4_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-63024419/500000000 : ℝ)*x 0 + (692099947/1250000000 : ℝ)*x 1 + (1125954367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63024419/500000000 : ℝ)^17 ≤ (6664714781743/100000000000000 : ℝ)^13 := by
    have hnat : (63024419 : ℕ)^17*100000000000000^13 ≤ 6664714781743^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63024419 500000000 6664714781743 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692099947/1250000000 : ℝ)^17 ≤ (11539886045537/25000000000000 : ℝ)^13 := by
    have hnat : (692099947 : ℕ)^17*25000000000000^13 ≤ 11539886045537^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692099947 1250000000 11539886045537 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125954367/2000000000 : ℝ)^17 ≤ (23587870508687/50000000000000 : ℝ)^13 := by
    have hnat : (1125954367 : ℕ)^17*50000000000000^13 ≤ 23587870508687^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125954367 2000000000 23587870508687 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63024419/500000000 : ℝ), (692099947/1250000000 : ℝ), (1125954367/2000000000 : ℝ)] ![(6664714781743/100000000000000 : ℝ), (11539886045537/25000000000000 : ℝ), (23587870508687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63024419/500000000 : ℝ)|^17 ≤ (6664714781743/100000000000000 : ℝ)^13
        have hw : |(-63024419/500000000 : ℝ)|=(63024419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692099947/1250000000 : ℝ)|^17 ≤ (11539886045537/25000000000000 : ℝ)^13
        have hw : |(692099947/1250000000 : ℝ)|=(692099947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125954367/2000000000 : ℝ)|^17 ≤ (23587870508687/50000000000000 : ℝ)^13
        have hw : |(1125954367/2000000000 : ℝ)|=(1125954367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1107576209/2000000000 : ℝ)*x 0 + (-127370719/1000000000 : ℝ)*x 1 + (1124067843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1107576209/2000000000 : ℝ)^17 ≤ (23085667384237/50000000000000 : ℝ)^13 := by
    have hnat : (1107576209 : ℕ)^17*50000000000000^13 ≤ 23085667384237^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1107576209 2000000000 23085667384237 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127370719/1000000000 : ℝ)^17 ≤ (84453259023/1250000000000 : ℝ)^13 := by
    have hnat : (127370719 : ℕ)^17*1250000000000^13 ≤ 84453259023^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127370719 1000000000 84453259023 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124067843/2000000000 : ℝ)^17 ≤ (23536202247753/50000000000000 : ℝ)^13 := by
    have hnat : (1124067843 : ℕ)^17*50000000000000^13 ≤ 23536202247753^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124067843 2000000000 23536202247753 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1107576209/2000000000 : ℝ), (-127370719/1000000000 : ℝ), (1124067843/2000000000 : ℝ)] ![(23085667384237/50000000000000 : ℝ), (84453259023/1250000000000 : ℝ), (23536202247753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1107576209/2000000000 : ℝ)|^17 ≤ (23085667384237/50000000000000 : ℝ)^13
        have hw : |(1107576209/2000000000 : ℝ)|=(1107576209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127370719/1000000000 : ℝ)|^17 ≤ (84453259023/1250000000000 : ℝ)^13
        have hw : |(-127370719/1000000000 : ℝ)|=(127370719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124067843/2000000000 : ℝ)|^17 ≤ (23536202247753/50000000000000 : ℝ)^13
        have hw : |(1124067843/2000000000 : ℝ)|=(1124067843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (698177871/1250000000 : ℝ)*x 0 + (560570949/1000000000 : ℝ)*x 1 + (-610821463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (698177871/1250000000 : ℝ)^17 ≤ (11672588426553/25000000000000 : ℝ)^13 := by
    have hnat : (698177871 : ℕ)^17*25000000000000^13 ≤ 11672588426553^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698177871 1250000000 11672588426553 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (560570949/1000000000 : ℝ)^17 ≤ (11728059513291/25000000000000 : ℝ)^13 := by
    have hnat : (560570949 : ℕ)^17*25000000000000^13 ≤ 11728059513291^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560570949 1000000000 11728059513291 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (610821463/5000000000 : ℝ)^17 ≤ (3198704112589/50000000000000 : ℝ)^13 := by
    have hnat : (610821463 : ℕ)^17*50000000000000^13 ≤ 3198704112589^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610821463 5000000000 3198704112589 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(698177871/1250000000 : ℝ), (560570949/1000000000 : ℝ), (-610821463/5000000000 : ℝ)] ![(11672588426553/25000000000000 : ℝ), (11728059513291/25000000000000 : ℝ), (3198704112589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(698177871/1250000000 : ℝ)|^17 ≤ (11672588426553/25000000000000 : ℝ)^13
        have hw : |(698177871/1250000000 : ℝ)|=(698177871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(560570949/1000000000 : ℝ)|^17 ≤ (11728059513291/25000000000000 : ℝ)^13
        have hw : |(560570949/1000000000 : ℝ)|=(560570949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-610821463/5000000000 : ℝ)|^17 ≤ (3198704112589/50000000000000 : ℝ)^13
        have hw : |(-610821463/5000000000 : ℝ)|=(610821463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4402869203/10000000000 : ℝ)*x 0 + (2166493451/5000000000 : ℝ)*x 1 + (4213310701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4402869203/10000000000 : ℝ)^17 ≤ (34207081722039/100000000000000 : ℝ)^13 := by
    have hnat : (4402869203 : ℕ)^17*100000000000000^13 ≤ 34207081722039^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4402869203 10000000000 34207081722039 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2166493451/5000000000 : ℝ)^17 ≤ (33498830536787/100000000000000 : ℝ)^13 := by
    have hnat : (2166493451 : ℕ)^17*100000000000000^13 ≤ 33498830536787^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166493451 5000000000 33498830536787 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4213310701/10000000000 : ℝ)^17 ≤ (16147043860803/50000000000000 : ℝ)^13 := by
    have hnat : (4213310701 : ℕ)^17*50000000000000^13 ≤ 16147043860803^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4213310701 10000000000 16147043860803 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4402869203/10000000000 : ℝ), (2166493451/5000000000 : ℝ), (4213310701/10000000000 : ℝ)] ![(34207081722039/100000000000000 : ℝ), (33498830536787/100000000000000 : ℝ), (16147043860803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4402869203/10000000000 : ℝ)|^17 ≤ (34207081722039/100000000000000 : ℝ)^13
        have hw : |(4402869203/10000000000 : ℝ)|=(4402869203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2166493451/5000000000 : ℝ)|^17 ≤ (33498830536787/100000000000000 : ℝ)^13
        have hw : |(2166493451/5000000000 : ℝ)|=(2166493451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4213310701/10000000000 : ℝ)|^17 ≤ (16147043860803/50000000000000 : ℝ)^13
        have hw : |(4213310701/10000000000 : ℝ)|=(4213310701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-197228109/2000000000 : ℝ)*x 0 + (896476733/2000000000 : ℝ)*x 1 + (3389527291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197228109/2000000000 : ℝ)^17 ≤ (4834833553787/100000000000000 : ℝ)^13 := by
    have hnat : (197228109 : ℕ)^17*100000000000000^13 ≤ 4834833553787^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197228109 2000000000 4834833553787 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896476733/2000000000 : ℝ)^17 ≤ (2188573076843/6250000000000 : ℝ)^13 := by
    have hnat : (896476733 : ℕ)^17*6250000000000^13 ≤ 2188573076843^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896476733 2000000000 2188573076843 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3389527291/5000000000 : ℝ)^17 ≤ (60147997206149/100000000000000 : ℝ)^13 := by
    have hnat : (3389527291 : ℕ)^17*100000000000000^13 ≤ 60147997206149^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3389527291 5000000000 60147997206149 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197228109/2000000000 : ℝ), (896476733/2000000000 : ℝ), (3389527291/5000000000 : ℝ)] ![(4834833553787/100000000000000 : ℝ), (2188573076843/6250000000000 : ℝ), (60147997206149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197228109/2000000000 : ℝ)|^17 ≤ (4834833553787/100000000000000 : ℝ)^13
        have hw : |(-197228109/2000000000 : ℝ)|=(197228109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896476733/2000000000 : ℝ)|^17 ≤ (2188573076843/6250000000000 : ℝ)^13
        have hw : |(896476733/2000000000 : ℝ)|=(896476733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3389527291/5000000000 : ℝ)|^17 ≤ (60147997206149/100000000000000 : ℝ)^13
        have hw : |(3389527291/5000000000 : ℝ)|=(3389527291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (971829473/2000000000 : ℝ)*x 0 + (-30648643/1000000000 : ℝ)*x 1 + (3384708681/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (971829473/2000000000 : ℝ)^17 ≤ (7782999644587/20000000000000 : ℝ)^13 := by
    have hnat : (971829473 : ℕ)^17*20000000000000^13 ≤ 7782999644587^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971829473 2000000000 7782999644587 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30648643/1000000000 : ℝ)^17 ≤ (65549842503/6250000000000 : ℝ)^13 := by
    have hnat : (30648643 : ℕ)^17*6250000000000^13 ≤ 65549842503^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30648643 1000000000 65549842503 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3384708681/5000000000 : ℝ)^17 ≤ (7504525533957/12500000000000 : ℝ)^13 := by
    have hnat : (3384708681 : ℕ)^17*12500000000000^13 ≤ 7504525533957^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3384708681 5000000000 7504525533957 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(971829473/2000000000 : ℝ), (-30648643/1000000000 : ℝ), (3384708681/5000000000 : ℝ)] ![(7782999644587/20000000000000 : ℝ), (65549842503/6250000000000 : ℝ), (7504525533957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(971829473/2000000000 : ℝ)|^17 ≤ (7782999644587/20000000000000 : ℝ)^13
        have hw : |(971829473/2000000000 : ℝ)|=(971829473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30648643/1000000000 : ℝ)|^17 ≤ (65549842503/6250000000000 : ℝ)^13
        have hw : |(-30648643/1000000000 : ℝ)|=(30648643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3384708681/5000000000 : ℝ)|^17 ≤ (7504525533957/12500000000000 : ℝ)^13
        have hw : |(3384708681/5000000000 : ℝ)|=(3384708681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1149257567/2500000000 : ℝ)*x 0 + (7033721919/10000000000 : ℝ)*x 1 + (-4436839/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1149257567/2500000000 : ℝ)^17 ≤ (36192971786201/100000000000000 : ℝ)^13 := by
    have hnat : (1149257567 : ℕ)^17*100000000000000^13 ≤ 36192971786201^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149257567 2500000000 36192971786201 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7033721919/10000000000 : ℝ)^17 ≤ (63119747677559/100000000000000 : ℝ)^13 := by
    have hnat : (7033721919 : ℕ)^17*100000000000000^13 ≤ 63119747677559^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7033721919 10000000000 63119747677559 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4436839/200000000 : ℝ)^17 ≤ (343640260541/50000000000000 : ℝ)^13 := by
    have hnat : (4436839 : ℕ)^17*50000000000000^13 ≤ 343640260541^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436839 200000000 343640260541 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1149257567/2500000000 : ℝ), (7033721919/10000000000 : ℝ), (-4436839/200000000 : ℝ)] ![(36192971786201/100000000000000 : ℝ), (63119747677559/100000000000000 : ℝ), (343640260541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1149257567/2500000000 : ℝ)|^17 ≤ (36192971786201/100000000000000 : ℝ)^13
        have hw : |(1149257567/2500000000 : ℝ)|=(1149257567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7033721919/10000000000 : ℝ)|^17 ≤ (63119747677559/100000000000000 : ℝ)^13
        have hw : |(7033721919/10000000000 : ℝ)|=(7033721919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4436839/200000000 : ℝ)|^17 ≤ (343640260541/50000000000000 : ℝ)^13
        have hw : |(-4436839/200000000 : ℝ)|=(4436839/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4421530029/10000000000 : ℝ)*x 0 + (384764131/625000000 : ℝ)*x 1 + (2048559543/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4421530029/10000000000 : ℝ)^17 ≤ (537449933883/1562500000000 : ℝ)^13 := by
    have hnat : (4421530029 : ℕ)^17*1562500000000^13 ≤ 537449933883^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421530029 10000000000 537449933883 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384764131/625000000 : ℝ)^17 ≤ (424207419091/800000000000 : ℝ)^13 := by
    have hnat : (384764131 : ℕ)^17*800000000000^13 ≤ 424207419091^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384764131 625000000 424207419091 800000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2048559543/10000000000 : ℝ)^17 ≤ (12577276823573/100000000000000 : ℝ)^13 := by
    have hnat : (2048559543 : ℕ)^17*100000000000000^13 ≤ 12577276823573^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048559543 10000000000 12577276823573 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4421530029/10000000000 : ℝ), (384764131/625000000 : ℝ), (2048559543/10000000000 : ℝ)] ![(537449933883/1562500000000 : ℝ), (424207419091/800000000000 : ℝ), (12577276823573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4421530029/10000000000 : ℝ)|^17 ≤ (537449933883/1562500000000 : ℝ)^13
        have hw : |(4421530029/10000000000 : ℝ)|=(4421530029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(384764131/625000000 : ℝ)|^17 ≤ (424207419091/800000000000 : ℝ)^13
        have hw : |(384764131/625000000 : ℝ)|=(384764131/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2048559543/10000000000 : ℝ)|^17 ≤ (12577276823573/100000000000000 : ℝ)^13
        have hw : |(2048559543/10000000000 : ℝ)|=(2048559543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-69649107/2500000000 : ℝ)*x 0 + (4875839099/10000000000 : ℝ)*x 1 + (6764943467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69649107/2500000000 : ℝ)^17 ≤ (57861074951/6250000000000 : ℝ)^13 := by
    have hnat : (69649107 : ℕ)^17*6250000000000^13 ≤ 57861074951^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69649107 2500000000 57861074951 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4875839099/10000000000 : ℝ)^17 ≤ (39089899605451/100000000000000 : ℝ)^13 := by
    have hnat : (4875839099 : ℕ)^17*100000000000000^13 ≤ 39089899605451^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4875839099 10000000000 39089899605451 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6764943467/10000000000 : ℝ)^17 ≤ (59984323177651/100000000000000 : ℝ)^13 := by
    have hnat : (6764943467 : ℕ)^17*100000000000000^13 ≤ 59984323177651^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6764943467 10000000000 59984323177651 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69649107/2500000000 : ℝ), (4875839099/10000000000 : ℝ), (6764943467/10000000000 : ℝ)] ![(57861074951/6250000000000 : ℝ), (39089899605451/100000000000000 : ℝ), (59984323177651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69649107/2500000000 : ℝ)|^17 ≤ (57861074951/6250000000000 : ℝ)^13
        have hw : |(-69649107/2500000000 : ℝ)|=(69649107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4875839099/10000000000 : ℝ)|^17 ≤ (39089899605451/100000000000000 : ℝ)^13
        have hw : |(4875839099/10000000000 : ℝ)|=(4875839099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6764943467/10000000000 : ℝ)|^17 ≤ (59984323177651/100000000000000 : ℝ)^13
        have hw : |(6764943467/10000000000 : ℝ)|=(6764943467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (282337771/625000000 : ℝ)*x 0 + (-973200493/10000000000 : ℝ)*x 1 + (3377652801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (282337771/625000000 : ℝ)^17 ≤ (17687683471347/50000000000000 : ℝ)^13 := by
    have hnat : (282337771 : ℕ)^17*50000000000000^13 ≤ 17687683471347^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282337771 625000000 17687683471347 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (973200493/10000000000 : ℝ)^17 ≤ (9504077147/200000000000 : ℝ)^13 := by
    have hnat : (973200493 : ℕ)^17*200000000000^13 ≤ 9504077147^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973200493 10000000000 9504077147 200000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3377652801/5000000000 : ℝ)^17 ≤ (59872594471861/100000000000000 : ℝ)^13 := by
    have hnat : (3377652801 : ℕ)^17*100000000000000^13 ≤ 59872594471861^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3377652801 5000000000 59872594471861 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(282337771/625000000 : ℝ), (-973200493/10000000000 : ℝ), (3377652801/5000000000 : ℝ)] ![(17687683471347/50000000000000 : ℝ), (9504077147/200000000000 : ℝ), (59872594471861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(282337771/625000000 : ℝ)|^17 ≤ (17687683471347/50000000000000 : ℝ)^13
        have hw : |(282337771/625000000 : ℝ)|=(282337771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-973200493/10000000000 : ℝ)|^17 ≤ (9504077147/200000000000 : ℝ)^13
        have hw : |(-973200493/10000000000 : ℝ)|=(973200493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3377652801/5000000000 : ℝ)|^17 ≤ (59872594471861/100000000000000 : ℝ)^13
        have hw : |(3377652801/5000000000 : ℝ)|=(3377652801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (419792181/625000000 : ℝ)*x 0 + (197850143/400000000 : ℝ)*x 1 + (-235952277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419792181/625000000 : ℝ)^17 ≤ (59425253647633/100000000000000 : ℝ)^13 := by
    have hnat : (419792181 : ℕ)^17*100000000000000^13 ≤ 59425253647633^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419792181 625000000 59425253647633 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197850143/400000000 : ℝ)^17 ≤ (19914874526259/50000000000000 : ℝ)^13 := by
    have hnat : (197850143 : ℕ)^17*50000000000000^13 ≤ 19914874526259^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197850143 400000000 19914874526259 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235952277/10000000000 : ℝ)^17 ≤ (93124660067/12500000000000 : ℝ)^13 := by
    have hnat : (235952277 : ℕ)^17*12500000000000^13 ≤ 93124660067^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235952277 10000000000 93124660067 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419792181/625000000 : ℝ), (197850143/400000000 : ℝ), (-235952277/10000000000 : ℝ)] ![(59425253647633/100000000000000 : ℝ), (19914874526259/50000000000000 : ℝ), (93124660067/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419792181/625000000 : ℝ)|^17 ≤ (59425253647633/100000000000000 : ℝ)^13
        have hw : |(419792181/625000000 : ℝ)|=(419792181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197850143/400000000 : ℝ)|^17 ≤ (19914874526259/50000000000000 : ℝ)^13
        have hw : |(197850143/400000000 : ℝ)|=(197850143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235952277/10000000000 : ℝ)|^17 ≤ (93124660067/12500000000000 : ℝ)^13
        have hw : |(-235952277/10000000000 : ℝ)|=(235952277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6809825901/10000000000 : ℝ)*x 0 + (3640623587/10000000000 : ℝ)*x 1 + (519579959/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6809825901/10000000000 : ℝ)^17 ≤ (60505275459017/100000000000000 : ℝ)^13 := by
    have hnat : (6809825901 : ℕ)^17*100000000000000^13 ≤ 60505275459017^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6809825901 10000000000 60505275459017 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3640623587/10000000000 : ℝ)^17 ≤ (166737374409/625000000000 : ℝ)^13 := by
    have hnat : (3640623587 : ℕ)^17*625000000000^13 ≤ 166737374409^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3640623587 10000000000 166737374409 625000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519579959/2500000000 : ℝ)^17 ≤ (6408372314151/50000000000000 : ℝ)^13 := by
    have hnat : (519579959 : ℕ)^17*50000000000000^13 ≤ 6408372314151^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519579959 2500000000 6408372314151 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6809825901/10000000000 : ℝ), (3640623587/10000000000 : ℝ), (519579959/2500000000 : ℝ)] ![(60505275459017/100000000000000 : ℝ), (166737374409/625000000000 : ℝ), (6408372314151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6809825901/10000000000 : ℝ)|^17 ≤ (60505275459017/100000000000000 : ℝ)^13
        have hw : |(6809825901/10000000000 : ℝ)|=(6809825901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3640623587/10000000000 : ℝ)|^17 ≤ (166737374409/625000000000 : ℝ)^13
        have hw : |(3640623587/10000000000 : ℝ)|=(3640623587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519579959/2500000000 : ℝ)|^17 ≤ (6408372314151/50000000000000 : ℝ)^13
        have hw : |(519579959/2500000000 : ℝ)|=(519579959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-56818911/2500000000 : ℝ)*x 0 + (3163541357/5000000000 : ℝ)*x 1 + (5368378381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56818911/2500000000 : ℝ)^17 ≤ (354688305663/50000000000000 : ℝ)^13 := by
    have hnat : (56818911 : ℕ)^17*50000000000000^13 ≤ 354688305663^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56818911 2500000000 354688305663 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3163541357/5000000000 : ℝ)^17 ≤ (54958562136031/100000000000000 : ℝ)^13 := by
    have hnat : (3163541357 : ℕ)^17*100000000000000^13 ≤ 54958562136031^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3163541357 5000000000 54958562136031 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5368378381/10000000000 : ℝ)^17 ≤ (44332061241989/100000000000000 : ℝ)^13 := by
    have hnat : (5368378381 : ℕ)^17*100000000000000^13 ≤ 44332061241989^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368378381 10000000000 44332061241989 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56818911/2500000000 : ℝ), (3163541357/5000000000 : ℝ), (5368378381/10000000000 : ℝ)] ![(354688305663/50000000000000 : ℝ), (54958562136031/100000000000000 : ℝ), (44332061241989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56818911/2500000000 : ℝ)|^17 ≤ (354688305663/50000000000000 : ℝ)^13
        have hw : |(-56818911/2500000000 : ℝ)|=(56818911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3163541357/5000000000 : ℝ)|^17 ≤ (54958562136031/100000000000000 : ℝ)^13
        have hw : |(3163541357/5000000000 : ℝ)|=(3163541357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5368378381/10000000000 : ℝ)|^17 ≤ (44332061241989/100000000000000 : ℝ)^13
        have hw : |(5368378381/10000000000 : ℝ)|=(5368378381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6719417403/10000000000 : ℝ)*x 0 + (-221953237/10000000000 : ℝ)*x 1 + (618584777/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6719417403/10000000000 : ℝ)^17 ≤ (59456985637571/100000000000000 : ℝ)^13 := by
    have hnat : (6719417403 : ℕ)^17*100000000000000^13 ≤ 59456985637571^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6719417403 10000000000 59456985637571 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221953237/10000000000 : ℝ)^17 ≤ (687731414481/100000000000000 : ℝ)^13 := by
    have hnat : (221953237 : ℕ)^17*100000000000000^13 ≤ 687731414481^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221953237 10000000000 687731414481 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (618584777/1250000000 : ℝ)^17 ≤ (39855282940813/100000000000000 : ℝ)^13 := by
    have hnat : (618584777 : ℕ)^17*100000000000000^13 ≤ 39855282940813^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618584777 1250000000 39855282940813 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6719417403/10000000000 : ℝ), (-221953237/10000000000 : ℝ), (618584777/1250000000 : ℝ)] ![(59456985637571/100000000000000 : ℝ), (687731414481/100000000000000 : ℝ), (39855282940813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6719417403/10000000000 : ℝ)|^17 ≤ (59456985637571/100000000000000 : ℝ)^13
        have hw : |(6719417403/10000000000 : ℝ)|=(6719417403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-221953237/10000000000 : ℝ)|^17 ≤ (687731414481/100000000000000 : ℝ)^13
        have hw : |(-221953237/10000000000 : ℝ)|=(221953237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(618584777/1250000000 : ℝ)|^17 ≤ (39855282940813/100000000000000 : ℝ)^13
        have hw : |(618584777/1250000000 : ℝ)|=(618584777/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (280708427/625000000 : ℝ)*x 0 + (3403779713/5000000000 : ℝ)*x 1 + (-229887873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280708427/625000000 : ℝ)^17 ≤ (35108641736377/100000000000000 : ℝ)^13 := by
    have hnat : (280708427 : ℕ)^17*100000000000000^13 ≤ 35108641736377^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280708427 625000000 35108641736377 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3403779713/5000000000 : ℝ)^17 ≤ (60478942995217/100000000000000 : ℝ)^13 := by
    have hnat : (3403779713 : ℕ)^17*100000000000000^13 ≤ 60478942995217^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3403779713 5000000000 60478942995217 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (229887873/2500000000 : ℝ)^17 ≤ (4412415256029/100000000000000 : ℝ)^13 := by
    have hnat : (229887873 : ℕ)^17*100000000000000^13 ≤ 4412415256029^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229887873 2500000000 4412415256029 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280708427/625000000 : ℝ), (3403779713/5000000000 : ℝ), (-229887873/2500000000 : ℝ)] ![(35108641736377/100000000000000 : ℝ), (60478942995217/100000000000000 : ℝ), (4412415256029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280708427/625000000 : ℝ)|^17 ≤ (35108641736377/100000000000000 : ℝ)^13
        have hw : |(280708427/625000000 : ℝ)|=(280708427/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3403779713/5000000000 : ℝ)|^17 ≤ (60478942995217/100000000000000 : ℝ)^13
        have hw : |(3403779713/5000000000 : ℝ)|=(3403779713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-229887873/2500000000 : ℝ)|^17 ≤ (4412415256029/100000000000000 : ℝ)^13
        have hw : |(-229887873/2500000000 : ℝ)|=(229887873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307063_s4_s4_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (435453431/625000000 : ℝ)*x 0 + (1460537767/5000000000 : ℝ)*x 1 + (663799387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435453431/625000000 : ℝ)^17 ≤ (62340889057413/100000000000000 : ℝ)^13 := by
    have hnat : (435453431 : ℕ)^17*100000000000000^13 ≤ 62340889057413^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435453431 625000000 62340889057413 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1460537767/5000000000 : ℝ)^17 ≤ (800118671887/4000000000000 : ℝ)^13 := by
    have hnat : (1460537767 : ℕ)^17*4000000000000^13 ≤ 800118671887^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460537767 5000000000 800118671887 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (663799387/2500000000 : ℝ)^17 ≤ (8828072067827/50000000000000 : ℝ)^13 := by
    have hnat : (663799387 : ℕ)^17*50000000000000^13 ≤ 8828072067827^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663799387 2500000000 8828072067827 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435453431/625000000 : ℝ), (1460537767/5000000000 : ℝ), (663799387/2500000000 : ℝ)] ![(62340889057413/100000000000000 : ℝ), (800118671887/4000000000000 : ℝ), (8828072067827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435453431/625000000 : ℝ)|^17 ≤ (62340889057413/100000000000000 : ℝ)^13
        have hw : |(435453431/625000000 : ℝ)|=(435453431/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1460537767/5000000000 : ℝ)|^17 ≤ (800118671887/4000000000000 : ℝ)^13
        have hw : |(1460537767/5000000000 : ℝ)|=(1460537767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(663799387/2500000000 : ℝ)|^17 ≤ (8828072067827/50000000000000 : ℝ)^13
        have hw : |(663799387/2500000000 : ℝ)|=(663799387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307063_s4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((6499/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6499/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1641/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1641/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15757/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15757/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((50751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10323/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10323/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49329/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(49329/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (6499/10000 : ℝ) ^ (135/32 : ℝ) ≤ (16234777010162392753/100000000000000000000 : ℝ) := by
    have hpowers : (6499/10000 : ℝ)^135 ≤ (16234777010162392753/100000000000000000000 : ℝ)^32 := by
      have hnat : (6499 : ℕ)^135*100000000000000000000^32 ≤ 16234777010162392753^32*10000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6499 10000 16234777010162392753 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6499/10000 : ℝ)) (X := (16234777010162392753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner0a : (116234777010162392753/100000000000000000000 : ℝ) ≤ (10363037564749889/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (116234777010162392753/100000000000000000000 : ℝ)^32 ≤ (10363037564749889/10000000000000000 : ℝ)^135 := by
      have hnat : (116234777010162392753 : ℕ)^32*10000000000000000^135 ≤ 10363037564749889^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116234777010162392753 100000000000000000000 10363037564749889 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10363037564749889/10000000000000000 : ℝ)) (X := (116234777010162392753/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner0b : (66234777010162392753/50000000000000000000 : ℝ) ≤ (5344610206926917/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (66234777010162392753/50000000000000000000 : ℝ)^32 ≤ (5344610206926917/5000000000000000 : ℝ)^135 := by
      have hnat : (66234777010162392753 : ℕ)^32*5000000000000000^135 ≤ 5344610206926917^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66234777010162392753 50000000000000000000 5344610206926917 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5344610206926917/5000000000000000 : ℝ)) (X := (66234777010162392753/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(363037564749889/6499000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(65236569820789/1299800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (6499/10000 : ℝ)) (alpha := (363037564749889/6499000000000000 : ℝ)) (beta := (65236569820789/1299800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6499/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(363037564749889/6499000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(65236569820789/1299800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (1641/2500 : ℝ) ^ (135/32 : ℝ) ≤ (8465447468165888011/50000000000000000000 : ℝ) := by
    have hpowers : (1641/2500 : ℝ)^135 ≤ (8465447468165888011/50000000000000000000 : ℝ)^32 := by
      have hnat : (1641 : ℕ)^135*50000000000000000000^32 ≤ 8465447468165888011^32*2500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1641 2500 8465447468165888011 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1641/2500 : ℝ)) (X := (8465447468165888011/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner1a : (58465447468165888011/50000000000000000000 : ℝ) ≤ (10377715337232503/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (58465447468165888011/50000000000000000000 : ℝ)^32 ≤ (10377715337232503/10000000000000000 : ℝ)^135 := by
      have hnat : (58465447468165888011 : ℕ)^32*10000000000000000^135 ≤ 10377715337232503^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58465447468165888011 50000000000000000000 10377715337232503 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10377715337232503/10000000000000000 : ℝ)) (X := (58465447468165888011/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner1b : (33465447468165888011/25000000000000000000 : ℝ) ≤ (10715743556284353/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (33465447468165888011/25000000000000000000 : ℝ)^32 ≤ (10715743556284353/10000000000000000 : ℝ)^135 := by
      have hnat : (33465447468165888011 : ℕ)^32*10000000000000000^135 ≤ 10715743556284353^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33465447468165888011 25000000000000000000 10715743556284353 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10715743556284353/10000000000000000 : ℝ)) (X := (33465447468165888011/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(377715337232503/6564000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(6760564381037/131280000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1641/2500 : ℝ)) (alpha := (377715337232503/6564000000000000 : ℝ)) (beta := (6760564381037/131280000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1641/2500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(377715337232503/6564000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(6760564381037/131280000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (15757/25000 : ℝ) ^ (135/32 : ℝ) ≤ (7132668968118999283/50000000000000000000 : ℝ) := by
    have hpowers : (15757/25000 : ℝ)^135 ≤ (7132668968118999283/50000000000000000000 : ℝ)^32 := by
      have hnat : (15757 : ℕ)^135*50000000000000000000^32 ≤ 7132668968118999283^32*25000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15757 25000 7132668968118999283 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15757/25000 : ℝ)) (X := (7132668968118999283/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner2a : (57132668968118999283/50000000000000000000 : ℝ) ≤ (10321145096148571/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (57132668968118999283/50000000000000000000 : ℝ)^32 ≤ (10321145096148571/10000000000000000 : ℝ)^135 := by
      have hnat : (57132668968118999283 : ℕ)^32*10000000000000000^135 ≤ 10321145096148571^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57132668968118999283 50000000000000000000 10321145096148571 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10321145096148571/10000000000000000 : ℝ)) (X := (57132668968118999283/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s4_corner2b : (32132668968118999283/25000000000000000000 : ℝ) ≤ (663313237074011/625000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (32132668968118999283/25000000000000000000 : ℝ)^32 ≤ (663313237074011/625000000000000 : ℝ)^135 := by
      have hnat : (32132668968118999283 : ℕ)^32*625000000000000^135 ≤ 663313237074011^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32132668968118999283 25000000000000000000 663313237074011 625000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (663313237074011/625000000000000 : ℝ)) (X := (32132668968118999283/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(321145096148571/6302800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(58373339407121/1260560000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (15757/25000 : ℝ)) (alpha := (321145096148571/6302800000000000 : ℝ)) (beta := (58373339407121/1260560000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15757/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(321145096148571/6302800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(58373339407121/1260560000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-63024419/500000000 : ℝ)*X 0 0+(692099947/1250000000 : ℝ)*X 0 1+(1125954367/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((1107576209/2000000000 : ℝ)*X 1 0+(-127370719/1000000000 : ℝ)*X 1 1+(1124067843/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((698177871/1250000000 : ℝ)*X 2 0+(560570949/1000000000 : ℝ)*X 2 1+(-610821463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((4402869203/10000000000 : ℝ)*X 0 0+(2166493451/5000000000 : ℝ)*X 0 1+(4213310701/10000000000 : ℝ)*X 0 2+(4402869203/10000000000 : ℝ)*X 1 0+(2166493451/5000000000 : ℝ)*X 1 1+(4213310701/10000000000 : ℝ)*X 1 2+(4402869203/10000000000 : ℝ)*X 2 0+(2166493451/5000000000 : ℝ)*X 2 1+(4213310701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-197228109/2000000000 : ℝ)*X 0 0+(896476733/2000000000 : ℝ)*X 0 1+(3389527291/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((971829473/2000000000 : ℝ)*X 1 0+(-30648643/1000000000 : ℝ)*X 1 1+(3384708681/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((1149257567/2500000000 : ℝ)*X 2 0+(7033721919/10000000000 : ℝ)*X 2 1+(-4436839/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((4421530029/10000000000 : ℝ)*X 0 0+(384764131/625000000 : ℝ)*X 0 1+(2048559543/10000000000 : ℝ)*X 0 2+(4421530029/10000000000 : ℝ)*X 1 0+(384764131/625000000 : ℝ)*X 1 1+(2048559543/10000000000 : ℝ)*X 1 2+(4421530029/10000000000 : ℝ)*X 2 0+(384764131/625000000 : ℝ)*X 2 1+(2048559543/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-69649107/2500000000 : ℝ)*X 0 0+(4875839099/10000000000 : ℝ)*X 0 1+(6764943467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((282337771/625000000 : ℝ)*X 1 0+(-973200493/10000000000 : ℝ)*X 1 1+(3377652801/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((419792181/625000000 : ℝ)*X 2 0+(197850143/400000000 : ℝ)*X 2 1+(-235952277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((6809825901/10000000000 : ℝ)*X 0 0+(3640623587/10000000000 : ℝ)*X 0 1+(519579959/2500000000 : ℝ)*X 0 2+(6809825901/10000000000 : ℝ)*X 1 0+(3640623587/10000000000 : ℝ)*X 1 1+(519579959/2500000000 : ℝ)*X 1 2+(6809825901/10000000000 : ℝ)*X 2 0+(3640623587/10000000000 : ℝ)*X 2 1+(519579959/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-56818911/2500000000 : ℝ)*X 0 0+(3163541357/5000000000 : ℝ)*X 0 1+(5368378381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((6719417403/10000000000 : ℝ)*X 1 0+(-221953237/10000000000 : ℝ)*X 1 1+(618584777/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((280708427/625000000 : ℝ)*X 2 0+(3403779713/5000000000 : ℝ)*X 2 1+(-229887873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((435453431/625000000 : ℝ)*X 0 0+(1460537767/5000000000 : ℝ)*X 0 1+(663799387/2500000000 : ℝ)*X 0 2+(435453431/625000000 : ℝ)*X 1 0+(1460537767/5000000000 : ℝ)*X 1 1+(663799387/2500000000 : ℝ)*X 1 2+(435453431/625000000 : ℝ)*X 2 0+(1460537767/5000000000 : ℝ)*X 2 1+(663799387/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307063_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((50751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (34164651481411219241989241181/7001924302625000000000000000000000 : ℝ) := by norm_num
    linear_combination (18891/6250000000 : ℝ)*(base23) + (370587/1000000000000 : ℝ)*(base50) + (143164157279/1000000000000 : ℝ)*(base60) + (424543415193/125000000000 : ℝ)*(major_s4_0) + (424543415193/125000000000 : ℝ)*(major_s4_1) + (424543415193/125000000000 : ℝ)*(major_s4_2) + (4078703/1000000000000 : ℝ)*(sp_s4_6) + (4607801676217/1000000000000 : ℝ)*(sp_s4_7) + (921558195911/200000000000 : ℝ)*(sp_s4_8) + (18431177029/4000000000 : ℝ)*(sp_s4_9) + (1092436371417/500000000000 : ℝ)*(sp_s4_13) + (14518879/1000000000000 : ℝ)*(sp_s4_14) + (1260777/50000000000 : ℝ)*(sp_s4_15) + (3783057/200000000000 : ℝ)*(sp_s4_23) + (2184876821537/1000000000000 : ℝ)*(f.failure) + (575977024387/125000000000 : ℝ)*(f.sum) + (2725897965173862911/4309539500000000000000000000000 : ℝ)*base63 + (85709810100881/157570000000000000000000000 : ℝ)*base65 + (459951067197/5470000000000000000000000 : ℝ)*base66 + (726154405979853/787850000000000000000000000 : ℝ)*base69 + (7451217907134721753/25601185750000000000000000000000 : ℝ)*base71 + (308980509180329/324950000000000000000000000 : ℝ)*base73 + (393789966862443/273500000000000000000000000 : ℝ)*base75 + (410425802508851/406187500000000000000000000 : ℝ)*base77 + (22028875728554811/88873825000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (14553/12500000000000000 : ℝ)*base86 + (14553/12500000000000000 : ℝ)*base88 + (14553/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10323/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10323/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (112829507158317716524356664329/8002199203000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5075179/500000000000 : ℝ)*(base21) + (15161/250000000000 : ℝ)*(base39) + (30911/125000000000 : ℝ)*(base60) + (1713602557821/500000000000 : ℝ)*(major_s4_0) + (1713602557821/500000000000 : ℝ)*(major_s4_1) + (1713602557821/500000000000 : ℝ)*(major_s4_2) + (38947969/1000000000000 : ℝ)*(sp_s4_2) + (64451859/1000000000000 : ℝ)*(sp_s4_7) + (2103297/50000000000 : ℝ)*(sp_s4_8) + (4649613379133/1000000000000 : ℝ)*(sp_s4_14) + (1162408941263/250000000000 : ℝ)*(sp_s4_15) + (929925746533/200000000000 : ℝ)*(sp_s4_16) + (2204673851323/1000000000000 : ℝ)*(sp_s4_20) + (13462257/250000000000 : ℝ)*(sp_s4_27) + (2204727700351/1000000000000 : ℝ)*(f.failure) + (290604864437/62500000000 : ℝ)*(f.sum) + (878807037254604881/2462594000000000000000000000000 : ℝ)*base63 + (18510260524057/90040000000000000000000000 : ℝ)*base64 + (694367291689/21880000000000000000000000 : ℝ)*base66 + (111866437120453/450200000000000000000000000 : ℝ)*base69 + (1565381998486860637/14629249000000000000000000000000 : ℝ)*base70 + (102670411180329/649900000000000000000000000 : ℝ)*base73 + (163426671721121/1094000000000000000000000000 : ℝ)*base75 + (409798614531231/3249500000000000000000000000 : ℝ)*base76 + (198296759031872111/710990600000000000000000000000 : ℝ)*base79 + (4719/12500000000000000 : ℝ)*base86 + (4719/12500000000000000 : ℝ)*base88 + (4719/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49329/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(49329/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24628187684269180061752643/1777476500000000000000000000000 : ℝ) := by norm_num
    linear_combination (9493529/1000000000000 : ℝ)*(base15) + (180119593743/1000000000000 : ℝ)*(base40) + (1618795337321/500000000000 : ℝ)*(major_s4_0) + (1618795337321/500000000000 : ℝ)*(major_s4_1) + (1618795337321/500000000000 : ℝ)*(major_s4_2) + (12623887/200000000000 : ℝ)*(sp_s4_0) + (26760689/500000000000 : ℝ)*(sp_s4_1) + (791813/25000000000 : ℝ)*(sp_s4_2) + (30044929/500000000000 : ℝ)*(sp_s4_9) + (22220973/200000000000 : ℝ)*(sp_s4_20) + (1098091312177/250000000000 : ℝ)*(sp_s4_21) + (4392365353237/1000000000000 : ℝ)*(sp_s4_22) + (2196168302883/500000000000 : ℝ)*(sp_s4_23) + (2082637257701/1000000000000 : ℝ)*(sp_s4_27) + (1041374181283/500000000000 : ℝ)*(f.failure) + (4392428368143/1000000000000 : ℝ)*(f.sum) + (8710928751610352201/51714474000000000000000000000000 : ℝ)*base63 + (204252555647333/630280000000000000000000000 : ℝ)*base65 + (17493175572673/65640000000000000000000000 : ℝ)*base67 + (1039621828849189/3151400000000000000000000000 : ℝ)*base68 + (32036467677406511859/102404743000000000000000000000000 : ℝ)*base70 + (197624956043769/649900000000000000000000000 : ℝ)*base73 + (417474888126937/3282000000000000000000000000 : ℝ)*base74 + (2412188312432281/3249500000000000000000000000 : ℝ)*base76 + (1086353803807412693/2132971800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (2527/6250000000000000 : ℝ)*base86 + (2527/6250000000000000 : ℝ)*base88 + (2527/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev3 : (0 : ℝ) ≤ ((6499/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6499/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1641/2500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(1641/2500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15757/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15757/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((50751/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50751/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10323/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(10323/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(49329/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(49329/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307063_s4 p hpa hpb X hX hprev3

#print axioms solution
