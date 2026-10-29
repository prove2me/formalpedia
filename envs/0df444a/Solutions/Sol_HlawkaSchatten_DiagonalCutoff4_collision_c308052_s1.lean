-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308052_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:36:13.486096+00:00
-- url     : https://prove2.me/submissions/bc0558ee-e649-46af-a66d-ef094354ba13

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
theorem collision_support_c308052_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-782240149/5000000000 : ℝ)*x 0 + (844830447/2500000000 : ℝ)*x 1 + (-3648584859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (782240149/5000000000 : ℝ)^35 ≤ (564345361211/6250000000000 : ℝ)^27 := by
    have hnat : (782240149 : ℕ)^35*6250000000000^27 ≤ 564345361211^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782240149 5000000000 564345361211 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (844830447/2500000000 : ℝ)^35 ≤ (49006477167/200000000000 : ℝ)^27 := by
    have hnat : (844830447 : ℕ)^35*200000000000^27 ≤ 49006477167^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844830447 2500000000 49006477167 200000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3648584859/5000000000 : ℝ)^35 ≤ (16616808903857/25000000000000 : ℝ)^27 := by
    have hnat : (3648584859 : ℕ)^35*25000000000000^27 ≤ 16616808903857^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648584859 5000000000 16616808903857 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-782240149/5000000000 : ℝ), (844830447/2500000000 : ℝ), (-3648584859/5000000000 : ℝ)] ![(564345361211/6250000000000 : ℝ), (49006477167/200000000000 : ℝ), (16616808903857/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-782240149/5000000000 : ℝ)|^35 ≤ (564345361211/6250000000000 : ℝ)^27
        have hw : |(-782240149/5000000000 : ℝ)|=(782240149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(844830447/2500000000 : ℝ)|^35 ≤ (49006477167/200000000000 : ℝ)^27
        have hw : |(844830447/2500000000 : ℝ)|=(844830447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3648584859/5000000000 : ℝ)|^35 ≤ (16616808903857/25000000000000 : ℝ)^27
        have hw : |(-3648584859/5000000000 : ℝ)|=(3648584859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1173854811/2500000000 : ℝ)*x 0 + (-292287073/1000000000 : ℝ)*x 1 + (-40131409/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1173854811/2500000000 : ℝ)^35 ≤ (586425349131/1562500000000 : ℝ)^27 := by
    have hnat : (1173854811 : ℕ)^35*1562500000000^27 ≤ 586425349131^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1173854811 2500000000 586425349131 1562500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (292287073/1000000000 : ℝ)^35 ≤ (406032660931/2000000000000 : ℝ)^27 := by
    have hnat : (292287073 : ℕ)^35*2000000000000^27 ≤ 406032660931^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      292287073 1000000000 406032660931 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40131409/78125000 : ℝ)^35 ≤ (21083572296729/50000000000000 : ℝ)^27 := by
    have hnat : (40131409 : ℕ)^35*50000000000000^27 ≤ 21083572296729^27*78125000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40131409 78125000 21083572296729 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1173854811/2500000000 : ℝ), (-292287073/1000000000 : ℝ), (-40131409/78125000 : ℝ)] ![(586425349131/1562500000000 : ℝ), (406032660931/2000000000000 : ℝ), (21083572296729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1173854811/2500000000 : ℝ)|^35 ≤ (586425349131/1562500000000 : ℝ)^27
        have hw : |(1173854811/2500000000 : ℝ)|=(1173854811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-292287073/1000000000 : ℝ)|^35 ≤ (406032660931/2000000000000 : ℝ)^27
        have hw : |(-292287073/1000000000 : ℝ)|=(292287073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40131409/78125000 : ℝ)|^35 ≤ (21083572296729/50000000000000 : ℝ)^27
        have hw : |(-40131409/78125000 : ℝ)|=(40131409/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4991903843/10000000000 : ℝ)*x 0 + (3016945143/5000000000 : ℝ)*x 1 + (672165937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4991903843/10000000000 : ℝ)^35 ≤ (10157892576177/25000000000000 : ℝ)^27 := by
    have hnat : (4991903843 : ℕ)^35*25000000000000^27 ≤ 10157892576177^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991903843 10000000000 10157892576177 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3016945143/5000000000 : ℝ)^35 ≤ (25975220231471/50000000000000 : ℝ)^27 := by
    have hnat : (3016945143 : ℕ)^35*50000000000000^27 ≤ 25975220231471^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016945143 5000000000 25975220231471 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672165937/5000000000 : ℝ)^35 ≤ (1483597845529/20000000000000 : ℝ)^27 := by
    have hnat : (672165937 : ℕ)^35*20000000000000^27 ≤ 1483597845529^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672165937 5000000000 1483597845529 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4991903843/10000000000 : ℝ), (3016945143/5000000000 : ℝ), (672165937/5000000000 : ℝ)] ![(10157892576177/25000000000000 : ℝ), (25975220231471/50000000000000 : ℝ), (1483597845529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4991903843/10000000000 : ℝ)|^35 ≤ (10157892576177/25000000000000 : ℝ)^27
        have hw : |(4991903843/10000000000 : ℝ)|=(4991903843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3016945143/5000000000 : ℝ)|^35 ≤ (25975220231471/50000000000000 : ℝ)^27
        have hw : |(3016945143/5000000000 : ℝ)|=(3016945143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672165937/5000000000 : ℝ)|^35 ≤ (1483597845529/20000000000000 : ℝ)^27
        have hw : |(672165937/5000000000 : ℝ)|=(672165937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-155227971/1250000000 : ℝ)*x 0 + (2343283721/10000000000 : ℝ)*x 1 + (-8260897751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (155227971/1250000000 : ℝ)^35 ≤ (6693192128053/100000000000000 : ℝ)^27 := by
    have hnat : (155227971 : ℕ)^35*100000000000000^27 ≤ 6693192128053^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155227971 1250000000 6693192128053 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2343283721/10000000000 : ℝ)^35 ≤ (7622129521151/50000000000000 : ℝ)^27 := by
    have hnat : (2343283721 : ℕ)^35*50000000000000^27 ≤ 7622129521151^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343283721 10000000000 7622129521151 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8260897751/10000000000 : ℝ)^35 ≤ (39031274402597/50000000000000 : ℝ)^27 := by
    have hnat : (8260897751 : ℕ)^35*50000000000000^27 ≤ 39031274402597^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8260897751 10000000000 39031274402597 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-155227971/1250000000 : ℝ), (2343283721/10000000000 : ℝ), (-8260897751/10000000000 : ℝ)] ![(6693192128053/100000000000000 : ℝ), (7622129521151/50000000000000 : ℝ), (39031274402597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-155227971/1250000000 : ℝ)|^35 ≤ (6693192128053/100000000000000 : ℝ)^27
        have hw : |(-155227971/1250000000 : ℝ)|=(155227971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2343283721/10000000000 : ℝ)|^35 ≤ (7622129521151/50000000000000 : ℝ)^27
        have hw : |(2343283721/10000000000 : ℝ)|=(2343283721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8260897751/10000000000 : ℝ)|^35 ≤ (39031274402597/50000000000000 : ℝ)^27
        have hw : |(-8260897751/10000000000 : ℝ)|=(8260897751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3796276009/10000000000 : ℝ)*x 0 + (-193924461/1000000000 : ℝ)*x 1 + (-6706672773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3796276009/10000000000 : ℝ)^35 ≤ (3561500926303/12500000000000 : ℝ)^27 := by
    have hnat : (3796276009 : ℕ)^35*12500000000000^27 ≤ 3561500926303^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3796276009 10000000000 3561500926303 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193924461/1000000000 : ℝ)^35 ≤ (2385562308613/20000000000000 : ℝ)^27 := by
    have hnat : (193924461 : ℕ)^35*20000000000000^27 ≤ 2385562308613^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193924461 1000000000 2385562308613 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6706672773/10000000000 : ℝ)^35 ≤ (2979009051423/5000000000000 : ℝ)^27 := by
    have hnat : (6706672773 : ℕ)^35*5000000000000^27 ≤ 2979009051423^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6706672773 10000000000 2979009051423 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3796276009/10000000000 : ℝ), (-193924461/1000000000 : ℝ), (-6706672773/10000000000 : ℝ)] ![(3561500926303/12500000000000 : ℝ), (2385562308613/20000000000000 : ℝ), (2979009051423/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3796276009/10000000000 : ℝ)|^35 ≤ (3561500926303/12500000000000 : ℝ)^27
        have hw : |(3796276009/10000000000 : ℝ)|=(3796276009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-193924461/1000000000 : ℝ)|^35 ≤ (2385562308613/20000000000000 : ℝ)^27
        have hw : |(-193924461/1000000000 : ℝ)|=(193924461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6706672773/10000000000 : ℝ)|^35 ≤ (2979009051423/5000000000000 : ℝ)^27
        have hw : |(-6706672773/10000000000 : ℝ)|=(6706672773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4112487267/10000000000 : ℝ)*x 0 + (740502509/1000000000 : ℝ)*x 1 + (205698831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4112487267/10000000000 : ℝ)^35 ≤ (7901420725619/25000000000000 : ℝ)^27 := by
    have hnat : (4112487267 : ℕ)^35*25000000000000^27 ≤ 7901420725619^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112487267 10000000000 7901420725619 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740502509/1000000000 : ℝ)^35 ≤ (3387175770561/5000000000000 : ℝ)^27 := by
    have hnat : (740502509 : ℕ)^35*5000000000000^27 ≤ 3387175770561^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740502509 1000000000 3387175770561 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205698831/10000000000 : ℝ)^35 ≤ (325400836123/50000000000000 : ℝ)^27 := by
    have hnat : (205698831 : ℕ)^35*50000000000000^27 ≤ 325400836123^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205698831 10000000000 325400836123 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4112487267/10000000000 : ℝ), (740502509/1000000000 : ℝ), (205698831/10000000000 : ℝ)] ![(7901420725619/25000000000000 : ℝ), (3387175770561/5000000000000 : ℝ), (325400836123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4112487267/10000000000 : ℝ)|^35 ≤ (7901420725619/25000000000000 : ℝ)^27
        have hw : |(4112487267/10000000000 : ℝ)|=(4112487267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740502509/1000000000 : ℝ)|^35 ≤ (3387175770561/5000000000000 : ℝ)^27
        have hw : |(740502509/1000000000 : ℝ)|=(740502509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205698831/10000000000 : ℝ)|^35 ≤ (325400836123/50000000000000 : ℝ)^27
        have hw : |(205698831/10000000000 : ℝ)|=(205698831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (322025611/625000000 : ℝ)*x 0 + (3245327259/5000000000 : ℝ)*x 1 + (-36757979/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (322025611/625000000 : ℝ)^35 ≤ (21166553408261/50000000000000 : ℝ)^27 := by
    have hnat : (322025611 : ℕ)^35*50000000000000^27 ≤ 21166553408261^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      322025611 625000000 21166553408261 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3245327259/5000000000 : ℝ)^35 ≤ (57104491561531/100000000000000 : ℝ)^27 := by
    have hnat : (3245327259 : ℕ)^35*100000000000000^27 ≤ 57104491561531^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3245327259 5000000000 57104491561531 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36757979/2000000000 : ℝ)^35 ≤ (70300201521/12500000000000 : ℝ)^27 := by
    have hnat : (36757979 : ℕ)^35*12500000000000^27 ≤ 70300201521^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36757979 2000000000 70300201521 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(322025611/625000000 : ℝ), (3245327259/5000000000 : ℝ), (-36757979/2000000000 : ℝ)] ![(21166553408261/50000000000000 : ℝ), (57104491561531/100000000000000 : ℝ), (70300201521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(322025611/625000000 : ℝ)|^35 ≤ (21166553408261/50000000000000 : ℝ)^27
        have hw : |(322025611/625000000 : ℝ)|=(322025611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3245327259/5000000000 : ℝ)|^35 ≤ (57104491561531/100000000000000 : ℝ)^27
        have hw : |(3245327259/5000000000 : ℝ)|=(3245327259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-36757979/2000000000 : ℝ)|^35 ≤ (70300201521/12500000000000 : ℝ)^27
        have hw : |(-36757979/2000000000 : ℝ)|=(36757979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-371470467/10000000000 : ℝ)*x 0 + (2547689567/10000000000 : ℝ)*x 1 + (-8549012413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (371470467/10000000000 : ℝ)^35 ≤ (87514128717/6250000000000 : ℝ)^27 := by
    have hnat : (371470467 : ℕ)^35*6250000000000^27 ≤ 87514128717^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371470467 10000000000 87514128717 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2547689567/10000000000 : ℝ)^35 ≤ (16989864630467/100000000000000 : ℝ)^27 := by
    have hnat : (2547689567 : ℕ)^35*100000000000000^27 ≤ 16989864630467^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547689567 10000000000 16989864630467 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8549012413/10000000000 : ℝ)^35 ≤ (81609909288409/100000000000000 : ℝ)^27 := by
    have hnat : (8549012413 : ℕ)^35*100000000000000^27 ≤ 81609909288409^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8549012413 10000000000 81609909288409 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-371470467/10000000000 : ℝ), (2547689567/10000000000 : ℝ), (-8549012413/10000000000 : ℝ)] ![(87514128717/6250000000000 : ℝ), (16989864630467/100000000000000 : ℝ), (81609909288409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-371470467/10000000000 : ℝ)|^35 ≤ (87514128717/6250000000000 : ℝ)^27
        have hw : |(-371470467/10000000000 : ℝ)|=(371470467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2547689567/10000000000 : ℝ)|^35 ≤ (16989864630467/100000000000000 : ℝ)^27
        have hw : |(2547689567/10000000000 : ℝ)|=(2547689567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8549012413/10000000000 : ℝ)|^35 ≤ (81609909288409/100000000000000 : ℝ)^27
        have hw : |(-8549012413/10000000000 : ℝ)|=(8549012413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (677881641/2000000000 : ℝ)*x 0 + (-2209931519/10000000000 : ℝ)*x 1 + (-1370633101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677881641/2000000000 : ℝ)^35 ≤ (24598086326581/100000000000000 : ℝ)^27 := by
    have hnat : (677881641 : ℕ)^35*100000000000000^27 ≤ 24598086326581^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677881641 2000000000 24598086326581 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209931519/10000000000 : ℝ)^35 ≤ (1412930133697/10000000000000 : ℝ)^27 := by
    have hnat : (2209931519 : ℕ)^35*10000000000000^27 ≤ 1412930133697^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209931519 10000000000 1412930133697 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370633101/2000000000 : ℝ)^35 ≤ (478692283729/781250000000 : ℝ)^27 := by
    have hnat : (1370633101 : ℕ)^35*781250000000^27 ≤ 478692283729^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370633101 2000000000 478692283729 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677881641/2000000000 : ℝ), (-2209931519/10000000000 : ℝ), (-1370633101/2000000000 : ℝ)] ![(24598086326581/100000000000000 : ℝ), (1412930133697/10000000000000 : ℝ), (478692283729/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677881641/2000000000 : ℝ)|^35 ≤ (24598086326581/100000000000000 : ℝ)^27
        have hw : |(677881641/2000000000 : ℝ)|=(677881641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2209931519/10000000000 : ℝ)|^35 ≤ (1412930133697/10000000000000 : ℝ)^27
        have hw : |(-2209931519/10000000000 : ℝ)|=(2209931519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370633101/2000000000 : ℝ)|^35 ≤ (478692283729/781250000000 : ℝ)^27
        have hw : |(-1370633101/2000000000 : ℝ)|=(1370633101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1730297179/2500000000 : ℝ)*x 0 + (4606612643/10000000000 : ℝ)*x 1 + (177906993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1730297179/2500000000 : ℝ)^35 ≤ (12412430145749/20000000000000 : ℝ)^27 := by
    have hnat : (1730297179 : ℕ)^35*20000000000000^27 ≤ 12412430145749^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730297179 2500000000 12412430145749 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4606612643/10000000000 : ℝ)^35 ≤ (18306821313111/50000000000000 : ℝ)^27 := by
    have hnat : (4606612643 : ℕ)^35*50000000000000^27 ≤ 18306821313111^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4606612643 10000000000 18306821313111 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177906993/5000000000 : ℝ)^35 ≤ (1324206636459/100000000000000 : ℝ)^27 := by
    have hnat : (177906993 : ℕ)^35*100000000000000^27 ≤ 1324206636459^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177906993 5000000000 1324206636459 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1730297179/2500000000 : ℝ), (4606612643/10000000000 : ℝ), (177906993/5000000000 : ℝ)] ![(12412430145749/20000000000000 : ℝ), (18306821313111/50000000000000 : ℝ), (1324206636459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1730297179/2500000000 : ℝ)|^35 ≤ (12412430145749/20000000000000 : ℝ)^27
        have hw : |(1730297179/2500000000 : ℝ)|=(1730297179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4606612643/10000000000 : ℝ)|^35 ≤ (18306821313111/50000000000000 : ℝ)^27
        have hw : |(4606612643/10000000000 : ℝ)|=(4606612643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(177906993/5000000000 : ℝ)|^35 ≤ (1324206636459/100000000000000 : ℝ)^27
        have hw : |(177906993/5000000000 : ℝ)|=(177906993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (649673/800000 : ℝ)*x 0 + (127592711/400000000 : ℝ)*x 1 + (-133301253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649673/800000 : ℝ)^35 ≤ (15270423197903/20000000000000 : ℝ)^27 := by
    have hnat : (649673 : ℕ)^35*20000000000000^27 ≤ 15270423197903^27*800000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649673 800000 15270423197903 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127592711/400000000 : ℝ)^35 ≤ (22737019805927/100000000000000 : ℝ)^27 := by
    have hnat : (127592711 : ℕ)^35*100000000000000^27 ≤ 22737019805927^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127592711 400000000 22737019805927 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133301253/5000000000 : ℝ)^35 ≤ (182172837849/20000000000000 : ℝ)^27 := by
    have hnat : (133301253 : ℕ)^35*20000000000000^27 ≤ 182172837849^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133301253 5000000000 182172837849 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649673/800000 : ℝ), (127592711/400000000 : ℝ), (-133301253/5000000000 : ℝ)] ![(15270423197903/20000000000000 : ℝ), (22737019805927/100000000000000 : ℝ), (182172837849/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649673/800000 : ℝ)|^35 ≤ (15270423197903/20000000000000 : ℝ)^27
        have hw : |(649673/800000 : ℝ)|=(649673/800000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127592711/400000000 : ℝ)|^35 ≤ (22737019805927/100000000000000 : ℝ)^27
        have hw : |(127592711/400000000 : ℝ)|=(127592711/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133301253/5000000000 : ℝ)|^35 ≤ (182172837849/20000000000000 : ℝ)^27
        have hw : |(-133301253/5000000000 : ℝ)|=(133301253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2889469/2500000000 : ℝ)*x 0 + (4233223831/10000000000 : ℝ)*x 1 + (-7356676699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2889469/2500000000 : ℝ)^35 ≤ (15581873331/100000000000000 : ℝ)^27 := by
    have hnat : (2889469 : ℕ)^35*100000000000000^27 ≤ 15581873331^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2889469 2500000000 15581873331 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233223831/10000000000 : ℝ)^35 ≤ (32813707399837/100000000000000 : ℝ)^27 := by
    have hnat : (4233223831 : ℕ)^35*100000000000000^27 ≤ 32813707399837^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233223831 10000000000 32813707399837 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7356676699/10000000000 : ℝ)^35 ≤ (13434142143453/20000000000000 : ℝ)^27 := by
    have hnat : (7356676699 : ℕ)^35*20000000000000^27 ≤ 13434142143453^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7356676699 10000000000 13434142143453 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2889469/2500000000 : ℝ), (4233223831/10000000000 : ℝ), (-7356676699/10000000000 : ℝ)] ![(15581873331/100000000000000 : ℝ), (32813707399837/100000000000000 : ℝ), (13434142143453/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2889469/2500000000 : ℝ)|^35 ≤ (15581873331/100000000000000 : ℝ)^27
        have hw : |(-2889469/2500000000 : ℝ)|=(2889469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233223831/10000000000 : ℝ)|^35 ≤ (32813707399837/100000000000000 : ℝ)^27
        have hw : |(4233223831/10000000000 : ℝ)|=(4233223831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7356676699/10000000000 : ℝ)|^35 ≤ (13434142143453/20000000000000 : ℝ)^27
        have hw : |(-7356676699/10000000000 : ℝ)|=(7356676699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3207850269/5000000000 : ℝ)*x 0 + (-89498349/400000000 : ℝ)*x 1 + (-3888351083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3207850269/5000000000 : ℝ)^35 ≤ (28125563016481/50000000000000 : ℝ)^27 := by
    have hnat : (3207850269 : ℕ)^35*50000000000000^27 ≤ 28125563016481^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3207850269 5000000000 28125563016481 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89498349/400000000 : ℝ)^35 ≤ (7178932357959/50000000000000 : ℝ)^27 := by
    have hnat : (89498349 : ℕ)^35*50000000000000^27 ≤ 7178932357959^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89498349 400000000 7178932357959 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3888351083/10000000000 : ℝ)^35 ≤ (29391009240429/100000000000000 : ℝ)^27 := by
    have hnat : (3888351083 : ℕ)^35*100000000000000^27 ≤ 29391009240429^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888351083 10000000000 29391009240429 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3207850269/5000000000 : ℝ), (-89498349/400000000 : ℝ), (-3888351083/10000000000 : ℝ)] ![(28125563016481/50000000000000 : ℝ), (7178932357959/50000000000000 : ℝ), (29391009240429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3207850269/5000000000 : ℝ)|^35 ≤ (28125563016481/50000000000000 : ℝ)^27
        have hw : |(3207850269/5000000000 : ℝ)|=(3207850269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-89498349/400000000 : ℝ)|^35 ≤ (7178932357959/50000000000000 : ℝ)^27
        have hw : |(-89498349/400000000 : ℝ)|=(89498349/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3888351083/10000000000 : ℝ)|^35 ≤ (29391009240429/100000000000000 : ℝ)^27
        have hw : |(-3888351083/10000000000 : ℝ)|=(3888351083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (428342977/1000000000 : ℝ)*x 0 + (6971145529/10000000000 : ℝ)*x 1 + (420419351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428342977/1000000000 : ℝ)^35 ≤ (3331907074087/10000000000000 : ℝ)^27 := by
    have hnat : (428342977 : ℕ)^35*10000000000000^27 ≤ 3331907074087^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428342977 1000000000 3331907074087 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6971145529/10000000000 : ℝ)^35 ≤ (31321730841543/50000000000000 : ℝ)^27 := by
    have hnat : (6971145529 : ℕ)^35*50000000000000^27 ≤ 31321730841543^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6971145529 10000000000 31321730841543 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420419351/5000000000 : ℝ)^35 ≤ (4037467566791/100000000000000 : ℝ)^27 := by
    have hnat : (420419351 : ℕ)^35*100000000000000^27 ≤ 4037467566791^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420419351 5000000000 4037467566791 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428342977/1000000000 : ℝ), (6971145529/10000000000 : ℝ), (420419351/5000000000 : ℝ)] ![(3331907074087/10000000000000 : ℝ), (31321730841543/50000000000000 : ℝ), (4037467566791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428342977/1000000000 : ℝ)|^35 ≤ (3331907074087/10000000000000 : ℝ)^27
        have hw : |(428342977/1000000000 : ℝ)|=(428342977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6971145529/10000000000 : ℝ)|^35 ≤ (31321730841543/50000000000000 : ℝ)^27
        have hw : |(6971145529/10000000000 : ℝ)|=(6971145529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(420419351/5000000000 : ℝ)|^35 ≤ (4037467566791/100000000000000 : ℝ)^27
        have hw : |(420419351/5000000000 : ℝ)|=(420419351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308052_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1059324137/1250000000 : ℝ)*x 0 + (133990207/500000000 : ℝ)*x 1 + (-1262617/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059324137/1250000000 : ℝ)^35 ≤ (40345094976939/50000000000000 : ℝ)^27 := by
    have hnat : (1059324137 : ℕ)^35*50000000000000^27 ≤ 40345094976939^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059324137 1250000000 40345094976939 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133990207/500000000 : ℝ)^35 ≤ (9070309595299/50000000000000 : ℝ)^27 := by
    have hnat : (133990207 : ℕ)^35*50000000000000^27 ≤ 9070309595299^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133990207 500000000 9070309595299 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262617/39062500 : ℝ)^35 ≤ (374141069/32000000000 : ℝ)^27 := by
    have hnat : (1262617 : ℕ)^35*32000000000^27 ≤ 374141069^27*39062500^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262617 39062500 374141069 32000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059324137/1250000000 : ℝ), (133990207/500000000 : ℝ), (-1262617/39062500 : ℝ)] ![(40345094976939/50000000000000 : ℝ), (9070309595299/50000000000000 : ℝ), (374141069/32000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059324137/1250000000 : ℝ)|^35 ≤ (40345094976939/50000000000000 : ℝ)^27
        have hw : |(1059324137/1250000000 : ℝ)|=(1059324137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(133990207/500000000 : ℝ)|^35 ≤ (9070309595299/50000000000000 : ℝ)^27
        have hw : |(133990207/500000000 : ℝ)|=(133990207/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1262617/39062500 : ℝ)|^35 ≤ (374141069/32000000000 : ℝ)^27
        have hw : |(-1262617/39062500 : ℝ)|=(1262617/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308052_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((17103/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17103/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8709/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8709/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37649/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16793/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16793/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70341/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70341/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10123/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10123/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (17103/20000 : ℝ) ^ (17/4 : ℝ) ≤ (10285129657581761227/20000000000000000000 : ℝ) := by
    have hpowers : (17103/20000 : ℝ)^17 ≤ (10285129657581761227/20000000000000000000 : ℝ)^4 := by
      have hnat : (17103 : ℕ)^17*20000000000000000000^4 ≤ 10285129657581761227^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17103 20000 10285129657581761227 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17103/20000 : ℝ)) (X := (10285129657581761227/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (30285129657581761227/20000000000000000000 : ℝ) ≤ (11025539985756369/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (30285129657581761227/20000000000000000000 : ℝ)^4 ≤ (11025539985756369/10000000000000000 : ℝ)^17 := by
      have hnat : (30285129657581761227 : ℕ)^4*10000000000000000^17 ≤ 11025539985756369^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        30285129657581761227 20000000000000000000 11025539985756369 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11025539985756369/10000000000000000 : ℝ)) (X := (30285129657581761227/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (20285129657581761227/10000000000000000000 : ℝ) ≤ (11810740474852633/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (20285129657581761227/10000000000000000000 : ℝ)^4 ≤ (11810740474852633/10000000000000000 : ℝ)^17 := by
      have hnat : (20285129657581761227 : ℕ)^4*10000000000000000^17 ≤ 11810740474852633^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20285129657581761227 10000000000000000000 11810740474852633 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11810740474852633/10000000000000000 : ℝ)) (X := (20285129657581761227/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1025539985756369/8551500000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(98150061137033/1068937500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (17103/20000 : ℝ)) (alpha := (1025539985756369/8551500000000000 : ℝ)) (beta := (98150061137033/1068937500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (17103/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1025539985756369/8551500000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(98150061137033/1068937500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (8709/10000 : ℝ) ^ (17/4 : ℝ) ≤ (6946647279495728937/12500000000000000000 : ℝ) := by
    have hpowers : (8709/10000 : ℝ)^17 ≤ (6946647279495728937/12500000000000000000 : ℝ)^4 := by
      have hnat : (8709 : ℕ)^17*12500000000000000000^4 ≤ 6946647279495728937^4*10000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8709 10000 6946647279495728937 12500000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8709/10000 : ℝ)) (X := (6946647279495728937/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (19446647279495728937/12500000000000000000 : ℝ) ≤ (11095863655653217/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (19446647279495728937/12500000000000000000 : ℝ)^4 ≤ (11095863655653217/10000000000000000 : ℝ)^17 := by
      have hnat : (19446647279495728937 : ℕ)^4*10000000000000000^17 ≤ 11095863655653217^17*12500000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19446647279495728937 12500000000000000000 11095863655653217 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11095863655653217/10000000000000000 : ℝ)) (X := (19446647279495728937/12500000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (13196647279495728937/6250000000000000000 : ℝ) ≤ (596132245735909/500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (13196647279495728937/6250000000000000000 : ℝ)^4 ≤ (596132245735909/500000000000000 : ℝ)^17 := by
      have hnat : (13196647279495728937 : ℕ)^4*500000000000000^17 ≤ 596132245735909^17*6250000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13196647279495728937 6250000000000000000 596132245735909 500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (596132245735909/500000000000000 : ℝ)) (X := (13196647279495728937/6250000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(365287885217739/2903000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(826781259064963/8709000000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (8709/10000 : ℝ)) (alpha := (365287885217739/2903000000000000 : ℝ)) (beta := (826781259064963/8709000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (8709/10000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(365287885217739/2903000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(826781259064963/8709000000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (37649/50000 : ℝ) ^ (17/4 : ℝ) ≤ (29945365913423351691/100000000000000000000 : ℝ) := by
    have hpowers : (37649/50000 : ℝ)^17 ≤ (29945365913423351691/100000000000000000000 : ℝ)^4 := by
      have hnat : (37649 : ℕ)^17*100000000000000000000^4 ≤ 29945365913423351691^4*50000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        37649 50000 29945365913423351691 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (37649/50000 : ℝ)) (X := (29945365913423351691/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (129945365913423351691/100000000000000000000 : ℝ) ≤ (10635728590973197/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (129945365913423351691/100000000000000000000 : ℝ)^4 ≤ (10635728590973197/10000000000000000 : ℝ)^17 := by
      have hnat : (129945365913423351691 : ℕ)^4*10000000000000000^17 ≤ 10635728590973197^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        129945365913423351691 100000000000000000000 10635728590973197 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10635728590973197/10000000000000000 : ℝ)) (X := (129945365913423351691/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (79945365913423351691/50000000000000000000 : ℝ) ≤ (11167563259600721/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (79945365913423351691/50000000000000000000 : ℝ)^4 ≤ (11167563259600721/10000000000000000 : ℝ)^17 := by
      have hnat : (79945365913423351691 : ℕ)^4*10000000000000000^17 ≤ 11167563259600721^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79945365913423351691 50000000000000000000 11167563259600721 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11167563259600721/10000000000000000 : ℝ)) (X := (79945365913423351691/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(635728590973197/7529800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(132958667156881/1882450000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (37649/50000 : ℝ)) (alpha := (635728590973197/7529800000000000 : ℝ)) (beta := (132958667156881/1882450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (37649/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(635728590973197/7529800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(132958667156881/1882450000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-782240149/5000000000 : ℝ)*X 0 0+(844830447/2500000000 : ℝ)*X 0 1+(-3648584859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1173854811/2500000000 : ℝ)*X 1 0+(-292287073/1000000000 : ℝ)*X 1 1+(-40131409/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4991903843/10000000000 : ℝ)*X 2 0+(3016945143/5000000000 : ℝ)*X 2 1+(672165937/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-155227971/1250000000 : ℝ)*X 0 0+(2343283721/10000000000 : ℝ)*X 0 1+(-8260897751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3796276009/10000000000 : ℝ)*X 1 0+(-193924461/1000000000 : ℝ)*X 1 1+(-6706672773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4112487267/10000000000 : ℝ)*X 2 0+(740502509/1000000000 : ℝ)*X 2 1+(205698831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((322025611/625000000 : ℝ)*X 0 0+(3245327259/5000000000 : ℝ)*X 0 1+(-36757979/2000000000 : ℝ)*X 0 2+(322025611/625000000 : ℝ)*X 1 0+(3245327259/5000000000 : ℝ)*X 1 1+(-36757979/2000000000 : ℝ)*X 1 2+(322025611/625000000 : ℝ)*X 2 0+(3245327259/5000000000 : ℝ)*X 2 1+(-36757979/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-371470467/10000000000 : ℝ)*X 0 0+(2547689567/10000000000 : ℝ)*X 0 1+(-8549012413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((677881641/2000000000 : ℝ)*X 1 0+(-2209931519/10000000000 : ℝ)*X 1 1+(-1370633101/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1730297179/2500000000 : ℝ)*X 2 0+(4606612643/10000000000 : ℝ)*X 2 1+(177906993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((649673/800000 : ℝ)*X 0 0+(127592711/400000000 : ℝ)*X 0 1+(-133301253/5000000000 : ℝ)*X 0 2+(649673/800000 : ℝ)*X 1 0+(127592711/400000000 : ℝ)*X 1 1+(-133301253/5000000000 : ℝ)*X 1 2+(649673/800000 : ℝ)*X 2 0+(127592711/400000000 : ℝ)*X 2 1+(-133301253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2889469/2500000000 : ℝ)*X 0 0+(4233223831/10000000000 : ℝ)*X 0 1+(-7356676699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3207850269/5000000000 : ℝ)*X 1 0+(-89498349/400000000 : ℝ)*X 1 1+(-3888351083/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((428342977/1000000000 : ℝ)*X 2 0+(6971145529/10000000000 : ℝ)*X 2 1+(420419351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1059324137/1250000000 : ℝ)*X 0 0+(133990207/500000000 : ℝ)*X 0 1+(-1262617/39062500 : ℝ)*X 0 2+(1059324137/1250000000 : ℝ)*X 1 0+(133990207/500000000 : ℝ)*X 1 1+(-1262617/39062500 : ℝ)*X 1 2+(1059324137/1250000000 : ℝ)*X 2 0+(133990207/500000000 : ℝ)*X 2 1+(-1262617/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308052_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((16793/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16793/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (613118673934116717915892752897/77886382868375000000000000000000000 : ℝ) := by norm_num
    linear_combination (33481082447/125000000000 : ℝ)*(base7) + (52441553657/1000000000000 : ℝ)*(base39) + (478649931983/1000000000000 : ℝ)*(base59) + (3131415501447/1000000000000 : ℝ)*(major_s1_0) + (3131415501447/1000000000000 : ℝ)*(major_s1_1) + (3131415501447/1000000000000 : ℝ)*(major_s1_2) + (2051011/125000000000 : ℝ)*(sp_s1_0) + (299513/100000000000 : ℝ)*(sp_s1_1) + (1025009620173/250000000000 : ℝ)*(sp_s1_7) + (205004467923/50000000000 : ℝ)*(sp_s1_8) + (4100094617283/1000000000000 : ℝ)*(sp_s1_9) + (283257382567/125000000000 : ℝ)*(sp_s1_13) + (39728503/1000000000000 : ℝ)*(sp_s1_14) + (2263693/1000000000000 : ℝ)*(sp_s1_15) + (1998210400959/1000000000000 : ℝ)*(f.failure) + (4100094617283/1000000000000 : ℝ)*(f.sum) + (12515776251287551499/54647523500000000000000000000000 : ℝ)*base62 + (178444523213429/235306250000000000000000000 : ℝ)*base64 + (1971863870950013/2903000000000000000000000000 : ℝ)*base67 + (5640995971239721/7529800000000000000000000000 : ℝ)*base68 + (20502573089424627851/107318474500000000000000000000000 : ℝ)*base70 + (185762714003793/1425250000000000000000000000 : ℝ)*base73 + (2294814180210767/2903000000000000000000000000 : ℝ)*base74 + (2555707743913919/2850500000000000000000000000 : ℝ)*base76 + (7516717798525675471/16550003000000000000000000000000 : ℝ)*base78 + (14151/100000000000000000 : ℝ)*base86 + (14151/100000000000000000 : ℝ)*base88 + (14151/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70341/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70341/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (95973393006686479877517007813/9735797858546875000000000000000000 : ℝ) := by norm_num
    linear_combination (107736256913/250000000000 : ℝ)*(base7) + (6506132793/100000000000 : ℝ)*(base39) + (621821/1000000000000 : ℝ)*(base49) + (168995329219/1000000000000 : ℝ)*(base59) + (1243781628127/500000000000 : ℝ)*(major_s1_0) + (1243781628127/500000000000 : ℝ)*(major_s1_1) + (1243781628127/500000000000 : ℝ)*(major_s1_2) + (3004971/1000000000000 : ℝ)*(sp_s1_2) + (168301/1562500000 : ℝ)*(sp_s1_8) + (312306240731/100000000000 : ℝ)*(sp_s1_14) + (312295469467/100000000000 : ℝ)*(sp_s1_15) + (3123059402339/1000000000000 : ℝ)*(sp_s1_16) + (252284711203/125000000000 : ℝ)*(sp_s1_20) + (24483509/1000000000000 : ℝ)*(sp_s1_27) + (1587357145481/1000000000000 : ℝ)*(f.failure) + (312306240731/100000000000 : ℝ)*(f.sum) + (5442835062164897259/27323761750000000000000000000000 : ℝ)*base62 + (238515959584531/470612500000000000000000000 : ℝ)*base64 + (1003053207009599/4354500000000000000000000000 : ℝ)*base67 + (2126124349649241/3764900000000000000000000000 : ℝ)*base68 + (26485874957802515273/160977711750000000000000000000000 : ℝ)*base70 + (1008331171975589/2137875000000000000000000000 : ℝ)*base73 + (939621423321297/1451500000000000000000000000 : ℝ)*base74 + (963710609078681/2137875000000000000000000000 : ℝ)*base76 + (397008454050860211/8275001500000000000000000000000 : ℝ)*base78 + (72991/100000000000000000 : ℝ)*base87 + (72991/100000000000000000 : ℝ)*base89 + (72991/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10123/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10123/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (531037434274961562085365619321/155772765736750000000000000000000000 : ℝ) := by norm_num
    linear_combination (8775702431/1000000000000 : ℝ)*(base7) + (575908925669/1000000000000 : ℝ)*(base39) + (283962006957/1000000000000 : ℝ)*(base49) + (54864711457/100000000000 : ℝ)*(base59) + (3017395780927/1000000000000 : ℝ)*(major_s1_0) + (3017395780927/1000000000000 : ℝ)*(major_s1_1) + (3017395780927/1000000000000 : ℝ)*(major_s1_2) + (275197/250000000000 : ℝ)*(sp_s1_0) + (33608563/500000000000 : ℝ)*(sp_s1_9) + (2454959/250000000000 : ℝ)*(sp_s1_16) + (2051973246173/500000000000 : ℝ)*(sp_s1_21) + (2051973796567/500000000000 : ℝ)*(sp_s1_22) + (4103870556173/1000000000000 : ℝ)*(sp_s1_23) + (193422814733/100000000000 : ℝ)*(sp_s1_27) + (19254524449/10000000000 : ℝ)*(f.failure) + (2051973796567/500000000000 : ℝ)*(f.sum) + (28655029317373369591/54647523500000000000000000000000 : ℝ)*base63 + (2340357761327163/1882450000000000000000000000 : ℝ)*base65 + (4865904974482501/8709000000000000000000000000 : ℝ)*base66 + (9099432647293059/7529800000000000000000000000 : ℝ)*base69 + (174018514194366442777/321955423500000000000000000000000 : ℝ)*base71 + (1571092944222743/2137875000000000000000000000 : ℝ)*base72 + (1960117754211653/2903000000000000000000000000 : ℝ)*base75 + (2515641923008313/8551500000000000000000000000 : ℝ)*base77 + (2471648826095282389/16550003000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (239/1000000000000000 : ℝ)*base87 + (239/1000000000000000 : ℝ)*base89 + (239/1000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((17103/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17103/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8709/10000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8709/10000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37649/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-37649/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((16793/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16793/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(70341/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(70341/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-10123/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-10123/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308052_s1 p hpa hpb X hX hprev0

#print axioms solution
