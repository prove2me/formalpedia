-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c318063_s0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:25:04.408761+00:00
-- url     : https://prove2.me/submissions/d7da9139-b6a6-477a-ae19-663a97f8d374

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
theorem collision_support_c318063_s0_s0_0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-194793503/10000000000 : ℝ)*x 0 + (692650493/1250000000 : ℝ)*x 1 + (2949371419/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (194793503/10000000000 : ℝ)^79 ≤ (71644141283/10000000000000 : ℝ)^63 := by
    have hnat : (194793503 : ℕ)^79*10000000000000^63 ≤ 71644141283^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194793503 10000000000 71644141283 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692650493/1250000000 : ℝ)^79 ≤ (11924158305031/25000000000000 : ℝ)^63 := by
    have hnat : (692650493 : ℕ)^79*25000000000000^63 ≤ 11924158305031^63*1250000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692650493 1250000000 11924158305031 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2949371419/5000000000 : ℝ)^79 ≤ (5158692535369/10000000000000 : ℝ)^63 := by
    have hnat : (2949371419 : ℕ)^79*10000000000000^63 ≤ 5158692535369^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2949371419 5000000000 5158692535369 10000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-194793503/10000000000 : ℝ), (692650493/1250000000 : ℝ), (2949371419/5000000000 : ℝ)] ![(71644141283/10000000000000 : ℝ), (11924158305031/25000000000000 : ℝ), (5158692535369/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-194793503/10000000000 : ℝ)|^79 ≤ (71644141283/10000000000000 : ℝ)^63
        have hw : |(-194793503/10000000000 : ℝ)|=(194793503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692650493/1250000000 : ℝ)|^79 ≤ (11924158305031/25000000000000 : ℝ)^63
        have hw : |(692650493/1250000000 : ℝ)|=(692650493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2949371419/5000000000 : ℝ)|^79 ≤ (5158692535369/10000000000000 : ℝ)^63
        have hw : |(2949371419/5000000000 : ℝ)|=(2949371419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_2 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5541205827/10000000000 : ℝ)*x 0 + (5898742023/10000000000 : ℝ)*x 1 + (-194791033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5541205827/10000000000 : ℝ)^79 ≤ (11924163386163/25000000000000 : ℝ)^63 := by
    have hnat : (5541205827 : ℕ)^79*25000000000000^63 ≤ 11924163386163^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5541205827 10000000000 11924163386163 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5898742023/10000000000 : ℝ)^79 ≤ (2579345820801/5000000000000 : ℝ)^63 := by
    have hnat : (5898742023 : ℕ)^79*5000000000000^63 ≤ 2579345820801^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5898742023 10000000000 2579345820801 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194791033/10000000000 : ℝ)^79 ≤ (716430021117/100000000000000 : ℝ)^63 := by
    have hnat : (194791033 : ℕ)^79*100000000000000^63 ≤ 716430021117^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194791033 10000000000 716430021117 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5541205827/10000000000 : ℝ), (5898742023/10000000000 : ℝ), (-194791033/10000000000 : ℝ)] ![(11924163386163/25000000000000 : ℝ), (2579345820801/5000000000000 : ℝ), (716430021117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5541205827/10000000000 : ℝ)|^79 ≤ (11924163386163/25000000000000 : ℝ)^63
        have hw : |(5541205827/10000000000 : ℝ)|=(5541205827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5898742023/10000000000 : ℝ)|^79 ≤ (2579345820801/5000000000000 : ℝ)^63
        have hw : |(5898742023/10000000000 : ℝ)|=(5898742023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194791033/10000000000 : ℝ)|^79 ≤ (716430021117/100000000000000 : ℝ)^63
        have hw : |(-194791033/10000000000 : ℝ)|=(194791033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_7 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1121633277/10000000000 : ℝ)*x 0 + (1369303433/10000000000 : ℝ)*x 1 + (880922747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1121633277/10000000000 : ℝ)^79 ≤ (804365040687/12500000000000 : ℝ)^63 := by
    have hnat : (1121633277 : ℕ)^79*12500000000000^63 ≤ 804365040687^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121633277 10000000000 804365040687 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369303433/10000000000 : ℝ)^79 ≤ (8264146982007/100000000000000 : ℝ)^63 := by
    have hnat : (1369303433 : ℕ)^79*100000000000000^63 ≤ 8264146982007^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369303433 10000000000 8264146982007 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (880922747/1000000000 : ℝ)^79 ≤ (42650466342393/50000000000000 : ℝ)^63 := by
    have hnat : (880922747 : ℕ)^79*50000000000000^63 ≤ 42650466342393^63*1000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      880922747 1000000000 42650466342393 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1121633277/10000000000 : ℝ), (1369303433/10000000000 : ℝ), (880922747/1000000000 : ℝ)] ![(804365040687/12500000000000 : ℝ), (8264146982007/100000000000000 : ℝ), (42650466342393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1121633277/10000000000 : ℝ)|^79 ≤ (804365040687/12500000000000 : ℝ)^63
        have hw : |(-1121633277/10000000000 : ℝ)|=(1121633277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369303433/10000000000 : ℝ)|^79 ≤ (8264146982007/100000000000000 : ℝ)^63
        have hw : |(1369303433/10000000000 : ℝ)|=(1369303433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(880922747/1000000000 : ℝ)|^79 ≤ (42650466342393/50000000000000 : ℝ)^63
        have hw : |(880922747/1000000000 : ℝ)|=(880922747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_8 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1066698403/5000000000 : ℝ)*x 0 + (-47167531/5000000000 : ℝ)*x 1 + (8809229563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066698403/5000000000 : ℝ)^79 ≤ (14410436517837/100000000000000 : ℝ)^63 := by
    have hnat : (1066698403 : ℕ)^79*100000000000000^63 ≤ 14410436517837^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066698403 5000000000 14410436517837 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (47167531/5000000000 : ℝ)^79 ≤ (288605373349/100000000000000 : ℝ)^63 := by
    have hnat : (47167531 : ℕ)^79*100000000000000^63 ≤ 288605373349^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47167531 5000000000 288605373349 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8809229563/10000000000 : ℝ)^79 ≤ (85300958098711/100000000000000 : ℝ)^63 := by
    have hnat : (8809229563 : ℕ)^79*100000000000000^63 ≤ 85300958098711^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8809229563 10000000000 85300958098711 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066698403/5000000000 : ℝ), (-47167531/5000000000 : ℝ), (8809229563/10000000000 : ℝ)] ![(14410436517837/100000000000000 : ℝ), (288605373349/100000000000000 : ℝ), (85300958098711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066698403/5000000000 : ℝ)|^79 ≤ (14410436517837/100000000000000 : ℝ)^63
        have hw : |(1066698403/5000000000 : ℝ)|=(1066698403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-47167531/5000000000 : ℝ)|^79 ≤ (288605373349/100000000000000 : ℝ)^63
        have hw : |(-47167531/5000000000 : ℝ)|=(47167531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8809229563/10000000000 : ℝ)|^79 ≤ (85300958098711/100000000000000 : ℝ)^63
        have hw : |(8809229563/10000000000 : ℝ)|=(8809229563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_9 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2107455371/10000000000 : ℝ)*x 0 + (353795731/400000000 : ℝ)*x 1 + (-16057609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107455371/10000000000 : ℝ)^79 ≤ (14191048509467/100000000000000 : ℝ)^63 := by
    have hnat : (2107455371 : ℕ)^79*100000000000000^63 ≤ 14191048509467^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107455371 10000000000 14191048509467 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (353795731/400000000 : ℝ)^79 ≤ (85734221546841/100000000000000 : ℝ)^63 := by
    have hnat : (353795731 : ℕ)^79*100000000000000^63 ≤ 85734221546841^63*400000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353795731 400000000 85734221546841 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16057609/5000000000 : ℝ)^79 ≤ (74729932247/100000000000000 : ℝ)^63 := by
    have hnat : (16057609 : ℕ)^79*100000000000000^63 ≤ 74729932247^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16057609 5000000000 74729932247 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107455371/10000000000 : ℝ), (353795731/400000000 : ℝ), (-16057609/5000000000 : ℝ)] ![(14191048509467/100000000000000 : ℝ), (85734221546841/100000000000000 : ℝ), (74729932247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107455371/10000000000 : ℝ)|^79 ≤ (14191048509467/100000000000000 : ℝ)^63
        have hw : |(2107455371/10000000000 : ℝ)|=(2107455371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(353795731/400000000 : ℝ)|^79 ≤ (85734221546841/100000000000000 : ℝ)^63
        have hw : |(353795731/400000000 : ℝ)|=(353795731/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16057609/5000000000 : ℝ)|^79 ≤ (74729932247/100000000000000 : ℝ)^63
        have hw : |(-16057609/5000000000 : ℝ)|=(16057609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_13 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (773084989/2500000000 : ℝ)*x 0 + (3652850169/5000000000 : ℝ)*x 1 + (770826163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (773084989/2500000000 : ℝ)^79 ≤ (286910460991/1250000000000 : ℝ)^63 := by
    have hnat : (773084989 : ℕ)^79*1250000000000^63 ≤ 286910460991^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773084989 2500000000 286910460991 1250000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3652850169/5000000000 : ℝ)^79 ≤ (67458440005023/100000000000000 : ℝ)^63 := by
    have hnat : (3652850169 : ℕ)^79*100000000000000^63 ≤ 67458440005023^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3652850169 5000000000 67458440005023 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (770826163/5000000000 : ℝ)^79 ≤ (4794361546857/50000000000000 : ℝ)^63 := by
    have hnat : (770826163 : ℕ)^79*50000000000000^63 ≤ 4794361546857^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      770826163 5000000000 4794361546857 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(773084989/2500000000 : ℝ), (3652850169/5000000000 : ℝ), (770826163/5000000000 : ℝ)] ![(286910460991/1250000000000 : ℝ), (67458440005023/100000000000000 : ℝ), (4794361546857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(773084989/2500000000 : ℝ)|^79 ≤ (286910460991/1250000000000 : ℝ)^63
        have hw : |(773084989/2500000000 : ℝ)|=(773084989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3652850169/5000000000 : ℝ)|^79 ≤ (67458440005023/100000000000000 : ℝ)^63
        have hw : |(3652850169/5000000000 : ℝ)|=(3652850169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(770826163/5000000000 : ℝ)|^79 ≤ (4794361546857/50000000000000 : ℝ)^63
        have hw : |(770826163/5000000000 : ℝ)|=(770826163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_14 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-558803/125000000 : ℝ)*x 0 + (2050661237/10000000000 : ℝ)*x 1 + (8881033259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (558803/125000000 : ℝ)^79 ≤ (22627776353/20000000000000 : ℝ)^63 := by
    have hnat : (558803 : ℕ)^79*20000000000000^63 ≤ 22627776353^63*125000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558803 125000000 22627776353 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2050661237/10000000000 : ℝ)^79 ≤ (13713137259507/100000000000000 : ℝ)^63 := by
    have hnat : (2050661237 : ℕ)^79*100000000000000^63 ≤ 13713137259507^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050661237 10000000000 13713137259507 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8881033259/10000000000 : ℝ)^79 ≤ (21543430963207/25000000000000 : ℝ)^63 := by
    have hnat : (8881033259 : ℕ)^79*25000000000000^63 ≤ 21543430963207^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8881033259 10000000000 21543430963207 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-558803/125000000 : ℝ), (2050661237/10000000000 : ℝ), (8881033259/10000000000 : ℝ)] ![(22627776353/20000000000000 : ℝ), (13713137259507/100000000000000 : ℝ), (21543430963207/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-558803/125000000 : ℝ)|^79 ≤ (22627776353/20000000000000 : ℝ)^63
        have hw : |(-558803/125000000 : ℝ)|=(558803/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2050661237/10000000000 : ℝ)|^79 ≤ (13713137259507/100000000000000 : ℝ)^63
        have hw : |(2050661237/10000000000 : ℝ)|=(2050661237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8881033259/10000000000 : ℝ)|^79 ≤ (21543430963207/25000000000000 : ℝ)^63
        have hw : |(8881033259/10000000000 : ℝ)|=(8881033259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_15 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (607145537/5000000000 : ℝ)*x 0 + (-1160797117/10000000000 : ℝ)*x 1 + (8881033241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (607145537/5000000000 : ℝ)^79 ≤ (1421673470617/20000000000000 : ℝ)^63 := by
    have hnat : (607145537 : ℕ)^79*20000000000000^63 ≤ 1421673470617^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607145537 5000000000 1421673470617 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1160797117/10000000000 : ℝ)^79 ≤ (6717908998697/100000000000000 : ℝ)^63 := by
    have hnat : (1160797117 : ℕ)^79*100000000000000^63 ≤ 6717908998697^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1160797117 10000000000 6717908998697 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8881033241/10000000000 : ℝ)^79 ≤ (17234744726763/20000000000000 : ℝ)^63 := by
    have hnat : (8881033241 : ℕ)^79*20000000000000^63 ≤ 17234744726763^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8881033241 10000000000 17234744726763 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(607145537/5000000000 : ℝ), (-1160797117/10000000000 : ℝ), (8881033241/10000000000 : ℝ)] ![(1421673470617/20000000000000 : ℝ), (6717908998697/100000000000000 : ℝ), (17234744726763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(607145537/5000000000 : ℝ)|^79 ≤ (1421673470617/20000000000000 : ℝ)^63
        have hw : |(607145537/5000000000 : ℝ)|=(607145537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1160797117/10000000000 : ℝ)|^79 ≤ (6717908998697/100000000000000 : ℝ)^63
        have hw : |(-1160797117/10000000000 : ℝ)|=(1160797117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8881033241/10000000000 : ℝ)|^79 ≤ (17234744726763/20000000000000 : ℝ)^63
        have hw : |(8881033241/10000000000 : ℝ)|=(8881033241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_16 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4274004977/5000000000 : ℝ)*x 0 + (125589211/500000000 : ℝ)*x 1 + (-31529337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4274004977/5000000000 : ℝ)^79 ≤ (82141172376449/100000000000000 : ℝ)^63 := by
    have hnat : (4274004977 : ℕ)^79*100000000000000^63 ≤ 82141172376449^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4274004977 5000000000 82141172376449 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125589211/500000000 : ℝ)^79 ≤ (884233351229/5000000000000 : ℝ)^63 := by
    have hnat : (125589211 : ℕ)^79*5000000000000^63 ≤ 884233351229^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125589211 500000000 884233351229 5000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31529337/5000000000 : ℝ)^79 ≤ (174160583627/100000000000000 : ℝ)^63 := by
    have hnat : (31529337 : ℕ)^79*100000000000000^63 ≤ 174160583627^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31529337 5000000000 174160583627 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4274004977/5000000000 : ℝ), (125589211/500000000 : ℝ), (-31529337/5000000000 : ℝ)] ![(82141172376449/100000000000000 : ℝ), (884233351229/5000000000000 : ℝ), (174160583627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4274004977/5000000000 : ℝ)|^79 ≤ (82141172376449/100000000000000 : ℝ)^63
        have hw : |(4274004977/5000000000 : ℝ)|=(4274004977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125589211/500000000 : ℝ)|^79 ≤ (884233351229/5000000000000 : ℝ)^63
        have hw : |(125589211/500000000 : ℝ)|=(125589211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-31529337/5000000000 : ℝ)|^79 ≤ (174160583627/100000000000000 : ℝ)^63
        have hw : |(-31529337/5000000000 : ℝ)|=(31529337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_20 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1533483829/2000000000 : ℝ)*x 0 + (52711939/200000000 : ℝ)*x 1 + (1535755849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1533483829/2000000000 : ℝ)^79 ≤ (35836349976499/50000000000000 : ℝ)^63 := by
    have hnat : (1533483829 : ℕ)^79*50000000000000^63 ≤ 35836349976499^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533483829 2000000000 35836349976499 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52711939/200000000 : ℝ)^79 ≤ (93922717673/500000000000 : ℝ)^63 := by
    have hnat : (52711939 : ℕ)^79*500000000000^63 ≤ 93922717673^63*200000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52711939 200000000 93922717673 500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1535755849/10000000000 : ℝ)^79 ≤ (298211140691/3125000000000 : ℝ)^63 := by
    have hnat : (1535755849 : ℕ)^79*3125000000000^63 ≤ 298211140691^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1535755849 10000000000 298211140691 3125000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1533483829/2000000000 : ℝ), (52711939/200000000 : ℝ), (1535755849/10000000000 : ℝ)] ![(35836349976499/50000000000000 : ℝ), (93922717673/500000000000 : ℝ), (298211140691/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1533483829/2000000000 : ℝ)|^79 ≤ (35836349976499/50000000000000 : ℝ)^63
        have hw : |(1533483829/2000000000 : ℝ)|=(1533483829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52711939/200000000 : ℝ)|^79 ≤ (93922717673/500000000000 : ℝ)^63
        have hw : |(52711939/200000000 : ℝ)|=(52711939/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1535755849/10000000000 : ℝ)|^79 ≤ (298211140691/3125000000000 : ℝ)^63
        have hw : |(1535755849/10000000000 : ℝ)|=(1535755849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_21 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-4934597/312500000 : ℝ)*x 0 + (1944393559/2500000000 : ℝ)*x 1 + (693212237/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4934597/312500000 : ℝ)^79 ≤ (110124229241/20000000000000 : ℝ)^63 := by
    have hnat : (4934597 : ℕ)^79*20000000000000^63 ≤ 110124229241^63*312500000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4934597 312500000 110124229241 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1944393559/2500000000 : ℝ)^79 ≤ (18241563399977/25000000000000 : ℝ)^63 := by
    have hnat : (1944393559 : ℕ)^79*25000000000000^63 ≤ 18241563399977^63*2500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944393559 2500000000 18241563399977 25000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693212237/2000000000 : ℝ)^79 ≤ (26483125241981/100000000000000 : ℝ)^63 := by
    have hnat : (693212237 : ℕ)^79*100000000000000^63 ≤ 26483125241981^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693212237 2000000000 26483125241981 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4934597/312500000 : ℝ), (1944393559/2500000000 : ℝ), (693212237/2000000000 : ℝ)] ![(110124229241/20000000000000 : ℝ), (18241563399977/25000000000000 : ℝ), (26483125241981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4934597/312500000 : ℝ)|^79 ≤ (110124229241/20000000000000 : ℝ)^63
        have hw : |(-4934597/312500000 : ℝ)|=(4934597/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1944393559/2500000000 : ℝ)|^79 ≤ (18241563399977/25000000000000 : ℝ)^63
        have hw : |(1944393559/2500000000 : ℝ)|=(1944393559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(693212237/2000000000 : ℝ)|^79 ≤ (26483125241981/100000000000000 : ℝ)^63
        have hw : |(693212237/2000000000 : ℝ)|=(693212237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_22 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4228912737/5000000000 : ℝ)*x 0 + (-10356109/5000000000 : ℝ)*x 1 + (2648615073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4228912737/5000000000 : ℝ)^79 ≤ (16211184140919/20000000000000 : ℝ)^63 := by
    have hnat : (4228912737 : ℕ)^79*20000000000000^63 ≤ 16211184140919^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228912737 5000000000 16211184140919 20000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10356109/5000000000 : ℝ)^79 ≤ (5389436747/12500000000000 : ℝ)^63 := by
    have hnat : (10356109 : ℕ)^79*12500000000000^63 ≤ 5389436747^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10356109 5000000000 5389436747 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2648615073/10000000000 : ℝ)^79 ≤ (2362620473517/12500000000000 : ℝ)^63 := by
    have hnat : (2648615073 : ℕ)^79*12500000000000^63 ≤ 2362620473517^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648615073 10000000000 2362620473517 12500000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4228912737/5000000000 : ℝ), (-10356109/5000000000 : ℝ), (2648615073/10000000000 : ℝ)] ![(16211184140919/20000000000000 : ℝ), (5389436747/12500000000000 : ℝ), (2362620473517/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4228912737/5000000000 : ℝ)|^79 ≤ (16211184140919/20000000000000 : ℝ)^63
        have hw : |(4228912737/5000000000 : ℝ)|=(4228912737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10356109/5000000000 : ℝ)|^79 ≤ (5389436747/12500000000000 : ℝ)^63
        have hw : |(-10356109/5000000000 : ℝ)|=(10356109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2648615073/10000000000 : ℝ)|^79 ≤ (2362620473517/12500000000000 : ℝ)^63
        have hw : |(2648615073/10000000000 : ℝ)|=(2648615073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_23 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (46155441/500000000 : ℝ)*x 0 + (1826411511/2000000000 : ℝ)*x 1 + (-1021191269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46155441/500000000 : ℝ)^79 ≤ (5040341778877/100000000000000 : ℝ)^63 := by
    have hnat : (46155441 : ℕ)^79*100000000000000^63 ≤ 5040341778877^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46155441 500000000 5040341778877 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1826411511/2000000000 : ℝ)^79 ≤ (44619462122433/50000000000000 : ℝ)^63 := by
    have hnat : (1826411511 : ℕ)^79*50000000000000^63 ≤ 44619462122433^63*2000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1826411511 2000000000 44619462122433 50000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021191269/10000000000 : ℝ)^79 ≤ (178772936239/3125000000000 : ℝ)^63 := by
    have hnat : (1021191269 : ℕ)^79*3125000000000^63 ≤ 178772936239^63*10000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021191269 10000000000 178772936239 3125000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(46155441/500000000 : ℝ), (1826411511/2000000000 : ℝ), (-1021191269/10000000000 : ℝ)] ![(5040341778877/100000000000000 : ℝ), (44619462122433/50000000000000 : ℝ), (178772936239/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(46155441/500000000 : ℝ)|^79 ≤ (5040341778877/100000000000000 : ℝ)^63
        have hw : |(46155441/500000000 : ℝ)|=(46155441/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1826411511/2000000000 : ℝ)|^79 ≤ (44619462122433/50000000000000 : ℝ)^63
        have hw : |(1826411511/2000000000 : ℝ)|=(1826411511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021191269/10000000000 : ℝ)|^79 ≤ (178772936239/3125000000000 : ℝ)^63
        have hw : |(-1021191269/10000000000 : ℝ)|=(1021191269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c318063_s0_s0_27 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ)) (x : Fin 3 → ℝ) :
    (388006129/500000000 : ℝ)*x 0 + (4783607/19531250 : ℝ)*x 1 + (803749947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (388006129/500000000 : ℝ)^79 ≤ (72761006401663/100000000000000 : ℝ)^63 := by
    have hnat : (388006129 : ℕ)^79*100000000000000^63 ≤ 72761006401663^63*500000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388006129 500000000 72761006401663 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4783607/19531250 : ℝ)^79 ≤ (17133942888729/100000000000000 : ℝ)^63 := by
    have hnat : (4783607 : ℕ)^79*100000000000000^63 ≤ 17133942888729^63*19531250^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783607 19531250 17133942888729 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803749947/5000000000 : ℝ)^79 ≤ (10105050693661/100000000000000 : ℝ)^63 := by
    have hnat : (803749947 : ℕ)^79*100000000000000^63 ≤ 10105050693661^63*5000000000^79 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803749947 5000000000 10105050693661 100000000000000 79 63 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (79/16 : ℝ)) 79 63 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(388006129/500000000 : ℝ), (4783607/19531250 : ℝ), (803749947/5000000000 : ℝ)] ![(72761006401663/100000000000000 : ℝ), (17133942888729/100000000000000 : ℝ), (10105050693661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(388006129/500000000 : ℝ)|^79 ≤ (72761006401663/100000000000000 : ℝ)^63
        have hw : |(388006129/500000000 : ℝ)|=(388006129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4783607/19531250 : ℝ)|^79 ≤ (17133942888729/100000000000000 : ℝ)^63
        have hw : |(4783607/19531250 : ℝ)|=(4783607/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803749947/5000000000 : ℝ)|^79 ≤ (10105050693661/100000000000000 : ℝ)^63
        have hw : |(803749947/5000000000 : ℝ)|=(803749947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c318063_s0 (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((75399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15019/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15019/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7277/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7277/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (39911/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (39911/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (39911/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34269/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base27 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 1 0+(1 : ℝ)*X 2 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s0_pow0 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner0b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow0,s0_corner0a]) (by linarith only [s0_pow0,s0_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order0.2.2])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow1 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner1b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow1,s0_corner1a]) (by linarith only [s0_pow1,s0_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order1.2.2])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s0_pow2 : (1 : ℝ) ^ (39/8 : ℝ) ≤ (1 : ℝ) := by
    have hpowers : (1 : ℝ)^39 ≤ (1 : ℝ)^8 := by
      have hnat : (1 : ℕ)^39*1^8 ≤ 1^8*1^39 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 39 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2a : (2 : ℝ) ≤ (5763943924246341/5000000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (2 : ℝ)^8 ≤ (5763943924246341/5000000000000000 : ℝ)^39 := by
      have hnat : (2 : ℕ)^8*5000000000000000^39 ≤ 5763943924246341^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 1 5763943924246341 5000000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5763943924246341/5000000000000000 : ℝ)) (X := (2 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have s0_corner2b : (3 : ℝ) ≤ (782980676308869/625000000000000 : ℝ) ^ (39/8 : ℝ) := by
    have hpowers : (3 : ℝ)^8 ≤ (782980676308869/625000000000000 : ℝ)^39 := by
      have hnat : (3 : ℕ)^8*625000000000000^39 ≤ 782980676308869^39*1^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 1 782980676308869 625000000000000 8 39 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (782980676308869/625000000000000 : ℝ)) (X := (3 : ℝ)) (by norm_num) 39 8 (by norm_num) hpowers
    exact h
  have major_s0_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (39/8 : ℝ)) (rho := (1 : ℝ)) (alpha := (763943924246341/5000000000000000 : ℝ)) (beta := (499901486224611/5000000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s0_pow2,s0_corner2a]) (by linarith only [s0_pow2,s0_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [order2.2.2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(763943924246341/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(499901486224611/5000000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s0_0 : ((-194793503/10000000000 : ℝ)*X 0 0+(692650493/1250000000 : ℝ)*X 0 1+(2949371419/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_2 : ((5541205827/10000000000 : ℝ)*X 2 0+(5898742023/10000000000 : ℝ)*X 2 1+(-194791033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_7 : ((-1121633277/10000000000 : ℝ)*X 0 0+(1369303433/10000000000 : ℝ)*X 0 1+(880922747/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_8 : ((1066698403/5000000000 : ℝ)*X 1 0+(-47167531/5000000000 : ℝ)*X 1 1+(8809229563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_9 : ((2107455371/10000000000 : ℝ)*X 2 0+(353795731/400000000 : ℝ)*X 2 1+(-16057609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_13 : ((773084989/2500000000 : ℝ)*X 0 0+(3652850169/5000000000 : ℝ)*X 0 1+(770826163/5000000000 : ℝ)*X 0 2+(773084989/2500000000 : ℝ)*X 1 0+(3652850169/5000000000 : ℝ)*X 1 1+(770826163/5000000000 : ℝ)*X 1 2+(773084989/2500000000 : ℝ)*X 2 0+(3652850169/5000000000 : ℝ)*X 2 1+(770826163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_14 : ((-558803/125000000 : ℝ)*X 0 0+(2050661237/10000000000 : ℝ)*X 0 1+(8881033259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_15 : ((607145537/5000000000 : ℝ)*X 1 0+(-1160797117/10000000000 : ℝ)*X 1 1+(8881033241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_16 : ((4274004977/5000000000 : ℝ)*X 2 0+(125589211/500000000 : ℝ)*X 2 1+(-31529337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_20 : ((1533483829/2000000000 : ℝ)*X 0 0+(52711939/200000000 : ℝ)*X 0 1+(1535755849/10000000000 : ℝ)*X 0 2+(1533483829/2000000000 : ℝ)*X 1 0+(52711939/200000000 : ℝ)*X 1 1+(1535755849/10000000000 : ℝ)*X 1 2+(1533483829/2000000000 : ℝ)*X 2 0+(52711939/200000000 : ℝ)*X 2 1+(1535755849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_21 : ((-4934597/312500000 : ℝ)*X 0 0+(1944393559/2500000000 : ℝ)*X 0 1+(693212237/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_22 : ((4228912737/5000000000 : ℝ)*X 1 0+(-10356109/5000000000 : ℝ)*X 1 1+(2648615073/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_23 : ((46155441/500000000 : ℝ)*X 2 0+(1826411511/2000000000 : ℝ)*X 2 1+(-1021191269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s0_27 : ((388006129/500000000 : ℝ)*X 0 0+(4783607/19531250 : ℝ)*X 0 1+(803749947/5000000000 : ℝ)*X 0 2+(388006129/500000000 : ℝ)*X 1 0+(4783607/19531250 : ℝ)*X 1 1+(803749947/5000000000 : ℝ)*X 1 2+(388006129/500000000 : ℝ)*X 2 0+(4783607/19531250 : ℝ)*X 2 1+(803749947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c318063_s0_s0_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s0_0 : (0 : ℝ) ≤ ((75399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2076014554784977676979/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68232141197/62500000000 : ℝ)*(base7) + (1700169/500000000000 : ℝ)*(base19) + (27929/25000000000 : ℝ)*(base50) + (15366375879/250000000000 : ℝ)*(base53) + (666607/1000000000000 : ℝ)*(base60) + (708801618587/500000000000 : ℝ)*(major_s0_0) + (708801618587/500000000000 : ℝ)*(major_s0_1) + (1356137733659/1000000000000 : ℝ)*(major_s0_2) + (2364677/1000000000000 : ℝ)*(sp_s0_0) + (343322809033/250000000000 : ℝ)*(sp_s0_7) + (1373326884997/1000000000000 : ℝ)*(sp_s0_8) + (1434795788851/1000000000000 : ℝ)*(sp_s0_9) + (186858957751/100000000000 : ℝ)*(sp_s0_13) + (18342263/500000000000 : ℝ)*(sp_s0_14) + (388437659179/500000000000 : ℝ)*(f.failure) + (1434795788851/1000000000000 : ℝ)*(f.sum) + (4195122575472053/5000000000000000000000000000 : ℝ)*base63 + (1305252374118351/5000000000000000000000000000 : ℝ)*base64 + (317581169444657/2500000000000000000000000000 : ℝ)*base67 + (2065108792291719/5000000000000000000000000000 : ℝ)*base69 + (380867189438017/5000000000000000000000000000 : ℝ)*base70 + (1070571991694657/2500000000000000000000000000 : ℝ)*base73 + (122550342090167/2500000000000000000000000000 : ℝ)*base75 + (642503938909833/2500000000000000000000000000 : ℝ)*base76 + (350958583305343/1250000000000000000000000000 : ℝ)*base78 + (479/2000000000000000 : ℝ)*base86 + (479/2000000000000000 : ℝ)*base88 + (2479/2000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15019/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15019/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18557900149956248922711/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (544528014431/500000000000 : ℝ)*(base7) + (1869633/1000000000000 : ℝ)*(base19) + (11430238067/125000000000 : ℝ)*(base53) + (304563277/1000000000000 : ℝ)*(base60) + (10959302179/8000000000 : ℝ)*(major_s0_0) + (10959302179/8000000000 : ℝ)*(major_s0_1) + (639235433919/500000000000 : ℝ)*(major_s0_2) + (661047/1000000000000 : ℝ)*(sp_s0_0) + (28135947/500000000000 : ℝ)*(sp_s0_8) + (63781185143/50000000000 : ℝ)*(sp_s0_14) + (1275566222379/1000000000000 : ℝ)*(sp_s0_15) + (1367066268443/1000000000000 : ℝ)*(sp_s0_16) + (1839605977557/1000000000000 : ℝ)*(sp_s0_20) + (38005589/200000000000 : ℝ)*(sp_s0_27) + (2346062427/3125000000 : ℝ)*(f.failure) + (1367066268443/1000000000000 : ℝ)*(f.sum) + (2226528713710633/5000000000000000000000000000 : ℝ)*base63 + (369004377480509/2500000000000000000000000000 : ℝ)*base65 + (31763267668631/40000000000000000000000000 : ℝ)*base66 + (2030068564290379/2500000000000000000000000000 : ℝ)*base69 + (272508494090893/5000000000000000000000000000 : ℝ)*base71 + (713869808631/40000000000000000000000000 : ℝ)*base72 + (17905020129039/40000000000000000000000000 : ℝ)*base75 + (16925456117039/40000000000000000000000000 : ℝ)*base77 + (3065027445369/20000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (29/25000000000000 : ℝ)*base86 + (29/25000000000000 : ℝ)*base88 + (1/6250000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s0_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7277/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7277/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11501932518654042455529/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (276866478793/250000000000 : ℝ)*(base7) + (1909147/1000000000000 : ℝ)*(base27) + (54244443557/500000000000 : ℝ)*(base40) + (738751/125000000000 : ℝ)*(base43) + (53163/62500000000 : ℝ)*(base49) + (1349694559713/1000000000000 : ℝ)*(major_s0_0) + (269937729941/200000000000 : ℝ)*(major_s0_1) + (1349694559713/1000000000000 : ℝ)*(major_s0_2) + (949569/500000000000 : ℝ)*(sp_s0_2) + (34032307/1000000000000 : ℝ)*(sp_s0_9) + (331797749659/250000000000 : ℝ)*(sp_s0_21) + (331799227161/250000000000 : ℝ)*(sp_s0_22) + (1327155067191/1000000000000 : ℝ)*(sp_s0_23) + (923561996083/500000000000 : ℝ)*(sp_s0_27) + (369829993071/500000000000 : ℝ)*(f.failure) + (331799227161/250000000000 : ℝ)*(f.sum) + (1824468177619769/2500000000000000000000000000 : ℝ)*base63 + (2503280149696643/5000000000000000000000000000 : ℝ)*base65 + (70638379377951/1000000000000000000000000000 : ℝ)*base67 + (5889788578260133/5000000000000000000000000000 : ℝ)*base69 + (25324842494597/625000000000000000000000000 : ℝ)*base71 + (2198567561696643/5000000000000000000000000000 : ℝ)*base73 + (1121460723095881/1000000000000000000000000000 : ℝ)*base75 + (1746969472260133/5000000000000000000000000000 : ℝ)*base77 + (373995786956801/2500000000000000000000000000 : ℝ)*base78 + (771/2000000000000000 : ℝ)*base86 + (771/2000000000000000 : ℝ)*base88 + (771/2000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (39/8 : ℝ) ≤ p) (hpb : p ≤ (79/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (7299/4000 : ℝ) (34269/20000 : ℝ) (39911/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]]) : (0 : ℝ) ≤ ((75399/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(75399/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15019/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15019/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7277/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7277/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c318063_s0 p hpa hpb X hX

#print axioms solution
