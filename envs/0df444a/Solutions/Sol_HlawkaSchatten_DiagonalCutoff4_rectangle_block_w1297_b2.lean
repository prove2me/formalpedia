-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1297_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:35:22.685032+00:00
-- url     : https://prove2.me/submissions/3a4d62ea-e487-410f-849c-225858546338

import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_rectangle_majorant
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
theorem frame_box_of_interval_base {p k A d ell u v w rho lo : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      -u ≤ X 0 0 ∧ X 0 0 ≤ -ell ∧ v ≤ X 0 1 ∧ X 0 1 ≤ w)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
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
    · intro i j hij
      rw [pair_relabel]
      exact hlower (e i) (e j) (e.injective.ne hij)
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

theorem frame_interval_of_base {p k A d rho lo R L : ℝ}
    (base : ∀ X : Fin 3 → Fin 3 → ℝ, Frame p k A d X →
      (∀ i h, i ≠ h → 0 ≤ pair X i h) →
      (∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i) →
      (∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) →
      L*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ R*pair X 0 0)
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p k A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ rho*pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → L*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ R*pair X i i := by
  have permuted (e : Equiv.Perm (Fin 3)) :
      L*pair X (e 0) (e 0) ≤ pair X (e 0) (e 1) ∧
        pair X (e 0) (e 1) ≤ R*pair X (e 0) (e 0) := by
    have hh := base (relabel e X) (frame_relabel hX e)
      (fun i j hij => by rw [pair_relabel];exact hsign (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hratio (e i) (e j) (e.injective.ne hij))
      (fun i j hij => by rw [pair_relabel];exact hlower (e i) (e j) (e.injective.ne hij))
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


theorem rectangle_pair_majorant {p a lo hi c alpha : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hlo : 0 ≤ lo) (hlohi : lo < hi) (hhi : hi ≤ 1) (halpha : 0 ≤ alpha)
    (hc : 1 ≤ c+2*alpha*lo)
    (hcorner00 : 1+2*lo^a ≤ (c+2*alpha*lo)^a)
    (hcorner10 : 1+hi^a+lo^a ≤ (c+alpha*(hi+lo))^a)
    (hcorner11 : 1+2*hi^a ≤ (c+2*alpha*hi)^a)
    (X : Fin 3 → Fin 3 → ℝ)
    (hmain : ∀ i, 0 ≤ pair X i i)
    (hlower : ∀ i h, i ≠ h → lo*pair X i i ≤ pair X i h)
    (hupper : ∀ i h, i ≠ h → |pair X i h| ≤ hi*pair X i i)
    (i j l : Fin 3) (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    lpNorm p (pair X i) ≤ c*pair X i i+alpha*(pair X i j+pair X i l) := by
  have hh := rectangle_majorant hp ha hap hlo hlohi hhi halpha hc hcorner00 hcorner10 hcorner11
    (hmain i) (hlower i j hij) ((le_abs_self _).trans (hupper i j hij))
    (hlower i l hil) ((le_abs_self _).trans (hupper i l hil))
  have he : lpNorm p (pair X i) =
      (|pair X i i|^p+|pair X i j|^p+|pair X i l|^p)^(1/p) := by
    simp only [lpNorm,Real.norm_eq_abs]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;> try contradiction
    all_goals simp [Fin.sum_univ_three] <;> ring
  rw [he]
  exact hh

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
theorem support_rectangle_w1297_s6_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-104174369/500000000 : ℝ)*x 0 + (1083011647/2000000000 : ℝ)*x 1 + (2621545879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104174369/500000000 : ℝ)^4257 ≤ (12677365111549/100000000000000 : ℝ)^3233 := by
    have hnat : (104174369 : ℕ)^4257*100000000000000^3233 ≤ 12677365111549^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104174369 500000000 12677365111549 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083011647/2000000000 : ℝ)^4257 ≤ (44588849841449/100000000000000 : ℝ)^3233 := by
    have hnat : (1083011647 : ℕ)^4257*100000000000000^3233 ≤ 44588849841449^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083011647 2000000000 44588849841449 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621545879/5000000000 : ℝ)^4257 ≤ (21366892510889/50000000000000 : ℝ)^3233 := by
    have hnat : (2621545879 : ℕ)^4257*50000000000000^3233 ≤ 21366892510889^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621545879 5000000000 21366892510889 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-104174369/500000000 : ℝ), (1083011647/2000000000 : ℝ), (2621545879/5000000000 : ℝ)] ![(12677365111549/100000000000000 : ℝ), (44588849841449/100000000000000 : ℝ), (21366892510889/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-104174369/500000000 : ℝ)|^4257 ≤ (12677365111549/100000000000000 : ℝ)^3233
        have hw : |(-104174369/500000000 : ℝ)|=(104174369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083011647/2000000000 : ℝ)|^4257 ≤ (44588849841449/100000000000000 : ℝ)^3233
        have hw : |(1083011647/2000000000 : ℝ)|=(1083011647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621545879/5000000000 : ℝ)|^4257 ≤ (21366892510889/50000000000000 : ℝ)^3233
        have hw : |(2621545879/5000000000 : ℝ)|=(2621545879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s6_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349731793/10000000000 : ℝ)*x 0 + (-2171143913/10000000000 : ℝ)*x 1 + (655386469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349731793/10000000000 : ℝ)^4257 ≤ (43881918438453/100000000000000 : ℝ)^3233 := by
    have hnat : (5349731793 : ℕ)^4257*100000000000000^3233 ≤ 43881918438453^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349731793 10000000000 43881918438453 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171143913/10000000000 : ℝ)^4257 ≤ (1673037073157/12500000000000 : ℝ)^3233 := by
    have hnat : (2171143913 : ℕ)^4257*12500000000000^3233 ≤ 1673037073157^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171143913 10000000000 1673037073157 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655386469/1250000000 : ℝ)^4257 ≤ (21366892478693/50000000000000 : ℝ)^3233 := by
    have hnat : (655386469 : ℕ)^4257*50000000000000^3233 ≤ 21366892478693^3233*1250000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655386469 1250000000 21366892478693 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349731793/10000000000 : ℝ), (-2171143913/10000000000 : ℝ), (655386469/1250000000 : ℝ)] ![(43881918438453/100000000000000 : ℝ), (1673037073157/12500000000000 : ℝ), (21366892478693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349731793/10000000000 : ℝ)|^4257 ≤ (43881918438453/100000000000000 : ℝ)^3233
        have hw : |(5349731793/10000000000 : ℝ)|=(5349731793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171143913/10000000000 : ℝ)|^4257 ≤ (1673037073157/12500000000000 : ℝ)^3233
        have hw : |(-2171143913/10000000000 : ℝ)|=(2171143913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655386469/1250000000 : ℝ)|^4257 ≤ (21366892478693/50000000000000 : ℝ)^3233
        have hw : |(655386469/1250000000 : ℝ)|=(655386469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s6_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349731789/10000000000 : ℝ)*x 0 + (5243091751/10000000000 : ℝ)*x 1 + (-27139299/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349731789/10000000000 : ℝ)^4257 ≤ (175527673581/400000000000 : ℝ)^3233 := by
    have hnat : (5349731789 : ℕ)^4257*400000000000^3233 ≤ 175527673581^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349731789 10000000000 175527673581 400000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243091751/10000000000 : ℝ)^4257 ≤ (21366892473327/50000000000000 : ℝ)^3233 := by
    have hnat : (5243091751 : ℕ)^4257*50000000000000^3233 ≤ 21366892473327^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243091751 10000000000 21366892473327 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27139299/125000000 : ℝ)^4257 ≤ (3346074160519/25000000000000 : ℝ)^3233 := by
    have hnat : (27139299 : ℕ)^4257*25000000000000^3233 ≤ 3346074160519^3233*125000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27139299 125000000 3346074160519 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349731789/10000000000 : ℝ), (5243091751/10000000000 : ℝ), (-27139299/125000000 : ℝ)] ![(175527673581/400000000000 : ℝ), (21366892473327/50000000000000 : ℝ), (3346074160519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349731789/10000000000 : ℝ)|^4257 ≤ (175527673581/400000000000 : ℝ)^3233
        have hw : |(5349731789/10000000000 : ℝ)|=(5349731789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243091751/10000000000 : ℝ)|^4257 ≤ (21366892473327/50000000000000 : ℝ)^3233
        have hw : |(5243091751/10000000000 : ℝ)|=(5243091751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27139299/125000000 : ℝ)|^4257 ≤ (3346074160519/25000000000000 : ℝ)^3233
        have hw : |(-27139299/125000000 : ℝ)|=(27139299/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s6_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169260531/5000000000 : ℝ)*x 0 + (832982599/2000000000 : ℝ)*x 1 + (1129755071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169260531/5000000000 : ℝ)^4257 ≤ (8325601555109/25000000000000 : ℝ)^3233 := by
    have hnat : (2169260531 : ℕ)^4257*25000000000000^3233 ≤ 8325601555109^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169260531 5000000000 8325601555109 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832982599/2000000000 : ℝ)^4257 ≤ (31558933581597/100000000000000 : ℝ)^3233 := by
    have hnat : (832982599 : ℕ)^4257*100000000000000^3233 ≤ 31558933581597^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832982599 2000000000 31558933581597 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129755071/2500000000 : ℝ)^4257 ≤ (68630195677/195312500000 : ℝ)^3233 := by
    have hnat : (1129755071 : ℕ)^4257*195312500000^3233 ≤ 68630195677^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129755071 2500000000 68630195677 195312500000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169260531/5000000000 : ℝ), (832982599/2000000000 : ℝ), (1129755071/2500000000 : ℝ)] ![(8325601555109/25000000000000 : ℝ), (31558933581597/100000000000000 : ℝ), (68630195677/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169260531/5000000000 : ℝ)|^4257 ≤ (8325601555109/25000000000000 : ℝ)^3233
        have hw : |(2169260531/5000000000 : ℝ)|=(2169260531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(832982599/2000000000 : ℝ)|^4257 ≤ (31558933581597/100000000000000 : ℝ)^3233
        have hw : |(832982599/2000000000 : ℝ)|=(832982599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129755071/2500000000 : ℝ)|^4257 ≤ (68630195677/195312500000 : ℝ)^3233
        have hw : |(1129755071/2500000000 : ℝ)|=(1129755071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s6_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-20835007/100000000 : ℝ)*x 0 + (1310926239/2500000000 : ℝ)*x 1 + (5414441409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20835007/100000000 : ℝ)^4257 ≤ (126774718303/1000000000000 : ℝ)^3233 := by
    have hnat : (20835007 : ℕ)^4257*1000000000000^3233 ≤ 126774718303^3233*100000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20835007 100000000 126774718303 1000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310926239/2500000000 : ℝ)^4257 ≤ (42740366002543/100000000000000 : ℝ)^3233 := by
    have hnat : (1310926239 : ℕ)^4257*100000000000000^3233 ≤ 42740366002543^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310926239 2500000000 42740366002543 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414441409/10000000000 : ℝ)^4257 ≤ (44582162154727/100000000000000 : ℝ)^3233 := by
    have hnat : (5414441409 : ℕ)^4257*100000000000000^3233 ≤ 44582162154727^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414441409 10000000000 44582162154727 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20835007/100000000 : ℝ), (1310926239/2500000000 : ℝ), (5414441409/10000000000 : ℝ)] ![(126774718303/1000000000000 : ℝ), (42740366002543/100000000000000 : ℝ), (44582162154727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20835007/100000000 : ℝ)|^4257 ≤ (126774718303/1000000000000 : ℝ)^3233
        have hw : |(-20835007/100000000 : ℝ)|=(20835007/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310926239/2500000000 : ℝ)|^4257 ≤ (42740366002543/100000000000000 : ℝ)^3233
        have hw : |(1310926239/2500000000 : ℝ)|=(1310926239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414441409/10000000000 : ℝ)|^4257 ≤ (44582162154727/100000000000000 : ℝ)^3233
        have hw : |(5414441409/10000000000 : ℝ)|=(5414441409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s6_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305676111/10000000000 : ℝ)*x 0 + (-999897233/5000000000 : ℝ)*x 1 + (216577653/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305676111/10000000000 : ℝ)^4257 ≤ (43406708363123/100000000000000 : ℝ)^3233 := by
    have hnat : (5305676111 : ℕ)^4257*100000000000000^3233 ≤ 43406708363123^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305676111 10000000000 43406708363123 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (999897233/5000000000 : ℝ)^4257 ≤ (3002782592831/25000000000000 : ℝ)^3233 := by
    have hnat : (999897233 : ℕ)^4257*25000000000000^3233 ≤ 3002782592831^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999897233 5000000000 3002782592831 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216577653/400000000 : ℝ)^4257 ≤ (5572770155501/12500000000000 : ℝ)^3233 := by
    have hnat : (216577653 : ℕ)^4257*12500000000000^3233 ≤ 5572770155501^3233*400000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216577653 400000000 5572770155501 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305676111/10000000000 : ℝ), (-999897233/5000000000 : ℝ), (216577653/400000000 : ℝ)] ![(43406708363123/100000000000000 : ℝ), (3002782592831/25000000000000 : ℝ), (5572770155501/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305676111/10000000000 : ℝ)|^4257 ≤ (43406708363123/100000000000000 : ℝ)^3233
        have hw : |(5305676111/10000000000 : ℝ)|=(5305676111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-999897233/5000000000 : ℝ)|^4257 ≤ (3002782592831/25000000000000 : ℝ)^3233
        have hw : |(-999897233/5000000000 : ℝ)|=(999897233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216577653/400000000 : ℝ)|^4257 ≤ (5572770155501/12500000000000 : ℝ)^3233
        have hw : |(216577653/400000000 : ℝ)|=(216577653/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s6_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165802383/312500000 : ℝ)*x 0 + (270722053/500000000 : ℝ)*x 1 + (-249974329/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165802383/312500000 : ℝ)^4257 ≤ (43406709925127/100000000000000 : ℝ)^3233 := by
    have hnat : (165802383 : ℕ)^4257*100000000000000^3233 ≤ 43406709925127^3233*312500000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165802383 312500000 43406709925127 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270722053/500000000 : ℝ)^4257 ≤ (5572769796363/12500000000000 : ℝ)^3233 := by
    have hnat : (270722053 : ℕ)^4257*12500000000000^3233 ≤ 5572769796363^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270722053 500000000 5572769796363 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249974329/1250000000 : ℝ)^4257 ≤ (12011131684143/100000000000000 : ℝ)^3233 := by
    have hnat : (249974329 : ℕ)^4257*100000000000000^3233 ≤ 12011131684143^3233*1250000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249974329 1250000000 12011131684143 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165802383/312500000 : ℝ), (270722053/500000000 : ℝ), (-249974329/1250000000 : ℝ)] ![(43406709925127/100000000000000 : ℝ), (5572769796363/12500000000000 : ℝ), (12011131684143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165802383/312500000 : ℝ)|^4257 ≤ (43406709925127/100000000000000 : ℝ)^3233
        have hw : |(165802383/312500000 : ℝ)|=(165802383/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270722053/500000000 : ℝ)|^4257 ≤ (5572769796363/12500000000000 : ℝ)^3233
        have hw : |(270722053/500000000 : ℝ)|=(270722053/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249974329/1250000000 : ℝ)|^4257 ≤ (12011131684143/100000000000000 : ℝ)^3233
        have hw : |(-249974329/1250000000 : ℝ)|=(249974329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s6_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (17354189/40000000 : ℝ)*x 0 + (1129439179/2500000000 : ℝ)*x 1 + (4166182997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17354189/40000000 : ℝ)^4257 ≤ (6660534181729/20000000000000 : ℝ)^3233 := by
    have hnat : (17354189 : ℕ)^4257*20000000000000^3233 ≤ 6660534181729^3233*40000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17354189 40000000 6660534181729 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1129439179/2500000000 : ℝ)^4257 ≤ (4390715455443/12500000000000 : ℝ)^3233 := by
    have hnat : (1129439179 : ℕ)^4257*12500000000000^3233 ≤ 4390715455443^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129439179 2500000000 4390715455443 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4166182997/10000000000 : ℝ)^4257 ≤ (31571605422359/100000000000000 : ℝ)^3233 := by
    have hnat : (4166182997 : ℕ)^4257*100000000000000^3233 ≤ 31571605422359^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166182997 10000000000 31571605422359 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17354189/40000000 : ℝ), (1129439179/2500000000 : ℝ), (4166182997/10000000000 : ℝ)] ![(6660534181729/20000000000000 : ℝ), (4390715455443/12500000000000 : ℝ), (31571605422359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17354189/40000000 : ℝ)|^4257 ≤ (6660534181729/20000000000000 : ℝ)^3233
        have hw : |(17354189/40000000 : ℝ)|=(17354189/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1129439179/2500000000 : ℝ)|^4257 ≤ (4390715455443/12500000000000 : ℝ)^3233
        have hw : |(1129439179/2500000000 : ℝ)|=(1129439179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4166182997/10000000000 : ℝ)|^4257 ≤ (31571605422359/100000000000000 : ℝ)^3233
        have hw : |(4166182997/10000000000 : ℝ)|=(4166182997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5519/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7339/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2757/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2757/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2757/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (2757/25000 : ℝ) ^ (133/32 : ℝ) ≤ (10480382857291517/100000000000000000000 : ℝ) := by
    have hpowers : (2757/25000 : ℝ)^133 ≤ (10480382857291517/100000000000000000000 : ℝ)^32 := by
      have hnat : (2757 : ℕ)^133*100000000000000000000^32 ≤ 10480382857291517^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2757 25000 10480382857291517 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2757/25000 : ℝ)) (X := (10480382857291517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (14689/100000 : ℝ) ^ (133/32 : ℝ) ≤ (8624848358170897/25000000000000000000 : ℝ) := by
    have hpowers : (14689/100000 : ℝ)^133 ≤ (8624848358170897/25000000000000000000 : ℝ)^32 := by
      have hnat : (14689 : ℕ)^133*25000000000000000000^32 ≤ 8624848358170897^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14689 100000 8624848358170897 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14689/100000 : ℝ)) (X := (8624848358170897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010480382857291517/50000000000000000000 : ℝ) ≤ (10000504279042333/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50010480382857291517/50000000000000000000 : ℝ)^32 ≤ (10000504279042333/10000000000000000 : ℝ)^133 := by
      have hnat : (50010480382857291517 : ℕ)^32*10000000000000000^133 ≤ 10000504279042333^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010480382857291517 50000000000000000000 10000504279042333 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000504279042333/10000000000000000 : ℝ)) (X := (50010480382857291517/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008995955257995021/20000000000000000000 : ℝ) ≤ (10001082035400073/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (20008995955257995021/20000000000000000000 : ℝ)^32 ≤ (10001082035400073/10000000000000000 : ℝ)^133 := by
      have hnat : (20008995955257995021 : ℕ)^32*10000000000000000^133 ≤ 10001082035400073^133*20000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008995955257995021 20000000000000000000 10001082035400073 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001082035400073/10000000000000000 : ℝ)) (X := (20008995955257995021/20000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508624848358170897/12500000000000000000 : ℝ) ≤ (10001659791757813/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12508624848358170897/12500000000000000000 : ℝ)^32 ≤ (10001659791757813/10000000000000000 : ℝ)^133 := by
      have hnat : (12508624848358170897 : ℕ)^32*10000000000000000^133 ≤ 10001659791757813^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508624848358170897 12500000000000000000 10001659791757813 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001659791757813/10000000000000000 : ℝ)) (X := (12508624848358170897/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10480382857291517/100000000000000000000 : ℝ) ≤ ((36599103171347667673/36610000000000000000 : ℝ)+2*(28887817887/18305000000000 : ℝ)*(2757/25000 : ℝ))^(133/32 : ℝ) := by
    rw [show (36599103171347667673/36610000000000000000 : ℝ)+2*(28887817887/18305000000000 : ℝ)*(2757/25000 : ℝ)=(10000504279042333/10000000000000000 : ℝ) by norm_num, show 1+2*(10480382857291517/100000000000000000000 : ℝ)=(50010480382857291517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8624848358170897/25000000000000000000 : ℝ)+(10480382857291517/100000000000000000000 : ℝ) ≤ ((36599103171347667673/36610000000000000000 : ℝ)+(28887817887/18305000000000 : ℝ)*((14689/100000 : ℝ)+(2757/25000 : ℝ)))^(133/32 : ℝ) := by
    rw [show (36599103171347667673/36610000000000000000 : ℝ)+(28887817887/18305000000000 : ℝ)*((14689/100000 : ℝ)+(2757/25000 : ℝ))=(10001082035400073/10000000000000000 : ℝ) by norm_num, show 1+(8624848358170897/25000000000000000000 : ℝ)+(10480382857291517/100000000000000000000 : ℝ)=(20008995955257995021/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8624848358170897/25000000000000000000 : ℝ) ≤ ((36599103171347667673/36610000000000000000 : ℝ)+2*(28887817887/18305000000000 : ℝ)*(14689/100000 : ℝ))^(133/32 : ℝ) := by
    rw [show (36599103171347667673/36610000000000000000 : ℝ)+2*(28887817887/18305000000000 : ℝ)*(14689/100000 : ℝ)=(10001659791757813/10000000000000000 : ℝ) by norm_num, show 1+2*(8624848358170897/25000000000000000000 : ℝ)=(12508624848358170897/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36599103171347667673/36610000000000000000 : ℝ)*(X 1 0+X 2 0)+(28887817887/18305000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (36599103171347667673/36610000000000000000 : ℝ)) (alpha := (28887817887/18305000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36599103171347667673/36610000000000000000 : ℝ)*(X 0 1+X 2 1)+(28887817887/18305000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (36599103171347667673/36610000000000000000 : ℝ)) (alpha := (28887817887/18305000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36599103171347667673/36610000000000000000 : ℝ)*(X 0 2+X 1 2)+(28887817887/18305000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (2757/25000 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (36599103171347667673/36610000000000000000 : ℝ)) (alpha := (28887817887/18305000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-104174369/500000000 : ℝ)*X 0 0+(1083011647/2000000000 : ℝ)*X 0 1+(2621545879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349731793/10000000000 : ℝ)*X 1 0+(-2171143913/10000000000 : ℝ)*X 1 1+(655386469/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349731789/10000000000 : ℝ)*X 2 0+(5243091751/10000000000 : ℝ)*X 2 1+(-27139299/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169260531/5000000000 : ℝ)*X 0 0+(832982599/2000000000 : ℝ)*X 0 1+(1129755071/2500000000 : ℝ)*X 0 2+(2169260531/5000000000 : ℝ)*X 1 0+(832982599/2000000000 : ℝ)*X 1 1+(1129755071/2500000000 : ℝ)*X 1 2+(2169260531/5000000000 : ℝ)*X 2 0+(832982599/2000000000 : ℝ)*X 2 1+(1129755071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-20835007/100000000 : ℝ)*X 0 0+(1310926239/2500000000 : ℝ)*X 0 1+(5414441409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305676111/10000000000 : ℝ)*X 1 0+(-999897233/5000000000 : ℝ)*X 1 1+(216577653/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165802383/312500000 : ℝ)*X 2 0+(270722053/500000000 : ℝ)*X 2 1+(-249974329/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((17354189/40000000 : ℝ)*X 0 0+(1129439179/2500000000 : ℝ)*X 0 1+(4166182997/10000000000 : ℝ)*X 0 2+(17354189/40000000 : ℝ)*X 1 0+(1129439179/2500000000 : ℝ)*X 1 1+(4166182997/10000000000 : ℝ)*X 1 2+(17354189/40000000 : ℝ)*X 2 0+(1129439179/2500000000 : ℝ)*X 2 1+(4166182997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9389845801874267849226457659/915250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244295609/12500000000000 : ℝ)*(base19) + (113075531/6250000000000 : ℝ)*(base23) + (75328703/100000000000000 : ℝ)*(lower2) + (26309439/10000000000000 : ℝ)*(upper3) + (149498283/100000000000000 : ℝ)*(upper5) + (4319604411737707/100000000000000 : ℝ)*(major0) + (4319604411737707/100000000000000 : ℝ)*(major1) + (1079901102934427/25000000000000 : ℝ)*(major2) + (2907563916716913/50000000000000 : ℝ)*(sp0) + (1453791144282823/25000000000000 : ℝ)*(sp1) + (1453791180571917/25000000000000 : ℝ)*(sp2) + (176501327111899/6250000000000 : ℝ)*(sp3) + (19349031169/50000000000000 : ℝ)*(sp4) + (20716211407/100000000000000 : ℝ)*(sp7) + (282404195000179/10000000000000 : ℝ)*(f.failure) + (1453791632874041/25000000000000 : ℝ)*(f.sum) + (1906229263663/915250000000000000000000000 : ℝ)*base65 + (35859447310058954189/3661000000000000000000000000000000 : ℝ)*base68 + (200583218294295947/130750000000000000000000000000000 : ℝ)*base70 + (43297176586882954189/3661000000000000000000000000000000 : ℝ)*base72 + (5188618518523/1830500000000000000000000000 : ℝ)*base74 + (728387396139795947/130750000000000000000000000000000 : ℝ)*base76 + (9507951009512954189/3661000000000000000000000000000000 : ℝ)*base78 + (2102112462062954189/3661000000000000000000000000000000 : ℝ)*base80 + (8302924816661/3661000000000000000000000000 : ℝ)*base81 + (654869/62500000000000000000 : ℝ)*base90 + (654869/62500000000000000000 : ℝ)*base92 + (1279869/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (583271091347649132057516861/114406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (345302989/25000000000000 : ℝ)*(base19) + (8539353/400000000000 : ℝ)*(base23) + (156603681/50000000000000 : ℝ)*(upper2) + (195329617/100000000000000 : ℝ)*(upper3) + (411591963/100000000000000 : ℝ)*(upper5) + (543833186824481/12500000000000 : ℝ)*(major0) + (543833186824481/12500000000000 : ℝ)*(major1) + (543833186824481/12500000000000 : ℝ)*(major2) + (907698983/4000000000000 : ℝ)*(sp1) + (923283591/4000000000000 : ℝ)*(sp2) + (5856981963188777/100000000000000 : ℝ)*(sp4) + (5856957889502247/100000000000000 : ℝ)*(sp5) + (366059796641297/6250000000000 : ℝ)*(sp6) + (2844348856061409/100000000000000 : ℝ)*(sp7) + (2844348856061409/100000000000000 : ℝ)*(f.failure) + (5856981963188777/100000000000000 : ℝ)*(f.sum) + (5218656919823/1830500000000000000000000000 : ℝ)*base66 + (2100679949285702713/457625000000000000000000000000000 : ℝ)*base67 + (3426750020721952713/457625000000000000000000000000000 : ℝ)*base69 + (1686124817807547287/457625000000000000000000000000000 : ℝ)*base72 + (9039047670283/3661000000000000000000000000 : ℝ)*base74 + (8636126092721702713/457625000000000000000000000000000 : ℝ)*base75 + (3242460922780577713/457625000000000000000000000000000 : ℝ)*base77 + (10008099323896577713/457625000000000000000000000000000 : ℝ)*base79 + (637655630349/732200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2776399/625000000000000000000 : ℝ)*base90 + (2776399/625000000000000000000 : ℝ)*base92 + (2776399/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1297_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1297_s7_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-520874977/2500000000 : ℝ)*x 0 + (541496407/1000000000 : ℝ)*x 1 + (5243177539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (520874977/2500000000 : ℝ)^4257 ≤ (2535493096971/20000000000000 : ℝ)^3233 := by
    have hnat : (520874977 : ℕ)^4257*20000000000000^3233 ≤ 2535493096971^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520874977 2500000000 2535493096971 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541496407/1000000000 : ℝ)^4257 ≤ (44587828879871/100000000000000 : ℝ)^3233 := by
    have hnat : (541496407 : ℕ)^4257*100000000000000^3233 ≤ 44587828879871^3233*1000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541496407 1000000000 44587828879871 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243177539/10000000000 : ℝ)^4257 ≤ (21367352814183/50000000000000 : ℝ)^3233 := by
    have hnat : (5243177539 : ℕ)^4257*50000000000000^3233 ≤ 21367352814183^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243177539 10000000000 21367352814183 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-520874977/2500000000 : ℝ), (541496407/1000000000 : ℝ), (5243177539/10000000000 : ℝ)] ![(2535493096971/20000000000000 : ℝ), (44587828879871/100000000000000 : ℝ), (21367352814183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-520874977/2500000000 : ℝ)|^4257 ≤ (2535493096971/20000000000000 : ℝ)^3233
        have hw : |(-520874977/2500000000 : ℝ)|=(520874977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541496407/1000000000 : ℝ)|^4257 ≤ (44587828879871/100000000000000 : ℝ)^3233
        have hw : |(541496407/1000000000 : ℝ)|=(541496407/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243177539/10000000000 : ℝ)|^4257 ≤ (21367352814183/50000000000000 : ℝ)^3233
        have hw : |(5243177539/10000000000 : ℝ)|=(5243177539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s7_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4179459/7812500 : ℝ)*x 0 + (-2171062639/10000000000 : ℝ)*x 1 + (5243177653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179459/7812500 : ℝ)^4257 ≤ (10970414068367/25000000000000 : ℝ)^3233 := by
    have hnat : (4179459 : ℕ)^4257*25000000000000^3233 ≤ 10970414068367^3233*7812500^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179459 7812500 10970414068367 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2171062639/10000000000 : ℝ)^4257 ≤ (13383636873921/100000000000000 : ℝ)^3233 := by
    have hnat : (2171062639 : ℕ)^4257*100000000000000^3233 ≤ 13383636873921^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171062639 10000000000 13383636873921 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243177653/10000000000 : ℝ)^4257 ≤ (42734706851823/100000000000000 : ℝ)^3233 := by
    have hnat : (5243177653 : ℕ)^4257*100000000000000^3233 ≤ 42734706851823^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243177653 10000000000 42734706851823 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179459/7812500 : ℝ), (-2171062639/10000000000 : ℝ), (5243177653/10000000000 : ℝ)] ![(10970414068367/25000000000000 : ℝ), (13383636873921/100000000000000 : ℝ), (42734706851823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179459/7812500 : ℝ)|^4257 ≤ (10970414068367/25000000000000 : ℝ)^3233
        have hw : |(4179459/7812500 : ℝ)|=(4179459/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2171062639/10000000000 : ℝ)|^4257 ≤ (13383636873921/100000000000000 : ℝ)^3233
        have hw : |(-2171062639/10000000000 : ℝ)|=(2171062639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243177653/10000000000 : ℝ)|^4257 ≤ (42734706851823/100000000000000 : ℝ)^3233
        have hw : |(5243177653/10000000000 : ℝ)|=(5243177653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s7_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349706889/10000000000 : ℝ)*x 0 + (5243179481/10000000000 : ℝ)*x 1 + (-2171061061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349706889/10000000000 : ℝ)^4257 ≤ (21940824729121/50000000000000 : ℝ)^3233 := by
    have hnat : (5349706889 : ℕ)^4257*50000000000000^3233 ≤ 21940824729121^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349706889 10000000000 21940824729121 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243179481/10000000000 : ℝ)^4257 ≤ (10683681617519/25000000000000 : ℝ)^3233 := by
    have hnat : (5243179481 : ℕ)^4257*25000000000000^3233 ≤ 10683681617519^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243179481 10000000000 10683681617519 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171061061/10000000000 : ℝ)^4257 ≤ (13383624065173/100000000000000 : ℝ)^3233 := by
    have hnat : (2171061061 : ℕ)^4257*100000000000000^3233 ≤ 13383624065173^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171061061 10000000000 13383624065173 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349706889/10000000000 : ℝ), (5243179481/10000000000 : ℝ), (-2171061061/10000000000 : ℝ)] ![(21940824729121/50000000000000 : ℝ), (10683681617519/25000000000000 : ℝ), (13383624065173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349706889/10000000000 : ℝ)|^4257 ≤ (21940824729121/50000000000000 : ℝ)^3233
        have hw : |(5349706889/10000000000 : ℝ)|=(5349706889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243179481/10000000000 : ℝ)|^4257 ≤ (10683681617519/25000000000000 : ℝ)^3233
        have hw : |(5243179481/10000000000 : ℝ)|=(5243179481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171061061/10000000000 : ℝ)|^4257 ≤ (13383624065173/100000000000000 : ℝ)^3233
        have hw : |(-2171061061/10000000000 : ℝ)|=(2171061061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s7_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2169264381/5000000000 : ℝ)*x 0 + (4165098659/10000000000 : ℝ)*x 1 + (4518831753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169264381/5000000000 : ℝ)^4257 ≤ (1332099361843/4000000000000 : ℝ)^3233 := by
    have hnat : (2169264381 : ℕ)^4257*4000000000000^3233 ≤ 1332099361843^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169264381 5000000000 1332099361843 4000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4165098659/10000000000 : ℝ)^4257 ≤ (631215720513/2000000000000 : ℝ)^3233 := by
    have hnat : (4165098659 : ℕ)^4257*2000000000000^3233 ≤ 631215720513^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165098659 10000000000 631215720513 2000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518831753/10000000000 : ℝ)^4257 ≤ (35136729913541/100000000000000 : ℝ)^3233 := by
    have hnat : (4518831753 : ℕ)^4257*100000000000000^3233 ≤ 35136729913541^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518831753 10000000000 35136729913541 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169264381/5000000000 : ℝ), (4165098659/10000000000 : ℝ), (4518831753/10000000000 : ℝ)] ![(1332099361843/4000000000000 : ℝ), (631215720513/2000000000000 : ℝ), (35136729913541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169264381/5000000000 : ℝ)|^4257 ≤ (1332099361843/4000000000000 : ℝ)^3233
        have hw : |(2169264381/5000000000 : ℝ)|=(2169264381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4165098659/10000000000 : ℝ)|^4257 ≤ (631215720513/2000000000000 : ℝ)^3233
        have hw : |(4165098659/10000000000 : ℝ)|=(4165098659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518831753/10000000000 : ℝ)|^4257 ≤ (35136729913541/100000000000000 : ℝ)^3233
        have hw : |(4518831753/10000000000 : ℝ)|=(4518831753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s7_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083511809/10000000000 : ℝ)*x 0 + (5243790919/10000000000 : ℝ)*x 1 + (676793513/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083511809/10000000000 : ℝ)^4257 ≤ (2535512166973/20000000000000 : ℝ)^3233 := by
    have hnat : (2083511809 : ℕ)^4257*20000000000000^3233 ≤ 2535512166973^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083511809 10000000000 2535512166973 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243790919/10000000000 : ℝ)^4257 ≤ (42741288596543/100000000000000 : ℝ)^3233 := by
    have hnat : (5243790919 : ℕ)^4257*100000000000000^3233 ≤ 42741288596543^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243790919 10000000000 42741288596543 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676793513/1250000000 : ℝ)^4257 ≤ (44581150553969/100000000000000 : ℝ)^3233 := by
    have hnat : (676793513 : ℕ)^4257*100000000000000^3233 ≤ 44581150553969^3233*1250000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676793513 1250000000 44581150553969 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083511809/10000000000 : ℝ), (5243790919/10000000000 : ℝ), (676793513/1250000000 : ℝ)] ![(2535512166973/20000000000000 : ℝ), (42741288596543/100000000000000 : ℝ), (44581150553969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083511809/10000000000 : ℝ)|^4257 ≤ (2535512166973/20000000000000 : ℝ)^3233
        have hw : |(-2083511809/10000000000 : ℝ)|=(2083511809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243790919/10000000000 : ℝ)|^4257 ≤ (42741288596543/100000000000000 : ℝ)^3233
        have hw : |(5243790919/10000000000 : ℝ)|=(5243790919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676793513/1250000000 : ℝ)|^4257 ≤ (44581150553969/100000000000000 : ℝ)^3233
        have hw : |(676793513/1250000000 : ℝ)|=(676793513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s7_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305698079/10000000000 : ℝ)*x 0 + (-1999892211/10000000000 : ℝ)*x 1 + (2707174099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305698079/10000000000 : ℝ)^4257 ≤ (4340694501223/10000000000000 : ℝ)^3233 := by
    have hnat : (5305698079 : ℕ)^4257*10000000000000^3233 ≤ 4340694501223^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305698079 10000000000 4340694501223 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999892211/10000000000 : ℝ)^4257 ≤ (2402380679563/20000000000000 : ℝ)^3233 := by
    have hnat : (1999892211 : ℕ)^4257*20000000000000^3233 ≤ 2402380679563^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999892211 10000000000 2402380679563 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707174099/5000000000 : ℝ)^4257 ≤ (22290575786551/50000000000000 : ℝ)^3233 := by
    have hnat : (2707174099 : ℕ)^4257*50000000000000^3233 ≤ 22290575786551^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707174099 5000000000 22290575786551 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305698079/10000000000 : ℝ), (-1999892211/10000000000 : ℝ), (2707174099/5000000000 : ℝ)] ![(4340694501223/10000000000000 : ℝ), (2402380679563/20000000000000 : ℝ), (22290575786551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305698079/10000000000 : ℝ)|^4257 ≤ (4340694501223/10000000000000 : ℝ)^3233
        have hw : |(5305698079/10000000000 : ℝ)|=(5305698079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1999892211/10000000000 : ℝ)|^4257 ≤ (2402380679563/20000000000000 : ℝ)^3233
        have hw : |(-1999892211/10000000000 : ℝ)|=(1999892211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707174099/5000000000 : ℝ)|^4257 ≤ (22290575786551/50000000000000 : ℝ)^3233
        have hw : |(2707174099/5000000000 : ℝ)|=(2707174099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s7_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305698207/10000000000 : ℝ)*x 0 + (270717407/500000000 : ℝ)*x 1 + (-1999892117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305698207/10000000000 : ℝ)^4257 ≤ (678233537361/1562500000000 : ℝ)^3233 := by
    have hnat : (5305698207 : ℕ)^4257*1562500000000^3233 ≤ 678233537361^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305698207 10000000000 678233537361 1562500000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270717407/500000000 : ℝ)^4257 ≤ (1783246037771/4000000000000 : ℝ)^3233 := by
    have hnat : (270717407 : ℕ)^4257*4000000000000^3233 ≤ 1783246037771^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270717407 500000000 1783246037771 4000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1999892117/10000000000 : ℝ)^4257 ≤ (7507439159/62500000000 : ℝ)^3233 := by
    have hnat : (1999892117 : ℕ)^4257*62500000000^3233 ≤ 7507439159^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999892117 10000000000 7507439159 62500000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305698207/10000000000 : ℝ), (270717407/500000000 : ℝ), (-1999892117/10000000000 : ℝ)] ![(678233537361/1562500000000 : ℝ), (1783246037771/4000000000000 : ℝ), (7507439159/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305698207/10000000000 : ℝ)|^4257 ≤ (678233537361/1562500000000 : ℝ)^3233
        have hw : |(5305698207/10000000000 : ℝ)|=(5305698207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270717407/500000000 : ℝ)|^4257 ≤ (1783246037771/4000000000000 : ℝ)^3233
        have hw : |(270717407/500000000 : ℝ)|=(270717407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1999892117/10000000000 : ℝ)|^4257 ≤ (7507439159/62500000000 : ℝ)^3233
        have hw : |(-1999892117/10000000000 : ℝ)|=(1999892117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s7_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173542143/400000000 : ℝ)*x 0 + (2258785807/5000000000 : ℝ)*x 1 + (2083183251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173542143/400000000 : ℝ)^4257 ≤ (4162841854621/12500000000000 : ℝ)^3233 := by
    have hnat : (173542143 : ℕ)^4257*12500000000000^3233 ≤ 4162841854621^3233*400000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173542143 400000000 4162841854621 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258785807/5000000000 : ℝ)^4257 ≤ (878095716147/2500000000000 : ℝ)^3233 := by
    have hnat : (2258785807 : ℕ)^4257*2500000000000^3233 ≤ 878095716147^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258785807 5000000000 878095716147 2500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083183251/5000000000 : ℝ)^4257 ≤ (15786718250931/50000000000000 : ℝ)^3233 := by
    have hnat : (2083183251 : ℕ)^4257*50000000000000^3233 ≤ 15786718250931^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083183251 5000000000 15786718250931 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173542143/400000000 : ℝ), (2258785807/5000000000 : ℝ), (2083183251/5000000000 : ℝ)] ![(4162841854621/12500000000000 : ℝ), (878095716147/2500000000000 : ℝ), (15786718250931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173542143/400000000 : ℝ)|^4257 ≤ (4162841854621/12500000000000 : ℝ)^3233
        have hw : |(173542143/400000000 : ℝ)|=(173542143/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258785807/5000000000 : ℝ)|^4257 ≤ (878095716147/2500000000000 : ℝ)^3233
        have hw : |(2258785807/5000000000 : ℝ)|=(2258785807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083183251/5000000000 : ℝ)|^4257 ≤ (15786718250931/50000000000000 : ℝ)^3233
        have hw : |(2083183251/5000000000 : ℝ)|=(2083183251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (69/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3669/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5519/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5519/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5519/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5519/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5519/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5519/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (5519/50000 : ℝ) ^ (133/32 : ℝ) ≤ (10519938049226381/100000000000000000000 : ℝ) := by
    have hpowers : (5519/50000 : ℝ)^133 ≤ (10519938049226381/100000000000000000000 : ℝ)^32 := by
      have hnat : (5519 : ℕ)^133*100000000000000000000^32 ≤ 10519938049226381^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5519 50000 10519938049226381 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5519/50000 : ℝ)) (X := (10519938049226381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (7339/50000 : ℝ) ^ (133/32 : ℝ) ≤ (34392142691377377/100000000000000000000 : ℝ) := by
    have hpowers : (7339/50000 : ℝ)^133 ≤ (34392142691377377/100000000000000000000 : ℝ)^32 := by
      have hnat : (7339 : ℕ)^133*100000000000000000000^32 ≤ 34392142691377377^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7339 50000 34392142691377377 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7339/50000 : ℝ)) (X := (34392142691377377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010519938049226381/50000000000000000000 : ℝ) ≤ (10000506182146573/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50010519938049226381/50000000000000000000 : ℝ)^32 ≤ (10000506182146573/10000000000000000 : ℝ)^133 := by
      have hnat : (50010519938049226381 : ℕ)^32*10000000000000000^133 ≤ 10000506182146573^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010519938049226381 50000000000000000000 10000506182146573 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000506182146573/10000000000000000 : ℝ)) (X := (50010519938049226381/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022456040370301879/50000000000000000000 : ℝ) ≤ (10001080407190683/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50022456040370301879/50000000000000000000 : ℝ)^32 ≤ (10001080407190683/10000000000000000 : ℝ)^133 := by
      have hnat : (50022456040370301879 : ℕ)^32*10000000000000000^133 ≤ 10001080407190683^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022456040370301879 50000000000000000000 10001080407190683 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001080407190683/10000000000000000 : ℝ)) (X := (50022456040370301879/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034392142691377377/50000000000000000000 : ℝ) ≤ (10001654632234793/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50034392142691377377/50000000000000000000 : ℝ)^32 ≤ (10001654632234793/10000000000000000 : ℝ)^133 := by
      have hnat : (50034392142691377377 : ℕ)^32*10000000000000000^133 ≤ 10001654632234793^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034392142691377377 50000000000000000000 10001654632234793 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001654632234793/10000000000000000 : ℝ)) (X := (50034392142691377377/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10519938049226381/100000000000000000000 : ℝ) ≤ ((454864573886746917/455000000000000000 : ℝ)+2*(57422504411/36400000000000 : ℝ)*(5519/50000 : ℝ))^(133/32 : ℝ) := by
    rw [show (454864573886746917/455000000000000000 : ℝ)+2*(57422504411/36400000000000 : ℝ)*(5519/50000 : ℝ)=(10000506182146573/10000000000000000 : ℝ) by norm_num, show 1+2*(10519938049226381/100000000000000000000 : ℝ)=(50010519938049226381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34392142691377377/100000000000000000000 : ℝ)+(10519938049226381/100000000000000000000 : ℝ) ≤ ((454864573886746917/455000000000000000 : ℝ)+(57422504411/36400000000000 : ℝ)*((7339/50000 : ℝ)+(5519/50000 : ℝ)))^(133/32 : ℝ) := by
    rw [show (454864573886746917/455000000000000000 : ℝ)+(57422504411/36400000000000 : ℝ)*((7339/50000 : ℝ)+(5519/50000 : ℝ))=(10001080407190683/10000000000000000 : ℝ) by norm_num, show 1+(34392142691377377/100000000000000000000 : ℝ)+(10519938049226381/100000000000000000000 : ℝ)=(50022456040370301879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34392142691377377/100000000000000000000 : ℝ) ≤ ((454864573886746917/455000000000000000 : ℝ)+2*(57422504411/36400000000000 : ℝ)*(7339/50000 : ℝ))^(133/32 : ℝ) := by
    rw [show (454864573886746917/455000000000000000 : ℝ)+2*(57422504411/36400000000000 : ℝ)*(7339/50000 : ℝ)=(10001654632234793/10000000000000000 : ℝ) by norm_num, show 1+2*(34392142691377377/100000000000000000000 : ℝ)=(50034392142691377377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (454864573886746917/455000000000000000 : ℝ)*(X 1 0+X 2 0)+(57422504411/36400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (454864573886746917/455000000000000000 : ℝ)) (alpha := (57422504411/36400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (454864573886746917/455000000000000000 : ℝ)*(X 0 1+X 2 1)+(57422504411/36400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (454864573886746917/455000000000000000 : ℝ)) (alpha := (57422504411/36400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (454864573886746917/455000000000000000 : ℝ)*(X 0 2+X 1 2)+(57422504411/36400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (5519/50000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (454864573886746917/455000000000000000 : ℝ)) (alpha := (57422504411/36400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-520874977/2500000000 : ℝ)*X 0 0+(541496407/1000000000 : ℝ)*X 0 1+(5243177539/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4179459/7812500 : ℝ)*X 1 0+(-2171062639/10000000000 : ℝ)*X 1 1+(5243177653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349706889/10000000000 : ℝ)*X 2 0+(5243179481/10000000000 : ℝ)*X 2 1+(-2171061061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169264381/5000000000 : ℝ)*X 0 0+(4165098659/10000000000 : ℝ)*X 0 1+(4518831753/10000000000 : ℝ)*X 0 2+(2169264381/5000000000 : ℝ)*X 1 0+(4165098659/10000000000 : ℝ)*X 1 1+(4518831753/10000000000 : ℝ)*X 1 2+(2169264381/5000000000 : ℝ)*X 2 0+(4165098659/10000000000 : ℝ)*X 2 1+(4518831753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2083511809/10000000000 : ℝ)*X 0 0+(5243790919/10000000000 : ℝ)*X 0 1+(676793513/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305698079/10000000000 : ℝ)*X 1 0+(-1999892211/10000000000 : ℝ)*X 1 1+(2707174099/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305698207/10000000000 : ℝ)*X 2 0+(270717407/500000000 : ℝ)*X 2 1+(-1999892117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173542143/400000000 : ℝ)*X 0 0+(2258785807/5000000000 : ℝ)*X 0 1+(2083183251/5000000000 : ℝ)*X 0 2+(173542143/400000000 : ℝ)*X 1 0+(2258785807/5000000000 : ℝ)*X 1 1+(2083183251/5000000000 : ℝ)*X 1 2+(173542143/400000000 : ℝ)*X 2 0+(2258785807/5000000000 : ℝ)*X 2 1+(2083183251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5851470494130983174626413/875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2466171689/100000000000000 : ℝ)*(base19) + (354017423/20000000000000 : ℝ)*(base23) + (47687189/50000000000000 : ℝ)*(lower2) + (189514313/20000000000000 : ℝ)*(upper5) + (4324182957031619/100000000000000 : ℝ)*(major0) + (4324182957031619/100000000000000 : ℝ)*(major1) + (216209147851581/5000000000000 : ℝ)*(major2) + (1455309369235533/25000000000000 : ℝ)*(sp0) + (5821307422588707/100000000000000 : ℝ)*(sp1) + (5821328640480969/100000000000000 : ℝ)*(sp2) + (1413510105574857/50000000000000 : ℝ)*(sp3) + (92933625953/100000000000000 : ℝ)*(sp4) + (20521807689/100000000000000 : ℝ)*(sp5) + (1506943227/10000000000000 : ℝ)*(sp7) + (88344852518187/3125000000000 : ℝ)*(f.failure) + (1164266082113617/20000000000000 : ℝ)*(f.sum) + (45815058881/40000000000000000000000000 : ℝ)*base66 + (575923683993981377/45500000000000000000000000000000 : ℝ)*base68 + (2679626625953201/1137500000000000000000000000000 : ℝ)*base69 + (161814990631981377/45500000000000000000000000000000 : ℝ)*base72 + (23106834359/40000000000000000000000000 : ℝ)*base73 + (12353963346584299/1137500000000000000000000000000 : ℝ)*base76 + (70623398324588411/6500000000000000000000000000000 : ℝ)*base78 + (97317465958588411/6500000000000000000000000000000 : ℝ)*base80 + (3824466961451/1820000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (230611/39062500000000000000 : ℝ)*base89 + (230611/39062500000000000000 : ℝ)*base91 + (80007/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187817282758206787068193407/22750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (505655331/100000000000000 : ℝ)*(base19) + (547098203/50000000000000 : ℝ)*(base23) + (13233311/6250000000000 : ℝ)*(lower1) + (75256313/100000000000000 : ℝ)*(upper3) + (38814309/20000000000000 : ℝ)*(lower4) + (1697709/1250000000000 : ℝ)*(upper5) + (4355227471045657/100000000000000 : ℝ)*(major0) + (4355227471045657/100000000000000 : ℝ)*(major1) + (4355227471045657/100000000000000 : ℝ)*(major2) + (1960641097/20000000000000 : ℝ)*(sp2) + (5863123312527121/100000000000000 : ℝ)*(sp4) + (586312280687179/10000000000000 : ℝ)*(sp5) + (5863112415125229/100000000000000 : ℝ)*(sp6) + (1423665677187013/50000000000000 : ℝ)*(sp7) + (1423665677187013/50000000000000 : ℝ)*(f.failure) + (5863123312527121/100000000000000 : ℝ)*(f.sum) + (12575093562007/1820000000000000000000000000 : ℝ)*base65 + (60452412591810433/6500000000000000000000000000000 : ℝ)*base68 + (31066520166310433/6500000000000000000000000000000 : ℝ)*base70 + (67501156872310433/6500000000000000000000000000000 : ℝ)*base72 + (1024100994347/1820000000000000000000000000 : ℝ)*base73 + (91337541899689567/6500000000000000000000000000000 : ℝ)*base75 + (4909791399310433/6500000000000000000000000000000 : ℝ)*base78 + (53681976959189567/6500000000000000000000000000000 : ℝ)*base79 + (850532326347/1820000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1603443/312500000000000000000 : ℝ)*base90 + (1603443/312500000000000000000 : ℝ)*base92 + (1603443/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1297_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5519/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1297_s8_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2083501133/10000000000 : ℝ)*x 0 + (1353736477/2500000000 : ℝ)*x 1 + (1310798743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083501133/10000000000 : ℝ)^4257 ≤ (2535495059893/20000000000000 : ℝ)^3233 := by
    have hnat : (2083501133 : ℕ)^4257*20000000000000^3233 ≤ 2535495059893^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083501133 10000000000 2535495059893 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353736477/2500000000 : ℝ)^4257 ≤ (44587631963359/100000000000000 : ℝ)^3233 := by
    have hnat : (1353736477 : ℕ)^4257*100000000000000^3233 ≤ 44587631963359^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353736477 2500000000 44587631963359 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310798743/2500000000 : ℝ)^4257 ≤ (427348927209/1000000000000 : ℝ)^3233 := by
    have hnat : (1310798743 : ℕ)^4257*1000000000000^3233 ≤ 427348927209^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310798743 2500000000 427348927209 1000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2083501133/10000000000 : ℝ), (1353736477/2500000000 : ℝ), (1310798743/2500000000 : ℝ)] ![(2535495059893/20000000000000 : ℝ), (44587631963359/100000000000000 : ℝ), (427348927209/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2083501133/10000000000 : ℝ)|^4257 ≤ (2535495059893/20000000000000 : ℝ)^3233
        have hw : |(-2083501133/10000000000 : ℝ)|=(2083501133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353736477/2500000000 : ℝ)|^4257 ≤ (44587631963359/100000000000000 : ℝ)^3233
        have hw : |(1353736477/2500000000 : ℝ)|=(1353736477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310798743/2500000000 : ℝ)|^4257 ≤ (427348927209/1000000000000 : ℝ)^3233
        have hw : |(1310798743/2500000000 : ℝ)|=(1310798743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s8_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534970303/1000000000 : ℝ)*x 0 + (-1085522847/5000000000 : ℝ)*x 1 + (2621597493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534970303/1000000000 : ℝ)^4257 ≤ (21940803889221/50000000000000 : ℝ)^3233 := by
    have hnat : (534970303 : ℕ)^4257*50000000000000^3233 ≤ 21940803889221^3233*1000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534970303 1000000000 21940803889221 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085522847/5000000000 : ℝ)^4257 ≤ (13383499330199/100000000000000 : ℝ)^3233 := by
    have hnat : (1085522847 : ℕ)^4257*100000000000000^3233 ≤ 13383499330199^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085522847 5000000000 13383499330199 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621597493/5000000000 : ℝ)^4257 ≤ (42734892871149/100000000000000 : ℝ)^3233 := by
    have hnat : (2621597493 : ℕ)^4257*100000000000000^3233 ≤ 42734892871149^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621597493 5000000000 42734892871149 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534970303/1000000000 : ℝ), (-1085522847/5000000000 : ℝ), (2621597493/5000000000 : ℝ)] ![(21940803889221/50000000000000 : ℝ), (13383499330199/100000000000000 : ℝ), (42734892871149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534970303/1000000000 : ℝ)|^4257 ≤ (21940803889221/50000000000000 : ℝ)^3233
        have hw : |(534970303/1000000000 : ℝ)|=(534970303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1085522847/5000000000 : ℝ)|^4257 ≤ (13383499330199/100000000000000 : ℝ)^3233
        have hw : |(-1085522847/5000000000 : ℝ)|=(1085522847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621597493/5000000000 : ℝ)|^4257 ≤ (42734892871149/100000000000000 : ℝ)^3233
        have hw : |(2621597493/5000000000 : ℝ)|=(2621597493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s8_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349703057/10000000000 : ℝ)*x 0 + (1048638991/2000000000 : ℝ)*x 1 + (-2171045699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349703057/10000000000 : ℝ)^4257 ≤ (2194080403503/5000000000000 : ℝ)^3233 := by
    have hnat : (5349703057 : ℕ)^4257*5000000000000^3233 ≤ 2194080403503^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349703057 10000000000 2194080403503 5000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048638991/2000000000 : ℝ)^4257 ≤ (21367446269227/50000000000000 : ℝ)^3233 := by
    have hnat : (1048638991 : ℕ)^4257*50000000000000^3233 ≤ 21367446269227^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048638991 2000000000 21367446269227 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2171045699/10000000000 : ℝ)^4257 ≤ (2676699874157/20000000000000 : ℝ)^3233 := by
    have hnat : (2171045699 : ℕ)^4257*20000000000000^3233 ≤ 2676699874157^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171045699 10000000000 2676699874157 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349703057/10000000000 : ℝ), (1048638991/2000000000 : ℝ), (-2171045699/10000000000 : ℝ)] ![(2194080403503/5000000000000 : ℝ), (21367446269227/50000000000000 : ℝ), (2676699874157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349703057/10000000000 : ℝ)|^4257 ≤ (2194080403503/5000000000000 : ℝ)^3233
        have hw : |(5349703057/10000000000 : ℝ)|=(5349703057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048638991/2000000000 : ℝ)|^4257 ≤ (21367446269227/50000000000000 : ℝ)^3233
        have hw : |(1048638991/2000000000 : ℝ)|=(1048638991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2171045699/10000000000 : ℝ)|^4257 ≤ (2676699874157/20000000000000 : ℝ)^3233
        have hw : |(-2171045699/10000000000 : ℝ)|=(2171045699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s8_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4338528733/10000000000 : ℝ)*x 0 + (2082566997/5000000000 : ℝ)*x 1 + (4518797347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338528733/10000000000 : ℝ)^4257 ≤ (6660496750593/20000000000000 : ℝ)^3233 := by
    have hnat : (4338528733 : ℕ)^4257*20000000000000^3233 ≤ 6660496750593^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338528733 10000000000 6660496750593 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082566997/5000000000 : ℝ)^4257 ≤ (7890284645013/25000000000000 : ℝ)^3233 := by
    have hnat : (2082566997 : ℕ)^4257*25000000000000^3233 ≤ 7890284645013^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082566997 5000000000 7890284645013 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518797347/10000000000 : ℝ)^4257 ≤ (17568188825373/50000000000000 : ℝ)^3233 := by
    have hnat : (4518797347 : ℕ)^4257*50000000000000^3233 ≤ 17568188825373^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518797347 10000000000 17568188825373 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338528733/10000000000 : ℝ), (2082566997/5000000000 : ℝ), (4518797347/10000000000 : ℝ)] ![(6660496750593/20000000000000 : ℝ), (7890284645013/25000000000000 : ℝ), (17568188825373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338528733/10000000000 : ℝ)|^4257 ≤ (6660496750593/20000000000000 : ℝ)^3233
        have hw : |(4338528733/10000000000 : ℝ)|=(4338528733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082566997/5000000000 : ℝ)|^4257 ≤ (7890284645013/25000000000000 : ℝ)^3233
        have hw : |(2082566997/5000000000 : ℝ)|=(2082566997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518797347/10000000000 : ℝ)|^4257 ≤ (17568188825373/50000000000000 : ℝ)^3233
        have hw : |(4518797347/10000000000 : ℝ)|=(4518797347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s8_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1041757043/5000000000 : ℝ)*x 0 + (655475969/1250000000 : ℝ)*x 1 + (2707164879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041757043/5000000000 : ℝ)^4257 ≤ (1584697384757/12500000000000 : ℝ)^3233 := by
    have hnat : (1041757043 : ℕ)^4257*12500000000000^3233 ≤ 1584697384757^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041757043 5000000000 1584697384757 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655475969/1250000000 : ℝ)^4257 ≤ (42741469256513/100000000000000 : ℝ)^3233 := by
    have hnat : (655475969 : ℕ)^4257*100000000000000^3233 ≤ 42741469256513^3233*1250000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655475969 1250000000 42741469256513 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707164879/5000000000 : ℝ)^4257 ≤ (5572618956207/12500000000000 : ℝ)^3233 := by
    have hnat : (2707164879 : ℕ)^4257*12500000000000^3233 ≤ 5572618956207^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707164879 5000000000 5572618956207 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1041757043/5000000000 : ℝ), (655475969/1250000000 : ℝ), (2707164879/5000000000 : ℝ)] ![(1584697384757/12500000000000 : ℝ), (42741469256513/100000000000000 : ℝ), (5572618956207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1041757043/5000000000 : ℝ)|^4257 ≤ (1584697384757/12500000000000 : ℝ)^3233
        have hw : |(-1041757043/5000000000 : ℝ)|=(1041757043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655475969/1250000000 : ℝ)|^4257 ≤ (42741469256513/100000000000000 : ℝ)^3233
        have hw : |(655475969/1250000000 : ℝ)|=(655475969/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707164879/5000000000 : ℝ)|^4257 ≤ (5572618956207/12500000000000 : ℝ)^3233
        have hw : |(2707164879/5000000000 : ℝ)|=(2707164879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s8_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4338554853/10000000000 : ℝ)*x 0 + (282346087/625000000 : ℝ)*x 1 + (2083200159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4338554853/10000000000 : ℝ)^4257 ≤ (3330274775403/10000000000000 : ℝ)^3233 := by
    have hnat : (4338554853 : ℕ)^4257*10000000000000^3233 ≤ 3330274775403^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338554853 10000000000 3330274775403 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282346087/625000000 : ℝ)^4257 ≤ (17561739148951/50000000000000 : ℝ)^3233 := by
    have hnat : (282346087 : ℕ)^4257*50000000000000^3233 ≤ 17561739148951^3233*625000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282346087 625000000 17561739148951 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083200159/5000000000 : ℝ)^4257 ≤ (31573773932973/100000000000000 : ℝ)^3233 := by
    have hnat : (2083200159 : ℕ)^4257*100000000000000^3233 ≤ 31573773932973^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083200159 5000000000 31573773932973 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4338554853/10000000000 : ℝ), (282346087/625000000 : ℝ), (2083200159/5000000000 : ℝ)] ![(3330274775403/10000000000000 : ℝ), (17561739148951/50000000000000 : ℝ), (31573773932973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4338554853/10000000000 : ℝ)|^4257 ≤ (3330274775403/10000000000000 : ℝ)^3233
        have hw : |(4338554853/10000000000 : ℝ)|=(4338554853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282346087/625000000 : ℝ)|^4257 ≤ (17561739148951/50000000000000 : ℝ)^3233
        have hw : |(282346087/625000000 : ℝ)|=(282346087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083200159/5000000000 : ℝ)|^4257 ≤ (31573773932973/100000000000000 : ℝ)^3233
        have hw : |(2083200159/5000000000 : ℝ)|=(2083200159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    (11041/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3669/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (69/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (69/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (69/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3669/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (69/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (69/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3669/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (69/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hlower 2 1 (by decide)
  have fm0 := f.main 0
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm0
  have fx01 := abs_le.mp (f.maximal 0 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx01
  have fx02 := abs_le.mp (f.maximal 0 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx02
  have fm1 := f.main 1
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm1
  have fx10 := abs_le.mp (f.maximal 1 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx10
  have fx12 := abs_le.mp (f.maximal 1 2)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx12
  have fm2 := f.main 2
  simp only [pair0,pair1,pair2,Pi.add_apply] at fm2
  have fx20 := abs_le.mp (f.maximal 2 0)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx20
  have fx21 := abs_le.mp (f.maximal 2 1)
  simp only [pair0,pair1,pair2,Pi.add_apply] at fx21
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base65 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base66 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base67 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base68 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base69 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base70 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base71 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base72 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base73 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base74 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base75 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base76 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base77 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base78 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base79 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base80 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base81 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base82 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base83 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base84 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base85 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base86 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base87 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base88 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base89 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base90 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base91 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base92 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base93 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base94 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base95 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  have base96 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have hpowlo : (69/625 : ℝ) ^ (133/32 : ℝ) ≤ (2631965668159841/25000000000000000000 : ℝ) := by
    have hpowers : (69/625 : ℝ)^133 ≤ (2631965668159841/25000000000000000000 : ℝ)^32 := by
      have hnat : (69 : ℕ)^133*25000000000000000000^32 ≤ 2631965668159841^32*625^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        69 625 2631965668159841 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (69/625 : ℝ)) (X := (2631965668159841/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (3669/25000 : ℝ) ^ (133/32 : ℝ) ≤ (137490679167857/400000000000000000 : ℝ) := by
    have hpowers : (3669/25000 : ℝ)^133 ≤ (137490679167857/400000000000000000 : ℝ)^32 := by
      have hnat : (3669 : ℕ)^133*400000000000000000^32 ≤ 137490679167857^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3669 25000 137490679167857 400000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3669/25000 : ℝ)) (X := (137490679167857/400000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502631965668159841/12500000000000000000 : ℝ) ≤ (2000101312684179/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12502631965668159841/12500000000000000000 : ℝ)^32 ≤ (2000101312684179/2000000000000000 : ℝ)^133 := by
      have hnat : (12502631965668159841 : ℕ)^32*2000000000000000^133 ≤ 2000101312684179^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502631965668159841 12500000000000000000 2000101312684179 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101312684179/2000000000000000 : ℝ)) (X := (12502631965668159841/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022450266232301807/50000000000000000000 : ℝ) ≤ (5000540064716071/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50022450266232301807/50000000000000000000 : ℝ)^32 ≤ (5000540064716071/5000000000000000 : ℝ)^133 := by
      have hnat : (50022450266232301807 : ℕ)^32*5000000000000000^133 ≤ 5000540064716071^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022450266232301807 50000000000000000000 5000540064716071 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000540064716071/5000000000000000 : ℝ)) (X := (50022450266232301807/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (200137490679167857/200000000000000000 : ℝ) ≤ (10001653695443389/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (200137490679167857/200000000000000000 : ℝ)^32 ≤ (10001653695443389/10000000000000000 : ℝ)^133 := by
      have hnat : (200137490679167857 : ℕ)^32*10000000000000000^133 ≤ 10001653695443389^133*200000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        200137490679167857 200000000000000000 10001653695443389 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001653695443389/10000000000000000 : ℝ)) (X := (200137490679167857/200000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2631965668159841/25000000000000000000 : ℝ) ≤ ((605819625451167341/606000000000000000 : ℝ)+2*(573566011247/363600000000000 : ℝ)*(69/625 : ℝ))^(133/32 : ℝ) := by
    rw [show (605819625451167341/606000000000000000 : ℝ)+2*(573566011247/363600000000000 : ℝ)*(69/625 : ℝ)=(2000101312684179/2000000000000000 : ℝ) by norm_num, show 1+2*(2631965668159841/25000000000000000000 : ℝ)=(12502631965668159841/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(137490679167857/400000000000000000 : ℝ)+(2631965668159841/25000000000000000000 : ℝ) ≤ ((605819625451167341/606000000000000000 : ℝ)+(573566011247/363600000000000 : ℝ)*((3669/25000 : ℝ)+(69/625 : ℝ)))^(133/32 : ℝ) := by
    rw [show (605819625451167341/606000000000000000 : ℝ)+(573566011247/363600000000000 : ℝ)*((3669/25000 : ℝ)+(69/625 : ℝ))=(5000540064716071/5000000000000000 : ℝ) by norm_num, show 1+(137490679167857/400000000000000000 : ℝ)+(2631965668159841/25000000000000000000 : ℝ)=(50022450266232301807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(137490679167857/400000000000000000 : ℝ) ≤ ((605819625451167341/606000000000000000 : ℝ)+2*(573566011247/363600000000000 : ℝ)*(3669/25000 : ℝ))^(133/32 : ℝ) := by
    rw [show (605819625451167341/606000000000000000 : ℝ)+2*(573566011247/363600000000000 : ℝ)*(3669/25000 : ℝ)=(10001653695443389/10000000000000000 : ℝ) by norm_num, show 1+2*(137490679167857/400000000000000000 : ℝ)=(200137490679167857/200000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (605819625451167341/606000000000000000 : ℝ)*(X 1 0+X 2 0)+(573566011247/363600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (69/625 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (605819625451167341/606000000000000000 : ℝ)) (alpha := (573566011247/363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (605819625451167341/606000000000000000 : ℝ)*(X 0 1+X 2 1)+(573566011247/363600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (69/625 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (605819625451167341/606000000000000000 : ℝ)) (alpha := (573566011247/363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (605819625451167341/606000000000000000 : ℝ)*(X 0 2+X 1 2)+(573566011247/363600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (69/625 : ℝ)) (hi := (3669/25000 : ℝ)) (c := (605819625451167341/606000000000000000 : ℝ)) (alpha := (573566011247/363600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2083501133/10000000000 : ℝ)*X 0 0+(1353736477/2500000000 : ℝ)*X 0 1+(1310798743/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534970303/1000000000 : ℝ)*X 1 0+(-1085522847/5000000000 : ℝ)*X 1 1+(2621597493/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349703057/10000000000 : ℝ)*X 2 0+(1048638991/2000000000 : ℝ)*X 2 1+(-2171045699/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4338528733/10000000000 : ℝ)*X 0 0+(2082566997/5000000000 : ℝ)*X 0 1+(4518797347/10000000000 : ℝ)*X 0 2+(4338528733/10000000000 : ℝ)*X 1 0+(2082566997/5000000000 : ℝ)*X 1 1+(4518797347/10000000000 : ℝ)*X 1 2+(4338528733/10000000000 : ℝ)*X 2 0+(2082566997/5000000000 : ℝ)*X 2 1+(4518797347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1041757043/5000000000 : ℝ)*X 0 0+(655475969/1250000000 : ℝ)*X 0 1+(2707164879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4338554853/10000000000 : ℝ)*X 0 0+(282346087/625000000 : ℝ)*X 0 1+(2083200159/5000000000 : ℝ)*X 0 2+(4338554853/10000000000 : ℝ)*X 1 0+(282346087/625000000 : ℝ)*X 1 1+(2083200159/5000000000 : ℝ)*X 1 2+(4338554853/10000000000 : ℝ)*X 2 0+(282346087/625000000 : ℝ)*X 2 1+(2083200159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15954924398896165314133/6060000000000000000000000000 : ℝ) := by norm_num
    linear_combination (248352473/50000000000000 : ℝ)*(base19) + (502995849/100000000000000 : ℝ)*(base23) + (2471009/20000000000000 : ℝ)*(lower2) + (13518527/20000000000000 : ℝ)*(upper3) + (24866583/50000000000000 : ℝ)*(upper5) + (4324981322797/100000000000 : ℝ)*(major0) + (4324981322797/100000000000 : ℝ)*(major1) + (4324981322797001/100000000000000 : ℝ)*(major2) + (5822394994161073/100000000000000 : ℝ)*(sp0) + (5822404830340123/100000000000000 : ℝ)*(sp1) + (5822404824049219/100000000000000 : ℝ)*(sp2) + (1413776108173347/50000000000000 : ℝ)*(sp3) + (2583220999/25000000000000 : ℝ)*(sp4) + (5014441367/100000000000000 : ℝ)*(sp5) + (1413778615394031/50000000000000 : ℝ)*(f.failure) + (1455601331761267/25000000000000 : ℝ)*(f.sum) + (62653213327189/12120000000000000000000000000 : ℝ)*base65 + (1027370698683617/90900000000000000000000000000 : ℝ)*base68 + (1791888884320433023/181800000000000000000000000000000 : ℝ)*base69 + (106947815666083/90900000000000000000000000000 : ℝ)*base71 + (1471078213189/12120000000000000000000000000 : ℝ)*base73 + (166414421036766977/181800000000000000000000000000000 : ℝ)*base76 + (1981314723091469/181800000000000000000000000000 : ℝ)*base78 + (2877040191192331/181800000000000000000000000000 : ℝ)*base79 + (9387893246263/909000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2622559/312500000000000000000 : ℝ)*base89 + (2622559/312500000000000000000 : ℝ)*base91 + (502441/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1297_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (69/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1297_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1297_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1297_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1297_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2757/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11041/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3669/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1297_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
