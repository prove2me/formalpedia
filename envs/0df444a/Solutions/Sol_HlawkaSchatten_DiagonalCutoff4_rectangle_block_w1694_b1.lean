-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1694_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:39:35.183052+00:00
-- url     : https://prove2.me/submissions/c341fee0-8d23-489f-bbf5-f3f8e3b4f630

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
theorem support_rectangle_w1694_s3_0 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1472047221/10000000000 : ℝ)*x 0 + (342531699/625000000 : ℝ)*x 1 + (5135982933/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1472047221/10000000000 : ℝ)^5175 ≤ (11470131893/125000000000 : ℝ)^4151 := by
    have hnat : (1472047221 : ℕ)^5175*125000000000^4151 ≤ 11470131893^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472047221 10000000000 11470131893 125000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342531699/625000000 : ℝ)^5175 ≤ (47248832711613/100000000000000 : ℝ)^4151 := by
    have hnat : (342531699 : ℕ)^5175*100000000000000^4151 ≤ 47248832711613^4151*625000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342531699 625000000 47248832711613 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135982933/10000000000 : ℝ)^5175 ≤ (4357506174927/10000000000000 : ℝ)^4151 := by
    have hnat : (5135982933 : ℕ)^5175*10000000000000^4151 ≤ 4357506174927^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135982933 10000000000 4357506174927 10000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1472047221/10000000000 : ℝ), (342531699/625000000 : ℝ), (5135982933/10000000000 : ℝ)] ![(11470131893/125000000000 : ℝ), (47248832711613/100000000000000 : ℝ), (4357506174927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1472047221/10000000000 : ℝ)|^5175 ≤ (11470131893/125000000000 : ℝ)^4151
        have hw : |(-1472047221/10000000000 : ℝ)|=(1472047221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342531699/625000000 : ℝ)|^5175 ≤ (47248832711613/100000000000000 : ℝ)^4151
        have hw : |(342531699/625000000 : ℝ)|=(342531699/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135982933/10000000000 : ℝ)|^5175 ≤ (4357506174927/10000000000000 : ℝ)^4151
        have hw : |(5135982933/10000000000 : ℝ)|=(5135982933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s3_1 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41788147/78125000 : ℝ)*x 0 + (-165094221/1000000000 : ℝ)*x 1 + (5135982887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41788147/78125000 : ℝ)^5175 ≤ (11459587346629/25000000000000 : ℝ)^4151 := by
    have hnat : (41788147 : ℕ)^5175*25000000000000^4151 ≤ 11459587346629^4151*78125000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41788147 78125000 11459587346629 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165094221/1000000000 : ℝ)^5175 ≤ (16541545851/156250000000 : ℝ)^4151 := by
    have hnat : (165094221 : ℕ)^5175*156250000000^4151 ≤ 16541545851^4151*1000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165094221 1000000000 16541545851 156250000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5135982887/10000000000 : ℝ)^5175 ≤ (21787530631359/50000000000000 : ℝ)^4151 := by
    have hnat : (5135982887 : ℕ)^5175*50000000000000^4151 ≤ 21787530631359^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5135982887 10000000000 21787530631359 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41788147/78125000 : ℝ), (-165094221/1000000000 : ℝ), (5135982887/10000000000 : ℝ)] ![(11459587346629/25000000000000 : ℝ), (16541545851/156250000000 : ℝ), (21787530631359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41788147/78125000 : ℝ)|^5175 ≤ (11459587346629/25000000000000 : ℝ)^4151
        have hw : |(41788147/78125000 : ℝ)|=(41788147/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165094221/1000000000 : ℝ)|^5175 ≤ (16541545851/156250000000 : ℝ)^4151
        have hw : |(-165094221/1000000000 : ℝ)|=(165094221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5135982887/10000000000 : ℝ)|^5175 ≤ (21787530631359/50000000000000 : ℝ)^4151
        have hw : |(5135982887/10000000000 : ℝ)|=(5135982887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s3_2 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337220817/2500000000 : ℝ)*x 0 + (1283995583/2500000000 : ℝ)*x 1 + (-1650942339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337220817/2500000000 : ℝ)^5175 ≤ (45838354215569/100000000000000 : ℝ)^4151 := by
    have hnat : (1337220817 : ℕ)^5175*100000000000000^4151 ≤ 45838354215569^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337220817 2500000000 45838354215569 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283995583/2500000000 : ℝ)^5175 ≤ (43575055392353/100000000000000 : ℝ)^4151 := by
    have hnat : (1283995583 : ℕ)^5175*100000000000000^4151 ≤ 43575055392353^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283995583 2500000000 43575055392353 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1650942339/10000000000 : ℝ)^5175 ≤ (2646647593977/25000000000000 : ℝ)^4151 := by
    have hnat : (1650942339 : ℕ)^5175*25000000000000^4151 ≤ 2646647593977^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650942339 10000000000 2646647593977 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337220817/2500000000 : ℝ), (1283995583/2500000000 : ℝ), (-1650942339/10000000000 : ℝ)] ![(45838354215569/100000000000000 : ℝ), (43575055392353/100000000000000 : ℝ), (2646647593977/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337220817/2500000000 : ℝ)|^5175 ≤ (45838354215569/100000000000000 : ℝ)^4151
        have hw : |(1337220817/2500000000 : ℝ)|=(1337220817/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283995583/2500000000 : ℝ)|^5175 ≤ (43575055392353/100000000000000 : ℝ)^4151
        have hw : |(1283995583/2500000000 : ℝ)|=(1283995583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1650942339/10000000000 : ℝ)|^5175 ≤ (2646647593977/25000000000000 : ℝ)^4151
        have hw : |(-1650942339/10000000000 : ℝ)|=(1650942339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s3_3 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4125793253/10000000000 : ℝ)*x 0 + (732616209/2000000000 : ℝ)*x 1 + (4625562607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4125793253/10000000000 : ℝ)^5175 ≤ (6632663072609/20000000000000 : ℝ)^4151 := by
    have hnat : (4125793253 : ℕ)^5175*20000000000000^4151 ≤ 6632663072609^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125793253 10000000000 6632663072609 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (732616209/2000000000 : ℝ)^5175 ≤ (3574068822117/12500000000000 : ℝ)^4151 := by
    have hnat : (732616209 : ℕ)^5175*12500000000000^4151 ≤ 3574068822117^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732616209 2000000000 3574068822117 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4625562607/10000000000 : ℝ)^5175 ≤ (38244134038523/100000000000000 : ℝ)^4151 := by
    have hnat : (4625562607 : ℕ)^5175*100000000000000^4151 ≤ 38244134038523^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4625562607 10000000000 38244134038523 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4125793253/10000000000 : ℝ), (732616209/2000000000 : ℝ), (4625562607/10000000000 : ℝ)] ![(6632663072609/20000000000000 : ℝ), (3574068822117/12500000000000 : ℝ), (38244134038523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4125793253/10000000000 : ℝ)|^5175 ≤ (6632663072609/20000000000000 : ℝ)^4151
        have hw : |(4125793253/10000000000 : ℝ)|=(4125793253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(732616209/2000000000 : ℝ)|^5175 ≤ (3574068822117/12500000000000 : ℝ)^4151
        have hw : |(732616209/2000000000 : ℝ)|=(732616209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4625562607/10000000000 : ℝ)|^5175 ≤ (38244134038523/100000000000000 : ℝ)^4151
        have hw : |(4625562607/10000000000 : ℝ)|=(4625562607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s3_4 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73610311/500000000 : ℝ)*x 0 + (513974503/1000000000 : ℝ)*x 1 + (1369172309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73610311/500000000 : ℝ)^5175 ≤ (9177341161507/100000000000000 : ℝ)^4151 := by
    have hnat : (73610311 : ℕ)^5175*100000000000000^4151 ≤ 9177341161507^4151*500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73610311 500000000 9177341161507 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513974503/1000000000 : ℝ)^5175 ≤ (43614857919341/100000000000000 : ℝ)^4151 := by
    have hnat : (513974503 : ℕ)^5175*100000000000000^4151 ≤ 43614857919341^4151*1000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513974503 1000000000 43614857919341 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369172309/2500000000 : ℝ)^5175 ≤ (47207800905241/100000000000000 : ℝ)^4151 := by
    have hnat : (1369172309 : ℕ)^5175*100000000000000^4151 ≤ 47207800905241^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369172309 2500000000 47207800905241 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73610311/500000000 : ℝ), (513974503/1000000000 : ℝ), (1369172309/2500000000 : ℝ)] ![(9177341161507/100000000000000 : ℝ), (43614857919341/100000000000000 : ℝ), (47207800905241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73610311/500000000 : ℝ)|^5175 ≤ (9177341161507/100000000000000 : ℝ)^4151
        have hw : |(-73610311/500000000 : ℝ)|=(73610311/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513974503/1000000000 : ℝ)|^5175 ≤ (43614857919341/100000000000000 : ℝ)^4151
        have hw : |(513974503/1000000000 : ℝ)|=(513974503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369172309/2500000000 : ℝ)|^5175 ≤ (47207800905241/100000000000000 : ℝ)^4151
        have hw : |(1369172309/2500000000 : ℝ)|=(1369172309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s3_5 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256742177/10000000000 : ℝ)*x 0 + (-1310234927/10000000000 : ℝ)*x 1 + (5476689223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256742177/10000000000 : ℝ)^5175 ≤ (560700537899/1250000000000 : ℝ)^4151 := by
    have hnat : (5256742177 : ℕ)^5175*1250000000000^4151 ≤ 560700537899^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256742177 10000000000 560700537899 1250000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310234927/10000000000 : ℝ)^5175 ≤ (1984039046701/25000000000000 : ℝ)^4151 := by
    have hnat : (1310234927 : ℕ)^5175*25000000000000^4151 ≤ 1984039046701^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310234927 10000000000 1984039046701 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5476689223/10000000000 : ℝ)^5175 ≤ (47207800765541/100000000000000 : ℝ)^4151 := by
    have hnat : (5476689223 : ℕ)^5175*100000000000000^4151 ≤ 47207800765541^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476689223 10000000000 47207800765541 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256742177/10000000000 : ℝ), (-1310234927/10000000000 : ℝ), (5476689223/10000000000 : ℝ)] ![(560700537899/1250000000000 : ℝ), (1984039046701/25000000000000 : ℝ), (47207800765541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256742177/10000000000 : ℝ)|^5175 ≤ (560700537899/1250000000000 : ℝ)^4151
        have hw : |(5256742177/10000000000 : ℝ)|=(5256742177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1310234927/10000000000 : ℝ)|^5175 ≤ (1984039046701/25000000000000 : ℝ)^4151
        have hw : |(-1310234927/10000000000 : ℝ)|=(1310234927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5476689223/10000000000 : ℝ)|^5175 ≤ (47207800765541/100000000000000 : ℝ)^4151
        have hw : |(5476689223/10000000000 : ℝ)|=(5476689223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s3_6 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256742159/10000000000 : ℝ)*x 0 + (85573269/156250000 : ℝ)*x 1 + (-1310234963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256742159/10000000000 : ℝ)^5175 ≤ (8971208568087/20000000000000 : ℝ)^4151 := by
    have hnat : (5256742159 : ℕ)^5175*20000000000000^4151 ≤ 8971208568087^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256742159 10000000000 8971208568087 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85573269/156250000 : ℝ)^5175 ≤ (23603900345159/50000000000000 : ℝ)^4151 := by
    have hnat : (85573269 : ℕ)^5175*50000000000000^4151 ≤ 23603900345159^4151*156250000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85573269 156250000 23603900345159 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310234963/10000000000 : ℝ)^5175 ≤ (7936156458649/100000000000000 : ℝ)^4151 := by
    have hnat : (1310234963 : ℕ)^5175*100000000000000^4151 ≤ 7936156458649^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310234963 10000000000 7936156458649 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256742159/10000000000 : ℝ), (85573269/156250000 : ℝ), (-1310234963/10000000000 : ℝ)] ![(8971208568087/20000000000000 : ℝ), (23603900345159/50000000000000 : ℝ), (7936156458649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256742159/10000000000 : ℝ)|^5175 ≤ (8971208568087/20000000000000 : ℝ)^4151
        have hw : |(5256742159/10000000000 : ℝ)|=(5256742159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(85573269/156250000 : ℝ)|^5175 ≤ (23603900345159/50000000000000 : ℝ)^4151
        have hw : |(85573269/156250000 : ℝ)|=(85573269/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1310234963/10000000000 : ℝ)|^5175 ≤ (7936156458649/100000000000000 : ℝ)^4151
        have hw : |(-1310234963/10000000000 : ℝ)|=(1310234963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s3_7 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2063119563/5000000000 : ℝ)*x 0 + (4615051341/10000000000 : ℝ)*x 1 + (3673748879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063119563/5000000000 : ℝ)^5175 ≤ (16583891742731/50000000000000 : ℝ)^4151 := by
    have hnat : (2063119563 : ℕ)^5175*50000000000000^4151 ≤ 16583891742731^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063119563 5000000000 16583891742731 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4615051341/10000000000 : ℝ)^5175 ≤ (38135818415917/100000000000000 : ℝ)^4151 := by
    have hnat : (4615051341 : ℕ)^5175*100000000000000^4151 ≤ 38135818415917^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4615051341 10000000000 38135818415917 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3673748879/10000000000 : ℝ)^5175 ≤ (28696398090083/100000000000000 : ℝ)^4151 := by
    have hnat : (3673748879 : ℕ)^5175*100000000000000^4151 ≤ 28696398090083^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3673748879 10000000000 28696398090083 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2063119563/5000000000 : ℝ), (4615051341/10000000000 : ℝ), (3673748879/10000000000 : ℝ)] ![(16583891742731/50000000000000 : ℝ), (38135818415917/100000000000000 : ℝ), (28696398090083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2063119563/5000000000 : ℝ)|^5175 ≤ (16583891742731/50000000000000 : ℝ)^4151
        have hw : |(2063119563/5000000000 : ℝ)|=(2063119563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4615051341/10000000000 : ℝ)|^5175 ≤ (38135818415917/100000000000000 : ℝ)^4151
        have hw : |(4615051341/10000000000 : ℝ)|=(4615051341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3673748879/10000000000 : ℝ)|^5175 ≤ (28696398090083/100000000000000 : ℝ)^4151
        have hw : |(3673748879/10000000000 : ℝ)|=(3673748879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1694_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (987/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17207/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17227/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9853/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17227/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9853/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17227/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9853/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9853/100000 : ℝ) ^ (5167/1024 : ℝ) ≤ (208731881832043/25000000000000000000 : ℝ) := by
    have hpowers : (9853/100000 : ℝ)^5167 ≤ (208731881832043/25000000000000000000 : ℝ)^1024 := by
      have hnat : (9853 : ℕ)^5167*25000000000000000000^1024 ≤ 208731881832043^1024*100000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9853 100000 208731881832043 25000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9853/100000 : ℝ)) (X := (208731881832043/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17227/100000 : ℝ) ^ (5167/1024 : ℝ) ≤ (13995598821811037/100000000000000000000 : ℝ) := by
    have hpowers : (17227/100000 : ℝ)^5167 ≤ (13995598821811037/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17227 : ℕ)^5167*100000000000000000000^1024 ≤ 13995598821811037^1024*100000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17227 100000 13995598821811037 100000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17227/100000 : ℝ)) (X := (13995598821811037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500208731881832043/12500000000000000000 : ℝ) ≤ (10000033093093261/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (12500208731881832043/12500000000000000000 : ℝ)^1024 ≤ (10000033093093261/10000000000000000 : ℝ)^5167 := by
      have hnat : (12500208731881832043 : ℕ)^1024*10000000000000000^5167 ≤ 10000033093093261^5167*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500208731881832043 12500000000000000000 10000033093093261 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033093093261/10000000000000000 : ℝ)) (X := (12500208731881832043/12500000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014830526349139209/100000000000000000000 : ℝ) ≤ (10000293895028461/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (100014830526349139209/100000000000000000000 : ℝ)^1024 ≤ (10000293895028461/10000000000000000 : ℝ)^5167 := by
      have hnat : (100014830526349139209 : ℕ)^1024*10000000000000000^5167 ≤ 10000293895028461^5167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014830526349139209 100000000000000000000 10000293895028461 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000293895028461/10000000000000000 : ℝ)) (X := (100014830526349139209/100000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013995598821811037/50000000000000000000 : ℝ) ≤ (10000554696963661/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (50013995598821811037/50000000000000000000 : ℝ)^1024 ≤ (10000554696963661/10000000000000000 : ℝ)^5167 := by
      have hnat : (50013995598821811037 : ℕ)^1024*10000000000000000^5167 ≤ 10000554696963661^5167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013995598821811037 50000000000000000000 10000554696963661 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000554696963661/10000000000000000 : ℝ)) (X := (50013995598821811037/50000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(208731881832043/25000000000000000000 : ℝ) ≤ ((12289184110922442569/12290000000000000000 : ℝ)+2*(108667473/307250000000 : ℝ)*(9853/100000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (12289184110922442569/12290000000000000000 : ℝ)+2*(108667473/307250000000 : ℝ)*(9853/100000 : ℝ)=(10000033093093261/10000000000000000 : ℝ) by norm_num, show 1+2*(208731881832043/25000000000000000000 : ℝ)=(12500208731881832043/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13995598821811037/100000000000000000000 : ℝ)+(208731881832043/25000000000000000000 : ℝ) ≤ ((12289184110922442569/12290000000000000000 : ℝ)+(108667473/307250000000 : ℝ)*((17227/100000 : ℝ)+(9853/100000 : ℝ)))^(5167/1024 : ℝ) := by
    rw [show (12289184110922442569/12290000000000000000 : ℝ)+(108667473/307250000000 : ℝ)*((17227/100000 : ℝ)+(9853/100000 : ℝ))=(10000293895028461/10000000000000000 : ℝ) by norm_num, show 1+(13995598821811037/100000000000000000000 : ℝ)+(208731881832043/25000000000000000000 : ℝ)=(100014830526349139209/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13995598821811037/100000000000000000000 : ℝ) ≤ ((12289184110922442569/12290000000000000000 : ℝ)+2*(108667473/307250000000 : ℝ)*(17227/100000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (12289184110922442569/12290000000000000000 : ℝ)+2*(108667473/307250000000 : ℝ)*(17227/100000 : ℝ)=(10000554696963661/10000000000000000 : ℝ) by norm_num, show 1+2*(13995598821811037/100000000000000000000 : ℝ)=(50013995598821811037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12289184110922442569/12290000000000000000 : ℝ)*(X 1 0+X 2 0)+(108667473/307250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (9853/100000 : ℝ)) (hi := (17227/100000 : ℝ)) (c := (12289184110922442569/12290000000000000000 : ℝ)) (alpha := (108667473/307250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12289184110922442569/12290000000000000000 : ℝ)*(X 0 1+X 2 1)+(108667473/307250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (9853/100000 : ℝ)) (hi := (17227/100000 : ℝ)) (c := (12289184110922442569/12290000000000000000 : ℝ)) (alpha := (108667473/307250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12289184110922442569/12290000000000000000 : ℝ)*(X 0 2+X 1 2)+(108667473/307250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (9853/100000 : ℝ)) (hi := (17227/100000 : ℝ)) (c := (12289184110922442569/12290000000000000000 : ℝ)) (alpha := (108667473/307250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1472047221/10000000000 : ℝ)*X 0 0+(342531699/625000000 : ℝ)*X 0 1+(5135982933/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((41788147/78125000 : ℝ)*X 1 0+(-165094221/1000000000 : ℝ)*X 1 1+(5135982887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337220817/2500000000 : ℝ)*X 2 0+(1283995583/2500000000 : ℝ)*X 2 1+(-1650942339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4125793253/10000000000 : ℝ)*X 0 0+(732616209/2000000000 : ℝ)*X 0 1+(4625562607/10000000000 : ℝ)*X 0 2+(4125793253/10000000000 : ℝ)*X 1 0+(732616209/2000000000 : ℝ)*X 1 1+(4625562607/10000000000 : ℝ)*X 1 2+(4125793253/10000000000 : ℝ)*X 2 0+(732616209/2000000000 : ℝ)*X 2 1+(4625562607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-73610311/500000000 : ℝ)*X 0 0+(513974503/1000000000 : ℝ)*X 0 1+(1369172309/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256742177/10000000000 : ℝ)*X 1 0+(-1310234927/10000000000 : ℝ)*X 1 1+(5476689223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5256742159/10000000000 : ℝ)*X 2 0+(85573269/156250000 : ℝ)*X 2 1+(-1310234963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2063119563/5000000000 : ℝ)*X 0 0+(4615051341/10000000000 : ℝ)*X 0 1+(3673748879/10000000000 : ℝ)*X 0 2+(2063119563/5000000000 : ℝ)*X 1 0+(4615051341/10000000000 : ℝ)*X 1 1+(3673748879/10000000000 : ℝ)*X 1 2+(2063119563/5000000000 : ℝ)*X 2 0+(4615051341/10000000000 : ℝ)*X 2 1+(3673748879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3605968083509860653609/614500000000000000000000000 : ℝ) := by norm_num
    linear_combination (183310249/100000000000000 : ℝ)*(base19) + (137300019/20000000000000 : ℝ)*(base23) + (72716337/50000000000000 : ℝ)*(upper2) + (15162137/20000000000000 : ℝ)*(upper3) + (268551449/100000000000000 : ℝ)*(upper5) + (9853836442309/500000000000 : ℝ)*(major0) + (9853836442309/500000000000 : ℝ)*(major1) + (9853836442309/500000000000 : ℝ)*(major2) + (580510186319097/20000000000000 : ℝ)*(sp0) + (725637687071309/25000000000000 : ℝ)*(sp1) + (2902549433558247/100000000000000 : ℝ)*(sp2) + (1038982809430649/100000000000000 : ℝ)*(sp3) + (811537143/100000000000000 : ℝ)*(sp6) + (64029301/10000000000000 : ℝ)*(sp7) + (1038983449723659/100000000000000 : ℝ)*(f.failure) + (580510186319097/20000000000000 : ℝ)*(f.sum) + (635382551339/153625000000000000000000000 : ℝ)*base65 + (26692655649723179/6145000000000000000000000000000 : ℝ)*base68 + (22502972423258179/6145000000000000000000000000000 : ℝ)*base70 + (28082115786466821/6145000000000000000000000000000 : ℝ)*base71 + (1245642576519/245800000000000000000000000 : ℝ)*base74 + (6557354284826821/6145000000000000000000000000000 : ℝ)*base75 + (40511494482701821/6145000000000000000000000000000 : ℝ)*base77 + (957258321263179/6145000000000000000000000000000 : ℝ)*base80 + (3735019528639/1229000000000000000000000000 : ℝ)*base82 + (729467/500000000000000000000 : ℝ)*base89 + (729467/500000000000000000000 : ℝ)*base91 + (729467/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2376488026001403881162031189/307250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1095081151/100000000000000 : ℝ)*(base19) + (1163931733/100000000000000 : ℝ)*(base23) + (66667007/20000000000000 : ℝ)*(lower1) + (15814601/10000000000000 : ℝ)*(upper3) + (19458517/50000000000000 : ℝ)*(lower4) + (163228257/100000000000000 : ℝ)*(upper5) + (2015097210753327/100000000000000 : ℝ)*(major0) + (2015097210753327/100000000000000 : ℝ)*(major1) + (2015097210753327/100000000000000 : ℝ)*(major2) + (142067549/50000000000000 : ℝ)*(sp2) + (18549000580329/625000000000 : ℝ)*(sp4) + (92744968680359/3125000000000 : ℝ)*(sp5) + (185489915299113/6250000000000 : ℝ)*(sp6) + (531177035415259/50000000000000 : ℝ)*(sp7) + (531177035415259/50000000000000 : ℝ)*(f.failure) + (18549000580329/625000000000 : ℝ)*(f.sum) + (523958228873/307250000000000000000000000 : ℝ)*base66 + (4307076406678822937/1229000000000000000000000000000000 : ℝ)*base68 + (12633512722674822937/1229000000000000000000000000000000 : ℝ)*base70 + (3024409034747177063/1229000000000000000000000000000000 : ℝ)*base71 + (302609032341/614500000000000000000000000 : ℝ)*base73 + (6886820296210822937/1229000000000000000000000000000000 : ℝ)*base76 + (1897207937692822937/1229000000000000000000000000000000 : ℝ)*base78 + (1320797963534822937/1229000000000000000000000000000000 : ℝ)*base80 + (829531727851/307250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (780267/250000000000000000000 : ℝ)*base89 + (780267/250000000000000000000 : ℝ)*base91 + (780267/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1694_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (987/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17207/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1694_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1694_s4_0 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-368014287/2500000000 : ℝ)*x 0 + (342529233/625000000 : ℝ)*x 1 + (2568007867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368014287/2500000000 : ℝ)^5175 ≤ (9176182660267/100000000000000 : ℝ)^4151 := by
    have hnat : (368014287 : ℕ)^5175*100000000000000^4151 ≤ 9176182660267^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368014287 2500000000 9176182660267 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342529233/625000000 : ℝ)^5175 ≤ (47248408638613/100000000000000 : ℝ)^4151 := by
    have hnat : (342529233 : ℕ)^5175*100000000000000^4151 ≤ 47248408638613^4151*625000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342529233 625000000 47248408638613 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568007867/5000000000 : ℝ)^5175 ≤ (21787704346677/50000000000000 : ℝ)^4151 := by
    have hnat : (2568007867 : ℕ)^5175*50000000000000^4151 ≤ 21787704346677^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568007867 5000000000 21787704346677 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-368014287/2500000000 : ℝ), (342529233/625000000 : ℝ), (2568007867/5000000000 : ℝ)] ![(9176182660267/100000000000000 : ℝ), (47248408638613/100000000000000 : ℝ), (21787704346677/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-368014287/2500000000 : ℝ)|^5175 ≤ (9176182660267/100000000000000 : ℝ)^4151
        have hw : |(-368014287/2500000000 : ℝ)|=(368014287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(342529233/625000000 : ℝ)|^5175 ≤ (47248408638613/100000000000000 : ℝ)^4151
        have hw : |(342529233/625000000 : ℝ)|=(342529233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568007867/5000000000 : ℝ)|^5175 ≤ (21787704346677/50000000000000 : ℝ)^4151
        have hw : |(2568007867/5000000000 : ℝ)|=(2568007867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s4_1 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069774193/2000000000 : ℝ)*x 0 + (-1650910611/10000000000 : ℝ)*x 1 + (5136018739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069774193/2000000000 : ℝ)^5175 ≤ (4583822277349/10000000000000 : ℝ)^4151 := by
    have hnat : (1069774193 : ℕ)^5175*10000000000000^4151 ≤ 4583822277349^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069774193 2000000000 4583822277349 10000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1650910611/10000000000 : ℝ)^5175 ≤ (10586336732551/100000000000000 : ℝ)^4151 := by
    have hnat : (1650910611 : ℕ)^5175*100000000000000^4151 ≤ 10586336732551^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650910611 10000000000 10586336732551 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5136018739/10000000000 : ℝ)^5175 ≤ (43575440477991/100000000000000 : ℝ)^4151 := by
    have hnat : (5136018739 : ℕ)^5175*100000000000000^4151 ≤ 43575440477991^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136018739 10000000000 43575440477991 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069774193/2000000000 : ℝ), (-1650910611/10000000000 : ℝ), (5136018739/10000000000 : ℝ)] ![(4583822277349/10000000000000 : ℝ), (10586336732551/100000000000000 : ℝ), (43575440477991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069774193/2000000000 : ℝ)|^5175 ≤ (4583822277349/10000000000000 : ℝ)^4151
        have hw : |(1069774193/2000000000 : ℝ)|=(1069774193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1650910611/10000000000 : ℝ)|^5175 ≤ (10586336732551/100000000000000 : ℝ)^4151
        have hw : |(-1650910611/10000000000 : ℝ)|=(1650910611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5136018739/10000000000 : ℝ)|^5175 ≤ (43575440477991/100000000000000 : ℝ)^4151
        have hw : |(5136018739/10000000000 : ℝ)|=(5136018739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s4_2 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534887401/1000000000 : ℝ)*x 0 + (5136016527/10000000000 : ℝ)*x 1 + (-1650909469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534887401/1000000000 : ℝ)^5175 ≤ (22919127652739/50000000000000 : ℝ)^4151 := by
    have hnat : (534887401 : ℕ)^5175*50000000000000^4151 ≤ 22919127652739^4151*1000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534887401 1000000000 22919127652739 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136016527/10000000000 : ℝ)^5175 ≤ (43575417081113/100000000000000 : ℝ)^4151 := by
    have hnat : (5136016527 : ℕ)^5175*100000000000000^4151 ≤ 43575417081113^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136016527 10000000000 43575417081113 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1650909469/10000000000 : ℝ)^5175 ≤ (2646581900769/25000000000000 : ℝ)^4151 := by
    have hnat : (1650909469 : ℕ)^5175*25000000000000^4151 ≤ 2646581900769^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650909469 10000000000 2646581900769 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534887401/1000000000 : ℝ), (5136016527/10000000000 : ℝ), (-1650909469/10000000000 : ℝ)] ![(22919127652739/50000000000000 : ℝ), (43575417081113/100000000000000 : ℝ), (2646581900769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534887401/1000000000 : ℝ)|^5175 ≤ (22919127652739/50000000000000 : ℝ)^4151
        have hw : |(534887401/1000000000 : ℝ)|=(534887401/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136016527/10000000000 : ℝ)|^5175 ≤ (43575417081113/100000000000000 : ℝ)^4151
        have hw : |(5136016527/10000000000 : ℝ)|=(5136016527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1650909469/10000000000 : ℝ)|^5175 ≤ (2646581900769/25000000000000 : ℝ)^4151
        have hw : |(-1650909469/10000000000 : ℝ)|=(1650909469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s4_3 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4125797451/10000000000 : ℝ)*x 0 + (3663188221/10000000000 : ℝ)*x 1 + (4625457343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4125797451/10000000000 : ℝ)^5175 ≤ (33163357430921/100000000000000 : ℝ)^4151 := by
    have hnat : (4125797451 : ℕ)^5175*100000000000000^4151 ≤ 33163357430921^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125797451 10000000000 33163357430921 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3663188221/10000000000 : ℝ)^5175 ≤ (2859359352601/10000000000000 : ℝ)^4151 := by
    have hnat : (3663188221 : ℕ)^5175*10000000000000^4151 ≤ 2859359352601^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3663188221 10000000000 2859359352601 10000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4625457343/10000000000 : ℝ)^5175 ≤ (9560762255383/25000000000000 : ℝ)^4151 := by
    have hnat : (4625457343 : ℕ)^5175*25000000000000^4151 ≤ 9560762255383^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4625457343 10000000000 9560762255383 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4125797451/10000000000 : ℝ), (3663188221/10000000000 : ℝ), (4625457343/10000000000 : ℝ)] ![(33163357430921/100000000000000 : ℝ), (2859359352601/10000000000000 : ℝ), (9560762255383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4125797451/10000000000 : ℝ)|^5175 ≤ (33163357430921/100000000000000 : ℝ)^4151
        have hw : |(4125797451/10000000000 : ℝ)|=(4125797451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3663188221/10000000000 : ℝ)|^5175 ≤ (2859359352601/10000000000000 : ℝ)^4151
        have hw : |(3663188221/10000000000 : ℝ)|=(3663188221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4625457343/10000000000 : ℝ)|^5175 ≤ (9560762255383/25000000000000 : ℝ)^4151
        have hw : |(4625457343/10000000000 : ℝ)|=(4625457343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s4_4 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1472216983/10000000000 : ℝ)*x 0 + (1284944429/2500000000 : ℝ)*x 1 + (2738324637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1472216983/10000000000 : ℝ)^5175 ≤ (9177424806429/100000000000000 : ℝ)^4151 := by
    have hnat : (1472216983 : ℕ)^5175*100000000000000^4151 ≤ 9177424806429^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1472216983 10000000000 9177424806429 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284944429/2500000000 : ℝ)^5175 ≤ (5451900463687/12500000000000 : ℝ)^4151 := by
    have hnat : (1284944429 : ℕ)^5175*12500000000000^4151 ≤ 5451900463687^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284944429 2500000000 5451900463687 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2738324637/5000000000 : ℝ)^5175 ≤ (5900921433449/12500000000000 : ℝ)^4151 := by
    have hnat : (2738324637 : ℕ)^5175*12500000000000^4151 ≤ 5900921433449^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738324637 5000000000 5900921433449 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1472216983/10000000000 : ℝ), (1284944429/2500000000 : ℝ), (2738324637/5000000000 : ℝ)] ![(9177424806429/100000000000000 : ℝ), (5451900463687/12500000000000 : ℝ), (5900921433449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1472216983/10000000000 : ℝ)|^5175 ≤ (9177424806429/100000000000000 : ℝ)^4151
        have hw : |(-1472216983/10000000000 : ℝ)|=(1472216983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284944429/2500000000 : ℝ)|^5175 ≤ (5451900463687/12500000000000 : ℝ)^4151
        have hw : |(1284944429/2500000000 : ℝ)|=(1284944429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2738324637/5000000000 : ℝ)|^5175 ≤ (5900921433449/12500000000000 : ℝ)^4151
        have hw : |(2738324637/5000000000 : ℝ)|=(2738324637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s4_5 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256751029/10000000000 : ℝ)*x 0 + (-655140381/5000000000 : ℝ)*x 1 + (1369162063/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256751029/10000000000 : ℝ)^5175 ≤ (11214034299983/25000000000000 : ℝ)^4151 := by
    have hnat : (5256751029 : ℕ)^5175*25000000000000^4151 ≤ 11214034299983^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256751029 10000000000 11214034299983 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655140381/5000000000 : ℝ)^5175 ≤ (7936502299687/100000000000000 : ℝ)^4151 := by
    have hnat : (655140381 : ℕ)^5175*100000000000000^4151 ≤ 7936502299687^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655140381 5000000000 7936502299687 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369162063/2500000000 : ℝ)^5175 ≤ (47207360485037/100000000000000 : ℝ)^4151 := by
    have hnat : (1369162063 : ℕ)^5175*100000000000000^4151 ≤ 47207360485037^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369162063 2500000000 47207360485037 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256751029/10000000000 : ℝ), (-655140381/5000000000 : ℝ), (1369162063/2500000000 : ℝ)] ![(11214034299983/25000000000000 : ℝ), (7936502299687/100000000000000 : ℝ), (47207360485037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256751029/10000000000 : ℝ)|^5175 ≤ (11214034299983/25000000000000 : ℝ)^4151
        have hw : |(5256751029/10000000000 : ℝ)|=(5256751029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-655140381/5000000000 : ℝ)|^5175 ≤ (7936502299687/100000000000000 : ℝ)^4151
        have hw : |(-655140381/5000000000 : ℝ)|=(655140381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369162063/2500000000 : ℝ)|^5175 ≤ (47207360485037/100000000000000 : ℝ)^4151
        have hw : |(1369162063/2500000000 : ℝ)|=(1369162063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s4_6 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628375179/5000000000 : ℝ)*x 0 + (2738324359/5000000000 : ℝ)*x 1 + (-327570261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628375179/5000000000 : ℝ)^5175 ≤ (44856130061799/100000000000000 : ℝ)^4151 := by
    have hnat : (2628375179 : ℕ)^5175*100000000000000^4151 ≤ 44856130061799^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628375179 5000000000 44856130061799 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738324359/5000000000 : ℝ)^5175 ≤ (23603682746369/50000000000000 : ℝ)^4151 := by
    have hnat : (2738324359 : ℕ)^5175*50000000000000^4151 ≤ 23603682746369^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738324359 5000000000 23603682746369 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327570261/2500000000 : ℝ)^5175 ≤ (7936504429157/100000000000000 : ℝ)^4151 := by
    have hnat : (327570261 : ℕ)^5175*100000000000000^4151 ≤ 7936504429157^4151*2500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327570261 2500000000 7936504429157 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628375179/5000000000 : ℝ), (2738324359/5000000000 : ℝ), (-327570261/2500000000 : ℝ)] ![(44856130061799/100000000000000 : ℝ), (23603682746369/50000000000000 : ℝ), (7936504429157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628375179/5000000000 : ℝ)|^5175 ≤ (44856130061799/100000000000000 : ℝ)^4151
        have hw : |(2628375179/5000000000 : ℝ)|=(2628375179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738324359/5000000000 : ℝ)|^5175 ≤ (23603682746369/50000000000000 : ℝ)^4151
        have hw : |(2738324359/5000000000 : ℝ)|=(2738324359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-327570261/2500000000 : ℝ)|^5175 ≤ (7936504429157/100000000000000 : ℝ)^4151
        have hw : |(-327570261/2500000000 : ℝ)|=(327570261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_s4_7 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4126246791/10000000000 : ℝ)*x 0 + (57686861/125000000 : ℝ)*x 1 + (1836924691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4126246791/10000000000 : ℝ)^5175 ≤ (2072991268623/6250000000000 : ℝ)^4151 := by
    have hnat : (4126246791 : ℕ)^5175*6250000000000^4151 ≤ 2072991268623^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126246791 10000000000 2072991268623 6250000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57686861/125000000 : ℝ)^5175 ≤ (9533690720887/25000000000000 : ℝ)^4151 := by
    have hnat : (57686861 : ℕ)^5175*25000000000000^4151 ≤ 9533690720887^4151*125000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57686861 125000000 9533690720887 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1836924691/5000000000 : ℝ)^5175 ≤ (112099128143/390625000000 : ℝ)^4151 := by
    have hnat : (1836924691 : ℕ)^5175*390625000000^4151 ≤ 112099128143^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836924691 5000000000 112099128143 390625000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4126246791/10000000000 : ℝ), (57686861/125000000 : ℝ), (1836924691/5000000000 : ℝ)] ![(2072991268623/6250000000000 : ℝ), (9533690720887/25000000000000 : ℝ), (112099128143/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4126246791/10000000000 : ℝ)|^5175 ≤ (2072991268623/6250000000000 : ℝ)^4151
        have hw : |(4126246791/10000000000 : ℝ)|=(4126246791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57686861/125000000 : ℝ)|^5175 ≤ (9533690720887/25000000000000 : ℝ)^4151
        have hw : |(57686861/125000000 : ℝ)|=(57686861/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1836924691/5000000000 : ℝ)|^5175 ≤ (112099128143/390625000000 : ℝ)^4151
        have hw : |(1836924691/5000000000 : ℝ)|=(1836924691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1694_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (987/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (9871/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8603/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17207/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (987/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17207/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (987/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17207/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (987/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17207/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (987/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17207/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (987/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17207/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (987/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (987/10000 : ℝ) ^ (5167/1024 : ℝ) ≤ (421110913150971/50000000000000000000 : ℝ) := by
    have hpowers : (987/10000 : ℝ)^5167 ≤ (421110913150971/50000000000000000000 : ℝ)^1024 := by
      have hnat : (987 : ℕ)^5167*50000000000000000000^1024 ≤ 421110913150971^1024*10000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        987 10000 421110913150971 50000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (987/10000 : ℝ)) (X := (421110913150971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17207/100000 : ℝ) ^ (5167/1024 : ℝ) ≤ (434806348215389/3125000000000000000 : ℝ) := by
    have hpowers : (17207/100000 : ℝ)^5167 ≤ (434806348215389/3125000000000000000 : ℝ)^1024 := by
      have hnat : (17207 : ℕ)^5167*3125000000000000000^1024 ≤ 434806348215389^1024*100000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17207 100000 434806348215389 3125000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17207/100000 : ℝ)) (X := (434806348215389/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000421110913150971/25000000000000000000 : ℝ) ≤ (10000033382207319/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (25000421110913150971/25000000000000000000 : ℝ)^1024 ≤ (10000033382207319/10000000000000000 : ℝ)^5167 := by
      have hnat : (25000421110913150971 : ℕ)^1024*10000000000000000^5167 ≤ 10000033382207319^5167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000421110913150971 25000000000000000000 10000033382207319 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000033382207319/10000000000000000 : ℝ)) (X := (25000421110913150971/25000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10001475602496919439/10000000000000000000 : ℝ) ≤ (10000292418729541/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (10001475602496919439/10000000000000000000 : ℝ)^1024 ≤ (10000292418729541/10000000000000000 : ℝ)^5167 := by
      have hnat : (10001475602496919439 : ℕ)^1024*10000000000000000^5167 ≤ 10000292418729541^5167*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001475602496919439 10000000000000000000 10000292418729541 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000292418729541/10000000000000000 : ℝ)) (X := (10001475602496919439/10000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1562934806348215389/1562500000000000000 : ℝ) ≤ (10000551455251763/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (1562934806348215389/1562500000000000000 : ℝ)^1024 ≤ (10000551455251763/10000000000000000 : ℝ)^5167 := by
      have hnat : (1562934806348215389 : ℕ)^1024*10000000000000000^5167 ≤ 10000551455251763^5167*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562934806348215389 1562500000000000000 10000551455251763 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000551455251763/10000000000000000 : ℝ)) (X := (1562934806348215389/1562500000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(421110913150971/50000000000000000000 : ℝ) ≤ ((73365131544306437223/73370000000000000000 : ℝ)+2*(129518261111/366850000000000 : ℝ)*(987/10000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (73365131544306437223/73370000000000000000 : ℝ)+2*(129518261111/366850000000000 : ℝ)*(987/10000 : ℝ)=(10000033382207319/10000000000000000 : ℝ) by norm_num, show 1+2*(421110913150971/50000000000000000000 : ℝ)=(25000421110913150971/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(434806348215389/3125000000000000000 : ℝ)+(421110913150971/50000000000000000000 : ℝ) ≤ ((73365131544306437223/73370000000000000000 : ℝ)+(129518261111/366850000000000 : ℝ)*((17207/100000 : ℝ)+(987/10000 : ℝ)))^(5167/1024 : ℝ) := by
    rw [show (73365131544306437223/73370000000000000000 : ℝ)+(129518261111/366850000000000 : ℝ)*((17207/100000 : ℝ)+(987/10000 : ℝ))=(10000292418729541/10000000000000000 : ℝ) by norm_num, show 1+(434806348215389/3125000000000000000 : ℝ)+(421110913150971/50000000000000000000 : ℝ)=(10001475602496919439/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(434806348215389/3125000000000000000 : ℝ) ≤ ((73365131544306437223/73370000000000000000 : ℝ)+2*(129518261111/366850000000000 : ℝ)*(17207/100000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (73365131544306437223/73370000000000000000 : ℝ)+2*(129518261111/366850000000000 : ℝ)*(17207/100000 : ℝ)=(10000551455251763/10000000000000000 : ℝ) by norm_num, show 1+2*(434806348215389/3125000000000000000 : ℝ)=(1562934806348215389/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73365131544306437223/73370000000000000000 : ℝ)*(X 1 0+X 2 0)+(129518261111/366850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (987/10000 : ℝ)) (hi := (17207/100000 : ℝ)) (c := (73365131544306437223/73370000000000000000 : ℝ)) (alpha := (129518261111/366850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73365131544306437223/73370000000000000000 : ℝ)*(X 0 1+X 2 1)+(129518261111/366850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (987/10000 : ℝ)) (hi := (17207/100000 : ℝ)) (c := (73365131544306437223/73370000000000000000 : ℝ)) (alpha := (129518261111/366850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73365131544306437223/73370000000000000000 : ℝ)*(X 0 2+X 1 2)+(129518261111/366850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (987/10000 : ℝ)) (hi := (17207/100000 : ℝ)) (c := (73365131544306437223/73370000000000000000 : ℝ)) (alpha := (129518261111/366850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-368014287/2500000000 : ℝ)*X 0 0+(342529233/625000000 : ℝ)*X 0 1+(2568007867/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069774193/2000000000 : ℝ)*X 1 0+(-1650910611/10000000000 : ℝ)*X 1 1+(5136018739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534887401/1000000000 : ℝ)*X 2 0+(5136016527/10000000000 : ℝ)*X 2 1+(-1650909469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4125797451/10000000000 : ℝ)*X 0 0+(3663188221/10000000000 : ℝ)*X 0 1+(4625457343/10000000000 : ℝ)*X 0 2+(4125797451/10000000000 : ℝ)*X 1 0+(3663188221/10000000000 : ℝ)*X 1 1+(4625457343/10000000000 : ℝ)*X 1 2+(4125797451/10000000000 : ℝ)*X 2 0+(3663188221/10000000000 : ℝ)*X 2 1+(4625457343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1472216983/10000000000 : ℝ)*X 0 0+(1284944429/2500000000 : ℝ)*X 0 1+(2738324637/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5256751029/10000000000 : ℝ)*X 1 0+(-655140381/5000000000 : ℝ)*X 1 1+(1369162063/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628375179/5000000000 : ℝ)*X 2 0+(2738324359/5000000000 : ℝ)*X 2 1+(-327570261/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4126246791/10000000000 : ℝ)*X 0 0+(57686861/125000000 : ℝ)*X 0 1+(1836924691/5000000000 : ℝ)*X 0 2+(4126246791/10000000000 : ℝ)*X 1 0+(57686861/125000000 : ℝ)*X 1 1+(1836924691/5000000000 : ℝ)*X 1 2+(4126246791/10000000000 : ℝ)*X 2 0+(57686861/125000000 : ℝ)*X 2 1+(1836924691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30806412847648202845125483/18342500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (408107429/100000000000000 : ℝ)*(base23) + (63536239/25000000000000 : ℝ)*(lower2) + (135996963/50000000000000 : ℝ)*(lower3) + (82318443/20000000000000 : ℝ)*(upper4) + (53813279/25000000000000 : ℝ)*(lower5) + (19712174702707/1000000000000 : ℝ)*(major0) + (19712174702707/1000000000000 : ℝ)*(major1) + (19712174702707/1000000000000 : ℝ)*(major2) + (290318050363287/10000000000000 : ℝ)*(sp0) + (725803525035339/25000000000000 : ℝ)*(sp1) + (1451606846016963/50000000000000 : ℝ)*(sp2) + (64950855943323/6250000000000 : ℝ)*(sp3) + (16798254243/50000000000000 : ℝ)*(sp4) + (7089323203/100000000000000 : ℝ)*(sp7) + (1039220784416371/100000000000000 : ℝ)*(f.failure) + (725803525035339/25000000000000 : ℝ)*(f.sum) + (88600208007011/7337000000000000000000000000 : ℝ)*base66 + (175064206731417339/73370000000000000000000000000000 : ℝ)*base68 + (829546828358882661/73370000000000000000000000000000 : ℝ)*base69 + (83489699339907339/73370000000000000000000000000000 : ℝ)*base72 + (6190746086461/1834250000000000000000000000 : ℝ)*base74 + (175516103566917339/73370000000000000000000000000000 : ℝ)*base76 + (33270481746307339/73370000000000000000000000000000 : ℝ)*base78 + (148502628085837339/73370000000000000000000000000000 : ℝ)*base80 + (5008836595717/1834250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1613923/500000000000000000000 : ℝ)*base89 + (1613923/500000000000000000000 : ℝ)*base91 + (1613923/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14410809070616902435450046727/1834250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373545873/100000000000000 : ℝ)*(base19) + (315694907/100000000000000 : ℝ)*(base23) + (54322371/20000000000000 : ℝ)*(upper1) + (72069479/50000000000000 : ℝ)*(upper3) + (16877523/10000000000000 : ℝ)*(lower4) + (9326803/6250000000000 : ℝ)*(upper5) + (1007771190952117/50000000000000 : ℝ)*(major0) + (1007771190952117/50000000000000 : ℝ)*(major1) + (1007771190952117/50000000000000 : ℝ)*(major2) + (162977/80000000000 : ℝ)*(sp0) + (1484247767143117/50000000000000 : ℝ)*(sp4) + (2968495364461611/100000000000000 : ℝ)*(sp5) + (2968495422312577/100000000000000 : ℝ)*(sp6) + (1062588763917213/100000000000000 : ℝ)*(sp7) + (1062588763917213/100000000000000 : ℝ)*(f.failure) + (742123934501871/25000000000000 : ℝ)*(f.sum) + (111418855133837/36685000000000000000000000000 : ℝ)*base66 + (9407251890052851091/3668500000000000000000000000000000 : ℝ)*base67 + (4907238771110148909/3668500000000000000000000000000000 : ℝ)*base70 + (6585970857680148909/3668500000000000000000000000000000 : ℝ)*base72 + (3896219521391/18342500000000000000000000000 : ℝ)*base74 + (17434614600903851091/3668500000000000000000000000000000 : ℝ)*base75 + (5602969461100351091/3668500000000000000000000000000000 : ℝ)*base77 + (17438534804025851091/3668500000000000000000000000000000 : ℝ)*base79 + (66757399937491/18342500000000000000000000000 : ℝ)*base82 + (737069/500000000000000000000 : ℝ)*base89 + (737069/500000000000000000000 : ℝ)*base91 + (737069/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1694_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17207/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (987/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8603/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1694_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1694_box_0 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1140512527/10000000000 : ℝ)*x 0 + (5425853419/10000000000 : ℝ)*x 1 + (2712926697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1140512527/10000000000 : ℝ)^5175 ≤ (6675724233749/100000000000000 : ℝ)^4151 := by
    have hnat : (1140512527 : ℕ)^5175*100000000000000^4151 ≤ 6675724233749^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140512527 10000000000 6675724233749 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425853419/10000000000 : ℝ)^5175 ≤ (11665534501941/25000000000000 : ℝ)^4151 := by
    have hnat : (5425853419 : ℕ)^5175*25000000000000^4151 ≤ 11665534501941^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425853419 10000000000 11665534501941 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712926697/5000000000 : ℝ)^5175 ≤ (46662137739727/100000000000000 : ℝ)^4151 := by
    have hnat : (2712926697 : ℕ)^5175*100000000000000^4151 ≤ 46662137739727^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712926697 5000000000 46662137739727 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1140512527/10000000000 : ℝ), (5425853419/10000000000 : ℝ), (2712926697/5000000000 : ℝ)] ![(6675724233749/100000000000000 : ℝ), (11665534501941/25000000000000 : ℝ), (46662137739727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1140512527/10000000000 : ℝ)|^5175 ≤ (6675724233749/100000000000000 : ℝ)^4151
        have hw : |(-1140512527/10000000000 : ℝ)|=(1140512527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425853419/10000000000 : ℝ)|^5175 ≤ (11665534501941/25000000000000 : ℝ)^4151
        have hw : |(5425853419/10000000000 : ℝ)|=(5425853419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712926697/5000000000 : ℝ)|^5175 ≤ (46662137739727/100000000000000 : ℝ)^4151
        have hw : |(2712926697/5000000000 : ℝ)|=(2712926697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_1 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612985027/5000000000 : ℝ)*x 0 + (-178076341/1250000000 : ℝ)*x 1 + (217034131/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612985027/5000000000 : ℝ)^5175 ≤ (44528924452339/100000000000000 : ℝ)^4151 := by
    have hnat : (2612985027 : ℕ)^5175*100000000000000^4151 ≤ 44528924452339^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612985027 5000000000 44528924452339 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (178076341/1250000000 : ℝ)^5175 ≤ (550558692009/6250000000000 : ℝ)^4151 := by
    have hnat : (178076341 : ℕ)^5175*6250000000000^4151 ≤ 550558692009^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      178076341 1250000000 550558692009 6250000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217034131/400000000 : ℝ)^5175 ≤ (91136985281/195312500000 : ℝ)^4151 := by
    have hnat : (217034131 : ℕ)^5175*195312500000^4151 ≤ 91136985281^4151*400000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217034131 400000000 91136985281 195312500000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612985027/5000000000 : ℝ), (-178076341/1250000000 : ℝ), (217034131/400000000 : ℝ)] ![(44528924452339/100000000000000 : ℝ), (550558692009/6250000000000 : ℝ), (91136985281/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612985027/5000000000 : ℝ)|^5175 ≤ (44528924452339/100000000000000 : ℝ)^4151
        have hw : |(2612985027/5000000000 : ℝ)|=(2612985027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-178076341/1250000000 : ℝ)|^5175 ≤ (550558692009/6250000000000 : ℝ)^4151
        have hw : |(-178076341/1250000000 : ℝ)|=(178076341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217034131/400000000 : ℝ)|^5175 ≤ (91136985281/195312500000 : ℝ)^4151
        have hw : |(217034131/400000000 : ℝ)|=(217034131/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_2 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225969757/10000000000 : ℝ)*x 0 + (1085170687/2000000000 : ℝ)*x 1 + (-284922183/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225969757/10000000000 : ℝ)^5175 ≤ (11132230324353/25000000000000 : ℝ)^4151 := by
    have hnat : (5225969757 : ℕ)^5175*25000000000000^4151 ≤ 11132230324353^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225969757 10000000000 11132230324353 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085170687/2000000000 : ℝ)^5175 ≤ (46662138179307/100000000000000 : ℝ)^4151 := by
    have hnat : (1085170687 : ℕ)^5175*100000000000000^4151 ≤ 46662138179307^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085170687 2000000000 46662138179307 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284922183/2000000000 : ℝ)^5175 ≤ (8808940513683/100000000000000 : ℝ)^4151 := by
    have hnat : (284922183 : ℕ)^5175*100000000000000^4151 ≤ 8808940513683^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284922183 2000000000 8808940513683 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225969757/10000000000 : ℝ), (1085170687/2000000000 : ℝ), (-284922183/2000000000 : ℝ)] ![(11132230324353/25000000000000 : ℝ), (46662138179307/100000000000000 : ℝ), (8808940513683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225969757/10000000000 : ℝ)|^5175 ≤ (11132230324353/25000000000000 : ℝ)^4151
        have hw : |(5225969757/10000000000 : ℝ)|=(5225969757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085170687/2000000000 : ℝ)|^5175 ≤ (46662138179307/100000000000000 : ℝ)^4151
        have hw : |(1085170687/2000000000 : ℝ)|=(1085170687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-284922183/2000000000 : ℝ)|^5175 ≤ (8808940513683/100000000000000 : ℝ)^4151
        have hw : |(-284922183/2000000000 : ℝ)|=(284922183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_3 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (563695339/1250000000 : ℝ)*x 0 + (3956338629/10000000000 : ℝ)*x 1 + (791267631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563695339/1250000000 : ℝ)^5175 ≤ (9263043664363/25000000000000 : ℝ)^4151 := by
    have hnat : (563695339 : ℕ)^5175*25000000000000^4151 ≤ 9263043664363^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563695339 1250000000 9263043664363 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3956338629/10000000000 : ℝ)^5175 ≤ (7868478753141/25000000000000 : ℝ)^4151 := by
    have hnat : (3956338629 : ℕ)^5175*25000000000000^4151 ≤ 7868478753141^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3956338629 10000000000 7868478753141 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791267631/2000000000 : ℝ)^5175 ≤ (31473910311531/100000000000000 : ℝ)^4151 := by
    have hnat : (791267631 : ℕ)^5175*100000000000000^4151 ≤ 31473910311531^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791267631 2000000000 31473910311531 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(563695339/1250000000 : ℝ), (3956338629/10000000000 : ℝ), (791267631/2000000000 : ℝ)] ![(9263043664363/25000000000000 : ℝ), (7868478753141/25000000000000 : ℝ), (31473910311531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(563695339/1250000000 : ℝ)|^5175 ≤ (9263043664363/25000000000000 : ℝ)^4151
        have hw : |(563695339/1250000000 : ℝ)|=(563695339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3956338629/10000000000 : ℝ)|^5175 ≤ (7868478753141/25000000000000 : ℝ)^4151
        have hw : |(3956338629/10000000000 : ℝ)|=(3956338629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791267631/2000000000 : ℝ)|^5175 ≤ (31473910311531/100000000000000 : ℝ)^4151
        have hw : |(791267631/2000000000 : ℝ)|=(791267631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_4 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1824493513/10000000000 : ℝ)*x 0 + (258825883/500000000 : ℝ)*x 1 + (5176517897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1824493513/10000000000 : ℝ)^5175 ≤ (11991550400647/100000000000000 : ℝ)^4151 := by
    have hnat : (1824493513 : ℕ)^5175*100000000000000^4151 ≤ 11991550400647^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824493513 10000000000 11991550400647 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258825883/500000000 : ℝ)^5175 ≤ (8800844707001/20000000000000 : ℝ)^4151 := by
    have hnat : (258825883 : ℕ)^5175*20000000000000^4151 ≤ 8800844707001^4151*500000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258825883 500000000 8800844707001 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176517897/10000000000 : ℝ)^5175 ≤ (11001056511669/25000000000000 : ℝ)^4151 := by
    have hnat : (5176517897 : ℕ)^5175*25000000000000^4151 ≤ 11001056511669^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176517897 10000000000 11001056511669 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1824493513/10000000000 : ℝ), (258825883/500000000 : ℝ), (5176517897/10000000000 : ℝ)] ![(11991550400647/100000000000000 : ℝ), (8800844707001/20000000000000 : ℝ), (11001056511669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1824493513/10000000000 : ℝ)|^5175 ≤ (11991550400647/100000000000000 : ℝ)^4151
        have hw : |(-1824493513/10000000000 : ℝ)|=(1824493513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258825883/500000000 : ℝ)|^5175 ≤ (8800844707001/20000000000000 : ℝ)^4151
        have hw : |(258825883/500000000 : ℝ)|=(258825883/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176517897/10000000000 : ℝ)|^5175 ≤ (11001056511669/25000000000000 : ℝ)^4151
        have hw : |(5176517897/10000000000 : ℝ)|=(5176517897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_5 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697862381/5000000000 : ℝ)*x 0 + (-1533542177/10000000000 : ℝ)*x 1 + (5176517779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697862381/5000000000 : ℝ)^5175 ≤ (11584834041617/25000000000000 : ℝ)^4151 := by
    have hnat : (2697862381 : ℕ)^5175*25000000000000^4151 ≤ 11584834041617^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697862381 5000000000 11584834041617 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1533542177/10000000000 : ℝ)^5175 ≤ (1207054877343/12500000000000 : ℝ)^4151 := by
    have hnat : (1533542177 : ℕ)^5175*12500000000000^4151 ≤ 1207054877343^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1533542177 10000000000 1207054877343 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176517779/10000000000 : ℝ)^5175 ≤ (44004224796139/100000000000000 : ℝ)^4151 := by
    have hnat : (5176517779 : ℕ)^5175*100000000000000^4151 ≤ 44004224796139^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176517779 10000000000 44004224796139 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697862381/5000000000 : ℝ), (-1533542177/10000000000 : ℝ), (5176517779/10000000000 : ℝ)] ![(11584834041617/25000000000000 : ℝ), (1207054877343/12500000000000 : ℝ), (44004224796139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697862381/5000000000 : ℝ)|^5175 ≤ (11584834041617/25000000000000 : ℝ)^4151
        have hw : |(2697862381/5000000000 : ℝ)|=(2697862381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1533542177/10000000000 : ℝ)|^5175 ≤ (1207054877343/12500000000000 : ℝ)^4151
        have hw : |(-1533542177/10000000000 : ℝ)|=(1533542177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176517779/10000000000 : ℝ)|^5175 ≤ (44004224796139/100000000000000 : ℝ)^4151
        have hw : |(5176517779/10000000000 : ℝ)|=(5176517779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_6 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10791449/20000000 : ℝ)*x 0 + (2588259037/5000000000 : ℝ)*x 1 + (-766771069/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10791449/20000000 : ℝ)^5175 ≤ (46339333361299/100000000000000 : ℝ)^4151 := by
    have hnat : (10791449 : ℕ)^5175*100000000000000^4151 ≤ 46339333361299^4151*20000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10791449 20000000 46339333361299 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588259037/5000000000 : ℝ)^5175 ≤ (550052849031/1250000000000 : ℝ)^4151 := by
    have hnat : (2588259037 : ℕ)^5175*1250000000000^4151 ≤ 550052849031^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588259037 5000000000 550052849031 1250000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766771069/5000000000 : ℝ)^5175 ≤ (9656438712587/100000000000000 : ℝ)^4151 := by
    have hnat : (766771069 : ℕ)^5175*100000000000000^4151 ≤ 9656438712587^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766771069 5000000000 9656438712587 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10791449/20000000 : ℝ), (2588259037/5000000000 : ℝ), (-766771069/5000000000 : ℝ)] ![(46339333361299/100000000000000 : ℝ), (550052849031/1250000000000 : ℝ), (9656438712587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10791449/20000000 : ℝ)|^5175 ≤ (46339333361299/100000000000000 : ℝ)^4151
        have hw : |(10791449/20000000 : ℝ)|=(10791449/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588259037/5000000000 : ℝ)|^5175 ≤ (550052849031/1250000000000 : ℝ)^4151
        have hw : |(2588259037/5000000000 : ℝ)|=(2588259037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-766771069/5000000000 : ℝ)|^5175 ≤ (9656438712587/100000000000000 : ℝ)^4151
        have hw : |(-766771069/5000000000 : ℝ)|=(766771069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_7 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1863622241/5000000000 : ℝ)*x 0 + (4346643669/10000000000 : ℝ)*x 1 + (2173321711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1863622241/5000000000 : ℝ)^5175 ≤ (7304569364927/25000000000000 : ℝ)^4151 := by
    have hnat : (1863622241 : ℕ)^5175*25000000000000^4151 ≤ 7304569364927^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863622241 5000000000 7304569364927 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4346643669/10000000000 : ℝ)^5175 ≤ (35390862513583/100000000000000 : ℝ)^4151 := by
    have hnat : (4346643669 : ℕ)^5175*100000000000000^4151 ≤ 35390862513583^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4346643669 10000000000 35390862513583 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2173321711/5000000000 : ℝ)^5175 ≤ (35390860006367/100000000000000 : ℝ)^4151 := by
    have hnat : (2173321711 : ℕ)^5175*100000000000000^4151 ≤ 35390860006367^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173321711 5000000000 35390860006367 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1863622241/5000000000 : ℝ), (4346643669/10000000000 : ℝ), (2173321711/5000000000 : ℝ)] ![(7304569364927/25000000000000 : ℝ), (35390862513583/100000000000000 : ℝ), (35390860006367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1863622241/5000000000 : ℝ)|^5175 ≤ (7304569364927/25000000000000 : ℝ)^4151
        have hw : |(1863622241/5000000000 : ℝ)|=(1863622241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4346643669/10000000000 : ℝ)|^5175 ≤ (35390862513583/100000000000000 : ℝ)^4151
        have hw : |(4346643669/10000000000 : ℝ)|=(4346643669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2173321711/5000000000 : ℝ)|^5175 ≤ (35390860006367/100000000000000 : ℝ)^4151
        have hw : |(2173321711/5000000000 : ℝ)|=(2173321711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_8 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1677653637/10000000000 : ℝ)*x 0 + (4993336013/10000000000 : ℝ)*x 1 + (218770439/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1677653637/10000000000 : ℝ)^5175 ≤ (5400276805541/50000000000000 : ℝ)^4151 := by
    have hnat : (1677653637 : ℕ)^5175*50000000000000^4151 ≤ 5400276805541^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677653637 10000000000 5400276805541 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4993336013/10000000000 : ℝ)^5175 ≤ (21035728690943/50000000000000 : ℝ)^4151 := by
    have hnat : (4993336013 : ℕ)^5175*50000000000000^4151 ≤ 21035728690943^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4993336013 10000000000 21035728690943 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218770439/400000000 : ℝ)^5175 ≤ (9425597796981/20000000000000 : ℝ)^4151 := by
    have hnat : (218770439 : ℕ)^5175*20000000000000^4151 ≤ 9425597796981^4151*400000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218770439 400000000 9425597796981 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1677653637/10000000000 : ℝ), (4993336013/10000000000 : ℝ), (218770439/400000000 : ℝ)] ![(5400276805541/50000000000000 : ℝ), (21035728690943/50000000000000 : ℝ), (9425597796981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1677653637/10000000000 : ℝ)|^5175 ≤ (5400276805541/50000000000000 : ℝ)^4151
        have hw : |(-1677653637/10000000000 : ℝ)|=(1677653637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4993336013/10000000000 : ℝ)|^5175 ≤ (21035728690943/50000000000000 : ℝ)^4151
        have hw : |(4993336013/10000000000 : ℝ)|=(4993336013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218770439/400000000 : ℝ)|^5175 ≤ (9425597796981/20000000000000 : ℝ)^4151
        have hw : |(218770439/400000000 : ℝ)|=(218770439/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_9 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196430931/10000000000 : ℝ)*x 0 + (-1404822191/10000000000 : ℝ)*x 1 + (218770421/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196430931/10000000000 : ℝ)^5175 ≤ (11053839934321/25000000000000 : ℝ)^4151 := by
    have hnat : (5196430931 : ℕ)^5175*25000000000000^4151 ≤ 11053839934321^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196430931 10000000000 11053839934321 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1404822191/10000000000 : ℝ)^5175 ≤ (8656656090731/100000000000000 : ℝ)^4151 := by
    have hnat : (1404822191 : ℕ)^5175*100000000000000^4151 ≤ 8656656090731^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404822191 10000000000 8656656090731 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218770421/400000000 : ℝ)^5175 ≤ (1472749504711/3125000000000 : ℝ)^4151 := by
    have hnat : (218770421 : ℕ)^5175*3125000000000^4151 ≤ 1472749504711^4151*400000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218770421 400000000 1472749504711 3125000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196430931/10000000000 : ℝ), (-1404822191/10000000000 : ℝ), (218770421/400000000 : ℝ)] ![(11053839934321/25000000000000 : ℝ), (8656656090731/100000000000000 : ℝ), (1472749504711/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196430931/10000000000 : ℝ)|^5175 ≤ (11053839934321/25000000000000 : ℝ)^4151
        have hw : |(5196430931/10000000000 : ℝ)|=(5196430931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1404822191/10000000000 : ℝ)|^5175 ≤ (8656656090731/100000000000000 : ℝ)^4151
        have hw : |(-1404822191/10000000000 : ℝ)|=(1404822191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218770421/400000000 : ℝ)|^5175 ≤ (1472749504711/3125000000000 : ℝ)^4151
        have hw : |(218770421/400000000 : ℝ)|=(218770421/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_10 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (519643131/1000000000 : ℝ)*x 0 + (218770409/400000000 : ℝ)*x 1 + (-175602761/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (519643131/1000000000 : ℝ)^5175 ≤ (44215363757643/100000000000000 : ℝ)^4151 := by
    have hnat : (519643131 : ℕ)^5175*100000000000000^4151 ≤ 44215363757643^4151*1000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519643131 1000000000 44215363757643 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218770409/400000000 : ℝ)^5175 ≤ (47127980927983/100000000000000 : ℝ)^4151 := by
    have hnat : (218770409 : ℕ)^5175*100000000000000^4151 ≤ 47127980927983^4151*400000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218770409 400000000 47127980927983 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175602761/1250000000 : ℝ)^5175 ≤ (8656655299463/100000000000000 : ℝ)^4151 := by
    have hnat : (175602761 : ℕ)^5175*100000000000000^4151 ≤ 8656655299463^4151*1250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175602761 1250000000 8656655299463 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(519643131/1000000000 : ℝ), (218770409/400000000 : ℝ), (-175602761/1250000000 : ℝ)] ![(44215363757643/100000000000000 : ℝ), (47127980927983/100000000000000 : ℝ), (8656655299463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(519643131/1000000000 : ℝ)|^5175 ≤ (44215363757643/100000000000000 : ℝ)^4151
        have hw : |(519643131/1000000000 : ℝ)|=(519643131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(218770409/400000000 : ℝ)|^5175 ≤ (47127980927983/100000000000000 : ℝ)^4151
        have hw : |(218770409/400000000 : ℝ)|=(218770409/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175602761/1250000000 : ℝ)|^5175 ≤ (8656655299463/100000000000000 : ℝ)^4151
        have hw : |(-175602761/1250000000 : ℝ)|=(175602761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_11 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (290046269/625000000 : ℝ)*x 0 + (3888206241/10000000000 : ℝ)*x 1 + (3888215281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (290046269/625000000 : ℝ)^5175 ≤ (300005023851/781250000000 : ℝ)^4151 := by
    have hnat : (290046269 : ℕ)^5175*781250000000^4151 ≤ 300005023851^4151*625000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290046269 625000000 300005023851 781250000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3888206241/10000000000 : ℝ)^5175 ≤ (3079963382381/10000000000000 : ℝ)^4151 := by
    have hnat : (3888206241 : ℕ)^5175*10000000000000^4151 ≤ 3079963382381^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888206241 10000000000 3079963382381 10000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3888215281/10000000000 : ℝ)^5175 ≤ (7699930774321/25000000000000 : ℝ)^4151 := by
    have hnat : (3888215281 : ℕ)^5175*25000000000000^4151 ≤ 7699930774321^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3888215281 10000000000 7699930774321 25000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(290046269/625000000 : ℝ), (3888206241/10000000000 : ℝ), (3888215281/10000000000 : ℝ)] ![(300005023851/781250000000 : ℝ), (3079963382381/10000000000000 : ℝ), (7699930774321/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(290046269/625000000 : ℝ)|^5175 ≤ (300005023851/781250000000 : ℝ)^4151
        have hw : |(290046269/625000000 : ℝ)|=(290046269/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3888206241/10000000000 : ℝ)|^5175 ≤ (3079963382381/10000000000000 : ℝ)^4151
        have hw : |(3888206241/10000000000 : ℝ)|=(3888206241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3888215281/10000000000 : ℝ)|^5175 ≤ (7699930774321/25000000000000 : ℝ)^4151
        have hw : |(3888215281/10000000000 : ℝ)|=(3888215281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_12 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-641200467/5000000000 : ℝ)*x 0 + (1120006497/2000000000 : ℝ)*x 1 + (5151244207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (641200467/5000000000 : ℝ)^5175 ≤ (7726528535201/100000000000000 : ℝ)^4151 := by
    have hnat : (641200467 : ℕ)^5175*100000000000000^4151 ≤ 7726528535201^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641200467 5000000000 7726528535201 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120006497/2000000000 : ℝ)^5175 ≤ (9707385707667/20000000000000 : ℝ)^4151 := by
    have hnat : (1120006497 : ℕ)^5175*20000000000000^4151 ≤ 9707385707667^4151*2000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120006497 2000000000 9707385707667 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151244207/10000000000 : ℝ)^5175 ≤ (21868271457297/50000000000000 : ℝ)^4151 := by
    have hnat : (5151244207 : ℕ)^5175*50000000000000^4151 ≤ 21868271457297^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151244207 10000000000 21868271457297 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-641200467/5000000000 : ℝ), (1120006497/2000000000 : ℝ), (5151244207/10000000000 : ℝ)] ![(7726528535201/100000000000000 : ℝ), (9707385707667/20000000000000 : ℝ), (21868271457297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-641200467/5000000000 : ℝ)|^5175 ≤ (7726528535201/100000000000000 : ℝ)^4151
        have hw : |(-641200467/5000000000 : ℝ)|=(641200467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120006497/2000000000 : ℝ)|^5175 ≤ (9707385707667/20000000000000 : ℝ)^4151
        have hw : |(1120006497/2000000000 : ℝ)|=(1120006497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151244207/10000000000 : ℝ)|^5175 ≤ (21868271457297/50000000000000 : ℝ)^4151
        have hw : |(5151244207/10000000000 : ℝ)|=(5151244207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_13 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (338309939/625000000 : ℝ)*x 0 + (-96507263/625000000 : ℝ)*x 1 + (5151244957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (338309939/625000000 : ℝ)^5175 ≤ (9304786345963/20000000000000 : ℝ)^4151 := by
    have hnat : (338309939 : ℕ)^5175*20000000000000^4151 ≤ 9304786345963^4151*625000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338309939 625000000 9304786345963 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96507263/625000000 : ℝ)^5175 ≤ (1217439675347/12500000000000 : ℝ)^4151 := by
    have hnat : (96507263 : ℕ)^5175*12500000000000^4151 ≤ 1217439675347^4151*625000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96507263 625000000 1217439675347 12500000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151244957/10000000000 : ℝ)^5175 ≤ (43736550853327/100000000000000 : ℝ)^4151 := by
    have hnat : (5151244957 : ℕ)^5175*100000000000000^4151 ≤ 43736550853327^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151244957 10000000000 43736550853327 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(338309939/625000000 : ℝ), (-96507263/625000000 : ℝ), (5151244957/10000000000 : ℝ)] ![(9304786345963/20000000000000 : ℝ), (1217439675347/12500000000000 : ℝ), (43736550853327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(338309939/625000000 : ℝ)|^5175 ≤ (9304786345963/20000000000000 : ℝ)^4151
        have hw : |(338309939/625000000 : ℝ)|=(338309939/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-96507263/625000000 : ℝ)|^5175 ≤ (1217439675347/12500000000000 : ℝ)^4151
        have hw : |(-96507263/625000000 : ℝ)|=(96507263/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151244957/10000000000 : ℝ)|^5175 ≤ (43736550853327/100000000000000 : ℝ)^4151
        have hw : |(5151244957/10000000000 : ℝ)|=(5151244957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_14 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5412960131/10000000000 : ℝ)*x 0 + (5151243237/10000000000 : ℝ)*x 1 + (-772058507/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5412960131/10000000000 : ℝ)^5175 ≤ (9304788718303/20000000000000 : ℝ)^4151 := by
    have hnat : (5412960131 : ℕ)^5175*20000000000000^4151 ≤ 9304788718303^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412960131 10000000000 9304788718303 20000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151243237/10000000000 : ℝ)^5175 ≤ (21868266323583/50000000000000 : ℝ)^4151 := by
    have hnat : (5151243237 : ℕ)^5175*50000000000000^4151 ≤ 21868266323583^4151*10000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151243237 10000000000 21868266323583 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (772058507/5000000000 : ℝ)^5175 ≤ (4869761870373/50000000000000 : ℝ)^4151 := by
    have hnat : (772058507 : ℕ)^5175*50000000000000^4151 ≤ 4869761870373^4151*5000000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      772058507 5000000000 4869761870373 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5412960131/10000000000 : ℝ), (5151243237/10000000000 : ℝ), (-772058507/5000000000 : ℝ)] ![(9304788718303/20000000000000 : ℝ), (21868266323583/50000000000000 : ℝ), (4869761870373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5412960131/10000000000 : ℝ)|^5175 ≤ (9304788718303/20000000000000 : ℝ)^4151
        have hw : |(5412960131/10000000000 : ℝ)|=(5412960131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151243237/10000000000 : ℝ)|^5175 ≤ (21868266323583/50000000000000 : ℝ)^4151
        have hw : |(5151243237/10000000000 : ℝ)|=(5151243237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-772058507/5000000000 : ℝ)|^5175 ≤ (4869761870373/50000000000000 : ℝ)^4151
        have hw : |(-772058507/5000000000 : ℝ)|=(772058507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1694_box_15 (p : ℝ) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (113905077/312500000 : ℝ)*x 0 + (109652551/250000000 : ℝ)*x 1 + (175443997/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113905077/312500000 : ℝ)^5175 ≤ (28416343720657/100000000000000 : ℝ)^4151 := by
    have hnat : (113905077 : ℕ)^5175*100000000000000^4151 ≤ 28416343720657^4151*312500000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113905077 312500000 28416343720657 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109652551/250000000 : ℝ)^5175 ≤ (35791838889323/100000000000000 : ℝ)^4151 := by
    have hnat : (109652551 : ℕ)^5175*100000000000000^4151 ≤ 35791838889323^4151*250000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109652551 250000000 35791838889323 100000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175443997/400000000 : ℝ)^5175 ≤ (17895908686371/50000000000000 : ℝ)^4151 := by
    have hnat : (175443997 : ℕ)^5175*50000000000000^4151 ≤ 17895908686371^4151*400000000^5175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175443997 400000000 17895908686371 50000000000000 5175 4151 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5175/1024 : ℝ)) 5175 4151 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(113905077/312500000 : ℝ), (109652551/250000000 : ℝ), (175443997/400000000 : ℝ)] ![(28416343720657/100000000000000 : ℝ), (35791838889323/100000000000000 : ℝ), (17895908686371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(113905077/312500000 : ℝ)|^5175 ≤ (28416343720657/100000000000000 : ℝ)^4151
        have hw : |(113905077/312500000 : ℝ)|=(113905077/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109652551/250000000 : ℝ)|^5175 ≤ (35791838889323/100000000000000 : ℝ)^4151
        have hw : |(109652551/250000000 : ℝ)|=(109652551/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(175443997/400000000 : ℝ)|^5175 ≤ (17895908686371/50000000000000 : ℝ)^4151
        have hw : |(175443997/400000000 : ℝ)|=(175443997/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1694_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8603/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13321/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(2321/4000 : ℝ) ∧ (16189/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90191/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8603/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9871/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8603/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9871/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8603/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9871/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8603/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9871/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8603/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9871/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8603/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9871/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9871/100000 : ℝ) ^ (5167/1024 : ℝ) ≤ (421326244301751/50000000000000000000 : ℝ) := by
    have hpowers : (9871/100000 : ℝ)^5167 ≤ (421326244301751/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9871 : ℕ)^5167*50000000000000000000^1024 ≤ 421326244301751^1024*100000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9871 100000 421326244301751 50000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9871/100000 : ℝ)) (X := (421326244301751/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8603/50000 : ℝ) ^ (5167/1024 : ℝ) ≤ (13909723443698469/100000000000000000000 : ℝ) := by
    have hpowers : (8603/50000 : ℝ)^5167 ≤ (13909723443698469/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8603 : ℕ)^5167*100000000000000000000^1024 ≤ 13909723443698469^1024*50000^5167 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8603 50000 13909723443698469 100000000000000000000 5167 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8603/50000 : ℝ)) (X := (13909723443698469/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000421326244301751/25000000000000000000 : ℝ) ≤ (2000006679855377/2000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (25000421326244301751/25000000000000000000 : ℝ)^1024 ≤ (2000006679855377/2000000000000000 : ℝ)^5167 := by
      have hnat : (25000421326244301751 : ℕ)^1024*2000000000000000^5167 ≤ 2000006679855377^5167*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000421326244301751 25000000000000000000 2000006679855377 2000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000006679855377/2000000000000000 : ℝ)) (X := (25000421326244301751/25000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014752375932301971/100000000000000000000 : ℝ) ≤ (2500073086605301/2500000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (100014752375932301971/100000000000000000000 : ℝ)^1024 ≤ (2500073086605301/2500000000000000 : ℝ)^5167 := by
      have hnat : (100014752375932301971 : ℕ)^1024*2500000000000000^5167 ≤ 2500073086605301^5167*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014752375932301971 100000000000000000000 2500073086605301 2500000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500073086605301/2500000000000000 : ℝ)) (X := (100014752375932301971/100000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013909723443698469/50000000000000000000 : ℝ) ≤ (10000551293565523/10000000000000000 : ℝ) ^ (5167/1024 : ℝ) := by
    have hpowers : (50013909723443698469/50000000000000000000 : ℝ)^1024 ≤ (10000551293565523/10000000000000000 : ℝ)^5167 := by
      have hnat : (50013909723443698469 : ℕ)^1024*10000000000000000^5167 ≤ 10000551293565523^5167*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013909723443698469 50000000000000000000 10000551293565523 10000000000000000 1024 5167 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000551293565523/10000000000000000 : ℝ)) (X := (50013909723443698469/50000000000000000000 : ℝ)) (by norm_num) 5167 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(421326244301751/50000000000000000000 : ℝ) ≤ ((24448377616390935259/24450000000000000000 : ℝ)+2*(86315714773/244500000000000 : ℝ)*(9871/100000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (24448377616390935259/24450000000000000000 : ℝ)+2*(86315714773/244500000000000 : ℝ)*(9871/100000 : ℝ)=(2000006679855377/2000000000000000 : ℝ) by norm_num, show 1+2*(421326244301751/50000000000000000000 : ℝ)=(25000421326244301751/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13909723443698469/100000000000000000000 : ℝ)+(421326244301751/50000000000000000000 : ℝ) ≤ ((24448377616390935259/24450000000000000000 : ℝ)+(86315714773/244500000000000 : ℝ)*((8603/50000 : ℝ)+(9871/100000 : ℝ)))^(5167/1024 : ℝ) := by
    rw [show (24448377616390935259/24450000000000000000 : ℝ)+(86315714773/244500000000000 : ℝ)*((8603/50000 : ℝ)+(9871/100000 : ℝ))=(2500073086605301/2500000000000000 : ℝ) by norm_num, show 1+(13909723443698469/100000000000000000000 : ℝ)+(421326244301751/50000000000000000000 : ℝ)=(100014752375932301971/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13909723443698469/100000000000000000000 : ℝ) ≤ ((24448377616390935259/24450000000000000000 : ℝ)+2*(86315714773/244500000000000 : ℝ)*(8603/50000 : ℝ))^(5167/1024 : ℝ) := by
    rw [show (24448377616390935259/24450000000000000000 : ℝ)+2*(86315714773/244500000000000 : ℝ)*(8603/50000 : ℝ)=(10000551293565523/10000000000000000 : ℝ) by norm_num, show 1+2*(13909723443698469/100000000000000000000 : ℝ)=(50013909723443698469/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24448377616390935259/24450000000000000000 : ℝ)*(X 1 0+X 2 0)+(86315714773/244500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (9871/100000 : ℝ)) (hi := (8603/50000 : ℝ)) (c := (24448377616390935259/24450000000000000000 : ℝ)) (alpha := (86315714773/244500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24448377616390935259/24450000000000000000 : ℝ)*(X 0 1+X 2 1)+(86315714773/244500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (9871/100000 : ℝ)) (hi := (8603/50000 : ℝ)) (c := (24448377616390935259/24450000000000000000 : ℝ)) (alpha := (86315714773/244500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24448377616390935259/24450000000000000000 : ℝ)*(X 0 2+X 1 2)+(86315714773/244500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5167/1024 : ℝ)) (lo := (9871/100000 : ℝ)) (hi := (8603/50000 : ℝ)) (c := (24448377616390935259/24450000000000000000 : ℝ)) (alpha := (86315714773/244500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1140512527/10000000000 : ℝ)*X 0 0+(5425853419/10000000000 : ℝ)*X 0 1+(2712926697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612985027/5000000000 : ℝ)*X 1 0+(-178076341/1250000000 : ℝ)*X 1 1+(217034131/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225969757/10000000000 : ℝ)*X 2 0+(1085170687/2000000000 : ℝ)*X 2 1+(-284922183/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((563695339/1250000000 : ℝ)*X 0 0+(3956338629/10000000000 : ℝ)*X 0 1+(791267631/2000000000 : ℝ)*X 0 2+(563695339/1250000000 : ℝ)*X 1 0+(3956338629/10000000000 : ℝ)*X 1 1+(791267631/2000000000 : ℝ)*X 1 2+(563695339/1250000000 : ℝ)*X 2 0+(3956338629/10000000000 : ℝ)*X 2 1+(791267631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1824493513/10000000000 : ℝ)*X 0 0+(258825883/500000000 : ℝ)*X 0 1+(5176517897/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2697862381/5000000000 : ℝ)*X 1 0+(-1533542177/10000000000 : ℝ)*X 1 1+(5176517779/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10791449/20000000 : ℝ)*X 2 0+(2588259037/5000000000 : ℝ)*X 2 1+(-766771069/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1863622241/5000000000 : ℝ)*X 0 0+(4346643669/10000000000 : ℝ)*X 0 1+(2173321711/5000000000 : ℝ)*X 0 2+(1863622241/5000000000 : ℝ)*X 1 0+(4346643669/10000000000 : ℝ)*X 1 1+(2173321711/5000000000 : ℝ)*X 1 2+(1863622241/5000000000 : ℝ)*X 2 0+(4346643669/10000000000 : ℝ)*X 2 1+(2173321711/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1677653637/10000000000 : ℝ)*X 0 0+(4993336013/10000000000 : ℝ)*X 0 1+(218770439/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5196430931/10000000000 : ℝ)*X 1 0+(-1404822191/10000000000 : ℝ)*X 1 1+(218770421/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((519643131/1000000000 : ℝ)*X 2 0+(218770409/400000000 : ℝ)*X 2 1+(-175602761/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((290046269/625000000 : ℝ)*X 0 0+(3888206241/10000000000 : ℝ)*X 0 1+(3888215281/10000000000 : ℝ)*X 0 2+(290046269/625000000 : ℝ)*X 1 0+(3888206241/10000000000 : ℝ)*X 1 1+(3888215281/10000000000 : ℝ)*X 1 2+(290046269/625000000 : ℝ)*X 2 0+(3888206241/10000000000 : ℝ)*X 2 1+(3888215281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-641200467/5000000000 : ℝ)*X 0 0+(1120006497/2000000000 : ℝ)*X 0 1+(5151244207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((338309939/625000000 : ℝ)*X 1 0+(-96507263/625000000 : ℝ)*X 1 1+(5151244957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5412960131/10000000000 : ℝ)*X 2 0+(5151243237/10000000000 : ℝ)*X 2 1+(-772058507/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((113905077/312500000 : ℝ)*X 0 0+(109652551/250000000 : ℝ)*X 0 1+(175443997/400000000 : ℝ)*X 0 2+(113905077/312500000 : ℝ)*X 1 0+(109652551/250000000 : ℝ)*X 1 1+(175443997/400000000 : ℝ)*X 1 2+(113905077/312500000 : ℝ)*X 2 0+(109652551/250000000 : ℝ)*X 2 1+(175443997/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1694_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13321/20000 : ℝ) ≤ (-135703187112810094952110634012849/203750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11142213/25000000000000 : ℝ)*(lower0) + (6321989/50000000000000 : ℝ)*(lower2) + (22710723/100000000000000 : ℝ)*(lower3) + (5480757/12500000000000 : ℝ)*(lower4) + (1315841913524989/100000000000000 : ℝ)*(major0) + (1315841913524989/100000000000000 : ℝ)*(major1) + (1315841913524989/100000000000000 : ℝ)*(major2) + (980088058177379/50000000000000 : ℝ)*(sp4) + (245022035285147/12500000000000 : ℝ)*(sp5) + (1960164588747271/100000000000000 : ℝ)*(sp6) + (346847678254691/50000000000000 : ℝ)*(sp7) + (165926417/100000000000000 : ℝ)*(sp12) + (730845869/6250000000000 : ℝ)*(sp14) + (2623733283/20000000000000 : ℝ)*(sp15) + (173427118793949/25000000000000 : ℝ)*(f.failure) + (245022035285147/12500000000000 : ℝ)*(f.sum) + (70122142609297/12225000000000000000000000000 : ℝ)*base65 + (13738758397507612849/2445000000000000000000000000000000 : ℝ)*base68 + (4201186604752612849/2445000000000000000000000000000000 : ℝ)*base70 + (45325387501207387151/2445000000000000000000000000000000 : ℝ)*base71 + (64497242635853/12225000000000000000000000000 : ℝ)*base74 + (20566568820007612849/2445000000000000000000000000000000 : ℝ)*base76 + (13603857784132612849/2445000000000000000000000000000000 : ℝ)*base78 + (13807709297272612849/2445000000000000000000000000000000 : ℝ)*base80 + (2665775992891/1528125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (217763/125000000000000000000 : ℝ)*base90 + (217763/125000000000000000000 : ℝ)*base92 + (217763/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (2321/4000 : ℝ) ≤ (14778917099658582382961024130729/25468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49376821/100000000000000 : ℝ)*(lower0) + (57409991/100000000000000 : ℝ)*(upper2) + (4652493/50000000000000 : ℝ)*(upper3) + (3598211/20000000000000 : ℝ)*(lower5) + (177003945052831/12500000000000 : ℝ)*(major0) + (177003945052831/12500000000000 : ℝ)*(major1) + (177003945052831/12500000000000 : ℝ)*(major2) + (516548092829783/25000000000000 : ℝ)*(sp0) + (258273070406409/12500000000000 : ℝ)*(sp1) + (2066185902317657/100000000000000 : ℝ)*(sp2) + (746528193139833/100000000000000 : ℝ)*(sp3) + (3199521/50000000000000 : ℝ)*(sp7) + (390403393/5000000000000 : ℝ)*(sp9) + (258760059/4000000000000 : ℝ)*(sp10) + (5972225596311/800000000000 : ℝ)*(f.failure) + (516548092829783/25000000000000 : ℝ)*(f.sum) + (2573037735697/382031250000000000000000000 : ℝ)*base65 + (1869769468699906771/305625000000000000000000000000000 : ℝ)*base68 + (465385149747406771/305625000000000000000000000000000 : ℝ)*base70 + (195920428653031771/305625000000000000000000000000000 : ℝ)*base72 + (49182031994371/12225000000000000000000000000 : ℝ)*base74 + (902125808989906771/305625000000000000000000000000000 : ℝ)*base76 + (1205402210260093229/305625000000000000000000000000000 : ℝ)*base77 + (3849034059961156771/305625000000000000000000000000000 : ℝ)*base80 + (9893242599251/3056250000000000000000000000 : ℝ)*base81 + (12857/4000000000000000000 : ℝ)*base90 + (12857/4000000000000000000 : ℝ)*base92 + (12857/4000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (16189/20000 : ℝ) ≤ (329860078362064393157357986528707/407500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (39360829/10000000000000 : ℝ)*(upper0) + (226914523/100000000000000 : ℝ)*(lower1) + (10752757/2500000000000 : ℝ)*(lower3) + (287009147/100000000000000 : ℝ)*(lower5) + (1444962684017273/100000000000000 : ℝ)*(major0) + (1444962684017273/100000000000000 : ℝ)*(major1) + (1444962684017273/100000000000000 : ℝ)*(major2) + (964976793/50000000000000 : ℝ)*(sp0) + (26958841179/100000000000000 : ℝ)*(sp1) + (16086665243/100000000000000 : ℝ)*(sp3) + (2101160405036319/100000000000000 : ℝ)*(sp8) + (84045415045949/4000000000000 : ℝ)*(sp9) + (420232466997981/20000000000000 : ℝ)*(sp10) + (761764526881471/100000000000000 : ℝ)*(sp11) + (380890306773357/50000000000000 : ℝ)*(f.failure) + (420232466997981/20000000000000 : ℝ)*(f.sum) + (2083191532673/6112500000000000000000000000 : ℝ)*base66 + (14053027027171371293/2445000000000000000000000000000000 : ℝ)*base68 + (28783486708441371293/2445000000000000000000000000000000 : ℝ)*base70 + (2900129126938628707/2445000000000000000000000000000000 : ℝ)*base71 + (77409945890723/6112500000000000000000000000 : ℝ)*base74 + (40584415285813628707/2445000000000000000000000000000000 : ℝ)*base75 + (8429166905566371293/2445000000000000000000000000000000 : ℝ)*base78 + (18571293980251371293/2445000000000000000000000000000000 : ℝ)*base80 + (50852581502429/12225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (677341/250000000000000000000 : ℝ)*base89 + (677341/250000000000000000000 : ℝ)*base91 + (677341/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-90191/100000 : ℝ) ≤ (-45939855872536604402644654507647/50937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8335049/20000000000000 : ℝ)*(upper1) + (13045063/25000000000000 : ℝ)*(lower2) + (51318663/25000000000000 : ℝ)*(upper3) + (1266617/6250000000000 : ℝ)*(upper5) + (373125655954933/25000000000000 : ℝ)*(major0) + (373125655954933/25000000000000 : ℝ)*(major1) + (373125655954933/25000000000000 : ℝ)*(major2) + (1391738801/100000000000000 : ℝ)*(sp4) + (22567692467/20000000000000 : ℝ)*(sp6) + (16122185377/100000000000000 : ℝ)*(sp7) + (2228223199633403/100000000000000 : ℝ)*(sp12) + (557056147843051/25000000000000 : ℝ)*(sp13) + (222811175290987/10000000000000 : ℝ)*(sp14) + (786827425450407/100000000000000 : ℝ)*(sp15) + (98355443454473/12500000000000 : ℝ)*(f.failure) + (557056147843051/25000000000000 : ℝ)*(f.sum) + (21794876068739/12225000000000000000000000000 : ℝ)*base66 + (3029261150505582647/611250000000000000000000000000000 : ℝ)*base67 + (4380217245716832647/611250000000000000000000000000000 : ℝ)*base69 + (4670680818443082647/611250000000000000000000000000000 : ℝ)*base71 + (57891753544889/12225000000000000000000000000 : ℝ)*base74 + (5289936152479332647/611250000000000000000000000000000 : ℝ)*base75 + (615734106164417353/611250000000000000000000000000000 : ℝ)*base78 + (566553320524332647/611250000000000000000000000000000 : ℝ)*base79 + (88493048082061/12225000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (212551/62500000000000000000 : ℝ)*base90 + (212551/62500000000000000000 : ℝ)*base92 + (212551/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1694_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8603/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13321/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2321/4000 : ℝ) else (16189/20000 : ℝ) ≤ X j i ∧ X j i ≤ (90191/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1694_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1694_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13321/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2321/4000 : ℝ) else (16189/20000 : ℝ) ≤ X j i ∧ X j i ≤ (90191/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1694_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1694_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1694_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5167/1024 : ℝ) ≤ p) (hpb : p ≤ (5175/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9484113/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17227/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9853/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13321/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(2321/4000 : ℝ) else (16189/20000 : ℝ) ≤ X j i ∧ X j i ≤ (90191/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1694_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
