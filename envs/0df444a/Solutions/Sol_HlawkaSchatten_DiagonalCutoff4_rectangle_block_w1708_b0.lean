-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1708_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:50:03.140575+00:00
-- url     : https://prove2.me/submissions/afc130a5-7f41-4fc2-b0ef-1a5c519562d6

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
theorem support_rectangle_w1708_s0_0 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-41953119/312500000 : ℝ)*x 0 + (2850934147/5000000000 : ℝ)*x 1 + (4958078331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41953119/312500000 : ℝ)^5287 ≤ (8287692435611/100000000000000 : ℝ)^4263 := by
    have hnat : (41953119 : ℕ)^5287*100000000000000^4263 ≤ 8287692435611^4263*312500000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41953119 312500000 8287692435611 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850934147/5000000000 : ℝ)^5287 ≤ (389225218029/781250000000 : ℝ)^4263 := by
    have hnat : (2850934147 : ℕ)^5287*781250000000^4263 ≤ 389225218029^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850934147 5000000000 389225218029 781250000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4958078331/10000000000 : ℝ)^5287 ≤ (41891479634107/100000000000000 : ℝ)^4263 := by
    have hnat : (4958078331 : ℕ)^5287*100000000000000^4263 ≤ 41891479634107^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4958078331 10000000000 41891479634107 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-41953119/312500000 : ℝ), (2850934147/5000000000 : ℝ), (4958078331/10000000000 : ℝ)] ![(8287692435611/100000000000000 : ℝ), (389225218029/781250000000 : ℝ), (41891479634107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-41953119/312500000 : ℝ)|^5287 ≤ (8287692435611/100000000000000 : ℝ)^4263
        have hw : |(-41953119/312500000 : ℝ)|=(41953119/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850934147/5000000000 : ℝ)|^5287 ≤ (389225218029/781250000000 : ℝ)^4263
        have hw : |(2850934147/5000000000 : ℝ)|=(2850934147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4958078331/10000000000 : ℝ)|^5287 ≤ (41891479634107/100000000000000 : ℝ)^4263
        have hw : |(4958078331/10000000000 : ℝ)|=(4958078331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s0_1 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351419087/2500000000 : ℝ)*x 0 + (-1745523277/10000000000 : ℝ)*x 1 + (1239519459/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351419087/2500000000 : ℝ)^5287 ≤ (5828931011991/12500000000000 : ℝ)^4263 := by
    have hnat : (1351419087 : ℕ)^5287*12500000000000^4263 ≤ 5828931011991^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351419087 2500000000 5828931011991 12500000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1745523277/10000000000 : ℝ)^5287 ≤ (11477077440393/100000000000000 : ℝ)^4263 := by
    have hnat : (1745523277 : ℕ)^5287*100000000000000^4263 ≤ 11477077440393^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1745523277 10000000000 11477077440393 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1239519459/2500000000 : ℝ)^5287 ≤ (10472868611791/25000000000000 : ℝ)^4263 := by
    have hnat : (1239519459 : ℕ)^5287*25000000000000^4263 ≤ 10472868611791^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1239519459 2500000000 10472868611791 25000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351419087/2500000000 : ℝ), (-1745523277/10000000000 : ℝ), (1239519459/2500000000 : ℝ)] ![(5828931011991/12500000000000 : ℝ), (11477077440393/100000000000000 : ℝ), (10472868611791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351419087/2500000000 : ℝ)|^5287 ≤ (5828931011991/12500000000000 : ℝ)^4263
        have hw : |(1351419087/2500000000 : ℝ)|=(1351419087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1745523277/10000000000 : ℝ)|^5287 ≤ (11477077440393/100000000000000 : ℝ)^4263
        have hw : |(-1745523277/10000000000 : ℝ)|=(1745523277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1239519459/2500000000 : ℝ)|^5287 ≤ (10472868611791/25000000000000 : ℝ)^4263
        have hw : |(1239519459/2500000000 : ℝ)|=(1239519459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s0_2 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270283763/500000000 : ℝ)*x 0 + (198323139/400000000 : ℝ)*x 1 + (-436380971/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270283763/500000000 : ℝ)^5287 ≤ (46631436455961/100000000000000 : ℝ)^4263 := by
    have hnat : (270283763 : ℕ)^5287*100000000000000^4263 ≤ 46631436455961^4263*500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270283763 500000000 46631436455961 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (198323139/400000000 : ℝ)^5287 ≤ (10472870285759/25000000000000 : ℝ)^4263 := by
    have hnat : (198323139 : ℕ)^5287*25000000000000^4263 ≤ 10472870285759^4263*400000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198323139 400000000 10472870285759 25000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436380971/2500000000 : ℝ)^5287 ≤ (11477082390201/100000000000000 : ℝ)^4263 := by
    have hnat : (436380971 : ℕ)^5287*100000000000000^4263 ≤ 11477082390201^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436380971 2500000000 11477082390201 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270283763/500000000 : ℝ), (198323139/400000000 : ℝ), (-436380971/2500000000 : ℝ)] ![(46631436455961/100000000000000 : ℝ), (10472870285759/25000000000000 : ℝ), (11477082390201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270283763/500000000 : ℝ)|^5287 ≤ (46631436455961/100000000000000 : ℝ)^4263
        have hw : |(270283763/500000000 : ℝ)|=(270283763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(198323139/400000000 : ℝ)|^5287 ≤ (10472870285759/25000000000000 : ℝ)^4263
        have hw : |(198323139/400000000 : ℝ)|=(198323139/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436380971/2500000000 : ℝ)|^5287 ≤ (11477082390201/100000000000000 : ℝ)^4263
        have hw : |(-436380971/2500000000 : ℝ)|=(436380971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s0_3 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (252578123/625000000 : ℝ)*x 0 + (1528897443/5000000000 : ℝ)*x 1 + (520437701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252578123/625000000 : ℝ)^5287 ≤ (32508599466189/100000000000000 : ℝ)^4263 := by
    have hnat : (252578123 : ℕ)^5287*100000000000000^4263 ≤ 32508599466189^4263*625000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252578123 625000000 32508599466189 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1528897443/5000000000 : ℝ)^5287 ≤ (2300382887183/10000000000000 : ℝ)^4263 := by
    have hnat : (1528897443 : ℕ)^5287*10000000000000^4263 ≤ 2300382887183^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528897443 5000000000 2300382887183 10000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520437701/1000000000 : ℝ)^5287 ≤ (69511830693/156250000000 : ℝ)^4263 := by
    have hnat : (520437701 : ℕ)^5287*156250000000^4263 ≤ 69511830693^4263*1000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520437701 1000000000 69511830693 156250000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(252578123/625000000 : ℝ), (1528897443/5000000000 : ℝ), (520437701/1000000000 : ℝ)] ![(32508599466189/100000000000000 : ℝ), (2300382887183/10000000000000 : ℝ), (69511830693/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(252578123/625000000 : ℝ)|^5287 ≤ (32508599466189/100000000000000 : ℝ)^4263
        have hw : |(252578123/625000000 : ℝ)|=(252578123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1528897443/5000000000 : ℝ)|^5287 ≤ (2300382887183/10000000000000 : ℝ)^4263
        have hw : |(1528897443/5000000000 : ℝ)|=(1528897443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520437701/1000000000 : ℝ)|^5287 ≤ (69511830693/156250000000 : ℝ)^4263
        have hw : |(520437701/1000000000 : ℝ)|=(520437701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s0_4 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1344201233/10000000000 : ℝ)*x 0 + (4976396251/10000000000 : ℝ)*x 1 + (177591797/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344201233/10000000000 : ℝ)^5287 ≤ (83007208709/1000000000000 : ℝ)^4263 := by
    have hnat : (1344201233 : ℕ)^5287*1000000000000^4263 ≤ 83007208709^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344201233 10000000000 83007208709 1000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4976396251/10000000000 : ℝ)^5287 ≤ (21041756111823/50000000000000 : ℝ)^4263 := by
    have hnat : (4976396251 : ℕ)^5287*50000000000000^4263 ≤ 21041756111823^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4976396251 10000000000 21041756111823 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177591797/312500000 : ℝ)^5287 ≤ (49615766886007/100000000000000 : ℝ)^4263 := by
    have hnat : (177591797 : ℕ)^5287*100000000000000^4263 ≤ 49615766886007^4263*312500000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177591797 312500000 49615766886007 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1344201233/10000000000 : ℝ), (4976396251/10000000000 : ℝ), (177591797/312500000 : ℝ)] ![(83007208709/1000000000000 : ℝ), (21041756111823/50000000000000 : ℝ), (49615766886007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1344201233/10000000000 : ℝ)|^5287 ≤ (83007208709/1000000000000 : ℝ)^4263
        have hw : |(-1344201233/10000000000 : ℝ)|=(1344201233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4976396251/10000000000 : ℝ)|^5287 ≤ (21041756111823/50000000000000 : ℝ)^4263
        have hw : |(4976396251/10000000000 : ℝ)|=(4976396251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(177591797/312500000 : ℝ)|^5287 ≤ (49615766886007/100000000000000 : ℝ)^4263
        have hw : |(177591797/312500000 : ℝ)|=(177591797/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s0_5 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040823177/2000000000 : ℝ)*x 0 + (-510331927/5000000000 : ℝ)*x 1 + (5682937549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040823177/2000000000 : ℝ)^5287 ≤ (22242401682559/50000000000000 : ℝ)^4263 := by
    have hnat : (1040823177 : ℕ)^5287*50000000000000^4263 ≤ 22242401682559^4263*2000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040823177 2000000000 22242401682559 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510331927/5000000000 : ℝ)^5287 ≤ (2949714627137/50000000000000 : ℝ)^4263 := by
    have hnat : (510331927 : ℕ)^5287*50000000000000^4263 ≤ 2949714627137^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510331927 5000000000 2949714627137 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5682937549/10000000000 : ℝ)^5287 ≤ (49615767373259/100000000000000 : ℝ)^4263 := by
    have hnat : (5682937549 : ℕ)^5287*100000000000000^4263 ≤ 49615767373259^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682937549 10000000000 49615767373259 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040823177/2000000000 : ℝ), (-510331927/5000000000 : ℝ), (5682937549/10000000000 : ℝ)] ![(22242401682559/50000000000000 : ℝ), (2949714627137/50000000000000 : ℝ), (49615767373259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040823177/2000000000 : ℝ)|^5287 ≤ (22242401682559/50000000000000 : ℝ)^4263
        have hw : |(1040823177/2000000000 : ℝ)|=(1040823177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-510331927/5000000000 : ℝ)|^5287 ≤ (2949714627137/50000000000000 : ℝ)^4263
        have hw : |(-510331927/5000000000 : ℝ)|=(510331927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5682937549/10000000000 : ℝ)|^5287 ≤ (49615767373259/100000000000000 : ℝ)^4263
        have hw : |(5682937549/10000000000 : ℝ)|=(5682937549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s0_6 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1301028899/2500000000 : ℝ)*x 0 + (5682938247/10000000000 : ℝ)*x 1 + (-1020663227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1301028899/2500000000 : ℝ)^5287 ≤ (22242400150673/50000000000000 : ℝ)^4263 := by
    have hnat : (1301028899 : ℕ)^5287*50000000000000^4263 ≤ 22242400150673^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301028899 2500000000 22242400150673 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5682938247/10000000000 : ℝ)^5287 ≤ (49615774931073/100000000000000 : ℝ)^4263 := by
    have hnat : (5682938247 : ℕ)^5287*100000000000000^4263 ≤ 49615774931073^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5682938247 10000000000 49615774931073 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020663227/10000000000 : ℝ)^5287 ≤ (2949712379849/50000000000000 : ℝ)^4263 := by
    have hnat : (1020663227 : ℕ)^5287*50000000000000^4263 ≤ 2949712379849^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020663227 10000000000 2949712379849 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1301028899/2500000000 : ℝ), (5682938247/10000000000 : ℝ), (-1020663227/10000000000 : ℝ)] ![(22242400150673/50000000000000 : ℝ), (49615774931073/100000000000000 : ℝ), (2949712379849/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1301028899/2500000000 : ℝ)|^5287 ≤ (22242400150673/50000000000000 : ℝ)^4263
        have hw : |(1301028899/2500000000 : ℝ)|=(1301028899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5682938247/10000000000 : ℝ)|^5287 ≤ (49615774931073/100000000000000 : ℝ)^4263
        have hw : |(5682938247/10000000000 : ℝ)|=(5682938247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020663227/10000000000 : ℝ)|^5287 ≤ (2949712379849/50000000000000 : ℝ)^4263
        have hw : |(-1020663227/10000000000 : ℝ)|=(1020663227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s0_7 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (809231187/2000000000 : ℝ)*x 0 + (5151511919/10000000000 : ℝ)*x 1 + (3112426653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (809231187/2000000000 : ℝ)^5287 ≤ (32557550790187/100000000000000 : ℝ)^4263 := by
    have hnat : (809231187 : ℕ)^5287*100000000000000^4263 ≤ 32557550790187^4263*2000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809231187 2000000000 32557550790187 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5151511919/10000000000 : ℝ)^5287 ≤ (43927812256867/100000000000000 : ℝ)^4263 := by
    have hnat : (5151511919 : ℕ)^5287*100000000000000^4263 ≤ 43927812256867^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151511919 10000000000 43927812256867 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3112426653/10000000000 : ℝ)^5287 ≤ (1175731846743/5000000000000 : ℝ)^4263 := by
    have hnat : (3112426653 : ℕ)^5287*5000000000000^4263 ≤ 1175731846743^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3112426653 10000000000 1175731846743 5000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(809231187/2000000000 : ℝ), (5151511919/10000000000 : ℝ), (3112426653/10000000000 : ℝ)] ![(32557550790187/100000000000000 : ℝ), (43927812256867/100000000000000 : ℝ), (1175731846743/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(809231187/2000000000 : ℝ)|^5287 ≤ (32557550790187/100000000000000 : ℝ)^4263
        have hw : |(809231187/2000000000 : ℝ)|=(809231187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5151511919/10000000000 : ℝ)|^5287 ≤ (43927812256867/100000000000000 : ℝ)^4263
        have hw : |(5151511919/10000000000 : ℝ)|=(5151511919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3112426653/10000000000 : ℝ)|^5287 ≤ (1175731846743/5000000000000 : ℝ)^4263
        have hw : |(3112426653/10000000000 : ℝ)|=(3112426653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1708_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (749/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21979/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (0 : ℝ) ^ (5279/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5279 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5279*1^1024 ≤ 0^1024*1^5279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5279/1024 : ℝ) ≤ (177639866957275333/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5279 ≤ (177639866957275333/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5279*20000000000000000000^1024 ≤ 177639866957275333^1024*5^5279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 177639866957275333 20000000000000000000 5279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (177639866957275333/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5279 := by
      have hnat : (1 : ℕ)^1024*1^5279 ≤ 1^5279*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20177639866957275333/20000000000000000000 : ℝ) ≤ (5008583801490653/5000000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (20177639866957275333/20000000000000000000 : ℝ)^1024 ≤ (5008583801490653/5000000000000000 : ℝ)^5279 := by
      have hnat : (20177639866957275333 : ℕ)^1024*5000000000000000^5279 ≤ 5008583801490653^5279*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20177639866957275333 20000000000000000000 5008583801490653 5000000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5008583801490653/5000000000000000 : ℝ)) (X := (20177639866957275333/20000000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10177639866957275333/10000000000000000000 : ℝ) ≤ (2508583801490653/2500000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (10177639866957275333/10000000000000000000 : ℝ)^1024 ≤ (2508583801490653/2500000000000000 : ℝ)^5279 := by
      have hnat : (10177639866957275333 : ℕ)^1024*2500000000000000^5279 ≤ 2508583801490653^5279*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10177639866957275333 10000000000000000000 2508583801490653 2500000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2508583801490653/2500000000000000 : ℝ)) (X := (10177639866957275333/10000000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(8583801490653/2000000000000000 : ℝ)*(0 : ℝ))^(5279/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8583801490653/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(177639866957275333/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(8583801490653/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5279/1024 : ℝ) := by
    rw [show (1 : ℝ)+(8583801490653/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5008583801490653/5000000000000000 : ℝ) by norm_num, show 1+(177639866957275333/20000000000000000000 : ℝ)+(0 : ℝ)=(20177639866957275333/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(177639866957275333/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(8583801490653/2000000000000000 : ℝ)*(2/5 : ℝ))^(5279/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(8583801490653/2000000000000000 : ℝ)*(2/5 : ℝ)=(2508583801490653/2500000000000000 : ℝ) by norm_num, show 1+2*(177639866957275333/20000000000000000000 : ℝ)=(10177639866957275333/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(8583801490653/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8583801490653/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(8583801490653/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8583801490653/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(8583801490653/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (8583801490653/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-41953119/312500000 : ℝ)*X 0 0+(2850934147/5000000000 : ℝ)*X 0 1+(4958078331/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1351419087/2500000000 : ℝ)*X 1 0+(-1745523277/10000000000 : ℝ)*X 1 1+(1239519459/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270283763/500000000 : ℝ)*X 2 0+(198323139/400000000 : ℝ)*X 2 1+(-436380971/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((252578123/625000000 : ℝ)*X 0 0+(1528897443/5000000000 : ℝ)*X 0 1+(520437701/1000000000 : ℝ)*X 0 2+(252578123/625000000 : ℝ)*X 1 0+(1528897443/5000000000 : ℝ)*X 1 1+(520437701/1000000000 : ℝ)*X 1 2+(252578123/625000000 : ℝ)*X 2 0+(1528897443/5000000000 : ℝ)*X 2 1+(520437701/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1344201233/10000000000 : ℝ)*X 0 0+(4976396251/10000000000 : ℝ)*X 0 1+(177591797/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1040823177/2000000000 : ℝ)*X 1 0+(-510331927/5000000000 : ℝ)*X 1 1+(5682937549/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1301028899/2500000000 : ℝ)*X 2 0+(5682938247/10000000000 : ℝ)*X 2 1+(-1020663227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((809231187/2000000000 : ℝ)*X 0 0+(5151511919/10000000000 : ℝ)*X 0 1+(3112426653/10000000000 : ℝ)*X 0 2+(809231187/2000000000 : ℝ)*X 1 0+(5151511919/10000000000 : ℝ)*X 1 1+(3112426653/10000000000 : ℝ)*X 1 2+(809231187/2000000000 : ℝ)*X 2 0+(5151511919/10000000000 : ℝ)*X 2 1+(3112426653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34392525033674985421191/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11173551/6250000000000 : ℝ)*(base1) + (360357059/25000000000000 : ℝ)*(base19) + (9147079/781250000000 : ℝ)*(base23) + (339437537/100000000000000 : ℝ)*(upper3) + (40491871/100000000000000 : ℝ)*(upper5) + (45258376747849/5000000000000 : ℝ)*(major0) + (45258376747849/5000000000000 : ℝ)*(major1) + (45258376747849/5000000000000 : ℝ)*(major2) + (67223597829613/5000000000000 : ℝ)*(sp0) + (336118384696807/25000000000000 : ℝ)*(sp1) + (1344473809389353/100000000000000 : ℝ)*(sp2) + (465857826279193/100000000000000 : ℝ)*(sp3) + (3202400021/100000000000000 : ℝ)*(sp4) + (927679491/50000000000000 : ℝ)*(sp7) + (465859860414991/100000000000000 : ℝ)*(f.failure) + (268894996043093/20000000000000 : ℝ)*(f.sum) + (2046798749603/5000000000000000000000000000 : ℝ)*base66 + (27147880314603/10000000000000000000000000000 : ℝ)*base68 + (52778546844603/10000000000000000000000000000 : ℝ)*base70 + (17172062024603/10000000000000000000000000000 : ℝ)*base72 + (2640474855397/5000000000000000000000000000 : ℝ)*base73 + (23150723515397/10000000000000000000000000000 : ℝ)*base75 + (39326296384603/10000000000000000000000000000 : ℝ)*base78 + (64317389954603/10000000000000000000000000000 : ℝ)*base80 + (5153045735397/5000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4247059/1250000000000000000000 : ℝ)*base89 + (4247059/1250000000000000000000 : ℝ)*base91 + (4247059/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3632066529954117267/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1462298643/100000000000000 : ℝ)*(base19) + (213399831/12500000000000 : ℝ)*(base23) + (64479437/50000000000000 : ℝ)*(upper2) + (272367351/100000000000000 : ℝ)*(upper3) + (48916709/20000000000000 : ℝ)*(upper5) + (119110021384743/12500000000000 : ℝ)*(major0) + (119110021384743/12500000000000 : ℝ)*(major1) + (119110021384743/12500000000000 : ℝ)*(major2) + (1259847761/25000000000000 : ℝ)*(sp1) + (1748459017/25000000000000 : ℝ)*(sp2) + (1415344241340577/100000000000000 : ℝ)*(sp4) + (141533773965089/10000000000000 : ℝ)*(sp5) + (1415335540305861/100000000000000 : ℝ)*(sp6) + (19616639189857/4000000000000 : ℝ)*(sp7) + (19616639189857/4000000000000 : ℝ)*(f.failure) + (1415344241340577/100000000000000 : ℝ)*(f.sum) + (16014994632179/12500000000000000000000000000 : ℝ)*base65 + (121882278742821/25000000000000000000000000000 : ℝ)*base68 + (22873502017821/25000000000000000000000000000 : ℝ)*base70 + (11979302117821/25000000000000000000000000000 : ℝ)*base72 + (4527847780321/12500000000000000000000000000 : ℝ)*base74 + (5744758332179/25000000000000000000000000000 : ℝ)*base75 + (56861426032179/25000000000000000000000000000 : ℝ)*base77 + (56572907242821/25000000000000000000000000000 : ℝ)*base80 + (2401331732179/12500000000000000000000000000 : ℝ)*base81 + (190493/50000000000000000000 : ℝ)*base89 + (190493/50000000000000000000 : ℝ)*base91 + (190493/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1708_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (749/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21979/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1708_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1708_s1_0 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1415543789/10000000000 : ℝ)*x 0 + (2743391023/5000000000 : ℝ)*x 1 + (1281276923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1415543789/10000000000 : ℝ)^5287 ≤ (553158572567/6250000000000 : ℝ)^4263 := by
    have hnat : (1415543789 : ℕ)^5287*6250000000000^4263 ≤ 553158572567^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415543789 10000000000 553158572567 6250000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2743391023/5000000000 : ℝ)^5287 ≤ (9500143003599/20000000000000 : ℝ)^4263 := by
    have hnat : (2743391023 : ℕ)^5287*20000000000000^4263 ≤ 9500143003599^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743391023 5000000000 9500143003599 20000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1281276923/2500000000 : ℝ)^5287 ≤ (21824373901179/50000000000000 : ℝ)^4263 := by
    have hnat : (1281276923 : ℕ)^5287*50000000000000^4263 ≤ 21824373901179^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1281276923 2500000000 21824373901179 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1415543789/10000000000 : ℝ), (2743391023/5000000000 : ℝ), (1281276923/2500000000 : ℝ)] ![(553158572567/6250000000000 : ℝ), (9500143003599/20000000000000 : ℝ), (21824373901179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1415543789/10000000000 : ℝ)|^5287 ≤ (553158572567/6250000000000 : ℝ)^4263
        have hw : |(-1415543789/10000000000 : ℝ)|=(1415543789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2743391023/5000000000 : ℝ)|^5287 ≤ (9500143003599/20000000000000 : ℝ)^4263
        have hw : |(2743391023/5000000000 : ℝ)|=(2743391023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1281276923/2500000000 : ℝ)|^5287 ≤ (21824373901179/50000000000000 : ℝ)^4263
        have hw : |(1281276923/2500000000 : ℝ)|=(1281276923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s1_1 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348381209/10000000000 : ℝ)*x 0 + (-64147517/400000000 : ℝ)*x 1 + (512510677/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348381209/10000000000 : ℝ)^5287 ≤ (71905091453/156250000000 : ℝ)^4263 := by
    have hnat : (5348381209 : ℕ)^5287*156250000000^4263 ≤ 71905091453^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348381209 10000000000 71905091453 156250000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64147517/400000000 : ℝ)^5287 ≤ (1291500424809/12500000000000 : ℝ)^4263 := by
    have hnat : (64147517 : ℕ)^5287*12500000000000^4263 ≤ 1291500424809^4263*400000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64147517 400000000 1291500424809 12500000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (512510677/1000000000 : ℝ)^5287 ≤ (21824369031911/50000000000000 : ℝ)^4263 := by
    have hnat : (512510677 : ℕ)^5287*50000000000000^4263 ≤ 21824369031911^4263*1000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512510677 1000000000 21824369031911 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348381209/10000000000 : ℝ), (-64147517/400000000 : ℝ), (512510677/1000000000 : ℝ)] ![(71905091453/156250000000 : ℝ), (1291500424809/12500000000000 : ℝ), (21824369031911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348381209/10000000000 : ℝ)|^5287 ≤ (71905091453/156250000000 : ℝ)^4263
        have hw : |(5348381209/10000000000 : ℝ)|=(5348381209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64147517/400000000 : ℝ)|^5287 ≤ (1291500424809/12500000000000 : ℝ)^4263
        have hw : |(-64147517/400000000 : ℝ)|=(64147517/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(512510677/1000000000 : ℝ)|^5287 ≤ (21824369031911/50000000000000 : ℝ)^4263
        have hw : |(512510677/1000000000 : ℝ)|=(512510677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s1_2 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267418991/500000000 : ℝ)*x 0 + (640638497/1250000000 : ℝ)*x 1 + (-320737637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267418991/500000000 : ℝ)^5287 ≤ (46019243707693/100000000000000 : ℝ)^4263 := by
    have hnat : (267418991 : ℕ)^5287*100000000000000^4263 ≤ 46019243707693^4263*500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267418991 500000000 46019243707693 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (640638497/1250000000 : ℝ)^5287 ≤ (43648750802081/100000000000000 : ℝ)^4263 := by
    have hnat : (640638497 : ℕ)^5287*100000000000000^4263 ≤ 43648750802081^4263*1250000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640638497 1250000000 43648750802081 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (320737637/2000000000 : ℝ)^5287 ≤ (10332005475929/100000000000000 : ℝ)^4263 := by
    have hnat : (320737637 : ℕ)^5287*100000000000000^4263 ≤ 10332005475929^4263*2000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320737637 2000000000 10332005475929 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267418991/500000000 : ℝ), (640638497/1250000000 : ℝ), (-320737637/2000000000 : ℝ)] ![(46019243707693/100000000000000 : ℝ), (43648750802081/100000000000000 : ℝ), (10332005475929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267418991/500000000 : ℝ)|^5287 ≤ (46019243707693/100000000000000 : ℝ)^4263
        have hw : |(267418991/500000000 : ℝ)|=(267418991/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(640638497/1250000000 : ℝ)|^5287 ≤ (43648750802081/100000000000000 : ℝ)^4263
        have hw : |(640638497/1250000000 : ℝ)|=(640638497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-320737637/2000000000 : ℝ)|^5287 ≤ (10332005475929/100000000000000 : ℝ)^4263
        have hw : |(-320737637/2000000000 : ℝ)|=(320737637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s1_3 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026089751/2500000000 : ℝ)*x 0 + (1801774301/5000000000 : ℝ)*x 1 + (1161835643/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026089751/2500000000 : ℝ)^5287 ≤ (8284845136197/25000000000000 : ℝ)^4263 := by
    have hnat : (1026089751 : ℕ)^5287*25000000000000^4263 ≤ 8284845136197^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026089751 2500000000 8284845136197 25000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1801774301/5000000000 : ℝ)^5287 ≤ (14100164433643/50000000000000 : ℝ)^4263 := by
    have hnat : (1801774301 : ℕ)^5287*50000000000000^4263 ≤ 14100164433643^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801774301 5000000000 14100164433643 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1161835643/2500000000 : ℝ)^5287 ≤ (151016760039/390625000000 : ℝ)^4263 := by
    have hnat : (1161835643 : ℕ)^5287*390625000000^4263 ≤ 151016760039^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1161835643 2500000000 151016760039 390625000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026089751/2500000000 : ℝ), (1801774301/5000000000 : ℝ), (1161835643/2500000000 : ℝ)] ![(8284845136197/25000000000000 : ℝ), (14100164433643/50000000000000 : ℝ), (151016760039/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026089751/2500000000 : ℝ)|^5287 ≤ (8284845136197/25000000000000 : ℝ)^4263
        have hw : |(1026089751/2500000000 : ℝ)|=(1026089751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1801774301/5000000000 : ℝ)|^5287 ≤ (14100164433643/50000000000000 : ℝ)^4263
        have hw : |(1801774301/5000000000 : ℝ)|=(1801774301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1161835643/2500000000 : ℝ)|^5287 ≤ (151016760039/390625000000 : ℝ)^4263
        have hw : |(1161835643/2500000000 : ℝ)|=(1161835643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s1_4 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-707869143/5000000000 : ℝ)*x 0 + (5129443099/10000000000 : ℝ)*x 1 + (1096475149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (707869143/5000000000 : ℝ)^5287 ≤ (8852045366059/100000000000000 : ℝ)^4263 := by
    have hnat : (707869143 : ℕ)^5287*100000000000000^4263 ≤ 8852045366059^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707869143 5000000000 8852045366059 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129443099/10000000000 : ℝ)^5287 ≤ (43694544773619/100000000000000 : ℝ)^4263 := by
    have hnat : (5129443099 : ℕ)^5287*100000000000000^4263 ≤ 43694544773619^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129443099 10000000000 43694544773619 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1096475149/2000000000 : ℝ)^5287 ≤ (47453409840337/100000000000000 : ℝ)^4263 := by
    have hnat : (1096475149 : ℕ)^5287*100000000000000^4263 ≤ 47453409840337^4263*2000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096475149 2000000000 47453409840337 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-707869143/5000000000 : ℝ), (5129443099/10000000000 : ℝ), (1096475149/2000000000 : ℝ)] ![(8852045366059/100000000000000 : ℝ), (43694544773619/100000000000000 : ℝ), (47453409840337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-707869143/5000000000 : ℝ)|^5287 ≤ (8852045366059/100000000000000 : ℝ)^4263
        have hw : |(-707869143/5000000000 : ℝ)|=(707869143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129443099/10000000000 : ℝ)|^5287 ≤ (43694544773619/100000000000000 : ℝ)^4263
        have hw : |(5129443099/10000000000 : ℝ)|=(5129443099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1096475149/2000000000 : ℝ)|^5287 ≤ (47453409840337/100000000000000 : ℝ)^4263
        have hw : |(1096475149/2000000000 : ℝ)|=(1096475149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s1_5 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262576831/500000000 : ℝ)*x 0 + (-623209583/5000000000 : ℝ)*x 1 + (17132423/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262576831/500000000 : ℝ)^5287 ≤ (899761464357/2000000000000 : ℝ)^4263 := by
    have hnat : (262576831 : ℕ)^5287*2000000000000^4263 ≤ 899761464357^4263*500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262576831 500000000 899761464357 2000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623209583/5000000000 : ℝ)^5287 ≤ (7558521055087/100000000000000 : ℝ)^4263 := by
    have hnat : (623209583 : ℕ)^5287*100000000000000^4263 ≤ 7558521055087^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623209583 5000000000 7558521055087 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17132423/31250000 : ℝ)^5287 ≤ (11863351426863/25000000000000 : ℝ)^4263 := by
    have hnat : (17132423 : ℕ)^5287*25000000000000^4263 ≤ 11863351426863^4263*31250000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17132423 31250000 11863351426863 25000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262576831/500000000 : ℝ), (-623209583/5000000000 : ℝ), (17132423/31250000 : ℝ)] ![(899761464357/2000000000000 : ℝ), (7558521055087/100000000000000 : ℝ), (11863351426863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262576831/500000000 : ℝ)|^5287 ≤ (899761464357/2000000000000 : ℝ)^4263
        have hw : |(262576831/500000000 : ℝ)|=(262576831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-623209583/5000000000 : ℝ)|^5287 ≤ (7558521055087/100000000000000 : ℝ)^4263
        have hw : |(-623209583/5000000000 : ℝ)|=(623209583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17132423/31250000 : ℝ)|^5287 ≤ (11863351426863/25000000000000 : ℝ)^4263
        have hw : |(17132423/31250000 : ℝ)|=(17132423/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s1_6 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210061451/400000000 : ℝ)*x 0 + (5482374979/10000000000 : ℝ)*x 1 + (-623210099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210061451/400000000 : ℝ)^5287 ≤ (44988069552427/100000000000000 : ℝ)^4263 := by
    have hnat : (210061451 : ℕ)^5287*100000000000000^4263 ≤ 44988069552427^4263*400000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210061451 400000000 44988069552427 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5482374979/10000000000 : ℝ)^5287 ≤ (23726700808753/50000000000000 : ℝ)^4263 := by
    have hnat : (5482374979 : ℕ)^5287*50000000000000^4263 ≤ 23726700808753^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482374979 10000000000 23726700808753 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (623210099/5000000000 : ℝ)^5287 ≤ (7558528816601/100000000000000 : ℝ)^4263 := by
    have hnat : (623210099 : ℕ)^5287*100000000000000^4263 ≤ 7558528816601^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623210099 5000000000 7558528816601 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210061451/400000000 : ℝ), (5482374979/10000000000 : ℝ), (-623210099/5000000000 : ℝ)] ![(44988069552427/100000000000000 : ℝ), (23726700808753/50000000000000 : ℝ), (7558528816601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210061451/400000000 : ℝ)|^5287 ≤ (44988069552427/100000000000000 : ℝ)^4263
        have hw : |(210061451/400000000 : ℝ)|=(210061451/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5482374979/10000000000 : ℝ)|^5287 ≤ (23726700808753/50000000000000 : ℝ)^4263
        have hw : |(5482374979/10000000000 : ℝ)|=(5482374979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-623210099/5000000000 : ℝ)|^5287 ≤ (7558528816601/100000000000000 : ℝ)^4263
        have hw : |(-623210099/5000000000 : ℝ)|=(623210099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s1_7 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2052459023/5000000000 : ℝ)*x 0 + (4634829257/10000000000 : ℝ)*x 1 + (361626387/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052459023/5000000000 : ℝ)^5287 ≤ (6628995739043/20000000000000 : ℝ)^4263 := by
    have hnat : (2052459023 : ℕ)^5287*20000000000000^4263 ≤ 6628995739043^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052459023 5000000000 6628995739043 20000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4634829257/10000000000 : ℝ)^5287 ≤ (38531232187379/100000000000000 : ℝ)^4263 := by
    have hnat : (4634829257 : ℕ)^5287*100000000000000^4263 ≤ 38531232187379^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634829257 10000000000 38531232187379 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361626387/1000000000 : ℝ)^5287 ≤ (14161894555687/50000000000000 : ℝ)^4263 := by
    have hnat : (361626387 : ℕ)^5287*50000000000000^4263 ≤ 14161894555687^4263*1000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361626387 1000000000 14161894555687 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052459023/5000000000 : ℝ), (4634829257/10000000000 : ℝ), (361626387/1000000000 : ℝ)] ![(6628995739043/20000000000000 : ℝ), (38531232187379/100000000000000 : ℝ), (14161894555687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052459023/5000000000 : ℝ)|^5287 ≤ (6628995739043/20000000000000 : ℝ)^4263
        have hw : |(2052459023/5000000000 : ℝ)|=(2052459023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4634829257/10000000000 : ℝ)|^5287 ≤ (38531232187379/100000000000000 : ℝ)^4263
        have hw : |(4634829257/10000000000 : ℝ)|=(4634829257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(361626387/1000000000 : ℝ)|^5287 ≤ (14161894555687/50000000000000 : ℝ)^4263
        have hw : |(361626387/1000000000 : ℝ)|=(361626387/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1708_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (749/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (607/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2179/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (749/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (749/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (749/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (749/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (749/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (749/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (749/12500 : ℝ) ^ (5279/1024 : ℝ) ≤ (24947004179999/50000000000000000000 : ℝ) := by
    have hpowers : (749/12500 : ℝ)^5279 ≤ (24947004179999/50000000000000000000 : ℝ)^1024 := by
      have hnat : (749 : ℕ)^5279*50000000000000000000^1024 ≤ 24947004179999^1024*12500^5279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        749 12500 24947004179999 50000000000000000000 5279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (749/12500 : ℝ)) (X := (24947004179999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21979/100000 : ℝ) ^ (5279/1024 : ℝ) ≤ (40538806113924449/100000000000000000000 : ℝ) := by
    have hpowers : (21979/100000 : ℝ)^5279 ≤ (40538806113924449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (21979 : ℕ)^5279*100000000000000000000^1024 ≤ 40538806113924449^1024*100000^5279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21979 100000 40538806113924449 100000000000000000000 5279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21979/100000 : ℝ)) (X := (40538806113924449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000024947004179999/25000000000000000000 : ℝ) ≤ (10000001935648571/10000000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (25000024947004179999/25000000000000000000 : ℝ)^1024 ≤ (10000001935648571/10000000000000000 : ℝ)^5279 := by
      have hnat : (25000024947004179999 : ℕ)^1024*10000000000000000^5279 ≤ 10000001935648571^5279*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000024947004179999 25000000000000000000 10000001935648571 10000000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001935648571/10000000000000000 : ℝ)) (X := (25000024947004179999/25000000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040588700122284447/100000000000000000000 : ℝ) ≤ (2500196798786941/2500000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (100040588700122284447/100000000000000000000 : ℝ)^1024 ≤ (2500196798786941/2500000000000000 : ℝ)^5279 := by
      have hnat : (100040588700122284447 : ℕ)^1024*2500000000000000^5279 ≤ 2500196798786941^5279*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040588700122284447 100000000000000000000 2500196798786941 2500000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500196798786941/2500000000000000 : ℝ)) (X := (100040588700122284447/100000000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50040538806113924449/50000000000000000000 : ℝ) ≤ (10001572454646957/10000000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (50040538806113924449/50000000000000000000 : ℝ)^1024 ≤ (10001572454646957/10000000000000000 : ℝ)^5279 := by
      have hnat : (50040538806113924449 : ℕ)^1024*10000000000000000^5279 ≤ 10001572454646957^5279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50040538806113924449 50000000000000000000 10001572454646957 10000000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001572454646957/10000000000000000 : ℝ)) (X := (50040538806113924449/50000000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24947004179999/50000000000000000000 : ℝ) ≤ ((437974302453083221/438000000000000000 : ℝ)+2*(10756979441/21900000000000 : ℝ)*(749/12500 : ℝ))^(5279/1024 : ℝ) := by
    rw [show (437974302453083221/438000000000000000 : ℝ)+2*(10756979441/21900000000000 : ℝ)*(749/12500 : ℝ)=(10000001935648571/10000000000000000 : ℝ) by norm_num, show 1+2*(24947004179999/50000000000000000000 : ℝ)=(25000024947004179999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(40538806113924449/100000000000000000000 : ℝ)+(24947004179999/50000000000000000000 : ℝ) ≤ ((437974302453083221/438000000000000000 : ℝ)+(10756979441/21900000000000 : ℝ)*((21979/100000 : ℝ)+(749/12500 : ℝ)))^(5279/1024 : ℝ) := by
    rw [show (437974302453083221/438000000000000000 : ℝ)+(10756979441/21900000000000 : ℝ)*((21979/100000 : ℝ)+(749/12500 : ℝ))=(2500196798786941/2500000000000000 : ℝ) by norm_num, show 1+(40538806113924449/100000000000000000000 : ℝ)+(24947004179999/50000000000000000000 : ℝ)=(100040588700122284447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(40538806113924449/100000000000000000000 : ℝ) ≤ ((437974302453083221/438000000000000000 : ℝ)+2*(10756979441/21900000000000 : ℝ)*(21979/100000 : ℝ))^(5279/1024 : ℝ) := by
    rw [show (437974302453083221/438000000000000000 : ℝ)+2*(10756979441/21900000000000 : ℝ)*(21979/100000 : ℝ)=(10001572454646957/10000000000000000 : ℝ) by norm_num, show 1+2*(40538806113924449/100000000000000000000 : ℝ)=(50040538806113924449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (437974302453083221/438000000000000000 : ℝ)*(X 1 0+X 2 0)+(10756979441/21900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (749/12500 : ℝ)) (hi := (21979/100000 : ℝ)) (c := (437974302453083221/438000000000000000 : ℝ)) (alpha := (10756979441/21900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (437974302453083221/438000000000000000 : ℝ)*(X 0 1+X 2 1)+(10756979441/21900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (749/12500 : ℝ)) (hi := (21979/100000 : ℝ)) (c := (437974302453083221/438000000000000000 : ℝ)) (alpha := (10756979441/21900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (437974302453083221/438000000000000000 : ℝ)*(X 0 2+X 1 2)+(10756979441/21900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (749/12500 : ℝ)) (hi := (21979/100000 : ℝ)) (c := (437974302453083221/438000000000000000 : ℝ)) (alpha := (10756979441/21900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1415543789/10000000000 : ℝ)*X 0 0+(2743391023/5000000000 : ℝ)*X 0 1+(1281276923/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348381209/10000000000 : ℝ)*X 1 0+(-64147517/400000000 : ℝ)*X 1 1+(512510677/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267418991/500000000 : ℝ)*X 2 0+(640638497/1250000000 : ℝ)*X 2 1+(-320737637/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1026089751/2500000000 : ℝ)*X 0 0+(1801774301/5000000000 : ℝ)*X 0 1+(1161835643/2500000000 : ℝ)*X 0 2+(1026089751/2500000000 : ℝ)*X 1 0+(1801774301/5000000000 : ℝ)*X 1 1+(1161835643/2500000000 : ℝ)*X 1 2+(1026089751/2500000000 : ℝ)*X 2 0+(1801774301/5000000000 : ℝ)*X 2 1+(1161835643/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-707869143/5000000000 : ℝ)*X 0 0+(5129443099/10000000000 : ℝ)*X 0 1+(1096475149/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262576831/500000000 : ℝ)*X 1 0+(-623209583/5000000000 : ℝ)*X 1 1+(17132423/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210061451/400000000 : ℝ)*X 2 0+(5482374979/10000000000 : ℝ)*X 2 1+(-623210099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2052459023/5000000000 : ℝ)*X 0 0+(4634829257/10000000000 : ℝ)*X 0 1+(361626387/1000000000 : ℝ)*X 0 2+(2052459023/5000000000 : ℝ)*X 1 0+(4634829257/10000000000 : ℝ)*X 1 1+(361626387/1000000000 : ℝ)*X 1 2+(2052459023/5000000000 : ℝ)*X 2 0+(4634829257/10000000000 : ℝ)*X 2 1+(361626387/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13290296021338992202755003/912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1875617431/100000000000000 : ℝ)*(base19) + (1001574023/100000000000000 : ℝ)*(base23) + (123733703/100000000000000 : ℝ)*(lower2) + (384119827/100000000000000 : ℝ)*(upper3) + (201561/500000000000 : ℝ)*(lower4) + (232687043960957/12500000000000 : ℝ)*(major0) + (232687043960957/12500000000000 : ℝ)*(major1) + (232687043960957/12500000000000 : ℝ)*(major2) + (138246688401043/5000000000000 : ℝ)*(sp0) + (1382469798995683/50000000000000 : ℝ)*(sp1) + (1382470236017387/50000000000000 : ℝ)*(sp2) + (958046229810607/100000000000000 : ℝ)*(sp3) + (3852793969/50000000000000 : ℝ)*(sp4) + (902893127/20000000000000 : ℝ)*(sp7) + (479025372138121/50000000000000 : ℝ)*(f.failure) + (1382470736804399/50000000000000 : ℝ)*(f.sum) + (2802667586777/547500000000000000000000000 : ℝ)*base66 + (10596649873182503/5475000000000000000000000000000 : ℝ)*base68 + (33601034674142497/5475000000000000000000000000000 : ℝ)*base69 + (11927926623842497/5475000000000000000000000000000 : ℝ)*base71 + (484422760691/1095000000000000000000000000 : ℝ)*base73 + (18107174001392497/5475000000000000000000000000000 : ℝ)*base75 + (47289751580492497/5475000000000000000000000000000 : ℝ)*base77 + (6564520434132503/5475000000000000000000000000000 : ℝ)*base80 + (225174486701/68437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1444571/625000000000000000000 : ℝ)*base90 + (1444571/625000000000000000000 : ℝ)*base92 + (1444571/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21154789605915926192255787/3650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348859211/25000000000000 : ℝ)*(base19) + (1247752227/100000000000000 : ℝ)*(base23) + (49352767/50000000000000 : ℝ)*(upper2) + (130629011/100000000000000 : ℝ)*(upper3) + (27877199/12500000000000 : ℝ)*(upper5) + (1907586629283553/100000000000000 : ℝ)*(major0) + (1907586629283553/100000000000000 : ℝ)*(major1) + (1907586629283553/100000000000000 : ℝ)*(major2) + (1366937377/12500000000000 : ℝ)*(sp1) + (2828689933/100000000000000 : ℝ)*(sp2) + (2833401176161273/100000000000000 : ℝ)*(sp4) + (1416694422612707/50000000000000 : ℝ)*(sp5) + (1416698549859557/50000000000000 : ℝ)*(sp6) + (490885944605699/50000000000000 : ℝ)*(sp7) + (490885944605699/50000000000000 : ℝ)*(f.failure) + (2833401176161273/100000000000000 : ℝ)*(f.sum) + (5317753632023/1095000000000000000000000000 : ℝ)*base65 + (147539917283624213/43800000000000000000000000000000 : ℝ)*base67 + (39238402142024213/43800000000000000000000000000000 : ℝ)*base69 + (9853762948575787/43800000000000000000000000000000 : ℝ)*base72 + (198105780517/1095000000000000000000000000 : ℝ)*base74 + (114319750037024213/43800000000000000000000000000000 : ℝ)*base75 + (332304768344624213/43800000000000000000000000000000 : ℝ)*base77 + (118196142893024213/43800000000000000000000000000000 : ℝ)*base79 + (674492034253/273750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6108249/625000000000000000000 : ℝ)*base90 + (6108249/625000000000000000000 : ℝ)*base92 + (6108249/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1708_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (749/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (607/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2179/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1708_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1708_s2_0 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-354796689/2500000000 : ℝ)*x 0 + (683985209/1250000000 : ℝ)*x 1 + (2568785147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354796689/2500000000 : ℝ)^5287 ≤ (8878794396159/100000000000000 : ℝ)^4263 := by
    have hnat : (354796689 : ℕ)^5287*100000000000000^4263 ≤ 8878794396159^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354796689 2500000000 8878794396159 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (683985209/1250000000 : ℝ)^5287 ≤ (47340784326873/100000000000000 : ℝ)^4263 := by
    have hnat : (683985209 : ℕ)^5287*100000000000000^4263 ≤ 47340784326873^4263*1250000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683985209 1250000000 47340784326873 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568785147/5000000000 : ℝ)^5287 ≤ (43780421259207/100000000000000 : ℝ)^4263 := by
    have hnat : (2568785147 : ℕ)^5287*100000000000000^4263 ≤ 43780421259207^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568785147 5000000000 43780421259207 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-354796689/2500000000 : ℝ), (683985209/1250000000 : ℝ), (2568785147/5000000000 : ℝ)] ![(8878794396159/100000000000000 : ℝ), (47340784326873/100000000000000 : ℝ), (43780421259207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-354796689/2500000000 : ℝ)|^5287 ≤ (8878794396159/100000000000000 : ℝ)^4263
        have hw : |(-354796689/2500000000 : ℝ)|=(354796689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(683985209/1250000000 : ℝ)|^5287 ≤ (47340784326873/100000000000000 : ℝ)^4263
        have hw : |(683985209/1250000000 : ℝ)|=(683985209/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568785147/5000000000 : ℝ)|^5287 ≤ (43780421259207/100000000000000 : ℝ)^4263
        have hw : |(2568785147/5000000000 : ℝ)|=(2568785147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s2_1 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344347433/10000000000 : ℝ)*x 0 + (-796292527/5000000000 : ℝ)*x 1 + (5137570143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344347433/10000000000 : ℝ)^5287 ≤ (22988108699731/50000000000000 : ℝ)^4263 := by
    have hnat : (5344347433 : ℕ)^5287*50000000000000^4263 ≤ 22988108699731^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344347433 10000000000 22988108699731 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (796292527/5000000000 : ℝ)^5287 ≤ (5121681464801/50000000000000 : ℝ)^4263 := by
    have hnat : (796292527 : ℕ)^5287*50000000000000^4263 ≤ 5121681464801^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      796292527 5000000000 5121681464801 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137570143/10000000000 : ℝ)^5287 ≤ (43780419663353/100000000000000 : ℝ)^4263 := by
    have hnat : (5137570143 : ℕ)^5287*100000000000000^4263 ≤ 43780419663353^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137570143 10000000000 43780419663353 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344347433/10000000000 : ℝ), (-796292527/5000000000 : ℝ), (5137570143/10000000000 : ℝ)] ![(22988108699731/50000000000000 : ℝ), (5121681464801/50000000000000 : ℝ), (43780419663353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344347433/10000000000 : ℝ)|^5287 ≤ (22988108699731/50000000000000 : ℝ)^4263
        have hw : |(5344347433/10000000000 : ℝ)|=(5344347433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-796292527/5000000000 : ℝ)|^5287 ≤ (5121681464801/50000000000000 : ℝ)^4263
        have hw : |(-796292527/5000000000 : ℝ)|=(796292527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137570143/10000000000 : ℝ)|^5287 ≤ (43780419663353/100000000000000 : ℝ)^4263
        have hw : |(5137570143/10000000000 : ℝ)|=(5137570143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s2_2 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068869489/2000000000 : ℝ)*x 0 + (5137570219/10000000000 : ℝ)*x 1 + (-199073117/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068869489/2000000000 : ℝ)^5287 ≤ (45976217527493/100000000000000 : ℝ)^4263 := by
    have hnat : (1068869489 : ℕ)^5287*100000000000000^4263 ≤ 45976217527493^4263*2000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068869489 2000000000 45976217527493 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5137570219/10000000000 : ℝ)^5287 ≤ (10945105116641/25000000000000 : ℝ)^4263 := by
    have hnat : (5137570219 : ℕ)^5287*25000000000000^4263 ≤ 10945105116641^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137570219 10000000000 10945105116641 25000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199073117/1250000000 : ℝ)^5287 ≤ (10243361988329/100000000000000 : ℝ)^4263 := by
    have hnat : (199073117 : ℕ)^5287*100000000000000^4263 ≤ 10243361988329^4263*1250000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199073117 1250000000 10243361988329 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068869489/2000000000 : ℝ), (5137570219/10000000000 : ℝ), (-199073117/1250000000 : ℝ)] ![(45976217527493/100000000000000 : ℝ), (10945105116641/25000000000000 : ℝ), (10243361988329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068869489/2000000000 : ℝ)|^5287 ≤ (45976217527493/100000000000000 : ℝ)^4263
        have hw : |(1068869489/2000000000 : ℝ)|=(1068869489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5137570219/10000000000 : ℝ)|^5287 ≤ (10945105116641/25000000000000 : ℝ)^4263
        have hw : |(5137570219/10000000000 : ℝ)|=(5137570219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199073117/1250000000 : ℝ)|^5287 ≤ (10243361988329/100000000000000 : ℝ)^4263
        have hw : |(-199073117/1250000000 : ℝ)|=(199073117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s2_3 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1026794897/2500000000 : ℝ)*x 0 + (22767389/62500000 : ℝ)*x 1 + (921521511/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026794897/2500000000 : ℝ)^5287 ≤ (33167627256563/100000000000000 : ℝ)^4263 := by
    have hnat : (1026794897 : ℕ)^5287*100000000000000^4263 ≤ 33167627256563^4263*2500000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026794897 2500000000 33167627256563 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22767389/62500000 : ℝ)^5287 ≤ (893175230159/3125000000000 : ℝ)^4263 := by
    have hnat : (22767389 : ℕ)^5287*3125000000000^4263 ≤ 893175230159^4263*62500000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22767389 62500000 893175230159 3125000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (921521511/2000000000 : ℝ)^5287 ≤ (38250765365197/100000000000000 : ℝ)^4263 := by
    have hnat : (921521511 : ℕ)^5287*100000000000000^4263 ≤ 38250765365197^4263*2000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921521511 2000000000 38250765365197 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1026794897/2500000000 : ℝ), (22767389/62500000 : ℝ), (921521511/2000000000 : ℝ)] ![(33167627256563/100000000000000 : ℝ), (893175230159/3125000000000 : ℝ), (38250765365197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1026794897/2500000000 : ℝ)|^5287 ≤ (33167627256563/100000000000000 : ℝ)^4263
        have hw : |(1026794897/2500000000 : ℝ)|=(1026794897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(22767389/62500000 : ℝ)|^5287 ≤ (893175230159/3125000000000 : ℝ)^4263
        have hw : |(22767389/62500000 : ℝ)|=(22767389/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(921521511/2000000000 : ℝ)|^5287 ≤ (38250765365197/100000000000000 : ℝ)^4263
        have hw : |(921521511/2000000000 : ℝ)|=(921521511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s2_4 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-709669893/5000000000 : ℝ)*x 0 + (5141277493/10000000000 : ℝ)*x 1 + (54681189/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (709669893/5000000000 : ℝ)^5287 ≤ (8879981778621/100000000000000 : ℝ)^4263 := by
    have hnat : (709669893 : ℕ)^5287*100000000000000^4263 ≤ 8879981778621^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709669893 5000000000 8879981778621 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141277493/10000000000 : ℝ)^5287 ≤ (43819604437973/100000000000000 : ℝ)^4263 := by
    have hnat : (5141277493 : ℕ)^5287*100000000000000^4263 ≤ 43819604437973^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141277493 10000000000 43819604437973 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54681189/100000000 : ℝ)^5287 ≤ (47300413768431/100000000000000 : ℝ)^4263 := by
    have hnat : (54681189 : ℕ)^5287*100000000000000^4263 ≤ 47300413768431^4263*100000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54681189 100000000 47300413768431 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-709669893/5000000000 : ℝ), (5141277493/10000000000 : ℝ), (54681189/100000000 : ℝ)] ![(8879981778621/100000000000000 : ℝ), (43819604437973/100000000000000 : ℝ), (47300413768431/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-709669893/5000000000 : ℝ)|^5287 ≤ (8879981778621/100000000000000 : ℝ)^4263
        have hw : |(-709669893/5000000000 : ℝ)|=(709669893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141277493/10000000000 : ℝ)|^5287 ≤ (43819604437973/100000000000000 : ℝ)^4263
        have hw : |(5141277493/10000000000 : ℝ)|=(5141277493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54681189/100000000 : ℝ)|^5287 ≤ (47300413768431/100000000000000 : ℝ)^4263
        have hw : |(54681189/100000000 : ℝ)|=(54681189/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s2_5 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254864823/10000000000 : ℝ)*x 0 + (-1262036193/10000000000 : ℝ)*x 1 + (5468118863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254864823/10000000000 : ℝ)^5287 ≤ (22511718057213/50000000000000 : ℝ)^4263 := by
    have hnat : (5254864823 : ℕ)^5287*50000000000000^4263 ≤ 22511718057213^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254864823 10000000000 22511718057213 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262036193/10000000000 : ℝ)^5287 ≤ (3838075248763/50000000000000 : ℝ)^4263 := by
    have hnat : (1262036193 : ℕ)^5287*50000000000000^4263 ≤ 3838075248763^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262036193 10000000000 3838075248763 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468118863/10000000000 : ℝ)^5287 ≤ (47300413371493/100000000000000 : ℝ)^4263 := by
    have hnat : (5468118863 : ℕ)^5287*100000000000000^4263 ≤ 47300413371493^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468118863 10000000000 47300413371493 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254864823/10000000000 : ℝ), (-1262036193/10000000000 : ℝ), (5468118863/10000000000 : ℝ)] ![(22511718057213/50000000000000 : ℝ), (3838075248763/50000000000000 : ℝ), (47300413371493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254864823/10000000000 : ℝ)|^5287 ≤ (22511718057213/50000000000000 : ℝ)^4263
        have hw : |(5254864823/10000000000 : ℝ)|=(5254864823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1262036193/10000000000 : ℝ)|^5287 ≤ (3838075248763/50000000000000 : ℝ)^4263
        have hw : |(-1262036193/10000000000 : ℝ)|=(1262036193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468118863/10000000000 : ℝ)|^5287 ≤ (47300413371493/100000000000000 : ℝ)^4263
        have hw : |(5468118863/10000000000 : ℝ)|=(5468118863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s2_6 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254864761/10000000000 : ℝ)*x 0 + (5468118871/10000000000 : ℝ)*x 1 + (-1262036269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254864761/10000000000 : ℝ)^5287 ≤ (11255858863903/25000000000000 : ℝ)^4263 := by
    have hnat : (5254864761 : ℕ)^5287*25000000000000^4263 ≤ 11255858863903^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254864761 10000000000 11255858863903 25000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468118871/10000000000 : ℝ)^5287 ≤ (47300413457317/100000000000000 : ℝ)^4263 := by
    have hnat : (5468118871 : ℕ)^5287*100000000000000^4263 ≤ 47300413457317^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468118871 10000000000 47300413457317 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1262036269/10000000000 : ℝ)^5287 ≤ (7676151070823/100000000000000 : ℝ)^4263 := by
    have hnat : (1262036269 : ℕ)^5287*100000000000000^4263 ≤ 7676151070823^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262036269 10000000000 7676151070823 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254864761/10000000000 : ℝ), (5468118871/10000000000 : ℝ), (-1262036269/10000000000 : ℝ)] ![(11255858863903/25000000000000 : ℝ), (47300413457317/100000000000000 : ℝ), (7676151070823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254864761/10000000000 : ℝ)|^5287 ≤ (11255858863903/25000000000000 : ℝ)^4263
        have hw : |(5254864761/10000000000 : ℝ)|=(5254864761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468118871/10000000000 : ℝ)|^5287 ≤ (47300413457317/100000000000000 : ℝ)^4263
        have hw : |(5468118871/10000000000 : ℝ)|=(5468118871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1262036269/10000000000 : ℝ)|^5287 ≤ (7676151070823/100000000000000 : ℝ)^4263
        have hw : |(-1262036269/10000000000 : ℝ)|=(1262036269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1708_s2_7 (p : ℝ) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2053810501/5000000000 : ℝ)*x 0 + (91938161/200000000 : ℝ)*x 1 + (3653641611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053810501/5000000000 : ℝ)^5287 ≤ (8293012053663/25000000000000 : ℝ)^4263 := by
    have hnat : (2053810501 : ℕ)^5287*25000000000000^4263 ≤ 8293012053663^4263*5000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053810501 5000000000 8293012053663 25000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91938161/200000000 : ℝ)^5287 ≤ (38140636516227/100000000000000 : ℝ)^4263 := by
    have hnat : (91938161 : ℕ)^5287*100000000000000^4263 ≤ 38140636516227^4263*200000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91938161 200000000 38140636516227 100000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3653641611/10000000000 : ℝ)^5287 ≤ (14343657631247/50000000000000 : ℝ)^4263 := by
    have hnat : (3653641611 : ℕ)^5287*50000000000000^4263 ≤ 14343657631247^4263*10000000000^5287 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3653641611 10000000000 14343657631247 50000000000000 5287 4263 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5287/1024 : ℝ)) 5287 4263 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2053810501/5000000000 : ℝ), (91938161/200000000 : ℝ), (3653641611/10000000000 : ℝ)] ![(8293012053663/25000000000000 : ℝ), (38140636516227/100000000000000 : ℝ), (14343657631247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2053810501/5000000000 : ℝ)|^5287 ≤ (8293012053663/25000000000000 : ℝ)^4263
        have hw : |(2053810501/5000000000 : ℝ)|=(2053810501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91938161/200000000 : ℝ)|^5287 ≤ (38140636516227/100000000000000 : ℝ)^4263
        have hw : |(91938161/200000000 : ℝ)|=(91938161/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3653641611/10000000000 : ℝ)|^5287 ≤ (14343657631247/50000000000000 : ℝ)^4263
        have hw : |(3653641611/10000000000 : ℝ)|=(3653641611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1708_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2179/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (607/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (312/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17119/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2179/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (607/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2179/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (607/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2179/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (607/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2179/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (607/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2179/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (607/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2179/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (607/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (607/6250 : ℝ) ^ (5279/1024 : ℝ) ≤ (601588194748301/100000000000000000000 : ℝ) := by
    have hpowers : (607/6250 : ℝ)^5279 ≤ (601588194748301/100000000000000000000 : ℝ)^1024 := by
      have hnat : (607 : ℕ)^5279*100000000000000000000^1024 ≤ 601588194748301^1024*6250^5279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        607 6250 601588194748301 100000000000000000000 5279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (607/6250 : ℝ)) (X := (601588194748301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2179/12500 : ℝ) ^ (5279/1024 : ℝ) ≤ (767039056391889/6250000000000000000 : ℝ) := by
    have hpowers : (2179/12500 : ℝ)^5279 ≤ (767039056391889/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2179 : ℕ)^5279*6250000000000000000^1024 ≤ 767039056391889^1024*12500^5279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2179 12500 767039056391889 6250000000000000000 5279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2179/12500 : ℝ)) (X := (767039056391889/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000601588194748301/50000000000000000000 : ℝ) ≤ (10000023338637029/10000000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (50000601588194748301/50000000000000000000 : ℝ)^1024 ≤ (10000023338637029/10000000000000000 : ℝ)^5279 := by
      have hnat : (50000601588194748301 : ℕ)^1024*10000000000000000^5279 ≤ 10000023338637029^5279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000601588194748301 50000000000000000000 10000023338637029 10000000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000023338637029/10000000000000000 : ℝ)) (X := (50000601588194748301/50000000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000514968523880741/4000000000000000000 : ℝ) ≤ (500012485802481/500000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (4000514968523880741/4000000000000000000 : ℝ)^1024 ≤ (500012485802481/500000000000000 : ℝ)^5279 := by
      have hnat : (4000514968523880741 : ℕ)^1024*500000000000000^5279 ≤ 500012485802481^5279*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000514968523880741 4000000000000000000 500012485802481 500000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500012485802481/500000000000000 : ℝ)) (X := (4000514968523880741/4000000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3125767039056391889/3125000000000000000 : ℝ) ≤ (10000476093462211/10000000000000000 : ℝ) ^ (5279/1024 : ℝ) := by
    have hpowers : (3125767039056391889/3125000000000000000 : ℝ)^1024 ≤ (10000476093462211/10000000000000000 : ℝ)^5279 := by
      have hnat : (3125767039056391889 : ℕ)^1024*10000000000000000^5279 ≤ 10000476093462211^5279*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125767039056391889 3125000000000000000 10000476093462211 10000000000000000 1024 5279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000476093462211/10000000000000000 : ℝ)) (X := (3125767039056391889/3125000000000000000 : ℝ)) (by norm_num) 5279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(601588194748301/100000000000000000000 : ℝ) ≤ ((9649472877426962037/9650000000000000000 : ℝ)+2*(226377412591/772000000000000 : ℝ)*(607/6250 : ℝ))^(5279/1024 : ℝ) := by
    rw [show (9649472877426962037/9650000000000000000 : ℝ)+2*(226377412591/772000000000000 : ℝ)*(607/6250 : ℝ)=(10000023338637029/10000000000000000 : ℝ) by norm_num, show 1+2*(601588194748301/100000000000000000000 : ℝ)=(50000601588194748301/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(767039056391889/6250000000000000000 : ℝ)+(601588194748301/100000000000000000000 : ℝ) ≤ ((9649472877426962037/9650000000000000000 : ℝ)+(226377412591/772000000000000 : ℝ)*((2179/12500 : ℝ)+(607/6250 : ℝ)))^(5279/1024 : ℝ) := by
    rw [show (9649472877426962037/9650000000000000000 : ℝ)+(226377412591/772000000000000 : ℝ)*((2179/12500 : ℝ)+(607/6250 : ℝ))=(500012485802481/500000000000000 : ℝ) by norm_num, show 1+(767039056391889/6250000000000000000 : ℝ)+(601588194748301/100000000000000000000 : ℝ)=(4000514968523880741/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(767039056391889/6250000000000000000 : ℝ) ≤ ((9649472877426962037/9650000000000000000 : ℝ)+2*(226377412591/772000000000000 : ℝ)*(2179/12500 : ℝ))^(5279/1024 : ℝ) := by
    rw [show (9649472877426962037/9650000000000000000 : ℝ)+2*(226377412591/772000000000000 : ℝ)*(2179/12500 : ℝ)=(10000476093462211/10000000000000000 : ℝ) by norm_num, show 1+2*(767039056391889/6250000000000000000 : ℝ)=(3125767039056391889/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9649472877426962037/9650000000000000000 : ℝ)*(X 1 0+X 2 0)+(226377412591/772000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (607/6250 : ℝ)) (hi := (2179/12500 : ℝ)) (c := (9649472877426962037/9650000000000000000 : ℝ)) (alpha := (226377412591/772000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9649472877426962037/9650000000000000000 : ℝ)*(X 0 1+X 2 1)+(226377412591/772000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (607/6250 : ℝ)) (hi := (2179/12500 : ℝ)) (c := (9649472877426962037/9650000000000000000 : ℝ)) (alpha := (226377412591/772000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9649472877426962037/9650000000000000000 : ℝ)*(X 0 2+X 1 2)+(226377412591/772000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5279/1024 : ℝ)) (lo := (607/6250 : ℝ)) (hi := (2179/12500 : ℝ)) (c := (9649472877426962037/9650000000000000000 : ℝ)) (alpha := (226377412591/772000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-354796689/2500000000 : ℝ)*X 0 0+(683985209/1250000000 : ℝ)*X 0 1+(2568785147/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344347433/10000000000 : ℝ)*X 1 0+(-796292527/5000000000 : ℝ)*X 1 1+(5137570143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068869489/2000000000 : ℝ)*X 2 0+(5137570219/10000000000 : ℝ)*X 2 1+(-199073117/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1026794897/2500000000 : ℝ)*X 0 0+(22767389/62500000 : ℝ)*X 0 1+(921521511/2000000000 : ℝ)*X 0 2+(1026794897/2500000000 : ℝ)*X 1 0+(22767389/62500000 : ℝ)*X 1 1+(921521511/2000000000 : ℝ)*X 1 2+(1026794897/2500000000 : ℝ)*X 2 0+(22767389/62500000 : ℝ)*X 2 1+(921521511/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-709669893/5000000000 : ℝ)*X 0 0+(5141277493/10000000000 : ℝ)*X 0 1+(54681189/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254864823/10000000000 : ℝ)*X 1 0+(-1262036193/10000000000 : ℝ)*X 1 1+(5468118863/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254864761/10000000000 : ℝ)*X 2 0+(5468118871/10000000000 : ℝ)*X 2 1+(-1262036269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2053810501/5000000000 : ℝ)*X 0 0+(91938161/200000000 : ℝ)*X 0 1+(3653641611/10000000000 : ℝ)*X 0 2+(2053810501/5000000000 : ℝ)*X 1 0+(91938161/200000000 : ℝ)*X 1 1+(3653641611/10000000000 : ℝ)*X 1 2+(2053810501/5000000000 : ℝ)*X 2 0+(91938161/200000000 : ℝ)*X 2 1+(3653641611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1708_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (194146773000436795706869881/30156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (756272917/100000000000000 : ℝ)*(base19) + (638300261/100000000000000 : ℝ)*(base23) + (8329771/12500000000000 : ℝ)*(lower2) + (13631881/12500000000000 : ℝ)*(upper3) + (18989173/20000000000000 : ℝ)*(upper5) + (125865535135179/6250000000000 : ℝ)*(major0) + (125865535135179/6250000000000 : ℝ)*(major1) + (125865535135179/6250000000000 : ℝ)*(major2) + (747807262742299/25000000000000 : ℝ)*(sp0) + (2991234753948959/100000000000000 : ℝ)*(sp1) + (598246974384323/20000000000000 : ℝ)*(sp2) + (25911475996217/2500000000000 : ℝ)*(sp3) + (6459252679/100000000000000 : ℝ)*(sp4) + (1179827121/50000000000000 : ℝ)*(sp7) + (518230699751461/50000000000000 : ℝ)*(f.failure) + (747808877555469/25000000000000 : ℝ)*(f.sum) + (555019353007/1206250000000000000000000000 : ℝ)*base65 + (406326943803874623/60312500000000000000000000000000 : ℝ)*base67 + (118194998550437123/60312500000000000000000000000000 : ℝ)*base69 + (169329830767624623/60312500000000000000000000000000 : ℝ)*base71 + (1249755450309/603125000000000000000000000 : ℝ)*base74 + (238259983233625377/60312500000000000000000000000000 : ℝ)*base76 + (186165979016374623/60312500000000000000000000000000 : ℝ)*base77 + (254381670451750377/60312500000000000000000000000000 : ℝ)*base80 + (5239166537143/1206250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3140911/625000000000000000000 : ℝ)*base90 + (3140911/625000000000000000000 : ℝ)*base92 + (3140911/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2727585158718746373643000833/482500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191526789/25000000000000 : ℝ)*(base19) + (397393987/50000000000000 : ℝ)*(base23) + (3162447/3125000000000 : ℝ)*(upper3) + (9794211/25000000000000 : ℝ)*(lower4) + (137474879/100000000000000 : ℝ)*(upper5) + (2059866779922501/100000000000000 : ℝ)*(major0) + (2059866779922501/100000000000000 : ℝ)*(major1) + (2059866779922501/100000000000000 : ℝ)*(major2) + (7099464111/100000000000000 : ℝ)*(sp1) + (652549/10000000000 : ℝ)*(sp2) + (3059587913792511/100000000000000 : ℝ)*(sp4) + (764895012055311/25000000000000 : ℝ)*(sp5) + (1529790296757269/50000000000000 : ℝ)*(sp6) + (530072728809137/50000000000000 : ℝ)*(sp7) + (530072728809137/50000000000000 : ℝ)*(f.failure) + (3059587913792511/100000000000000 : ℝ)*(f.sum) + (11632312592891/38600000000000000000000000000 : ℝ)*base65 + (6931561762339767963/965000000000000000000000000000000 : ℝ)*base68 + (6561770569154767963/965000000000000000000000000000000 : ℝ)*base70 + (1311022324339767963/965000000000000000000000000000000 : ℝ)*base72 + (128098788490309/38600000000000000000000000000 : ℝ)*base74 + (8308232920079767963/965000000000000000000000000000000 : ℝ)*base76 + (4818863468334767963/965000000000000000000000000000000 : ℝ)*base78 + (9591778878714767963/965000000000000000000000000000000 : ℝ)*base80 + (46913573101109/38600000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (4714787/625000000000000000000 : ℝ)*base90 + (4714787/625000000000000000000 : ℝ)*base92 + (4714787/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1708_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2179/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (607/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (312/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1708_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1708_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (312/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17119/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1708_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1708_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1708_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5279/1024 : ℝ) ≤ p) (hpb : p ≤ (5287/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24287549/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (312/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17119/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1708_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
