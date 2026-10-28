-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:57.454979+00:00
-- url     : https://prove2.me/submissions/216dd7b3-6a15-4a11-a4ed-2e87820b4312

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
theorem support_rectangle_w1110_s9_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336213441/2500000000 : ℝ)*x 0 + (210610447/400000000 : ℝ)*x 1 + (-2247364463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336213441/2500000000 : ℝ)^8303 ≤ (43536859892421/100000000000000 : ℝ)^6255 := by
    have hnat : (1336213441 : ℕ)^8303*100000000000000^6255 ≤ 43536859892421^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336213441 2500000000 43536859892421 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210610447/400000000 : ℝ)^8303 ≤ (42678364395611/100000000000000 : ℝ)^6255 := by
    have hnat : (210610447 : ℕ)^8303*100000000000000^6255 ≤ 42678364395611^6255*400000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210610447 400000000 42678364395611 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247364463/10000000000 : ℝ)^8303 ≤ (1723096962053/12500000000000 : ℝ)^6255 := by
    have hnat : (2247364463 : ℕ)^8303*12500000000000^6255 ≤ 1723096962053^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247364463 10000000000 1723096962053 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336213441/2500000000 : ℝ), (210610447/400000000 : ℝ), (-2247364463/10000000000 : ℝ)] ![(43536859892421/100000000000000 : ℝ), (42678364395611/100000000000000 : ℝ), (1723096962053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336213441/2500000000 : ℝ)|^8303 ≤ (43536859892421/100000000000000 : ℝ)^6255
        have hw : |(1336213441/2500000000 : ℝ)|=(1336213441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210610447/400000000 : ℝ)|^8303 ≤ (42678364395611/100000000000000 : ℝ)^6255
        have hw : |(210610447/400000000 : ℝ)|=(210610447/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247364463/10000000000 : ℝ)|^8303 ≤ (1723096962053/12500000000000 : ℝ)^6255
        have hw : |(-2247364463/10000000000 : ℝ)|=(2247364463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s9_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873840719/2000000000 : ℝ)*x 0 + (4244231537/10000000000 : ℝ)*x 1 + (4497865831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873840719/2000000000 : ℝ)^8303 ≤ (33316816220993/100000000000000 : ℝ)^6255 := by
    have hnat : (873840719 : ℕ)^8303*100000000000000^6255 ≤ 33316816220993^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873840719 2000000000 33316816220993 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244231537/10000000000 : ℝ)^8303 ≤ (32057803236079/100000000000000 : ℝ)^6255 := by
    have hnat : (4244231537 : ℕ)^8303*100000000000000^6255 ≤ 32057803236079^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244231537 10000000000 32057803236079 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4497865831/10000000000 : ℝ)^8303 ≤ (17312690260493/50000000000000 : ℝ)^6255 := by
    have hnat : (4497865831 : ℕ)^8303*50000000000000^6255 ≤ 17312690260493^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497865831 10000000000 17312690260493 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873840719/2000000000 : ℝ), (4244231537/10000000000 : ℝ), (4497865831/10000000000 : ℝ)] ![(33316816220993/100000000000000 : ℝ), (32057803236079/100000000000000 : ℝ), (17312690260493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873840719/2000000000 : ℝ)|^8303 ≤ (33316816220993/100000000000000 : ℝ)^6255
        have hw : |(873840719/2000000000 : ℝ)|=(873840719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244231537/10000000000 : ℝ)|^8303 ≤ (32057803236079/100000000000000 : ℝ)^6255
        have hw : |(4244231537/10000000000 : ℝ)|=(4244231537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4497865831/10000000000 : ℝ)|^8303 ≤ (17312690260493/50000000000000 : ℝ)^6255
        have hw : |(4497865831/10000000000 : ℝ)|=(4497865831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s9_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182289703/10000000000 : ℝ)*x 0 + (2632791501/5000000000 : ℝ)*x 1 + (2696615287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182289703/10000000000 : ℝ)^8303 ≤ (13257461709859/100000000000000 : ℝ)^6255 := by
    have hnat : (2182289703 : ℕ)^8303*100000000000000^6255 ≤ 13257461709859^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182289703 10000000000 13257461709859 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632791501/5000000000 : ℝ)^8303 ≤ (21340913577817/50000000000000 : ℝ)^6255 := by
    have hnat : (2632791501 : ℕ)^8303*50000000000000^6255 ≤ 21340913577817^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632791501 5000000000 21340913577817 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696615287/5000000000 : ℝ)^8303 ≤ (344224305619/781250000000 : ℝ)^6255 := by
    have hnat : (2696615287 : ℕ)^8303*781250000000^6255 ≤ 344224305619^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696615287 5000000000 344224305619 781250000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182289703/10000000000 : ℝ), (2632791501/5000000000 : ℝ), (2696615287/5000000000 : ℝ)] ![(13257461709859/100000000000000 : ℝ), (21340913577817/50000000000000 : ℝ), (344224305619/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182289703/10000000000 : ℝ)|^8303 ≤ (13257461709859/100000000000000 : ℝ)^6255
        have hw : |(-2182289703/10000000000 : ℝ)|=(2182289703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632791501/5000000000 : ℝ)|^8303 ≤ (21340913577817/50000000000000 : ℝ)^6255
        have hw : |(2632791501/5000000000 : ℝ)|=(2632791501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696615287/5000000000 : ℝ)|^8303 ≤ (344224305619/781250000000 : ℝ)^6255
        have hw : |(2696615287/5000000000 : ℝ)|=(2696615287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s9_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312428563/10000000000 : ℝ)*x 0 + (-2119394683/10000000000 : ℝ)*x 1 + (1078646137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312428563/10000000000 : ℝ)^8303 ≤ (1079665218993/2500000000000 : ℝ)^6255 := by
    have hnat : (5312428563 : ℕ)^8303*2500000000000^6255 ≤ 1079665218993^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312428563 10000000000 1079665218993 2500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2119394683/10000000000 : ℝ)^8303 ≤ (12752678899283/100000000000000 : ℝ)^6255 := by
    have hnat : (2119394683 : ℕ)^8303*100000000000000^6255 ≤ 12752678899283^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119394683 10000000000 12752678899283 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078646137/2000000000 : ℝ)^8303 ≤ (44060712322973/100000000000000 : ℝ)^6255 := by
    have hnat : (1078646137 : ℕ)^8303*100000000000000^6255 ≤ 44060712322973^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078646137 2000000000 44060712322973 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312428563/10000000000 : ℝ), (-2119394683/10000000000 : ℝ), (1078646137/2000000000 : ℝ)] ![(1079665218993/2500000000000 : ℝ), (12752678899283/100000000000000 : ℝ), (44060712322973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312428563/10000000000 : ℝ)|^8303 ≤ (1079665218993/2500000000000 : ℝ)^6255
        have hw : |(5312428563/10000000000 : ℝ)|=(5312428563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2119394683/10000000000 : ℝ)|^8303 ≤ (12752678899283/100000000000000 : ℝ)^6255
        have hw : |(-2119394683/10000000000 : ℝ)|=(2119394683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078646137/2000000000 : ℝ)|^8303 ≤ (44060712322973/100000000000000 : ℝ)^6255
        have hw : |(1078646137/2000000000 : ℝ)|=(1078646137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s9_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312428759/10000000000 : ℝ)*x 0 + (5393231013/10000000000 : ℝ)*x 1 + (-2119393973/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312428759/10000000000 : ℝ)^8303 ≤ (21593305437383/50000000000000 : ℝ)^6255 := by
    have hnat : (5312428759 : ℕ)^8303*50000000000000^6255 ≤ 21593305437383^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312428759 10000000000 21593305437383 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393231013/10000000000 : ℝ)^8303 ≤ (1762428635199/4000000000000 : ℝ)^6255 := by
    have hnat : (5393231013 : ℕ)^8303*4000000000000^6255 ≤ 1762428635199^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393231013 10000000000 1762428635199 4000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2119393973/10000000000 : ℝ)^8303 ≤ (2550534645667/20000000000000 : ℝ)^6255 := by
    have hnat : (2119393973 : ℕ)^8303*20000000000000^6255 ≤ 2550534645667^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119393973 10000000000 2550534645667 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312428759/10000000000 : ℝ), (5393231013/10000000000 : ℝ), (-2119393973/10000000000 : ℝ)] ![(21593305437383/50000000000000 : ℝ), (1762428635199/4000000000000 : ℝ), (2550534645667/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312428759/10000000000 : ℝ)|^8303 ≤ (21593305437383/50000000000000 : ℝ)^6255
        have hw : |(5312428759/10000000000 : ℝ)|=(5312428759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393231013/10000000000 : ℝ)|^8303 ≤ (1762428635199/4000000000000 : ℝ)^6255
        have hw : |(5393231013/10000000000 : ℝ)|=(5393231013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2119393973/10000000000 : ℝ)|^8303 ≤ (2550534645667/20000000000000 : ℝ)^6255
        have hw : |(-2119393973/10000000000 : ℝ)|=(2119393973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s9_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2184606891/5000000000 : ℝ)*x 0 + (2248614753/5000000000 : ℝ)*x 1 + (848973951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184606891/5000000000 : ℝ)^8303 ≤ (520576864601/1562500000000 : ℝ)^6255 := by
    have hnat : (2184606891 : ℕ)^8303*1562500000000^6255 ≤ 520576864601^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184606891 5000000000 520576864601 1562500000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248614753/5000000000 : ℝ)^8303 ≤ (17309439127661/50000000000000 : ℝ)^6255 := by
    have hnat : (2248614753 : ℕ)^8303*50000000000000^6255 ≤ 17309439127661^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248614753 5000000000 17309439127661 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848973951/2000000000 : ℝ)^8303 ≤ (4008025298009/12500000000000 : ℝ)^6255 := by
    have hnat : (848973951 : ℕ)^8303*12500000000000^6255 ≤ 4008025298009^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848973951 2000000000 4008025298009 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184606891/5000000000 : ℝ), (2248614753/5000000000 : ℝ), (848973951/2000000000 : ℝ)] ![(520576864601/1562500000000 : ℝ), (17309439127661/50000000000000 : ℝ), (4008025298009/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184606891/5000000000 : ℝ)|^8303 ≤ (520576864601/1562500000000 : ℝ)^6255
        have hw : |(2184606891/5000000000 : ℝ)|=(2184606891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248614753/5000000000 : ℝ)|^8303 ≤ (17309439127661/50000000000000 : ℝ)^6255
        have hw : |(2248614753/5000000000 : ℝ)|=(2248614753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848973951/2000000000 : ℝ)|^8303 ≤ (4008025298009/12500000000000 : ℝ)^6255
        have hw : |(848973951/2000000000 : ℝ)|=(848973951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_s9_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-69655301/10000000000 : ℝ)*x 0 + (5704374711/10000000000 : ℝ)*x 1 + (122904937/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69655301/10000000000 : ℝ)^8303 ≤ (27398601579/20000000000000 : ℝ)^6255 := by
    have hnat : (69655301 : ℕ)^8303*20000000000000^6255 ≤ 27398601579^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69655301 10000000000 27398601579 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5704374711/10000000000 : ℝ)^8303 ≤ (47466384822929/100000000000000 : ℝ)^6255 := by
    have hnat : (5704374711 : ℕ)^8303*100000000000000^6255 ≤ 47466384822929^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5704374711 10000000000 47466384822929 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122904937/200000000 : ℝ)^8303 ≤ (6549577769293/12500000000000 : ℝ)^6255 := by
    have hnat : (122904937 : ℕ)^8303*12500000000000^6255 ≤ 6549577769293^6255*200000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122904937 200000000 6549577769293 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69655301/10000000000 : ℝ), (5704374711/10000000000 : ℝ), (122904937/200000000 : ℝ)] ![(27398601579/20000000000000 : ℝ), (47466384822929/100000000000000 : ℝ), (6549577769293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69655301/10000000000 : ℝ)|^8303 ≤ (27398601579/20000000000000 : ℝ)^6255
        have hw : |(-69655301/10000000000 : ℝ)|=(69655301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5704374711/10000000000 : ℝ)|^8303 ≤ (47466384822929/100000000000000 : ℝ)^6255
        have hw : |(5704374711/10000000000 : ℝ)|=(5704374711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(122904937/200000000 : ℝ)|^8303 ≤ (6549577769293/12500000000000 : ℝ)^6255
        have hw : |(122904937/200000000 : ℝ)|=(122904937/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (707/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1403/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1403/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (707/6250 : ℝ) ^ (4151/1024 : ℝ) ≤ (1456539609673227/10000000000000000000 : ℝ) := by
    have hpowers : (707/6250 : ℝ)^4151 ≤ (1456539609673227/10000000000000000000 : ℝ)^1024 := by
      have hnat : (707 : ℕ)^4151*10000000000000000000^1024 ≤ 1456539609673227^1024*6250^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        707 6250 1456539609673227 10000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (707/6250 : ℝ)) (X := (1456539609673227/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1403/10000 : ℝ) ^ (4151/1024 : ℝ) ≤ (2179206418280693/6250000000000000000 : ℝ) := by
    have hpowers : (1403/10000 : ℝ)^4151 ≤ (2179206418280693/6250000000000000000 : ℝ)^1024 := by
      have hnat : (1403 : ℕ)^4151*6250000000000000000^1024 ≤ 2179206418280693^1024*10000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1403 10000 2179206418280693 6250000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1403/10000 : ℝ)) (X := (2179206418280693/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001456539609673227/5000000000000000000 : ℝ) ≤ (10000718541525787/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (5001456539609673227/5000000000000000000 : ℝ)^1024 ≤ (10000718541525787/10000000000000000 : ℝ)^4151 := by
      have hnat : (5001456539609673227 : ℕ)^1024*10000000000000000^4151 ≤ 10000718541525787^4151*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001456539609673227 5000000000000000000 10000718541525787 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000718541525787/10000000000000000 : ℝ)) (X := (5001456539609673227/5000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024716349394611679/50000000000000000000 : ℝ) ≤ (2500304804031843/2500000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50024716349394611679/50000000000000000000 : ℝ)^1024 ≤ (2500304804031843/2500000000000000 : ℝ)^4151 := by
      have hnat : (50024716349394611679 : ℕ)^1024*2500000000000000^4151 ≤ 2500304804031843^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024716349394611679 50000000000000000000 2500304804031843 2500000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500304804031843/2500000000000000 : ℝ)) (X := (50024716349394611679/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127179206418280693/3125000000000000000 : ℝ) ≤ (10001719890728957/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (3127179206418280693/3125000000000000000 : ℝ)^1024 ≤ (10001719890728957/10000000000000000 : ℝ)^4151 := by
      have hnat : (3127179206418280693 : ℕ)^1024*10000000000000000^4151 ≤ 10001719890728957^4151*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127179206418280693 3125000000000000000 10001719890728957 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001719890728957/10000000000000000 : ℝ)) (X := (3127179206418280693/3125000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1456539609673227/10000000000000000000 : ℝ) ≤ ((13585312866840415013/13590000000000000000 : ℝ)+2*(100134920317/54360000000000 : ℝ)*(707/6250 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (13585312866840415013/13590000000000000000 : ℝ)+2*(100134920317/54360000000000 : ℝ)*(707/6250 : ℝ)=(10000718541525787/10000000000000000 : ℝ) by norm_num, show 1+2*(1456539609673227/10000000000000000000 : ℝ)=(5001456539609673227/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2179206418280693/6250000000000000000 : ℝ)+(1456539609673227/10000000000000000000 : ℝ) ≤ ((13585312866840415013/13590000000000000000 : ℝ)+(100134920317/54360000000000 : ℝ)*((1403/10000 : ℝ)+(707/6250 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (13585312866840415013/13590000000000000000 : ℝ)+(100134920317/54360000000000 : ℝ)*((1403/10000 : ℝ)+(707/6250 : ℝ))=(2500304804031843/2500000000000000 : ℝ) by norm_num, show 1+(2179206418280693/6250000000000000000 : ℝ)+(1456539609673227/10000000000000000000 : ℝ)=(50024716349394611679/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2179206418280693/6250000000000000000 : ℝ) ≤ ((13585312866840415013/13590000000000000000 : ℝ)+2*(100134920317/54360000000000 : ℝ)*(1403/10000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (13585312866840415013/13590000000000000000 : ℝ)+2*(100134920317/54360000000000 : ℝ)*(1403/10000 : ℝ)=(10001719890728957/10000000000000000 : ℝ) by norm_num, show 1+2*(2179206418280693/6250000000000000000 : ℝ)=(3127179206418280693/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13585312866840415013/13590000000000000000 : ℝ)*(X 1 0+X 2 0)+(100134920317/54360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (13585312866840415013/13590000000000000000 : ℝ)) (alpha := (100134920317/54360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13585312866840415013/13590000000000000000 : ℝ)*(X 0 1+X 2 1)+(100134920317/54360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (13585312866840415013/13590000000000000000 : ℝ)) (alpha := (100134920317/54360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13585312866840415013/13590000000000000000 : ℝ)*(X 0 2+X 1 2)+(100134920317/54360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (1403/10000 : ℝ)) (c := (13585312866840415013/13590000000000000000 : ℝ)) (alpha := (100134920317/54360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336213441/2500000000 : ℝ)*X 2 0+(210610447/400000000 : ℝ)*X 2 1+(-2247364463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((873840719/2000000000 : ℝ)*X 0 0+(4244231537/10000000000 : ℝ)*X 0 1+(4497865831/10000000000 : ℝ)*X 0 2+(873840719/2000000000 : ℝ)*X 1 0+(4244231537/10000000000 : ℝ)*X 1 1+(4497865831/10000000000 : ℝ)*X 1 2+(873840719/2000000000 : ℝ)*X 2 0+(4244231537/10000000000 : ℝ)*X 2 1+(4497865831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-2182289703/10000000000 : ℝ)*X 0 0+(2632791501/5000000000 : ℝ)*X 0 1+(2696615287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312428563/10000000000 : ℝ)*X 1 0+(-2119394683/10000000000 : ℝ)*X 1 1+(1078646137/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312428759/10000000000 : ℝ)*X 2 0+(5393231013/10000000000 : ℝ)*X 2 1+(-2119393973/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2184606891/5000000000 : ℝ)*X 0 0+(2248614753/5000000000 : ℝ)*X 0 1+(848973951/2000000000 : ℝ)*X 0 2+(2184606891/5000000000 : ℝ)*X 1 0+(2248614753/5000000000 : ℝ)*X 1 1+(848973951/2000000000 : ℝ)*X 1 2+(2184606891/5000000000 : ℝ)*X 2 0+(2248614753/5000000000 : ℝ)*X 2 1+(848973951/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((-69655301/10000000000 : ℝ)*X 0 0+(5704374711/10000000000 : ℝ)*X 0 1+(122904937/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_s9_6 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243778659431411677594387617/75500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (892043/125000000000 : ℝ)*(lower2) + (54846709/20000000000000 : ℝ)*(lower3) + (471049179/100000000000000 : ℝ)*(lower4) + (2970861/2500000000000 : ℝ)*(lower5) + (5898348689227527/100000000000000 : ℝ)*(major0) + (5898348689227527/100000000000000 : ℝ)*(major1) + (5898348689227527/100000000000000 : ℝ)*(major2) + (13729726617/50000000000000 : ℝ)*(sp0) + (10277752187/100000000000000 : ℝ)*(sp1) + (3917036435663313/50000000000000 : ℝ)*(sp2) + (7834077674305261/100000000000000 : ℝ)*(sp3) + (7834050214852027/100000000000000 : ℝ)*(sp4) + (1981304659384521/50000000000000 : ℝ)*(sp5) + (960595727/20000000000000 : ℝ)*(sp6) + (3962619596521229/100000000000000 : ℝ)*(f.failure) + (7834077674305261/100000000000000 : ℝ)*(f.sum) + (2521220888423/906000000000000000000000000 : ℝ)*base66 + (410397590099287461/151000000000000000000000000000000 : ℝ)*base68 + (6726950280822287461/151000000000000000000000000000000 : ℝ)*base70 + (10834476270343287461/151000000000000000000000000000000 : ℝ)*base72 + (464692659259/181200000000000000000000000 : ℝ)*base74 + (1449141008183287461/151000000000000000000000000000000 : ℝ)*base76 + (856918083430712539/151000000000000000000000000000000 : ℝ)*base77 + (1566525732736712539/151000000000000000000000000000000 : ℝ)*base79 + (566496532211/906000000000000000000000000 : ℝ)*base82 + (34518143/10000000000000000000000 : ℝ)*base90 + (34518143/10000000000000000000000 : ℝ)*base92 + (34518143/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1110_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1110_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1110_box_0 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2054333289/10000000000 : ℝ)*x 0 + (2688379621/5000000000 : ℝ)*x 1 + (2688379587/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054333289/10000000000 : ℝ)^8303 ≤ (305891176037/2500000000000 : ℝ)^6255 := by
    have hnat : (2054333289 : ℕ)^8303*2500000000000^6255 ≤ 305891176037^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054333289 10000000000 305891176037 2500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688379621/5000000000 : ℝ)^8303 ≤ (2742636052423/6250000000000 : ℝ)^6255 := by
    have hnat : (2688379621 : ℕ)^8303*6250000000000^6255 ≤ 2742636052423^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688379621 5000000000 2742636052423 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688379587/5000000000 : ℝ)^8303 ≤ (43882176102079/100000000000000 : ℝ)^6255 := by
    have hnat : (2688379587 : ℕ)^8303*100000000000000^6255 ≤ 43882176102079^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688379587 5000000000 43882176102079 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2054333289/10000000000 : ℝ), (2688379621/5000000000 : ℝ), (2688379587/5000000000 : ℝ)] ![(305891176037/2500000000000 : ℝ), (2742636052423/6250000000000 : ℝ), (43882176102079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2054333289/10000000000 : ℝ)|^8303 ≤ (305891176037/2500000000000 : ℝ)^6255
        have hw : |(-2054333289/10000000000 : ℝ)|=(2054333289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688379621/5000000000 : ℝ)|^8303 ≤ (2742636052423/6250000000000 : ℝ)^6255
        have hw : |(2688379621/5000000000 : ℝ)|=(2688379621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688379587/5000000000 : ℝ)|^8303 ≤ (43882176102079/100000000000000 : ℝ)^6255
        have hw : |(2688379587/5000000000 : ℝ)|=(2688379587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_1 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5295675031/10000000000 : ℝ)*x 0 + (-1082107821/5000000000 : ℝ)*x 1 + (2688379643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295675031/10000000000 : ℝ)^8303 ≤ (10751478488543/25000000000000 : ℝ)^6255 := by
    have hnat : (5295675031 : ℕ)^8303*25000000000000^6255 ≤ 10751478488543^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295675031 10000000000 10751478488543 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082107821/5000000000 : ℝ)^8303 ≤ (6555954364621/50000000000000 : ℝ)^6255 := by
    have hnat : (1082107821 : ℕ)^8303*50000000000000^6255 ≤ 6555954364621^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082107821 5000000000 6555954364621 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688379643/5000000000 : ℝ)^8303 ≤ (43882177315449/100000000000000 : ℝ)^6255 := by
    have hnat : (2688379643 : ℕ)^8303*100000000000000^6255 ≤ 43882177315449^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688379643 5000000000 43882177315449 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295675031/10000000000 : ℝ), (-1082107821/5000000000 : ℝ), (2688379643/5000000000 : ℝ)] ![(10751478488543/25000000000000 : ℝ), (6555954364621/50000000000000 : ℝ), (43882177315449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295675031/10000000000 : ℝ)|^8303 ≤ (10751478488543/25000000000000 : ℝ)^6255
        have hw : |(5295675031/10000000000 : ℝ)|=(5295675031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1082107821/5000000000 : ℝ)|^8303 ≤ (6555954364621/50000000000000 : ℝ)^6255
        have hw : |(-1082107821/5000000000 : ℝ)|=(1082107821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688379643/5000000000 : ℝ)|^8303 ≤ (43882177315449/100000000000000 : ℝ)^6255
        have hw : |(2688379643/5000000000 : ℝ)|=(2688379643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_2 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1323918781/2500000000 : ℝ)*x 0 + (2688379557/5000000000 : ℝ)*x 1 + (-2164215747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323918781/2500000000 : ℝ)^8303 ≤ (21502957478351/50000000000000 : ℝ)^6255 := by
    have hnat : (1323918781 : ℕ)^8303*50000000000000^6255 ≤ 21502957478351^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323918781 2500000000 21502957478351 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688379557/5000000000 : ℝ)^8303 ≤ (43882175452059/100000000000000 : ℝ)^6255 := by
    have hnat : (2688379557 : ℕ)^8303*100000000000000^6255 ≤ 43882175452059^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688379557 5000000000 43882175452059 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2164215747/10000000000 : ℝ)^8303 ≤ (1311190957367/10000000000000 : ℝ)^6255 := by
    have hnat : (2164215747 : ℕ)^8303*10000000000000^6255 ≤ 1311190957367^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164215747 10000000000 1311190957367 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323918781/2500000000 : ℝ), (2688379557/5000000000 : ℝ), (-2164215747/10000000000 : ℝ)] ![(21502957478351/50000000000000 : ℝ), (43882175452059/100000000000000 : ℝ), (1311190957367/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323918781/2500000000 : ℝ)|^8303 ≤ (21502957478351/50000000000000 : ℝ)^6255
        have hw : |(1323918781/2500000000 : ℝ)|=(1323918781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688379557/5000000000 : ℝ)|^8303 ≤ (43882175452059/100000000000000 : ℝ)^6255
        have hw : |(2688379557/5000000000 : ℝ)|=(2688379557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2164215747/10000000000 : ℝ)|^8303 ≤ (1311190957367/10000000000000 : ℝ)^6255
        have hw : |(-2164215747/10000000000 : ℝ)|=(2164215747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_3 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1119272601/2500000000 : ℝ)*x 0 + (4317389989/10000000000 : ℝ)*x 1 + (2158695161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119272601/2500000000 : ℝ)^8303 ≤ (3441324329879/10000000000000 : ℝ)^6255 := by
    have hnat : (1119272601 : ℕ)^8303*10000000000000^6255 ≤ 3441324329879^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119272601 2500000000 3441324329879 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4317389989/10000000000 : ℝ)^8303 ≤ (32793376665161/100000000000000 : ℝ)^6255 := by
    have hnat : (4317389989 : ℕ)^8303*100000000000000^6255 ≤ 32793376665161^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317389989 10000000000 32793376665161 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2158695161/5000000000 : ℝ)^8303 ≤ (32793380022667/100000000000000 : ℝ)^6255 := by
    have hnat : (2158695161 : ℕ)^8303*100000000000000^6255 ≤ 32793380022667^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158695161 5000000000 32793380022667 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119272601/2500000000 : ℝ), (4317389989/10000000000 : ℝ), (2158695161/5000000000 : ℝ)] ![(3441324329879/10000000000000 : ℝ), (32793376665161/100000000000000 : ℝ), (32793380022667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119272601/2500000000 : ℝ)|^8303 ≤ (3441324329879/10000000000000 : ℝ)^6255
        have hw : |(1119272601/2500000000 : ℝ)|=(1119272601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4317389989/10000000000 : ℝ)|^8303 ≤ (32793376665161/100000000000000 : ℝ)^6255
        have hw : |(4317389989/10000000000 : ℝ)|=(4317389989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2158695161/5000000000 : ℝ)|^8303 ≤ (32793380022667/100000000000000 : ℝ)^6255
        have hw : |(2158695161/5000000000 : ℝ)|=(2158695161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_4 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2311627463/10000000000 : ℝ)*x 0 + (1056144113/2000000000 : ℝ)*x 1 + (5280720177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2311627463/10000000000 : ℝ)^8303 ≤ (14310442296559/100000000000000 : ℝ)^6255 := by
    have hnat : (2311627463 : ℕ)^8303*100000000000000^6255 ≤ 14310442296559^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2311627463 10000000000 14310442296559 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056144113/2000000000 : ℝ)^8303 ≤ (21422390468143/50000000000000 : ℝ)^6255 := by
    have hnat : (1056144113 : ℕ)^8303*50000000000000^6255 ≤ 21422390468143^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056144113 2000000000 21422390468143 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280720177/10000000000 : ℝ)^8303 ≤ (42844776757557/100000000000000 : ℝ)^6255 := by
    have hnat : (5280720177 : ℕ)^8303*100000000000000^6255 ≤ 42844776757557^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280720177 10000000000 42844776757557 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2311627463/10000000000 : ℝ), (1056144113/2000000000 : ℝ), (5280720177/10000000000 : ℝ)] ![(14310442296559/100000000000000 : ℝ), (21422390468143/50000000000000 : ℝ), (42844776757557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2311627463/10000000000 : ℝ)|^8303 ≤ (14310442296559/100000000000000 : ℝ)^6255
        have hw : |(-2311627463/10000000000 : ℝ)|=(2311627463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056144113/2000000000 : ℝ)|^8303 ≤ (21422390468143/50000000000000 : ℝ)^6255
        have hw : |(1056144113/2000000000 : ℝ)|=(1056144113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280720177/10000000000 : ℝ)|^8303 ≤ (42844776757557/100000000000000 : ℝ)^6255
        have hw : |(5280720177/10000000000 : ℝ)|=(5280720177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_5 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363575603/10000000000 : ℝ)*x 0 + (-550474427/2500000000 : ℝ)*x 1 + (660090039/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363575603/10000000000 : ℝ)^8303 ≤ (43739407108651/100000000000000 : ℝ)^6255 := by
    have hnat : (5363575603 : ℕ)^8303*100000000000000^6255 ≤ 43739407108651^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363575603 10000000000 43739407108651 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550474427/2500000000 : ℝ)^8303 ≤ (13415814667947/100000000000000 : ℝ)^6255 := by
    have hnat : (550474427 : ℕ)^8303*100000000000000^6255 ≤ 13415814667947^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550474427 2500000000 13415814667947 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660090039/1250000000 : ℝ)^8303 ≤ (5355597276437/12500000000000 : ℝ)^6255 := by
    have hnat : (660090039 : ℕ)^8303*12500000000000^6255 ≤ 5355597276437^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660090039 1250000000 5355597276437 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363575603/10000000000 : ℝ), (-550474427/2500000000 : ℝ), (660090039/1250000000 : ℝ)] ![(43739407108651/100000000000000 : ℝ), (13415814667947/100000000000000 : ℝ), (5355597276437/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363575603/10000000000 : ℝ)|^8303 ≤ (43739407108651/100000000000000 : ℝ)^6255
        have hw : |(5363575603/10000000000 : ℝ)|=(5363575603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550474427/2500000000 : ℝ)|^8303 ≤ (13415814667947/100000000000000 : ℝ)^6255
        have hw : |(-550474427/2500000000 : ℝ)|=(550474427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660090039/1250000000 : ℝ)|^8303 ≤ (5355597276437/12500000000000 : ℝ)^6255
        have hw : |(660090039/1250000000 : ℝ)|=(660090039/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_6 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363575381/10000000000 : ℝ)*x 0 + (1320180097/2500000000 : ℝ)*x 1 + (-137618619/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363575381/10000000000 : ℝ)^8303 ≤ (4373940470551/10000000000000 : ℝ)^6255 := by
    have hnat : (5363575381 : ℕ)^8303*10000000000000^6255 ≤ 4373940470551^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363575381 10000000000 4373940470551 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320180097/2500000000 : ℝ)^8303 ≤ (4284477903001/10000000000000 : ℝ)^6255 := by
    have hnat : (1320180097 : ℕ)^8303*10000000000000^6255 ≤ 4284477903001^6255*2500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320180097 2500000000 4284477903001 10000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137618619/625000000 : ℝ)^8303 ≤ (6707908126573/50000000000000 : ℝ)^6255 := by
    have hnat : (137618619 : ℕ)^8303*50000000000000^6255 ≤ 6707908126573^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137618619 625000000 6707908126573 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363575381/10000000000 : ℝ), (1320180097/2500000000 : ℝ), (-137618619/625000000 : ℝ)] ![(4373940470551/10000000000000 : ℝ), (4284477903001/10000000000000 : ℝ), (6707908126573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363575381/10000000000 : ℝ)|^8303 ≤ (4373940470551/10000000000000 : ℝ)^6255
        have hw : |(5363575381/10000000000 : ℝ)|=(5363575381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320180097/2500000000 : ℝ)|^8303 ≤ (4284477903001/10000000000000 : ℝ)^6255
        have hw : |(1320180097/2500000000 : ℝ)|=(1320180097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137618619/625000000 : ℝ)|^8303 ≤ (6707908126573/50000000000000 : ℝ)^6255
        have hw : |(-137618619/625000000 : ℝ)|=(137618619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_7 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4260968373/10000000000 : ℝ)*x 0 + (4425430059/10000000000 : ℝ)*x 1 + (4425430097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4260968373/10000000000 : ℝ)^8303 ≤ (32225720677191/100000000000000 : ℝ)^6255 := by
    have hnat : (4260968373 : ℕ)^8303*100000000000000^6255 ≤ 32225720677191^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4260968373 10000000000 32225720677191 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4425430059/10000000000 : ℝ)^8303 ≤ (33887139462989/100000000000000 : ℝ)^6255 := by
    have hnat : (4425430059 : ℕ)^8303*100000000000000^6255 ≤ 33887139462989^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425430059 10000000000 33887139462989 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4425430097/10000000000 : ℝ)^8303 ≤ (33887139849241/100000000000000 : ℝ)^6255 := by
    have hnat : (4425430097 : ℕ)^8303*100000000000000^6255 ≤ 33887139849241^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4425430097 10000000000 33887139849241 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4260968373/10000000000 : ℝ), (4425430059/10000000000 : ℝ), (4425430097/10000000000 : ℝ)] ![(32225720677191/100000000000000 : ℝ), (33887139462989/100000000000000 : ℝ), (33887139849241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4260968373/10000000000 : ℝ)|^8303 ≤ (32225720677191/100000000000000 : ℝ)^6255
        have hw : |(4260968373/10000000000 : ℝ)|=(4260968373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4425430059/10000000000 : ℝ)|^8303 ≤ (33887139462989/100000000000000 : ℝ)^6255
        have hw : |(4425430059/10000000000 : ℝ)|=(4425430059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4425430097/10000000000 : ℝ)|^8303 ≤ (33887139849241/100000000000000 : ℝ)^6255
        have hw : |(4425430097/10000000000 : ℝ)|=(4425430097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_8 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1128930583/5000000000 : ℝ)*x 0 + (1043093307/2000000000 : ℝ)*x 1 + (5386364591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128930583/5000000000 : ℝ)^8303 ≤ (2774061137593/20000000000000 : ℝ)^6255 := by
    have hnat : (1128930583 : ℕ)^8303*20000000000000^6255 ≤ 2774061137593^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128930583 5000000000 2774061137593 20000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043093307/2000000000 : ℝ)^8303 ≤ (42143425930363/100000000000000 : ℝ)^6255 := by
    have hnat : (1043093307 : ℕ)^8303*100000000000000^6255 ≤ 42143425930363^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043093307 2000000000 42143425930363 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386364591/10000000000 : ℝ)^8303 ≤ (343642721627/781250000000 : ℝ)^6255 := by
    have hnat : (5386364591 : ℕ)^8303*781250000000^6255 ≤ 343642721627^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386364591 10000000000 343642721627 781250000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1128930583/5000000000 : ℝ), (1043093307/2000000000 : ℝ), (5386364591/10000000000 : ℝ)] ![(2774061137593/20000000000000 : ℝ), (42143425930363/100000000000000 : ℝ), (343642721627/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1128930583/5000000000 : ℝ)|^8303 ≤ (2774061137593/20000000000000 : ℝ)^6255
        have hw : |(-1128930583/5000000000 : ℝ)|=(1128930583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043093307/2000000000 : ℝ)|^8303 ≤ (42143425930363/100000000000000 : ℝ)^6255
        have hw : |(1043093307/2000000000 : ℝ)|=(1043093307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5386364591/10000000000 : ℝ)|^8303 ≤ (343642721627/781250000000 : ℝ)^6255
        have hw : |(5386364591/10000000000 : ℝ)|=(5386364591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_9 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528888047/1000000000 : ℝ)*x 0 + (-135023567/625000000 : ℝ)*x 1 + (67329557/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528888047/1000000000 : ℝ)^8303 ≤ (10733171170257/25000000000000 : ℝ)^6255 := by
    have hnat : (528888047 : ℕ)^8303*25000000000000^6255 ≤ 10733171170257^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528888047 1000000000 10733171170257 25000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135023567/625000000 : ℝ)^8303 ≤ (13081047273859/100000000000000 : ℝ)^6255 := by
    have hnat : (135023567 : ℕ)^8303*100000000000000^6255 ≤ 13081047273859^6255*625000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135023567 625000000 13081047273859 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67329557/125000000 : ℝ)^8303 ≤ (5498283504027/12500000000000 : ℝ)^6255 := by
    have hnat : (67329557 : ℕ)^8303*12500000000000^6255 ≤ 5498283504027^6255*125000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67329557 125000000 5498283504027 12500000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528888047/1000000000 : ℝ), (-135023567/625000000 : ℝ), (67329557/125000000 : ℝ)] ![(10733171170257/25000000000000 : ℝ), (13081047273859/100000000000000 : ℝ), (5498283504027/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528888047/1000000000 : ℝ)|^8303 ≤ (10733171170257/25000000000000 : ℝ)^6255
        have hw : |(528888047/1000000000 : ℝ)|=(528888047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-135023567/625000000 : ℝ)|^8303 ≤ (13081047273859/100000000000000 : ℝ)^6255
        have hw : |(-135023567/625000000 : ℝ)|=(135023567/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67329557/125000000 : ℝ)|^8303 ≤ (5498283504027/12500000000000 : ℝ)^6255
        have hw : |(67329557/125000000 : ℝ)|=(67329557/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_10 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288880573/10000000000 : ℝ)*x 0 + (5386364569/10000000000 : ℝ)*x 1 + (-2160376921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288880573/10000000000 : ℝ)^8303 ≤ (42932685790891/100000000000000 : ℝ)^6255 := by
    have hnat : (5288880573 : ℕ)^8303*100000000000000^6255 ≤ 42932685790891^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288880573 10000000000 42932685790891 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5386364569/10000000000 : ℝ)^8303 ≤ (2749141758111/6250000000000 : ℝ)^6255 := by
    have hnat : (5386364569 : ℕ)^8303*6250000000000^6255 ≤ 2749141758111^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386364569 10000000000 2749141758111 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160376921/10000000000 : ℝ)^8303 ≤ (13081046060197/100000000000000 : ℝ)^6255 := by
    have hnat : (2160376921 : ℕ)^8303*100000000000000^6255 ≤ 13081046060197^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160376921 10000000000 13081046060197 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288880573/10000000000 : ℝ), (5386364569/10000000000 : ℝ), (-2160376921/10000000000 : ℝ)] ![(42932685790891/100000000000000 : ℝ), (2749141758111/6250000000000 : ℝ), (13081046060197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288880573/10000000000 : ℝ)|^8303 ≤ (42932685790891/100000000000000 : ℝ)^6255
        have hw : |(5288880573/10000000000 : ℝ)|=(5288880573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5386364569/10000000000 : ℝ)|^8303 ≤ (2749141758111/6250000000000 : ℝ)^6255
        have hw : |(5386364569/10000000000 : ℝ)|=(5386364569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2160376921/10000000000 : ℝ)|^8303 ≤ (13081046060197/100000000000000 : ℝ)^6255
        have hw : |(-2160376921/10000000000 : ℝ)|=(2160376921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_11 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (562304119/1250000000 : ℝ)*x 0 + (861315663/2000000000 : ℝ)*x 1 + (538322301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (562304119/1250000000 : ℝ)^8303 ≤ (34631175881741/100000000000000 : ℝ)^6255 := by
    have hnat : (562304119 : ℕ)^8303*100000000000000^6255 ≤ 34631175881741^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562304119 1250000000 34631175881741 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861315663/2000000000 : ℝ)^8303 ≤ (32684411585151/100000000000000 : ℝ)^6255 := by
    have hnat : (861315663 : ℕ)^8303*100000000000000^6255 ≤ 32684411585151^6255*2000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861315663 2000000000 32684411585151 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538322301/1250000000 : ℝ)^8303 ≤ (2042775782629/6250000000000 : ℝ)^6255 := by
    have hnat : (538322301 : ℕ)^8303*6250000000000^6255 ≤ 2042775782629^6255*1250000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538322301 1250000000 2042775782629 6250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(562304119/1250000000 : ℝ), (861315663/2000000000 : ℝ), (538322301/1250000000 : ℝ)] ![(34631175881741/100000000000000 : ℝ), (32684411585151/100000000000000 : ℝ), (2042775782629/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(562304119/1250000000 : ℝ)|^8303 ≤ (34631175881741/100000000000000 : ℝ)^6255
        have hw : |(562304119/1250000000 : ℝ)|=(562304119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861315663/2000000000 : ℝ)|^8303 ≤ (32684411585151/100000000000000 : ℝ)^6255
        have hw : |(861315663/2000000000 : ℝ)|=(861315663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538322301/1250000000 : ℝ)|^8303 ≤ (2042775782629/6250000000000 : ℝ)^6255
        have hw : |(538322301/1250000000 : ℝ)|=(538322301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_12 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108439057/10000000000 : ℝ)*x 0 + (2720355897/5000000000 : ℝ)*x 1 + (2636348513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108439057/10000000000 : ℝ)^8303 ≤ (12665247706723/100000000000000 : ℝ)^6255 := by
    have hnat : (2108439057 : ℕ)^8303*100000000000000^6255 ≤ 12665247706723^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108439057 10000000000 12665247706723 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720355897/5000000000 : ℝ)^8303 ≤ (1393011334753/3125000000000 : ℝ)^6255 := by
    have hnat : (2720355897 : ℕ)^8303*3125000000000^6255 ≤ 1393011334753^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720355897 5000000000 1393011334753 3125000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636348513/5000000000 : ℝ)^8303 ≤ (1710335582701/4000000000000 : ℝ)^6255 := by
    have hnat : (2636348513 : ℕ)^8303*4000000000000^6255 ≤ 1710335582701^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636348513 5000000000 1710335582701 4000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108439057/10000000000 : ℝ), (2720355897/5000000000 : ℝ), (2636348513/5000000000 : ℝ)] ![(12665247706723/100000000000000 : ℝ), (1393011334753/3125000000000 : ℝ), (1710335582701/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108439057/10000000000 : ℝ)|^8303 ≤ (12665247706723/100000000000000 : ℝ)^6255
        have hw : |(-2108439057/10000000000 : ℝ)|=(2108439057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720355897/5000000000 : ℝ)|^8303 ≤ (1393011334753/3125000000000 : ℝ)^6255
        have hw : |(2720355897/5000000000 : ℝ)|=(2720355897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636348513/5000000000 : ℝ)|^8303 ≤ (1710335582701/4000000000000 : ℝ)^6255
        have hw : |(2636348513/5000000000 : ℝ)|=(2636348513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_13 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684622803/5000000000 : ℝ)*x 0 + (-220498763/1000000000 : ℝ)*x 1 + (5272697419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684622803/5000000000 : ℝ)^8303 ≤ (43800795271041/100000000000000 : ℝ)^6255 := by
    have hnat : (2684622803 : ℕ)^8303*100000000000000^6255 ≤ 43800795271041^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684622803 5000000000 43800795271041 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (220498763/1000000000 : ℝ)^8303 ≤ (168010136489/1250000000000 : ℝ)^6255 := by
    have hnat : (220498763 : ℕ)^8303*1250000000000^6255 ≤ 168010136489^6255*1000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220498763 1000000000 168010136489 1250000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272697419/10000000000 : ℝ)^8303 ≤ (42758393797997/100000000000000 : ℝ)^6255 := by
    have hnat : (5272697419 : ℕ)^8303*100000000000000^6255 ≤ 42758393797997^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272697419 10000000000 42758393797997 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684622803/5000000000 : ℝ), (-220498763/1000000000 : ℝ), (5272697419/10000000000 : ℝ)] ![(43800795271041/100000000000000 : ℝ), (168010136489/1250000000000 : ℝ), (42758393797997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684622803/5000000000 : ℝ)|^8303 ≤ (43800795271041/100000000000000 : ℝ)^6255
        have hw : |(2684622803/5000000000 : ℝ)|=(2684622803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-220498763/1000000000 : ℝ)|^8303 ≤ (168010136489/1250000000000 : ℝ)^6255
        have hw : |(-220498763/1000000000 : ℝ)|=(220498763/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272697419/10000000000 : ℝ)|^8303 ≤ (42758393797997/100000000000000 : ℝ)^6255
        have hw : |(5272697419/10000000000 : ℝ)|=(5272697419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_14 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (67115573/125000000 : ℝ)*x 0 + (2636348617/5000000000 : ℝ)*x 1 + (-2204987563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67115573/125000000 : ℝ)^8303 ≤ (21900398902479/50000000000000 : ℝ)^6255 := by
    have hnat : (67115573 : ℕ)^8303*50000000000000^6255 ≤ 21900398902479^6255*125000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67115573 125000000 21900398902479 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636348617/5000000000 : ℝ)^8303 ≤ (42758391806553/100000000000000 : ℝ)^6255 := by
    have hnat : (2636348617 : ℕ)^8303*100000000000000^6255 ≤ 42758391806553^6255*5000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636348617 5000000000 42758391806553 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2204987563/10000000000 : ℝ)^8303 ≤ (420025324281/3125000000000 : ℝ)^6255 := by
    have hnat : (2204987563 : ℕ)^8303*3125000000000^6255 ≤ 420025324281^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204987563 10000000000 420025324281 3125000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67115573/125000000 : ℝ), (2636348617/5000000000 : ℝ), (-2204987563/10000000000 : ℝ)] ![(21900398902479/50000000000000 : ℝ), (42758391806553/100000000000000 : ℝ), (420025324281/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67115573/125000000 : ℝ)|^8303 ≤ (21900398902479/50000000000000 : ℝ)^6255
        have hw : |(67115573/125000000 : ℝ)|=(67115573/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636348617/5000000000 : ℝ)|^8303 ≤ (42758391806553/100000000000000 : ℝ)^6255
        have hw : |(2636348617/5000000000 : ℝ)|=(2636348617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2204987563/10000000000 : ℝ)|^8303 ≤ (420025324281/3125000000000 : ℝ)^6255
        have hw : |(-2204987563/10000000000 : ℝ)|=(2204987563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1110_box_15 (p : ℝ) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4242682969/10000000000 : ℝ)*x 0 + (221722519/500000000 : ℝ)*x 1 + (4434451129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4242682969/10000000000 : ℝ)^8303 ≤ (16021138847379/50000000000000 : ℝ)^6255 := by
    have hnat : (4242682969 : ℕ)^8303*50000000000000^6255 ≤ 16021138847379^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4242682969 10000000000 16021138847379 50000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221722519/500000000 : ℝ)^8303 ≤ (33978857335719/100000000000000 : ℝ)^6255 := by
    have hnat : (221722519 : ℕ)^8303*100000000000000^6255 ≤ 33978857335719^6255*500000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221722519 500000000 33978857335719 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4434451129/10000000000 : ℝ)^8303 ≤ (33978864954027/100000000000000 : ℝ)^6255 := by
    have hnat : (4434451129 : ℕ)^8303*100000000000000^6255 ≤ 33978864954027^6255*10000000000^8303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4434451129 10000000000 33978864954027 100000000000000 8303 6255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8303/2048 : ℝ)) 8303 6255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4242682969/10000000000 : ℝ), (221722519/500000000 : ℝ), (4434451129/10000000000 : ℝ)] ![(16021138847379/50000000000000 : ℝ), (33978857335719/100000000000000 : ℝ), (33978864954027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4242682969/10000000000 : ℝ)|^8303 ≤ (16021138847379/50000000000000 : ℝ)^6255
        have hw : |(4242682969/10000000000 : ℝ)|=(4242682969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221722519/500000000 : ℝ)|^8303 ≤ (33978857335719/100000000000000 : ℝ)^6255
        have hw : |(221722519/500000000 : ℝ)|=(221722519/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4434451129/10000000000 : ℝ)|^8303 ≤ (33978864954027/100000000000000 : ℝ)^6255
        have hw : |(4434451129/10000000000 : ℝ)|=(4434451129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1110_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(15557/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29637/50000 : ℝ) ∧ (7971/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (20763/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (707/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14029/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (707/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14029/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (707/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (707/6250 : ℝ) ^ (4151/1024 : ℝ) ≤ (1456539609673227/10000000000000000000 : ℝ) := by
    have hpowers : (707/6250 : ℝ)^4151 ≤ (1456539609673227/10000000000000000000 : ℝ)^1024 := by
      have hnat : (707 : ℕ)^4151*10000000000000000000^1024 ≤ 1456539609673227^1024*6250^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        707 6250 1456539609673227 10000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (707/6250 : ℝ)) (X := (1456539609673227/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14029/100000 : ℝ) ^ (4151/1024 : ℝ) ≤ (8714307380444823/25000000000000000000 : ℝ) := by
    have hpowers : (14029/100000 : ℝ)^4151 ≤ (8714307380444823/25000000000000000000 : ℝ)^1024 := by
      have hnat : (14029 : ℕ)^4151*25000000000000000000^1024 ≤ 8714307380444823^1024*100000^4151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14029 100000 8714307380444823 25000000000000000000 4151 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14029/100000 : ℝ)) (X := (8714307380444823/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001456539609673227/5000000000000000000 : ℝ) ≤ (10000718541525787/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (5001456539609673227/5000000000000000000 : ℝ)^1024 ≤ (10000718541525787/10000000000000000 : ℝ)^4151 := by
      have hnat : (5001456539609673227 : ℕ)^1024*10000000000000000^4151 ≤ 10000718541525787^4151*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001456539609673227 5000000000000000000 10000718541525787 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000718541525787/10000000000000000 : ℝ)) (X := (5001456539609673227/5000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024711312809255781/50000000000000000000 : ℝ) ≤ (10001218967727281/10000000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (50024711312809255781/50000000000000000000 : ℝ)^1024 ≤ (10001218967727281/10000000000000000 : ℝ)^4151 := by
      have hnat : (50024711312809255781 : ℕ)^1024*10000000000000000^4151 ≤ 10001218967727281^4151*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024711312809255781 50000000000000000000 10001218967727281 10000000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001218967727281/10000000000000000 : ℝ)) (X := (50024711312809255781/50000000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508714307380444823/12500000000000000000 : ℝ) ≤ (400068775757151/400000000000000 : ℝ) ^ (4151/1024 : ℝ) := by
    have hpowers : (12508714307380444823/12500000000000000000 : ℝ)^1024 ≤ (400068775757151/400000000000000 : ℝ)^4151 := by
      have hnat : (12508714307380444823 : ℕ)^1024*400000000000000^4151 ≤ 400068775757151^4151*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508714307380444823 12500000000000000000 400068775757151 400000000000000 1024 4151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400068775757151/400000000000000 : ℝ)) (X := (12508714307380444823/12500000000000000000 : ℝ)) (by norm_num) 4151 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1456539609673227/10000000000000000000 : ℝ) ≤ ((27160630634942963023/27170000000000000000 : ℝ)+2*(250213100747/135850000000000 : ℝ)*(707/6250 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (27160630634942963023/27170000000000000000 : ℝ)+2*(250213100747/135850000000000 : ℝ)*(707/6250 : ℝ)=(10000718541525787/10000000000000000 : ℝ) by norm_num, show 1+2*(1456539609673227/10000000000000000000 : ℝ)=(5001456539609673227/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8714307380444823/25000000000000000000 : ℝ)+(1456539609673227/10000000000000000000 : ℝ) ≤ ((27160630634942963023/27170000000000000000 : ℝ)+(250213100747/135850000000000 : ℝ)*((14029/100000 : ℝ)+(707/6250 : ℝ)))^(4151/1024 : ℝ) := by
    rw [show (27160630634942963023/27170000000000000000 : ℝ)+(250213100747/135850000000000 : ℝ)*((14029/100000 : ℝ)+(707/6250 : ℝ))=(10001218967727281/10000000000000000 : ℝ) by norm_num, show 1+(8714307380444823/25000000000000000000 : ℝ)+(1456539609673227/10000000000000000000 : ℝ)=(50024711312809255781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8714307380444823/25000000000000000000 : ℝ) ≤ ((27160630634942963023/27170000000000000000 : ℝ)+2*(250213100747/135850000000000 : ℝ)*(14029/100000 : ℝ))^(4151/1024 : ℝ) := by
    rw [show (27160630634942963023/27170000000000000000 : ℝ)+2*(250213100747/135850000000000 : ℝ)*(14029/100000 : ℝ)=(400068775757151/400000000000000 : ℝ) by norm_num, show 1+2*(8714307380444823/25000000000000000000 : ℝ)=(12508714307380444823/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27160630634942963023/27170000000000000000 : ℝ)*(X 1 0+X 2 0)+(250213100747/135850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27160630634942963023/27170000000000000000 : ℝ)) (alpha := (250213100747/135850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27160630634942963023/27170000000000000000 : ℝ)*(X 0 1+X 2 1)+(250213100747/135850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27160630634942963023/27170000000000000000 : ℝ)) (alpha := (250213100747/135850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27160630634942963023/27170000000000000000 : ℝ)*(X 0 2+X 1 2)+(250213100747/135850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4151/1024 : ℝ)) (lo := (707/6250 : ℝ)) (hi := (14029/100000 : ℝ)) (c := (27160630634942963023/27170000000000000000 : ℝ)) (alpha := (250213100747/135850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2054333289/10000000000 : ℝ)*X 0 0+(2688379621/5000000000 : ℝ)*X 0 1+(2688379587/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295675031/10000000000 : ℝ)*X 1 0+(-1082107821/5000000000 : ℝ)*X 1 1+(2688379643/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323918781/2500000000 : ℝ)*X 2 0+(2688379557/5000000000 : ℝ)*X 2 1+(-2164215747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1119272601/2500000000 : ℝ)*X 0 0+(4317389989/10000000000 : ℝ)*X 0 1+(2158695161/5000000000 : ℝ)*X 0 2+(1119272601/2500000000 : ℝ)*X 1 0+(4317389989/10000000000 : ℝ)*X 1 1+(2158695161/5000000000 : ℝ)*X 1 2+(1119272601/2500000000 : ℝ)*X 2 0+(4317389989/10000000000 : ℝ)*X 2 1+(2158695161/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2311627463/10000000000 : ℝ)*X 0 0+(1056144113/2000000000 : ℝ)*X 0 1+(5280720177/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363575603/10000000000 : ℝ)*X 1 0+(-550474427/2500000000 : ℝ)*X 1 1+(660090039/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5363575381/10000000000 : ℝ)*X 2 0+(1320180097/2500000000 : ℝ)*X 2 1+(-137618619/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4260968373/10000000000 : ℝ)*X 0 0+(4425430059/10000000000 : ℝ)*X 0 1+(4425430097/10000000000 : ℝ)*X 0 2+(4260968373/10000000000 : ℝ)*X 1 0+(4425430059/10000000000 : ℝ)*X 1 1+(4425430097/10000000000 : ℝ)*X 1 2+(4260968373/10000000000 : ℝ)*X 2 0+(4425430059/10000000000 : ℝ)*X 2 1+(4425430097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1128930583/5000000000 : ℝ)*X 0 0+(1043093307/2000000000 : ℝ)*X 0 1+(5386364591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((528888047/1000000000 : ℝ)*X 1 0+(-135023567/625000000 : ℝ)*X 1 1+(67329557/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288880573/10000000000 : ℝ)*X 2 0+(5386364569/10000000000 : ℝ)*X 2 1+(-2160376921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((562304119/1250000000 : ℝ)*X 0 0+(861315663/2000000000 : ℝ)*X 0 1+(538322301/1250000000 : ℝ)*X 0 2+(562304119/1250000000 : ℝ)*X 1 0+(861315663/2000000000 : ℝ)*X 1 1+(538322301/1250000000 : ℝ)*X 1 2+(562304119/1250000000 : ℝ)*X 2 0+(861315663/2000000000 : ℝ)*X 2 1+(538322301/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2108439057/10000000000 : ℝ)*X 0 0+(2720355897/5000000000 : ℝ)*X 0 1+(2636348513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684622803/5000000000 : ℝ)*X 1 0+(-220498763/1000000000 : ℝ)*X 1 1+(5272697419/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((67115573/125000000 : ℝ)*X 2 0+(2636348617/5000000000 : ℝ)*X 2 1+(-2204987563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4242682969/10000000000 : ℝ)*X 0 0+(221722519/500000000 : ℝ)*X 0 1+(4434451129/10000000000 : ℝ)*X 0 2+(4242682969/10000000000 : ℝ)*X 1 0+(221722519/500000000 : ℝ)*X 1 1+(4434451129/10000000000 : ℝ)*X 1 2+(4242682969/10000000000 : ℝ)*X 2 0+(221722519/500000000 : ℝ)*X 2 1+(4434451129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1110_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15557/25000 : ℝ) ≤ (-422664612446659235429142841239069/679250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21391047/100000000000000 : ℝ)*(upper0) + (122071649/100000000000000 : ℝ)*(upper3) + (49664803/50000000000000 : ℝ)*(lower4) + (973469253009543/25000000000000 : ℝ)*(major0) + (973469253009543/25000000000000 : ℝ)*(major1) + (1946938506019087/50000000000000 : ℝ)*(major2) + (1611359251/20000000000000 : ℝ)*(sp1) + (5708642587/100000000000000 : ℝ)*(sp2) + (1006384227/10000000000000 : ℝ)*(sp3) + (5192514850236729/100000000000000 : ℝ)*(sp4) + (2596254599054483/50000000000000 : ℝ)*(sp5) + (2596255773131317/50000000000000 : ℝ)*(sp6) + (1307984217894373/50000000000000 : ℝ)*(sp7) + (2404668493/100000000000000 : ℝ)*(sp8) + (326997312453877/12500000000000 : ℝ)*(f.failure) + (5192517254905221/100000000000000 : ℝ)*(f.sum) + (35155048962743/13585000000000000000000000000 : ℝ)*base66 + (1323836498292971511/679250000000000000000000000000000 : ℝ)*base68 + (831743649688620001/1358500000000000000000000000000000 : ℝ)*base69 + (2630922746010221511/679250000000000000000000000000000 : ℝ)*base72 + (37206447414369/1698125000000000000000000000 : ℝ)*base73 + (19332504528717620001/1358500000000000000000000000000000 : ℝ)*base75 + (456908832242359347/52250000000000000000000000000000 : ℝ)*base78 + (845720541941140653/52250000000000000000000000000000 : ℝ)*base79 + (81174554038077/13585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (16264841/1250000000000000000000 : ℝ)*base89 + (16264841/1250000000000000000000 : ℝ)*base91 + (8735159/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29637/50000 : ℝ) ≤ (201317763384358049066234078493477/339625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36938093/100000000000000 : ℝ)*(upper0) + (70987199/100000000000000 : ℝ)*(upper2) + (524869/50000000000000 : ℝ)*(upper3) + (19635247/100000000000000 : ℝ)*(upper4) + (6722879/12500000000000 : ℝ)*(upper5) + (989374743459389/25000000000000 : ℝ)*(major0) + (989374743459389/25000000000000 : ℝ)*(major1) + (989374743459389/25000000000000 : ℝ)*(major2) + (5236518210508617/100000000000000 : ℝ)*(sp0) + (1309128053254981/25000000000000 : ℝ)*(sp1) + (2618215446535451/50000000000000 : ℝ)*(sp2) + (265872090871507/10000000000000 : ℝ)*(sp3) + (5997488693/100000000000000 : ℝ)*(sp5) + (21829359429/25000000000000 : ℝ)*(sp10) + (265872090871507/10000000000000 : ℝ)*(f.failure) + (5236518210508617/100000000000000 : ℝ)*(f.sum) + (138047198811969/13585000000000000000000000000 : ℝ)*base65 + (243953751202597919/52250000000000000000000000000000 : ℝ)*base67 + (265076735706097919/52250000000000000000000000000000 : ℝ)*base69 + (1197858997669847919/52250000000000000000000000000000 : ℝ)*base71 + (34749705160733/6792500000000000000000000000 : ℝ)*base74 + (321264080331597919/52250000000000000000000000000000 : ℝ)*base75 + (32471936185597919/52250000000000000000000000000000 : ℝ)*base77 + (80515912237097919/52250000000000000000000000000000 : ℝ)*base79 + (11059329643657/6792500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5742369/1000000000000000000000 : ℝ)*base90 + (5742369/1000000000000000000000 : ℝ)*base92 + (5742369/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7971/10000 : ℝ) ≤ (541445251066203145415215268826087/679250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3470827/12500000000000 : ℝ)*(lower1) + (39089977/50000000000000 : ℝ)*(lower3) + (78079221/100000000000000 : ℝ)*(upper4) + (4425614598595047/100000000000000 : ℝ)*(major0) + (4425614598595047/100000000000000 : ℝ)*(major1) + (553201824824381/12500000000000 : ℝ)*(major2) + (1538365953/50000000000000 : ℝ)*(sp0) + (18338453827/50000000000000 : ℝ)*(sp1) + (12577622121/20000000000000 : ℝ)*(sp2) + (75109664699/100000000000000 : ℝ)*(sp3) + (5851445748731673/100000000000000 : ℝ)*(sp8) + (1462853037138981/25000000000000 : ℝ)*(sp9) + (5851385937352973/100000000000000 : ℝ)*(sp10) + (59462690444459/2000000000000 : ℝ)*(sp11) + (92912800996489/3125000000000 : ℝ)*(f.failure) + (5851448825463579/100000000000000 : ℝ)*(f.sum) + (65298780351/543400000000000000000000000 : ℝ)*base66 + (30886571588112852919/2717000000000000000000000000000000 : ℝ)*base68 + (7290832007803963763/339625000000000000000000000000000 : ℝ)*base69 + (4423052671706852919/2717000000000000000000000000000000 : ℝ)*base72 + (2589005180139/339625000000000000000000000 : ℝ)*base74 + (5086926556860338763/339625000000000000000000000000000 : ℝ)*base75 + (173316634561337433/19000000000000000000000000000000 : ℝ)*base78 + (123619566198337433/19000000000000000000000000000000 : ℝ)*base80 + (203634330161/5937500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (287563/312500000000000000000 : ℝ)*base90 + (287563/312500000000000000000 : ℝ)*base92 + (3412563/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-20763/25000 : ℝ) ≤ (-141029091659216594637021437999511/169812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120122681/50000000000000 : ℝ)*(lower1) + (42282693/50000000000000 : ℝ)*(lower2) + (832079/10000000000000 : ℝ)*(lower3) + (5695293/12500000000000 : ℝ)*(upper5) + (557546723433819/12500000000000 : ℝ)*(major0) + (557546723433819/12500000000000 : ℝ)*(major1) + (557546723433819/12500000000000 : ℝ)*(major2) + (2472711701/100000000000000 : ℝ)*(sp4) + (48239795791/50000000000000 : ℝ)*(sp6) + (5461816841/100000000000000 : ℝ)*(sp7) + (1487966725335873/25000000000000 : ℝ)*(sp12) + (743983671756899/12500000000000 : ℝ)*(sp13) + (595177289446361/10000000000000 : ℝ)*(sp14) + (599311207037337/20000000000000 : ℝ)*(sp15) + (1498280748501763/50000000000000 : ℝ)*(f.failure) + (743983671756899/12500000000000 : ℝ)*(f.sum) + (57705865218853/13585000000000000000000000000 : ℝ)*base65 + (144847071822713449/26125000000000000000000000000000 : ℝ)*base67 + (328178374478661551/26125000000000000000000000000000 : ℝ)*base70 + (214963066422463449/26125000000000000000000000000000 : ℝ)*base71 + (45485979646673/13585000000000000000000000000 : ℝ)*base73 + (311834667980036551/26125000000000000000000000000000 : ℝ)*base76 + (81034853033713449/26125000000000000000000000000000 : ℝ)*base77 + (113892791299338449/26125000000000000000000000000000 : ℝ)*base79 + (56513874617/53066406250000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (27420721/5000000000000000000000 : ℝ)*base90 + (27420721/5000000000000000000000 : ℝ)*base92 + (27420721/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1110_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14029/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29637/50000 : ℝ) else (7971/10000 : ℝ) ≤ X j i ∧ X j i ≤ (20763/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1110_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1110_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29637/50000 : ℝ) else (7971/10000 : ℝ) ≤ X j i ∧ X j i ≤ (20763/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1110_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1110_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4151/1024 : ℝ) ≤ p) (hpb : p ≤ (8303/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148849733/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1403/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (707/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15557/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29637/50000 : ℝ) else (7971/10000 : ℝ) ≤ X j i ∧ X j i ≤ (20763/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1110_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
