-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1737_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:08:05.145994+00:00
-- url     : https://prove2.me/submissions/a6cf28c5-08ac-4efa-afc2-1ecd267faf3e

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
theorem support_rectangle_w1737_s0_0 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-621108801/5000000000 : ℝ)*x 0 + (709102947/1250000000 : ℝ)*x 1 + (4956610943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621108801/5000000000 : ℝ)^5567 ≤ (3881488330127/50000000000000 : ℝ)^4543 := by
    have hnat : (621108801 : ℕ)^5567*50000000000000^4543 ≤ 3881488330127^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621108801 5000000000 3881488330127 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (709102947/1250000000 : ℝ)^5567 ≤ (9984704293013/20000000000000 : ℝ)^4543 := by
    have hnat : (709102947 : ℕ)^5567*20000000000000^4543 ≤ 9984704293013^4543*1250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709102947 1250000000 9984704293013 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4956610943/10000000000 : ℝ)^5567 ≤ (1692540074533/4000000000000 : ℝ)^4543 := by
    have hnat : (4956610943 : ℕ)^5567*4000000000000^4543 ≤ 1692540074533^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4956610943 10000000000 1692540074533 4000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-621108801/5000000000 : ℝ), (709102947/1250000000 : ℝ), (4956610943/10000000000 : ℝ)] ![(3881488330127/50000000000000 : ℝ), (9984704293013/20000000000000 : ℝ), (1692540074533/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-621108801/5000000000 : ℝ)|^5567 ≤ (3881488330127/50000000000000 : ℝ)^4543
        have hw : |(-621108801/5000000000 : ℝ)|=(621108801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(709102947/1250000000 : ℝ)|^5567 ≤ (9984704293013/20000000000000 : ℝ)^4543
        have hw : |(709102947/1250000000 : ℝ)|=(709102947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4956610943/10000000000 : ℝ)|^5567 ≤ (1692540074533/4000000000000 : ℝ)^4543
        have hw : |(4956610943/10000000000 : ℝ)|=(4956610943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s0_1 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387533967/10000000000 : ℝ)*x 0 + (-1629051383/10000000000 : ℝ)*x 1 + (2478305591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387533967/10000000000 : ℝ)^5567 ≤ (23432297643807/50000000000000 : ℝ)^4543 := by
    have hnat : (5387533967 : ℕ)^5567*50000000000000^4543 ≤ 23432297643807^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387533967 10000000000 23432297643807 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1629051383/10000000000 : ℝ)^5567 ≤ (169092192719/1562500000000 : ℝ)^4543 := by
    have hnat : (1629051383 : ℕ)^5567*1562500000000^4543 ≤ 169092192719^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629051383 10000000000 169092192719 1562500000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2478305591/5000000000 : ℝ)^5567 ≤ (42313504363501/100000000000000 : ℝ)^4543 := by
    have hnat : (2478305591 : ℕ)^5567*100000000000000^4543 ≤ 42313504363501^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478305591 5000000000 42313504363501 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387533967/10000000000 : ℝ), (-1629051383/10000000000 : ℝ), (2478305591/5000000000 : ℝ)] ![(23432297643807/50000000000000 : ℝ), (169092192719/1562500000000 : ℝ), (42313504363501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387533967/10000000000 : ℝ)|^5567 ≤ (23432297643807/50000000000000 : ℝ)^4543
        have hw : |(5387533967/10000000000 : ℝ)|=(5387533967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1629051383/10000000000 : ℝ)|^5567 ≤ (169092192719/1562500000000 : ℝ)^4543
        have hw : |(-1629051383/10000000000 : ℝ)|=(1629051383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2478305591/5000000000 : ℝ)|^5567 ≤ (42313504363501/100000000000000 : ℝ)^4543
        have hw : |(2478305591/5000000000 : ℝ)|=(2478305591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s0_2 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346883333/2500000000 : ℝ)*x 0 + (4956611717/10000000000 : ℝ)*x 1 + (-203631441/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346883333/2500000000 : ℝ)^5567 ≤ (23432294259443/50000000000000 : ℝ)^4543 := by
    have hnat : (1346883333 : ℕ)^5567*50000000000000^4543 ≤ 23432294259443^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346883333 2500000000 23432294259443 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4956611717/10000000000 : ℝ)^5567 ≤ (42313509960129/100000000000000 : ℝ)^4543 := by
    have hnat : (4956611717 : ℕ)^5567*100000000000000^4543 ≤ 42313509960129^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4956611717 10000000000 42313509960129 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203631441/1250000000 : ℝ)^5567 ≤ (5410950757189/50000000000000 : ℝ)^4543 := by
    have hnat : (203631441 : ℕ)^5567*50000000000000^4543 ≤ 5410950757189^4543*1250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203631441 1250000000 5410950757189 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346883333/2500000000 : ℝ), (4956611717/10000000000 : ℝ), (-203631441/1250000000 : ℝ)] ![(23432294259443/50000000000000 : ℝ), (42313509960129/100000000000000 : ℝ), (5410950757189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346883333/2500000000 : ℝ)|^5567 ≤ (23432294259443/50000000000000 : ℝ)^4543
        have hw : |(1346883333/2500000000 : ℝ)|=(1346883333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4956611717/10000000000 : ℝ)|^5567 ≤ (42313509960129/100000000000000 : ℝ)^4543
        have hw : |(4956611717/10000000000 : ℝ)|=(4956611717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203631441/1250000000 : ℝ)|^5567 ≤ (5410950757189/50000000000000 : ℝ)^4543
        have hw : |(-203631441/1250000000 : ℝ)|=(203631441/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s0_3 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1998560643/5000000000 : ℝ)*x 0 + (594436567/2000000000 : ℝ)*x 1 + (1300211567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998560643/5000000000 : ℝ)^5567 ≤ (16253634683943/50000000000000 : ℝ)^4543 := by
    have hnat : (1998560643 : ℕ)^5567*50000000000000^4543 ≤ 16253634683943^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998560643 5000000000 16253634683943 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (594436567/2000000000 : ℝ)^5567 ≤ (4522054948727/20000000000000 : ℝ)^4543 := by
    have hnat : (594436567 : ℕ)^5567*20000000000000^4543 ≤ 4522054948727^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594436567 2000000000 4522054948727 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1300211567/2500000000 : ℝ)^5567 ≤ (22441227933161/50000000000000 : ℝ)^4543 := by
    have hnat : (1300211567 : ℕ)^5567*50000000000000^4543 ≤ 22441227933161^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300211567 2500000000 22441227933161 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1998560643/5000000000 : ℝ), (594436567/2000000000 : ℝ), (1300211567/2500000000 : ℝ)] ![(16253634683943/50000000000000 : ℝ), (4522054948727/20000000000000 : ℝ), (22441227933161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1998560643/5000000000 : ℝ)|^5567 ≤ (16253634683943/50000000000000 : ℝ)^4543
        have hw : |(1998560643/5000000000 : ℝ)|=(1998560643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(594436567/2000000000 : ℝ)|^5567 ≤ (4522054948727/20000000000000 : ℝ)^4543
        have hw : |(594436567/2000000000 : ℝ)|=(594436567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1300211567/2500000000 : ℝ)|^5567 ≤ (22441227933161/50000000000000 : ℝ)^4543
        have hw : |(1300211567/2500000000 : ℝ)|=(1300211567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s0_4 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-621944639/5000000000 : ℝ)*x 0 + (4975240049/10000000000 : ℝ)*x 1 + (5653550373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621944639/5000000000 : ℝ)^5567 ≤ (7775780110919/100000000000000 : ℝ)^4543 := by
    have hnat : (621944639 : ℕ)^5567*100000000000000^4543 ≤ 7775780110919^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621944639 5000000000 7775780110919 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4975240049/10000000000 : ℝ)^5567 ≤ (42508463147549/100000000000000 : ℝ)^4543 := by
    have hnat : (4975240049 : ℕ)^5567*100000000000000^4543 ≤ 42508463147549^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4975240049 10000000000 42508463147549 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5653550373/10000000000 : ℝ)^5567 ≤ (12428939181053/25000000000000 : ℝ)^4543 := by
    have hnat : (5653550373 : ℕ)^5567*25000000000000^4543 ≤ 12428939181053^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653550373 10000000000 12428939181053 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-621944639/5000000000 : ℝ), (4975240049/10000000000 : ℝ), (5653550373/10000000000 : ℝ)] ![(7775780110919/100000000000000 : ℝ), (42508463147549/100000000000000 : ℝ), (12428939181053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-621944639/5000000000 : ℝ)|^5567 ≤ (7775780110919/100000000000000 : ℝ)^4543
        have hw : |(-621944639/5000000000 : ℝ)|=(621944639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4975240049/10000000000 : ℝ)|^5567 ≤ (42508463147549/100000000000000 : ℝ)^4543
        have hw : |(4975240049/10000000000 : ℝ)|=(4975240049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5653550373/10000000000 : ℝ)|^5567 ≤ (12428939181053/25000000000000 : ℝ)^4543
        have hw : |(5653550373/10000000000 : ℝ)|=(5653550373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s0_5 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195349577/10000000000 : ℝ)*x 0 + (-58257073/625000000 : ℝ)*x 1 + (1130710127/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195349577/10000000000 : ℝ)^5567 ≤ (22412167595149/50000000000000 : ℝ)^4543 := by
    have hnat : (5195349577 : ℕ)^5567*50000000000000^4543 ≤ 22412167595149^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195349577 10000000000 22412167595149 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58257073/625000000 : ℝ)^5567 ≤ (5459905250633/100000000000000 : ℝ)^4543 := by
    have hnat : (58257073 : ℕ)^5567*100000000000000^4543 ≤ 5459905250633^4543*625000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58257073 625000000 5459905250633 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130710127/2000000000 : ℝ)^5567 ≤ (49715759547483/100000000000000 : ℝ)^4543 := by
    have hnat : (1130710127 : ℕ)^5567*100000000000000^4543 ≤ 49715759547483^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130710127 2000000000 49715759547483 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195349577/10000000000 : ℝ), (-58257073/625000000 : ℝ), (1130710127/2000000000 : ℝ)] ![(22412167595149/50000000000000 : ℝ), (5459905250633/100000000000000 : ℝ), (49715759547483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195349577/10000000000 : ℝ)|^5567 ≤ (22412167595149/50000000000000 : ℝ)^4543
        have hw : |(5195349577/10000000000 : ℝ)|=(5195349577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58257073/625000000 : ℝ)|^5567 ≤ (5459905250633/100000000000000 : ℝ)^4543
        have hw : |(-58257073/625000000 : ℝ)|=(58257073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130710127/2000000000 : ℝ)|^5567 ≤ (49715759547483/100000000000000 : ℝ)^4543
        have hw : |(1130710127/2000000000 : ℝ)|=(1130710127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s0_6 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207814013/400000000 : ℝ)*x 0 + (5653549923/10000000000 : ℝ)*x 1 + (-466056567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207814013/400000000 : ℝ)^5567 ≤ (22412171549263/50000000000000 : ℝ)^4543 := by
    have hnat : (207814013 : ℕ)^5567*50000000000000^4543 ≤ 22412171549263^4543*400000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207814013 400000000 22412171549263 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5653549923/10000000000 : ℝ)^5567 ≤ (24857875937541/50000000000000 : ℝ)^4543 := by
    have hnat : (5653549923 : ℕ)^5567*50000000000000^4543 ≤ 24857875937541^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5653549923 10000000000 24857875937541 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466056567/5000000000 : ℝ)^5567 ≤ (2729952503293/50000000000000 : ℝ)^4543 := by
    have hnat : (466056567 : ℕ)^5567*50000000000000^4543 ≤ 2729952503293^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466056567 5000000000 2729952503293 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207814013/400000000 : ℝ), (5653549923/10000000000 : ℝ), (-466056567/5000000000 : ℝ)] ![(22412171549263/50000000000000 : ℝ), (24857875937541/50000000000000 : ℝ), (2729952503293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207814013/400000000 : ℝ)|^5567 ≤ (22412171549263/50000000000000 : ℝ)^4543
        have hw : |(207814013/400000000 : ℝ)|=(207814013/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5653549923/10000000000 : ℝ)|^5567 ≤ (24857875937541/50000000000000 : ℝ)^4543
        have hw : |(5653549923/10000000000 : ℝ)|=(5653549923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-466056567/5000000000 : ℝ)|^5567 ≤ (2729952503293/50000000000000 : ℝ)^4543
        have hw : |(-466056567/5000000000 : ℝ)|=(466056567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s0_7 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4002326729/10000000000 : ℝ)*x 0 + (2571439601/5000000000 : ℝ)*x 1 + (3032157309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4002326729/10000000000 : ℝ)^5567 ≤ (32559153321063/100000000000000 : ℝ)^4543 := by
    have hnat : (4002326729 : ℕ)^5567*100000000000000^4543 ≤ 32559153321063^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002326729 10000000000 32559153321063 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571439601/5000000000 : ℝ)^5567 ≤ (8854045077441/20000000000000 : ℝ)^4543 := by
    have hnat : (2571439601 : ℕ)^5567*20000000000000^4543 ≤ 8854045077441^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571439601 5000000000 8854045077441 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3032157309/10000000000 : ℝ)^5567 ≤ (2896327659509/12500000000000 : ℝ)^4543 := by
    have hnat : (3032157309 : ℕ)^5567*12500000000000^4543 ≤ 2896327659509^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3032157309 10000000000 2896327659509 12500000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4002326729/10000000000 : ℝ), (2571439601/5000000000 : ℝ), (3032157309/10000000000 : ℝ)] ![(32559153321063/100000000000000 : ℝ), (8854045077441/20000000000000 : ℝ), (2896327659509/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4002326729/10000000000 : ℝ)|^5567 ≤ (32559153321063/100000000000000 : ℝ)^4543
        have hw : |(4002326729/10000000000 : ℝ)|=(4002326729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571439601/5000000000 : ℝ)|^5567 ≤ (8854045077441/20000000000000 : ℝ)^4543
        have hw : |(2571439601/5000000000 : ℝ)|=(2571439601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3032157309/10000000000 : ℝ)|^5567 ≤ (2896327659509/12500000000000 : ℝ)^4543
        have hw : |(3032157309/10000000000 : ℝ)|=(3032157309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1737_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1231/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (21587/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (5551/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5551 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5551*1^1024 ≤ 0^1024*1^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5551/1024 : ℝ) ≤ (348159005472082349/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5551 ≤ (348159005472082349/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5551*50000000000000000000^1024 ≤ 348159005472082349^1024*5^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 348159005472082349 50000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (348159005472082349/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5551 := by
      have hnat : (1 : ℕ)^1024*1^5551 ≤ 1^5551*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50348159005472082349/50000000000000000000 : ℝ) ≤ (5006404374001401/5000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (50348159005472082349/50000000000000000000 : ℝ)^1024 ≤ (5006404374001401/5000000000000000 : ℝ)^5551 := by
      have hnat : (50348159005472082349 : ℕ)^1024*5000000000000000^5551 ≤ 5006404374001401^5551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50348159005472082349 50000000000000000000 5006404374001401 5000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006404374001401/5000000000000000 : ℝ)) (X := (50348159005472082349/50000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25348159005472082349/25000000000000000000 : ℝ) ≤ (2506404374001401/2500000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (25348159005472082349/25000000000000000000 : ℝ)^1024 ≤ (2506404374001401/2500000000000000 : ℝ)^5551 := by
      have hnat : (25348159005472082349 : ℕ)^1024*2500000000000000^5551 ≤ 2506404374001401^5551*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25348159005472082349 25000000000000000000 2506404374001401 2500000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506404374001401/2500000000000000 : ℝ)) (X := (25348159005472082349/25000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6404374001401/2000000000000000 : ℝ)*(0 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6404374001401/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(348159005472082349/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6404374001401/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5551/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6404374001401/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5006404374001401/5000000000000000 : ℝ) by norm_num, show 1+(348159005472082349/50000000000000000000 : ℝ)+(0 : ℝ)=(50348159005472082349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(348159005472082349/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6404374001401/2000000000000000 : ℝ)*(2/5 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6404374001401/2000000000000000 : ℝ)*(2/5 : ℝ)=(2506404374001401/2500000000000000 : ℝ) by norm_num, show 1+2*(348159005472082349/50000000000000000000 : ℝ)=(25348159005472082349/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6404374001401/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6404374001401/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6404374001401/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6404374001401/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6404374001401/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6404374001401/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-621108801/5000000000 : ℝ)*X 0 0+(709102947/1250000000 : ℝ)*X 0 1+(4956610943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5387533967/10000000000 : ℝ)*X 1 0+(-1629051383/10000000000 : ℝ)*X 1 1+(2478305591/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1346883333/2500000000 : ℝ)*X 2 0+(4956611717/10000000000 : ℝ)*X 2 1+(-203631441/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1998560643/5000000000 : ℝ)*X 0 0+(594436567/2000000000 : ℝ)*X 0 1+(1300211567/2500000000 : ℝ)*X 0 2+(1998560643/5000000000 : ℝ)*X 1 0+(594436567/2000000000 : ℝ)*X 1 1+(1300211567/2500000000 : ℝ)*X 1 2+(1998560643/5000000000 : ℝ)*X 2 0+(594436567/2000000000 : ℝ)*X 2 1+(1300211567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-621944639/5000000000 : ℝ)*X 0 0+(4975240049/10000000000 : ℝ)*X 0 1+(5653550373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195349577/10000000000 : ℝ)*X 1 0+(-58257073/625000000 : ℝ)*X 1 1+(1130710127/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((207814013/400000000 : ℝ)*X 2 0+(5653549923/10000000000 : ℝ)*X 2 1+(-466056567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4002326729/10000000000 : ℝ)*X 0 0+(2571439601/5000000000 : ℝ)*X 0 1+(3032157309/10000000000 : ℝ)*X 0 2+(4002326729/10000000000 : ℝ)*X 1 0+(2571439601/5000000000 : ℝ)*X 1 1+(3032157309/10000000000 : ℝ)*X 1 2+(4002326729/10000000000 : ℝ)*X 2 0+(2571439601/5000000000 : ℝ)*X 2 1+(3032157309/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (326888075065508133739509/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52068361/100000000000000 : ℝ)*(base1) + (344817873/25000000000000 : ℝ)*(base19) + (242940693/20000000000000 : ℝ)*(base23) + (270136313/100000000000000 : ℝ)*(upper3) + (35576109/20000000000000 : ℝ)*(upper5) + (461237511572303/50000000000000 : ℝ)*(major0) + (461237511572303/50000000000000 : ℝ)*(major1) + (461237511572303/50000000000000 : ℝ)*(major2) + (174530057171477/12500000000000 : ℝ)*(sp0) + (698122619784973/50000000000000 : ℝ)*(sp1) + (698122702068987/50000000000000 : ℝ)*(sp2) + (448701136130473/100000000000000 : ℝ)*(sp3) + (97086531/1562500000000 : ℝ)*(sp4) + (2021323549/100000000000000 : ℝ)*(sp7) + (28043950595149/6250000000000 : ℝ)*(f.failure) + (698123309420719/50000000000000 : ℝ)*(f.sum) + (140999599046503/50000000000000000000000000000 : ℝ)*base65 + (811614373703497/100000000000000000000000000000 : ℝ)*base68 + (321347457703497/100000000000000000000000000000 : ℝ)*base70 + (353332506696503/100000000000000000000000000000 : ℝ)*base71 + (148764141953497/50000000000000000000000000000 : ℝ)*base74 + (112996022903497/100000000000000000000000000000 : ℝ)*base76 + (557126851903497/100000000000000000000000000000 : ℝ)*base78 + (554692986303497/100000000000000000000000000000 : ℝ)*base80 + (82718528146503/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1043249/625000000000000000000 : ℝ)*base89 + (1043249/625000000000000000000 : ℝ)*base91 + (1043249/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (54109973244621219273777/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (554977483/100000000000000 : ℝ)*(base19) + (161328849/20000000000000 : ℝ)*(base23) + (490074429/100000000000000 : ℝ)*(base32) + (2926507/10000000000000 : ℝ)*(base37) + (19269987/10000000000000 : ℝ)*(upper3) + (121751284310447/12500000000000 : ℝ)*(major0) + (121751284310447/12500000000000 : ℝ)*(major1) + (121751284310447/12500000000000 : ℝ)*(major2) + (156296977/12500000000000 : ℝ)*(sp1) + (578955153/25000000000000 : ℝ)*(sp2) + (737124835031459/50000000000000 : ℝ)*(sp4) + (1474247864709619/100000000000000 : ℝ)*(sp5) + (737123273799031/50000000000000 : ℝ)*(sp6) + (236885035489103/50000000000000 : ℝ)*(sp7) + (94754118063541/20000000000000 : ℝ)*(f.failure) + (737124835031459/50000000000000 : ℝ)*(f.sum) + (11186059811247/12500000000000000000000000000 : ℝ)*base65 + (122842632086247/25000000000000000000000000000 : ℝ)*base67 + (180870095236247/25000000000000000000000000000 : ℝ)*base69 + (169117211711247/25000000000000000000000000000 : ℝ)*base71 + (23970058286247/12500000000000000000000000000 : ℝ)*base73 + (58778491161247/25000000000000000000000000000 : ℝ)*base75 + (45395059236247/25000000000000000000000000000 : ℝ)*base77 + (43318705886247/25000000000000000000000000000 : ℝ)*base79 + (10657419311247/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4723559/2000000000000000000000 : ℝ)*base90 + (4723559/2000000000000000000000 : ℝ)*base92 + (4723559/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1737_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1231/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (21587/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1737_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1737_s1_0 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1296851113/10000000000 : ℝ)*x 0 + (5521116079/10000000000 : ℝ)*x 1 + (2536019301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1296851113/10000000000 : ℝ)^5567 ≤ (8183404693243/100000000000000 : ℝ)^4543 := by
    have hnat : (1296851113 : ℕ)^5567*100000000000000^4543 ≤ 8183404693243^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296851113 10000000000 8183404693243 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5521116079/10000000000 : ℝ)^5567 ≤ (12073114019211/25000000000000 : ℝ)^4543 := by
    have hnat : (5521116079 : ℕ)^5567*25000000000000^4543 ≤ 12073114019211^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521116079 10000000000 12073114019211 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2536019301/5000000000 : ℝ)^5567 ≤ (43524139222317/100000000000000 : ℝ)^4543 := by
    have hnat : (2536019301 : ℕ)^5567*100000000000000^4543 ≤ 43524139222317^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2536019301 5000000000 43524139222317 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1296851113/10000000000 : ℝ), (5521116079/10000000000 : ℝ), (2536019301/5000000000 : ℝ)] ![(8183404693243/100000000000000 : ℝ), (12073114019211/25000000000000 : ℝ), (43524139222317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1296851113/10000000000 : ℝ)|^5567 ≤ (8183404693243/100000000000000 : ℝ)^4543
        have hw : |(-1296851113/10000000000 : ℝ)|=(1296851113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5521116079/10000000000 : ℝ)|^5567 ≤ (12073114019211/25000000000000 : ℝ)^4543
        have hw : |(5521116079/10000000000 : ℝ)|=(5521116079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2536019301/5000000000 : ℝ)|^5567 ≤ (43524139222317/100000000000000 : ℝ)^4543
        have hw : |(2536019301/5000000000 : ℝ)|=(2536019301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s1_1 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347082989/10000000000 : ℝ)*x 0 + (-1532602601/10000000000 : ℝ)*x 1 + (1268009569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347082989/10000000000 : ℝ)^5567 ≤ (1451055535439/3125000000000 : ℝ)^4543 := by
    have hnat : (5347082989 : ℕ)^5567*3125000000000^4543 ≤ 1451055535439^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347082989 10000000000 1451055535439 3125000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1532602601/10000000000 : ℝ)^5567 ≤ (10042087059251/100000000000000 : ℝ)^4543 := by
    have hnat : (1532602601 : ℕ)^5567*100000000000000^4543 ≤ 10042087059251^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532602601 10000000000 10042087059251 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268009569/2500000000 : ℝ)^5567 ≤ (8704827158859/20000000000000 : ℝ)^4543 := by
    have hnat : (1268009569 : ℕ)^5567*20000000000000^4543 ≤ 8704827158859^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268009569 2500000000 8704827158859 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347082989/10000000000 : ℝ), (-1532602601/10000000000 : ℝ), (1268009569/2500000000 : ℝ)] ![(1451055535439/3125000000000 : ℝ), (10042087059251/100000000000000 : ℝ), (8704827158859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347082989/10000000000 : ℝ)|^5567 ≤ (1451055535439/3125000000000 : ℝ)^4543
        have hw : |(5347082989/10000000000 : ℝ)|=(5347082989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1532602601/10000000000 : ℝ)|^5567 ≤ (10042087059251/100000000000000 : ℝ)^4543
        have hw : |(-1532602601/10000000000 : ℝ)|=(1532602601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1268009569/2500000000 : ℝ)|^5567 ≤ (8704827158859/20000000000000 : ℝ)^4543
        have hw : |(1268009569/2500000000 : ℝ)|=(1268009569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s1_2 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347082399/10000000000 : ℝ)*x 0 + (5072038857/10000000000 : ℝ)*x 1 + (-1532602621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347082399/10000000000 : ℝ)^5567 ≤ (11608442713917/25000000000000 : ℝ)^4543 := by
    have hnat : (5347082399 : ℕ)^5567*25000000000000^4543 ≤ 11608442713917^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347082399 10000000000 11608442713917 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072038857/10000000000 : ℝ)^5567 ≤ (43524141903747/100000000000000 : ℝ)^4543 := by
    have hnat : (5072038857 : ℕ)^5567*100000000000000^4543 ≤ 43524141903747^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072038857 10000000000 43524141903747 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1532602621/10000000000 : ℝ)^5567 ≤ (2008417443967/20000000000000 : ℝ)^4543 := by
    have hnat : (1532602621 : ℕ)^5567*20000000000000^4543 ≤ 2008417443967^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532602621 10000000000 2008417443967 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347082399/10000000000 : ℝ), (5072038857/10000000000 : ℝ), (-1532602621/10000000000 : ℝ)] ![(11608442713917/25000000000000 : ℝ), (43524141903747/100000000000000 : ℝ), (2008417443967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347082399/10000000000 : ℝ)|^5567 ≤ (11608442713917/25000000000000 : ℝ)^4543
        have hw : |(5347082399/10000000000 : ℝ)|=(5347082399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072038857/10000000000 : ℝ)|^5567 ≤ (43524141903747/100000000000000 : ℝ)^4543
        have hw : |(5072038857/10000000000 : ℝ)|=(5072038857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1532602621/10000000000 : ℝ)|^5567 ≤ (2008417443967/20000000000000 : ℝ)^4543
        have hw : |(-1532602621/10000000000 : ℝ)|=(1532602621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s1_3 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (16190129/40000000 : ℝ)*x 0 + (845929649/2500000000 : ℝ)*x 1 + (4781128789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16190129/40000000 : ℝ)^5567 ≤ (8252591527823/25000000000000 : ℝ)^4543 := by
    have hnat : (16190129 : ℕ)^5567*25000000000000^4543 ≤ 8252591527823^4543*40000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16190129 40000000 8252591527823 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845929649/2500000000 : ℝ)^5567 ≤ (13252227896429/50000000000000 : ℝ)^4543 := by
    have hnat : (845929649 : ℕ)^5567*50000000000000^4543 ≤ 13252227896429^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845929649 2500000000 13252227896429 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4781128789/10000000000 : ℝ)^5567 ≤ (40485178079413/100000000000000 : ℝ)^4543 := by
    have hnat : (4781128789 : ℕ)^5567*100000000000000^4543 ≤ 40485178079413^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4781128789 10000000000 40485178079413 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16190129/40000000 : ℝ), (845929649/2500000000 : ℝ), (4781128789/10000000000 : ℝ)] ![(8252591527823/25000000000000 : ℝ), (13252227896429/50000000000000 : ℝ), (40485178079413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16190129/40000000 : ℝ)|^5567 ≤ (8252591527823/25000000000000 : ℝ)^4543
        have hw : |(16190129/40000000 : ℝ)|=(16190129/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845929649/2500000000 : ℝ)|^5567 ≤ (13252227896429/50000000000000 : ℝ)^4543
        have hw : |(845929649/2500000000 : ℝ)|=(845929649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4781128789/10000000000 : ℝ)|^5567 ≤ (40485178079413/100000000000000 : ℝ)^4543
        have hw : |(4781128789/10000000000 : ℝ)|=(4781128789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s1_4 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1297261483/10000000000 : ℝ)*x 0 + (2539678631/5000000000 : ℝ)*x 1 + (1378409417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1297261483/10000000000 : ℝ)^5567 ≤ (4093289005219/50000000000000 : ℝ)^4543 := by
    have hnat : (1297261483 : ℕ)^5567*50000000000000^4543 ≤ 4093289005219^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1297261483 10000000000 4093289005219 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539678631/5000000000 : ℝ)^5567 ≤ (43601110428139/100000000000000 : ℝ)^4543 := by
    have hnat : (2539678631 : ℕ)^5567*100000000000000^4543 ≤ 43601110428139^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539678631 5000000000 43601110428139 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378409417/2500000000 : ℝ)^5567 ≤ (24106155771783/50000000000000 : ℝ)^4543 := by
    have hnat : (1378409417 : ℕ)^5567*50000000000000^4543 ≤ 24106155771783^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378409417 2500000000 24106155771783 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1297261483/10000000000 : ℝ), (2539678631/5000000000 : ℝ), (1378409417/2500000000 : ℝ)] ![(4093289005219/50000000000000 : ℝ), (43601110428139/100000000000000 : ℝ), (24106155771783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1297261483/10000000000 : ℝ)|^5567 ≤ (4093289005219/50000000000000 : ℝ)^4543
        have hw : |(-1297261483/10000000000 : ℝ)|=(1297261483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539678631/5000000000 : ℝ)|^5567 ≤ (43601110428139/100000000000000 : ℝ)^4543
        have hw : |(2539678631/5000000000 : ℝ)|=(2539678631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378409417/2500000000 : ℝ)|^5567 ≤ (24106155771783/50000000000000 : ℝ)^4543
        have hw : |(1378409417/2500000000 : ℝ)|=(1378409417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s1_5 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5227669027/10000000000 : ℝ)*x 0 + (-1091004811/10000000000 : ℝ)*x 1 + (5513637357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5227669027/10000000000 : ℝ)^5567 ≤ (22583135826769/50000000000000 : ℝ)^4543 := by
    have hnat : (5227669027 : ℕ)^5567*50000000000000^4543 ≤ 22583135826769^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227669027 10000000000 22583135826769 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091004811/10000000000 : ℝ)^5567 ≤ (6621420120357/100000000000000 : ℝ)^4543 := by
    have hnat : (1091004811 : ℕ)^5567*100000000000000^4543 ≤ 6621420120357^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091004811 10000000000 6621420120357 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5513637357/10000000000 : ℝ)^5567 ≤ (9642461642231/20000000000000 : ℝ)^4543 := by
    have hnat : (5513637357 : ℕ)^5567*20000000000000^4543 ≤ 9642461642231^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513637357 10000000000 9642461642231 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5227669027/10000000000 : ℝ), (-1091004811/10000000000 : ℝ), (5513637357/10000000000 : ℝ)] ![(22583135826769/50000000000000 : ℝ), (6621420120357/100000000000000 : ℝ), (9642461642231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5227669027/10000000000 : ℝ)|^5567 ≤ (22583135826769/50000000000000 : ℝ)^4543
        have hw : |(5227669027/10000000000 : ℝ)|=(5227669027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1091004811/10000000000 : ℝ)|^5567 ≤ (6621420120357/100000000000000 : ℝ)^4543
        have hw : |(-1091004811/10000000000 : ℝ)|=(1091004811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5513637357/10000000000 : ℝ)|^5567 ≤ (9642461642231/20000000000000 : ℝ)^4543
        have hw : |(5513637357/10000000000 : ℝ)|=(5513637357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s1_6 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045533659/2000000000 : ℝ)*x 0 + (1378409507/2500000000 : ℝ)*x 1 + (-1091004887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045533659/2000000000 : ℝ)^5567 ≤ (9033252780729/20000000000000 : ℝ)^4543 := by
    have hnat : (1045533659 : ℕ)^5567*20000000000000^4543 ≤ 9033252780729^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045533659 2000000000 9033252780729 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1378409507/2500000000 : ℝ)^5567 ≤ (2410615770051/5000000000000 : ℝ)^4543 := by
    have hnat : (1378409507 : ℕ)^5567*5000000000000^4543 ≤ 2410615770051^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378409507 2500000000 2410615770051 5000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091004887/10000000000 : ℝ)^5567 ≤ (827677585697/12500000000000 : ℝ)^4543 := by
    have hnat : (1091004887 : ℕ)^5567*12500000000000^4543 ≤ 827677585697^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091004887 10000000000 827677585697 12500000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045533659/2000000000 : ℝ), (1378409507/2500000000 : ℝ), (-1091004887/10000000000 : ℝ)] ![(9033252780729/20000000000000 : ℝ), (2410615770051/5000000000000 : ℝ), (827677585697/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045533659/2000000000 : ℝ)|^5567 ≤ (9033252780729/20000000000000 : ℝ)^4543
        have hw : |(1045533659/2000000000 : ℝ)|=(1045533659/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1378409507/2500000000 : ℝ)|^5567 ≤ (2410615770051/5000000000000 : ℝ)^4543
        have hw : |(1378409507/2500000000 : ℝ)|=(1378409507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091004887/10000000000 : ℝ)|^5567 ≤ (827677585697/12500000000000 : ℝ)^4543
        have hw : |(-1091004887/10000000000 : ℝ)|=(1091004887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s1_7 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4048800041/10000000000 : ℝ)*x 0 + (4758349959/10000000000 : ℝ)*x 1 + (425874007/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4048800041/10000000000 : ℝ)^5567 ≤ (660460736747/2000000000000 : ℝ)^4543 := by
    have hnat : (4048800041 : ℕ)^5567*2000000000000^4543 ≤ 660460736747^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048800041 10000000000 660460736747 2000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4758349959/10000000000 : ℝ)^5567 ≤ (2515559019781/6250000000000 : ℝ)^4543 := by
    have hnat : (4758349959 : ℕ)^5567*6250000000000^4543 ≤ 2515559019781^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4758349959 10000000000 2515559019781 6250000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425874007/1250000000 : ℝ)^5567 ≤ (13364009418597/50000000000000 : ℝ)^4543 := by
    have hnat : (425874007 : ℕ)^5567*50000000000000^4543 ≤ 13364009418597^4543*1250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425874007 1250000000 13364009418597 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4048800041/10000000000 : ℝ), (4758349959/10000000000 : ℝ), (425874007/1250000000 : ℝ)] ![(660460736747/2000000000000 : ℝ), (2515559019781/6250000000000 : ℝ), (13364009418597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4048800041/10000000000 : ℝ)|^5567 ≤ (660460736747/2000000000000 : ℝ)^4543
        have hw : |(4048800041/10000000000 : ℝ)|=(4048800041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4758349959/10000000000 : ℝ)|^5567 ≤ (2515559019781/6250000000000 : ℝ)^4543
        have hw : |(4758349959/10000000000 : ℝ)|=(4758349959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425874007/1250000000 : ℝ)|^5567 ≤ (13364009418597/50000000000000 : ℝ)^4543
        have hw : |(425874007/1250000000 : ℝ)|=(425874007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1737_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (8749/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4589/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (21587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (21587/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (21587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (21587/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (21587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (21587/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1231/20000 : ℝ) ^ (5551/1024 : ℝ) ≤ (27322992786937/100000000000000000000 : ℝ) := by
    have hpowers : (1231/20000 : ℝ)^5551 ≤ (27322992786937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1231 : ℕ)^5551*100000000000000000000^1024 ≤ 27322992786937^1024*20000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1231 20000 27322992786937 100000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1231/20000 : ℝ)) (X := (27322992786937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (21587/100000 : ℝ) ^ (5551/1024 : ℝ) ≤ (12294023467421199/50000000000000000000 : ℝ) := by
    have hpowers : (21587/100000 : ℝ)^5551 ≤ (12294023467421199/50000000000000000000 : ℝ)^1024 := by
      have hnat : (21587 : ℕ)^5551*50000000000000000000^1024 ≤ 12294023467421199^1024*100000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21587 100000 12294023467421199 50000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21587/100000 : ℝ)) (X := (12294023467421199/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000027322992786937/50000000000000000000 : ℝ) ≤ (1250000126007649/1250000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (50000027322992786937/50000000000000000000 : ℝ)^1024 ≤ (1250000126007649/1250000000000000 : ℝ)^5551 := by
      have hnat : (50000027322992786937 : ℕ)^1024*1250000000000000^5551 ≤ 1250000126007649^5551*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000027322992786937 50000000000000000000 1250000126007649 1250000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000126007649/1250000000000000 : ℝ)) (X := (50000027322992786937/50000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004923073985525867/20000000000000000000 : ℝ) ≤ (1250056754659463/1250000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (20004923073985525867/20000000000000000000 : ℝ)^1024 ≤ (1250056754659463/1250000000000000 : ℝ)^5551 := by
      have hnat : (20004923073985525867 : ℕ)^1024*1250000000000000^5551 ≤ 1250056754659463^5551*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004923073985525867 20000000000000000000 1250056754659463 1250000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056754659463/1250000000000000 : ℝ)) (X := (20004923073985525867/20000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012294023467421199/25000000000000000000 : ℝ) ≤ (1250113383311277/1250000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (25012294023467421199/25000000000000000000 : ℝ)^1024 ≤ (1250113383311277/1250000000000000 : ℝ)^5551 := by
      have hnat : (25012294023467421199 : ℕ)^1024*1250000000000000^5551 ≤ 1250113383311277^5551*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012294023467421199 25000000000000000000 1250113383311277 1250000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250113383311277/1250000000000000 : ℝ)) (X := (25012294023467421199/25000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27322992786937/100000000000000000000 : ℝ) ≤ ((4822326211461552257/4822500000000000000 : ℝ)+2*(28314325907/96450000000000 : ℝ)*(1231/20000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (4822326211461552257/4822500000000000000 : ℝ)+2*(28314325907/96450000000000 : ℝ)*(1231/20000 : ℝ)=(1250000126007649/1250000000000000 : ℝ) by norm_num, show 1+2*(27322992786937/100000000000000000000 : ℝ)=(50000027322992786937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12294023467421199/50000000000000000000 : ℝ)+(27322992786937/100000000000000000000 : ℝ) ≤ ((4822326211461552257/4822500000000000000 : ℝ)+(28314325907/96450000000000 : ℝ)*((21587/100000 : ℝ)+(1231/20000 : ℝ)))^(5551/1024 : ℝ) := by
    rw [show (4822326211461552257/4822500000000000000 : ℝ)+(28314325907/96450000000000 : ℝ)*((21587/100000 : ℝ)+(1231/20000 : ℝ))=(1250056754659463/1250000000000000 : ℝ) by norm_num, show 1+(12294023467421199/50000000000000000000 : ℝ)+(27322992786937/100000000000000000000 : ℝ)=(20004923073985525867/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12294023467421199/50000000000000000000 : ℝ) ≤ ((4822326211461552257/4822500000000000000 : ℝ)+2*(28314325907/96450000000000 : ℝ)*(21587/100000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (4822326211461552257/4822500000000000000 : ℝ)+2*(28314325907/96450000000000 : ℝ)*(21587/100000 : ℝ)=(1250113383311277/1250000000000000 : ℝ) by norm_num, show 1+2*(12294023467421199/50000000000000000000 : ℝ)=(25012294023467421199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4822326211461552257/4822500000000000000 : ℝ)*(X 1 0+X 2 0)+(28314325907/96450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (1231/20000 : ℝ)) (hi := (21587/100000 : ℝ)) (c := (4822326211461552257/4822500000000000000 : ℝ)) (alpha := (28314325907/96450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4822326211461552257/4822500000000000000 : ℝ)*(X 0 1+X 2 1)+(28314325907/96450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (1231/20000 : ℝ)) (hi := (21587/100000 : ℝ)) (c := (4822326211461552257/4822500000000000000 : ℝ)) (alpha := (28314325907/96450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4822326211461552257/4822500000000000000 : ℝ)*(X 0 2+X 1 2)+(28314325907/96450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (1231/20000 : ℝ)) (hi := (21587/100000 : ℝ)) (c := (4822326211461552257/4822500000000000000 : ℝ)) (alpha := (28314325907/96450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1296851113/10000000000 : ℝ)*X 0 0+(5521116079/10000000000 : ℝ)*X 0 1+(2536019301/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347082989/10000000000 : ℝ)*X 1 0+(-1532602601/10000000000 : ℝ)*X 1 1+(1268009569/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347082399/10000000000 : ℝ)*X 2 0+(5072038857/10000000000 : ℝ)*X 2 1+(-1532602621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((16190129/40000000 : ℝ)*X 0 0+(845929649/2500000000 : ℝ)*X 0 1+(4781128789/10000000000 : ℝ)*X 0 2+(16190129/40000000 : ℝ)*X 1 0+(845929649/2500000000 : ℝ)*X 1 1+(4781128789/10000000000 : ℝ)*X 1 2+(16190129/40000000 : ℝ)*X 2 0+(845929649/2500000000 : ℝ)*X 2 1+(4781128789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1297261483/10000000000 : ℝ)*X 0 0+(2539678631/5000000000 : ℝ)*X 0 1+(1378409417/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5227669027/10000000000 : ℝ)*X 1 0+(-1091004811/10000000000 : ℝ)*X 1 1+(5513637357/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1045533659/2000000000 : ℝ)*X 2 0+(1378409507/2500000000 : ℝ)*X 2 1+(-1091004887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4048800041/10000000000 : ℝ)*X 0 0+(4758349959/10000000000 : ℝ)*X 0 1+(425874007/1250000000 : ℝ)*X 0 2+(4048800041/10000000000 : ℝ)*X 1 0+(4758349959/10000000000 : ℝ)*X 1 1+(425874007/1250000000 : ℝ)*X 1 2+(4048800041/10000000000 : ℝ)*X 2 0+(4758349959/10000000000 : ℝ)*X 2 1+(425874007/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31790357857058825025234449/5023437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (239933123/20000000000000 : ℝ)*(base19) + (806416521/100000000000000 : ℝ)*(base23) + (9861523/12500000000000 : ℝ)*(lower2) + (196285659/100000000000000 : ℝ)*(upper3) + (37789427/100000000000000 : ℝ)*(upper5) + (367802264062039/25000000000000 : ℝ)*(major0) + (367802264062039/25000000000000 : ℝ)*(major1) + (367802264062039/25000000000000 : ℝ)*(major2) + (222679640313611/10000000000000 : ℝ)*(sp0) + (556700625549719/25000000000000 : ℝ)*(sp1) + (222680289544797/10000000000000 : ℝ)*(sp2) + (143122293173731/20000000000000 : ℝ)*(sp3) + (364936419/5000000000000 : ℝ)*(sp4) + (1366908127/50000000000000 : ℝ)*(sp7) + (715614199684909/100000000000000 : ℝ)*(f.failure) + (2226803701864491/100000000000000 : ℝ)*(f.sum) + (15266473721927/4822500000000000000000000000 : ℝ)*base65 + (145786749130207341/40187500000000000000000000000000 : ℝ)*base67 + (322541210301605159/40187500000000000000000000000000 : ℝ)*base70 + (409912349658292659/40187500000000000000000000000000 : ℝ)*base72 + (23400809701967/4822500000000000000000000000 : ℝ)*base73 + (522974024263355159/40187500000000000000000000000000 : ℝ)*base76 + (114645128735667659/40187500000000000000000000000000 : ℝ)*base78 + (215770625352292659/40187500000000000000000000000000 : ℝ)*base80 + (27360638969621/9645000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (17777009/10000000000000000000000 : ℝ)*base89 + (17777009/10000000000000000000000 : ℝ)*base91 + (17777009/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30728155313432347423903/3215000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42812833/4000000000000 : ℝ)*(base19) + (1851823717/100000000000000 : ℝ)*(base23) + (116843567/20000000000000 : ℝ)*(upper2) + (17688977/25000000000000 : ℝ)*(upper3) + (1382163/195312500000 : ℝ)*(upper5) + (1521327433489343/100000000000000 : ℝ)*(major0) + (1521327433489343/100000000000000 : ℝ)*(major1) + (1521327433489343/100000000000000 : ℝ)*(major2) + (7649835563/100000000000000 : ℝ)*(sp1) + (1410728889/20000000000000 : ℝ)*(sp2) + (575665538228443/25000000000000 : ℝ)*(sp4) + (287831679094673/12500000000000 : ℝ)*(sp5) + (230265324744561/10000000000000 : ℝ)*(sp6) + (739992395473359/100000000000000 : ℝ)*(sp7) + (739992395473359/100000000000000 : ℝ)*(f.failure) + (575665538228443/25000000000000 : ℝ)*(f.sum) + (3798105647533/9645000000000000000000000000 : ℝ)*base66 + (589703427591965717/160750000000000000000000000000000 : ℝ)*base67 + (7234602850715717/160750000000000000000000000000000 : ℝ)*base69 + (203367109490215717/160750000000000000000000000000000 : ℝ)*base71 + (8527639373393/2411250000000000000000000000 : ℝ)*base73 + (206054891784284283/160750000000000000000000000000000 : ℝ)*base76 + (550658949807284283/160750000000000000000000000000000 : ℝ)*base78 + (277035524503784283/160750000000000000000000000000000 : ℝ)*base80 + (13668161367797/9645000000000000000000000000 : ℝ)*base81 + (4870459/10000000000000000000000 : ℝ)*base89 + (4870459/10000000000000000000000 : ℝ)*base91 + (4870459/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1737_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (21587/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8749/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4589/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1737_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1737_s2_0 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259731793/2000000000 : ℝ)*x 0 + (137883877/250000000 : ℝ)*x 1 + (634572507/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259731793/2000000000 : ℝ)^5567 ≤ (8197386183673/100000000000000 : ℝ)^4543 := by
    have hnat : (259731793 : ℕ)^5567*100000000000000^4543 ≤ 8197386183673^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259731793 2000000000 8197386183673 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137883877/250000000 : ℝ)^5567 ≤ (3014419657191/6250000000000 : ℝ)^4543 := by
    have hnat : (137883877 : ℕ)^5567*6250000000000^4543 ≤ 3014419657191^4543*250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137883877 250000000 3014419657191 6250000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634572507/1250000000 : ℝ)^5567 ≤ (8714379856329/20000000000000 : ℝ)^4543 := by
    have hnat : (634572507 : ℕ)^5567*20000000000000^4543 ≤ 8714379856329^4543*1250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634572507 1250000000 8714379856329 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259731793/2000000000 : ℝ), (137883877/250000000 : ℝ), (634572507/1250000000 : ℝ)] ![(8197386183673/100000000000000 : ℝ), (3014419657191/6250000000000 : ℝ), (8714379856329/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259731793/2000000000 : ℝ)|^5567 ≤ (8197386183673/100000000000000 : ℝ)^4543
        have hw : |(-259731793/2000000000 : ℝ)|=(259731793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(137883877/250000000 : ℝ)|^5567 ≤ (3014419657191/6250000000000 : ℝ)^4543
        have hw : |(137883877/250000000 : ℝ)|=(137883877/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634572507/1250000000 : ℝ)|^5567 ≤ (8714379856329/20000000000000 : ℝ)^4543
        have hw : |(634572507/1250000000 : ℝ)|=(634572507/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s2_1 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672750187/5000000000 : ℝ)*x 0 + (-764374513/5000000000 : ℝ)*x 1 + (1269145239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672750187/5000000000 : ℝ)^5567 ≤ (23208468290261/50000000000000 : ℝ)^4543 := by
    have hnat : (2672750187 : ℕ)^5567*50000000000000^4543 ≤ 23208468290261^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672750187 5000000000 23208468290261 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (764374513/5000000000 : ℝ)^5567 ≤ (2002230932691/20000000000000 : ℝ)^4543 := by
    have hnat : (764374513 : ℕ)^5567*20000000000000^4543 ≤ 2002230932691^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      764374513 5000000000 2002230932691 20000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1269145239/2500000000 : ℝ)^5567 ≤ (21785954373711/50000000000000 : ℝ)^4543 := by
    have hnat : (1269145239 : ℕ)^5567*50000000000000^4543 ≤ 21785954373711^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269145239 2500000000 21785954373711 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672750187/5000000000 : ℝ), (-764374513/5000000000 : ℝ), (1269145239/2500000000 : ℝ)] ![(23208468290261/50000000000000 : ℝ), (2002230932691/20000000000000 : ℝ), (21785954373711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672750187/5000000000 : ℝ)|^5567 ≤ (23208468290261/50000000000000 : ℝ)^4543
        have hw : |(2672750187/5000000000 : ℝ)|=(2672750187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-764374513/5000000000 : ℝ)|^5567 ≤ (2002230932691/20000000000000 : ℝ)^4543
        have hw : |(-764374513/5000000000 : ℝ)|=(764374513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1269145239/2500000000 : ℝ)|^5567 ≤ (21785954373711/50000000000000 : ℝ)^4543
        have hw : |(1269145239/2500000000 : ℝ)|=(1269145239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s2_2 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345502169/10000000000 : ℝ)*x 0 + (5076578407/10000000000 : ℝ)*x 1 + (-1528749987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345502169/10000000000 : ℝ)^5567 ≤ (2320847784021/5000000000000 : ℝ)^4543 := by
    have hnat : (5345502169 : ℕ)^5567*5000000000000^4543 ≤ 2320847784021^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345502169 10000000000 2320847784021 5000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5076578407/10000000000 : ℝ)^5567 ≤ (136162131057/312500000000 : ℝ)^4543 := by
    have hnat : (5076578407 : ℕ)^5567*312500000000^4543 ≤ 136162131057^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076578407 10000000000 136162131057 312500000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1528749987/10000000000 : ℝ)^5567 ≤ (200223247503/2000000000000 : ℝ)^4543 := by
    have hnat : (1528749987 : ℕ)^5567*2000000000000^4543 ≤ 200223247503^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528749987 10000000000 200223247503 2000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345502169/10000000000 : ℝ), (5076578407/10000000000 : ℝ), (-1528749987/10000000000 : ℝ)] ![(2320847784021/5000000000000 : ℝ), (136162131057/312500000000 : ℝ), (200223247503/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345502169/10000000000 : ℝ)|^5567 ≤ (2320847784021/5000000000000 : ℝ)^4543
        have hw : |(5345502169/10000000000 : ℝ)|=(5345502169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5076578407/10000000000 : ℝ)|^5567 ≤ (136162131057/312500000000 : ℝ)^4543
        have hw : |(5076578407/10000000000 : ℝ)|=(5076578407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1528749987/10000000000 : ℝ)|^5567 ≤ (200223247503/2000000000000 : ℝ)^4543
        have hw : |(-1528749987/10000000000 : ℝ)|=(1528749987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s2_3 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4049002151/10000000000 : ℝ)*x 0 + (1699813867/5000000000 : ℝ)*x 1 + (1191245629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4049002151/10000000000 : ℝ)^5567 ≤ (33025056874749/100000000000000 : ℝ)^4543 := by
    have hnat : (4049002151 : ℕ)^5567*100000000000000^4543 ≤ 33025056874749^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4049002151 10000000000 33025056874749 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1699813867/5000000000 : ℝ)^5567 ≤ (13328620194809/50000000000000 : ℝ)^4543 := by
    have hnat : (1699813867 : ℕ)^5567*50000000000000^4543 ≤ 13328620194809^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1699813867 5000000000 13328620194809 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1191245629/2500000000 : ℝ)^5567 ≤ (10079425679973/25000000000000 : ℝ)^4543 := by
    have hnat : (1191245629 : ℕ)^5567*25000000000000^4543 ≤ 10079425679973^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1191245629 2500000000 10079425679973 25000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4049002151/10000000000 : ℝ), (1699813867/5000000000 : ℝ), (1191245629/2500000000 : ℝ)] ![(33025056874749/100000000000000 : ℝ), (13328620194809/50000000000000 : ℝ), (10079425679973/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4049002151/10000000000 : ℝ)|^5567 ≤ (33025056874749/100000000000000 : ℝ)^4543
        have hw : |(4049002151/10000000000 : ℝ)|=(4049002151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1699813867/5000000000 : ℝ)|^5567 ≤ (13328620194809/50000000000000 : ℝ)^4543
        have hw : |(1699813867/5000000000 : ℝ)|=(1699813867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1191245629/2500000000 : ℝ)|^5567 ≤ (10079425679973/25000000000000 : ℝ)^4543
        have hw : |(1191245629/2500000000 : ℝ)|=(1191245629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s2_4 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-129903959/1000000000 : ℝ)*x 0 + (127089219/250000000 : ℝ)*x 1 + (2754109447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129903959/1000000000 : ℝ)^5567 ≤ (4100165202371/50000000000000 : ℝ)^4543 := by
    have hnat : (129903959 : ℕ)^5567*50000000000000^4543 ≤ 4100165202371^4543*1000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129903959 1000000000 4100165202371 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127089219/250000000 : ℝ)^5567 ≤ (2727838411363/6250000000000 : ℝ)^4543 := by
    have hnat : (127089219 : ℕ)^5567*6250000000000^4543 ≤ 2727838411363^4543*250000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127089219 250000000 2727838411363 6250000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2754109447/5000000000 : ℝ)^5567 ≤ (48154255005357/100000000000000 : ℝ)^4543 := by
    have hnat : (2754109447 : ℕ)^5567*100000000000000^4543 ≤ 48154255005357^4543*5000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754109447 5000000000 48154255005357 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129903959/1000000000 : ℝ), (127089219/250000000 : ℝ), (2754109447/5000000000 : ℝ)] ![(4100165202371/50000000000000 : ℝ), (2727838411363/6250000000000 : ℝ), (48154255005357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129903959/1000000000 : ℝ)|^5567 ≤ (4100165202371/50000000000000 : ℝ)^4543
        have hw : |(-129903959/1000000000 : ℝ)|=(129903959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127089219/250000000 : ℝ)|^5567 ≤ (2727838411363/6250000000000 : ℝ)^4543
        have hw : |(127089219/250000000 : ℝ)|=(127089219/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2754109447/5000000000 : ℝ)|^5567 ≤ (48154255005357/100000000000000 : ℝ)^4543
        have hw : |(2754109447/5000000000 : ℝ)|=(2754109447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s2_5 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307215179/2500000000 : ℝ)*x 0 + (-6856939/62500000 : ℝ)*x 1 + (5508218979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307215179/2500000000 : ℝ)^5567 ≤ (45178888729861/100000000000000 : ℝ)^4543 := by
    have hnat : (1307215179 : ℕ)^5567*100000000000000^4543 ≤ 45178888729861^4543*2500000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307215179 2500000000 45178888729861 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6856939/62500000 : ℝ)^5567 ≤ (6666855333839/100000000000000 : ℝ)^4543 := by
    have hnat : (6856939 : ℕ)^5567*100000000000000^4543 ≤ 6666855333839^4543*62500000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6856939 62500000 6666855333839 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508218979/10000000000 : ℝ)^5567 ≤ (48154255915943/100000000000000 : ℝ)^4543 := by
    have hnat : (5508218979 : ℕ)^5567*100000000000000^4543 ≤ 48154255915943^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508218979 10000000000 48154255915943 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307215179/2500000000 : ℝ), (-6856939/62500000 : ℝ), (5508218979/10000000000 : ℝ)] ![(45178888729861/100000000000000 : ℝ), (6666855333839/100000000000000 : ℝ), (48154255915943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307215179/2500000000 : ℝ)|^5567 ≤ (45178888729861/100000000000000 : ℝ)^4543
        have hw : |(1307215179/2500000000 : ℝ)|=(1307215179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6856939/62500000 : ℝ)|^5567 ≤ (6666855333839/100000000000000 : ℝ)^4543
        have hw : |(-6856939/62500000 : ℝ)|=(6856939/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508218979/10000000000 : ℝ)|^5567 ≤ (48154255915943/100000000000000 : ℝ)^4543
        have hw : |(5508218979/10000000000 : ℝ)|=(5508218979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s2_6 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5228860807/10000000000 : ℝ)*x 0 + (172131841/312500000 : ℝ)*x 1 + (-1097110207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5228860807/10000000000 : ℝ)^5567 ≤ (22589444846677/50000000000000 : ℝ)^4543 := by
    have hnat : (5228860807 : ℕ)^5567*50000000000000^4543 ≤ 22589444846677^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228860807 10000000000 22589444846677 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172131841/312500000 : ℝ)^5567 ≤ (48154255198187/100000000000000 : ℝ)^4543 := by
    have hnat : (172131841 : ℕ)^5567*100000000000000^4543 ≤ 48154255198187^4543*312500000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172131841 312500000 48154255198187 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097110207/10000000000 : ℝ)^5567 ≤ (3333427544053/50000000000000 : ℝ)^4543 := by
    have hnat : (1097110207 : ℕ)^5567*50000000000000^4543 ≤ 3333427544053^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097110207 10000000000 3333427544053 50000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5228860807/10000000000 : ℝ), (172131841/312500000 : ℝ), (-1097110207/10000000000 : ℝ)] ![(22589444846677/50000000000000 : ℝ), (48154255198187/100000000000000 : ℝ), (3333427544053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5228860807/10000000000 : ℝ)|^5567 ≤ (22589444846677/50000000000000 : ℝ)^4543
        have hw : |(5228860807/10000000000 : ℝ)|=(5228860807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172131841/312500000 : ℝ)|^5567 ≤ (48154255198187/100000000000000 : ℝ)^4543
        have hw : |(172131841/312500000 : ℝ)|=(172131841/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097110207/10000000000 : ℝ)|^5567 ≤ (3333427544053/50000000000000 : ℝ)^4543
        have hw : |(-1097110207/10000000000 : ℝ)|=(1097110207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1737_s2_7 (p : ℝ) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4050186191/10000000000 : ℝ)*x 0 + (948646991/2000000000 : ℝ)*x 1 + (3421834859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4050186191/10000000000 : ℝ)^5567 ≤ (1651844575309/5000000000000 : ℝ)^4543 := by
    have hnat : (4050186191 : ℕ)^5567*5000000000000^4543 ≤ 1651844575309^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4050186191 10000000000 1651844575309 5000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948646991/2000000000 : ℝ)^5567 ≤ (40092330802709/100000000000000 : ℝ)^4543 := by
    have hnat : (948646991 : ℕ)^5567*100000000000000^4543 ≤ 40092330802709^4543*2000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948646991 2000000000 40092330802709 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3421834859/10000000000 : ℝ)^5567 ≤ (26870777673101/100000000000000 : ℝ)^4543 := by
    have hnat : (3421834859 : ℕ)^5567*100000000000000^4543 ≤ 26870777673101^4543*10000000000^5567 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3421834859 10000000000 26870777673101 100000000000000 5567 4543 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5567/1024 : ℝ)) 5567 4543 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4050186191/10000000000 : ℝ), (948646991/2000000000 : ℝ), (3421834859/10000000000 : ℝ)] ![(1651844575309/5000000000000 : ℝ), (40092330802709/100000000000000 : ℝ), (26870777673101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4050186191/10000000000 : ℝ)|^5567 ≤ (1651844575309/5000000000000 : ℝ)^4543
        have hw : |(4050186191/10000000000 : ℝ)|=(4050186191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(948646991/2000000000 : ℝ)|^5567 ≤ (40092330802709/100000000000000 : ℝ)^4543
        have hw : |(948646991/2000000000 : ℝ)|=(948646991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3421834859/10000000000 : ℝ)|^5567 ≤ (26870777673101/100000000000000 : ℝ)^4543
        have hw : |(3421834859/10000000000 : ℝ)|=(3421834859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1737_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4589/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8749/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8849/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4589/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8749/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4589/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8749/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4589/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8749/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4589/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8749/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4589/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8749/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4589/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8749/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8749/100000 : ℝ) ^ (5551/1024 : ℝ) ≤ (18385016897531/10000000000000000000 : ℝ) := by
    have hpowers : (8749/100000 : ℝ)^5551 ≤ (18385016897531/10000000000000000000 : ℝ)^1024 := by
      have hnat : (8749 : ℕ)^5551*10000000000000000000^1024 ≤ 18385016897531^1024*100000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8749 100000 18385016897531 10000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8749/100000 : ℝ)) (X := (18385016897531/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4589/25000 : ℝ) ^ (5551/1024 : ℝ) ≤ (5104880505578597/50000000000000000000 : ℝ) := by
    have hpowers : (4589/25000 : ℝ)^5551 ≤ (5104880505578597/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4589 : ℕ)^5551*50000000000000000000^1024 ≤ 5104880505578597^1024*25000^5551 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4589 25000 5104880505578597 50000000000000000000 5551 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4589/25000 : ℝ)) (X := (5104880505578597/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000018385016897531/5000000000000000000 : ℝ) ≤ (2500001695751133/2500000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (5000018385016897531/5000000000000000000 : ℝ)^1024 ≤ (2500001695751133/2500000000000000 : ℝ)^5551 := by
      have hnat : (5000018385016897531 : ℕ)^1024*2500000000000000^5551 ≤ 2500001695751133^5551*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000018385016897531 5000000000000000000 2500001695751133 2500000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500001695751133/2500000000000000 : ℝ)) (X := (5000018385016897531/5000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501299201397516563/12500000000000000000 : ℝ) ≤ (10000191724136349/10000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (12501299201397516563/12500000000000000000 : ℝ)^1024 ≤ (10000191724136349/10000000000000000 : ℝ)^5551 := by
      have hnat : (12501299201397516563 : ℕ)^1024*10000000000000000^5551 ≤ 10000191724136349^5551*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501299201397516563 12500000000000000000 10000191724136349 10000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000191724136349/10000000000000000 : ℝ)) (X := (12501299201397516563/12500000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005104880505578597/25000000000000000000 : ℝ) ≤ (5000188332634083/5000000000000000 : ℝ) ^ (5551/1024 : ℝ) := by
    have hpowers : (25005104880505578597/25000000000000000000 : ℝ)^1024 ≤ (5000188332634083/5000000000000000 : ℝ)^5551 := by
      have hnat : (25005104880505578597 : ℕ)^1024*5000000000000000^5551 ≤ 5000188332634083^5551*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005104880505578597 25000000000000000000 5000188332634083 5000000000000000 1024 5551 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000188332634083/5000000000000000 : ℝ)) (X := (25005104880505578597/25000000000000000000 : ℝ)) (by norm_num) 5551 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(18385016897531/10000000000000000000 : ℝ) ≤ ((3694878040938461733/3695000000000000000 : ℝ)+2*(14226240909/73900000000000 : ℝ)*(8749/100000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (3694878040938461733/3695000000000000000 : ℝ)+2*(14226240909/73900000000000 : ℝ)*(8749/100000 : ℝ)=(2500001695751133/2500000000000000 : ℝ) by norm_num, show 1+2*(18385016897531/10000000000000000000 : ℝ)=(5000018385016897531/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5104880505578597/50000000000000000000 : ℝ)+(18385016897531/10000000000000000000 : ℝ) ≤ ((3694878040938461733/3695000000000000000 : ℝ)+(14226240909/73900000000000 : ℝ)*((4589/25000 : ℝ)+(8749/100000 : ℝ)))^(5551/1024 : ℝ) := by
    rw [show (3694878040938461733/3695000000000000000 : ℝ)+(14226240909/73900000000000 : ℝ)*((4589/25000 : ℝ)+(8749/100000 : ℝ))=(10000191724136349/10000000000000000 : ℝ) by norm_num, show 1+(5104880505578597/50000000000000000000 : ℝ)+(18385016897531/10000000000000000000 : ℝ)=(12501299201397516563/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5104880505578597/50000000000000000000 : ℝ) ≤ ((3694878040938461733/3695000000000000000 : ℝ)+2*(14226240909/73900000000000 : ℝ)*(4589/25000 : ℝ))^(5551/1024 : ℝ) := by
    rw [show (3694878040938461733/3695000000000000000 : ℝ)+2*(14226240909/73900000000000 : ℝ)*(4589/25000 : ℝ)=(5000188332634083/5000000000000000 : ℝ) by norm_num, show 1+2*(5104880505578597/50000000000000000000 : ℝ)=(25005104880505578597/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3694878040938461733/3695000000000000000 : ℝ)*(X 1 0+X 2 0)+(14226240909/73900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (8749/100000 : ℝ)) (hi := (4589/25000 : ℝ)) (c := (3694878040938461733/3695000000000000000 : ℝ)) (alpha := (14226240909/73900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3694878040938461733/3695000000000000000 : ℝ)*(X 0 1+X 2 1)+(14226240909/73900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (8749/100000 : ℝ)) (hi := (4589/25000 : ℝ)) (c := (3694878040938461733/3695000000000000000 : ℝ)) (alpha := (14226240909/73900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3694878040938461733/3695000000000000000 : ℝ)*(X 0 2+X 1 2)+(14226240909/73900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5551/1024 : ℝ)) (lo := (8749/100000 : ℝ)) (hi := (4589/25000 : ℝ)) (c := (3694878040938461733/3695000000000000000 : ℝ)) (alpha := (14226240909/73900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-259731793/2000000000 : ℝ)*X 0 0+(137883877/250000000 : ℝ)*X 0 1+(634572507/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672750187/5000000000 : ℝ)*X 1 0+(-764374513/5000000000 : ℝ)*X 1 1+(1269145239/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345502169/10000000000 : ℝ)*X 2 0+(5076578407/10000000000 : ℝ)*X 2 1+(-1528749987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4049002151/10000000000 : ℝ)*X 0 0+(1699813867/5000000000 : ℝ)*X 0 1+(1191245629/2500000000 : ℝ)*X 0 2+(4049002151/10000000000 : ℝ)*X 1 0+(1699813867/5000000000 : ℝ)*X 1 1+(1191245629/2500000000 : ℝ)*X 1 2+(4049002151/10000000000 : ℝ)*X 2 0+(1699813867/5000000000 : ℝ)*X 2 1+(1191245629/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-129903959/1000000000 : ℝ)*X 0 0+(127089219/250000000 : ℝ)*X 0 1+(2754109447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1307215179/2500000000 : ℝ)*X 1 0+(-6856939/62500000 : ℝ)*X 1 1+(5508218979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5228860807/10000000000 : ℝ)*X 2 0+(172131841/312500000 : ℝ)*X 2 1+(-1097110207/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4050186191/10000000000 : ℝ)*X 0 0+(948646991/2000000000 : ℝ)*X 0 1+(3421834859/10000000000 : ℝ)*X 0 2+(4050186191/10000000000 : ℝ)*X 1 0+(948646991/2000000000 : ℝ)*X 1 1+(3421834859/10000000000 : ℝ)*X 1 2+(4050186191/10000000000 : ℝ)*X 2 0+(948646991/2000000000 : ℝ)*X 2 1+(3421834859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1737_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (890542930767999797269398681/92375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1124543243/100000000000000 : ℝ)*(base19) + (884658127/50000000000000 : ℝ)*(base23) + (32216421/50000000000000 : ℝ)*(lower2) + (238698309/50000000000000 : ℝ)*(upper3) + (1754791/12500000000000 : ℝ)*(upper5) + (752876763134881/50000000000000 : ℝ)*(major0) + (752876763134881/50000000000000 : ℝ)*(major1) + (752876763134881/50000000000000 : ℝ)*(major2) + (1139541578520891/50000000000000 : ℝ)*(sp0) + (113954427570127/5000000000000 : ℝ)*(sp1) + (284885988328691/12500000000000 : ℝ)*(sp2) + (366206190625691/50000000000000 : ℝ)*(sp3) + (6518904001/100000000000000 : ℝ)*(sp4) + (186959669/4000000000000 : ℝ)*(sp7) + (732417055243107/100000000000000 : ℝ)*(f.failure) + (1139544837972891/50000000000000 : ℝ)*(f.sum) + (4753935011443/3695000000000000000000000000 : ℝ)*base65 + (835928057193208773/184750000000000000000000000000000 : ℝ)*base67 + (85888809334291227/184750000000000000000000000000000 : ℝ)*base70 + (132199822838291227/184750000000000000000000000000000 : ℝ)*base72 + (5255964367173/3695000000000000000000000000 : ℝ)*base73 + (151748916564208773/184750000000000000000000000000000 : ℝ)*base75 + (679056590909708773/184750000000000000000000000000000 : ℝ)*base77 + (1769868760777208773/184750000000000000000000000000000 : ℝ)*base79 + (6770200271287/3695000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (30258593/10000000000000000000000 : ℝ)*base90 + (30258593/10000000000000000000000 : ℝ)*base92 + (30258593/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19761306139486016144793/3695000000000000000000000000 : ℝ) := by norm_num
    linear_combination (728481297/100000000000000 : ℝ)*(base19) + (818437793/100000000000000 : ℝ)*(base23) + (16726919/12500000000000 : ℝ)*(upper3) + (18654163/100000000000000 : ℝ)*(lower4) + (60280199/50000000000000 : ℝ)*(upper5) + (194478296394997/12500000000000 : ℝ)*(major0) + (194478296394997/12500000000000 : ℝ)*(major1) + (194478296394997/12500000000000 : ℝ)*(major2) + (4944396879/100000000000000 : ℝ)*(sp1) + (5540463127/100000000000000 : ℝ)*(sp2) + (29435993256423/1250000000000 : ℝ)*(sp4) + (147179611727229/6250000000000 : ℝ)*(sp5) + (2354873101612921/100000000000000 : ℝ)*(sp6) + (189193275883853/25000000000000 : ℝ)*(sp7) + (189193275883853/25000000000000 : ℝ)*(f.failure) + (29435993256423/1250000000000 : ℝ)*(f.sum) + (4873865042061/923750000000000000000000000 : ℝ)*base65 + (39317406179549801/46187500000000000000000000000000 : ℝ)*base67 + (72583721747549801/46187500000000000000000000000000 : ℝ)*base69 + (309429342274674801/46187500000000000000000000000000 : ℝ)*base71 + (1203265482893/1847500000000000000000000000 : ℝ)*base74 + (129847334526200199/46187500000000000000000000000000 : ℝ)*base76 + (52477503854075199/46187500000000000000000000000000 : ℝ)*base78 + (140445371076637699/46187500000000000000000000000000 : ℝ)*base80 + (1191651556043/461875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (25790447/2500000000000000000000 : ℝ)*base90 + (25790447/2500000000000000000000 : ℝ)*base92 + (25790447/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1737_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4589/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8749/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1737_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1737_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9117/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1737_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1737_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1737_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5551/1024 : ℝ) ≤ p) (hpb : p ≤ (5567/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (205586901/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8849/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9117/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1737_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
