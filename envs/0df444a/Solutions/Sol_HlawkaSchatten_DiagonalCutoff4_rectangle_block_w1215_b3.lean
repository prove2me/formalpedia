-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:55.099356+00:00
-- url     : https://prove2.me/submissions/ce69143d-43a6-4094-909c-193a6edb76c1

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
theorem support_rectangle_w1215_box_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2007925963/10000000000 : ℝ)*x 0 + (5375244497/10000000000 : ℝ)*x 1 + (5375245057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2007925963/10000000000 : ℝ)^1051 ≤ (5986785347339/50000000000000 : ℝ)^795 := by
    have hnat : (2007925963 : ℕ)^1051*50000000000000^795 ≤ 5986785347339^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007925963 10000000000 5986785347339 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375244497/10000000000 : ℝ)^1051 ≤ (44013211616177/100000000000000 : ℝ)^795 := by
    have hnat : (5375244497 : ℕ)^1051*100000000000000^795 ≤ 44013211616177^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375244497 10000000000 44013211616177 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375245057/10000000000 : ℝ)^1051 ≤ (5501652209759/12500000000000 : ℝ)^795 := by
    have hnat : (5375245057 : ℕ)^1051*12500000000000^795 ≤ 5501652209759^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375245057 10000000000 5501652209759 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2007925963/10000000000 : ℝ), (5375244497/10000000000 : ℝ), (5375245057/10000000000 : ℝ)] ![(5986785347339/50000000000000 : ℝ), (44013211616177/100000000000000 : ℝ), (5501652209759/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2007925963/10000000000 : ℝ)|^1051 ≤ (5986785347339/50000000000000 : ℝ)^795
        have hw : |(-2007925963/10000000000 : ℝ)|=(2007925963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375244497/10000000000 : ℝ)|^1051 ≤ (44013211616177/100000000000000 : ℝ)^795
        have hw : |(5375244497/10000000000 : ℝ)|=(5375244497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375245057/10000000000 : ℝ)|^1051 ≤ (5501652209759/12500000000000 : ℝ)^795
        have hw : |(5375245057/10000000000 : ℝ)|=(5375245057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2648299573/5000000000 : ℝ)*x 0 + (-1057378157/5000000000 : ℝ)*x 1 + (5375244793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648299573/5000000000 : ℝ)^1051 ≤ (2697743904701/6250000000000 : ℝ)^795 := by
    have hnat : (2648299573 : ℕ)^1051*6250000000000^795 ≤ 2697743904701^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648299573 5000000000 2697743904701 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057378157/5000000000 : ℝ)^1051 ≤ (2564576539293/20000000000000 : ℝ)^795 := by
    have hnat : (1057378157 : ℕ)^1051*20000000000000^795 ≤ 2564576539293^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057378157 5000000000 2564576539293 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375244793/10000000000 : ℝ)^1051 ≤ (22006607410161/50000000000000 : ℝ)^795 := by
    have hnat : (5375244793 : ℕ)^1051*50000000000000^795 ≤ 22006607410161^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375244793 10000000000 22006607410161 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648299573/5000000000 : ℝ), (-1057378157/5000000000 : ℝ), (5375244793/10000000000 : ℝ)] ![(2697743904701/6250000000000 : ℝ), (2564576539293/20000000000000 : ℝ), (22006607410161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648299573/5000000000 : ℝ)|^1051 ≤ (2697743904701/6250000000000 : ℝ)^795
        have hw : |(2648299573/5000000000 : ℝ)|=(2648299573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1057378157/5000000000 : ℝ)|^1051 ≤ (2564576539293/20000000000000 : ℝ)^795
        have hw : |(-1057378157/5000000000 : ℝ)|=(1057378157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375244793/10000000000 : ℝ)|^1051 ≤ (22006607410161/50000000000000 : ℝ)^795
        have hw : |(5375244793/10000000000 : ℝ)|=(5375244793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5296599181/10000000000 : ℝ)*x 0 + (5375244613/10000000000 : ℝ)*x 1 + (-2114756509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296599181/10000000000 : ℝ)^1051 ≤ (43163902852291/100000000000000 : ℝ)^795 := by
    have hnat : (5296599181 : ℕ)^1051*100000000000000^795 ≤ 43163902852291^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296599181 10000000000 43163902852291 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375244613/10000000000 : ℝ)^1051 ≤ (8802642574371/20000000000000 : ℝ)^795 := by
    have hnat : (5375244613 : ℕ)^1051*20000000000000^795 ≤ 8802642574371^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375244613 10000000000 8802642574371 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114756509/10000000000 : ℝ)^1051 ≤ (12822884259597/100000000000000 : ℝ)^795 := by
    have hnat : (2114756509 : ℕ)^1051*100000000000000^795 ≤ 12822884259597^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114756509 10000000000 12822884259597 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296599181/10000000000 : ℝ), (5375244613/10000000000 : ℝ), (-2114756509/10000000000 : ℝ)] ![(43163902852291/100000000000000 : ℝ), (8802642574371/20000000000000 : ℝ), (12822884259597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296599181/10000000000 : ℝ)|^1051 ≤ (43163902852291/100000000000000 : ℝ)^795
        have hw : |(5296599181/10000000000 : ℝ)|=(5296599181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375244613/10000000000 : ℝ)|^1051 ≤ (8802642574371/20000000000000 : ℝ)^795
        have hw : |(5375244613/10000000000 : ℝ)|=(5375244613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2114756509/10000000000 : ℝ)|^1051 ≤ (12822884259597/100000000000000 : ℝ)^795
        have hw : |(-2114756509/10000000000 : ℝ)|=(2114756509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4461281717/10000000000 : ℝ)*x 0 + (268947241/625000000 : ℝ)*x 1 + (537894439/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4461281717/10000000000 : ℝ)^1051 ≤ (215011289297/625000000000 : ℝ)^795 := by
    have hnat : (4461281717 : ℕ)^1051*625000000000^795 ≤ 215011289297^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4461281717 10000000000 215011289297 625000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268947241/625000000 : ℝ)^1051 ≤ (32799098579671/100000000000000 : ℝ)^795 := by
    have hnat : (268947241 : ℕ)^1051*100000000000000^795 ≤ 32799098579671^795*625000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268947241 625000000 32799098579671 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537894439/1250000000 : ℝ)^1051 ≤ (32799095113349/100000000000000 : ℝ)^795 := by
    have hnat : (537894439 : ℕ)^1051*100000000000000^795 ≤ 32799095113349^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537894439 1250000000 32799095113349 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4461281717/10000000000 : ℝ), (268947241/625000000 : ℝ), (537894439/1250000000 : ℝ)] ![(215011289297/625000000000 : ℝ), (32799098579671/100000000000000 : ℝ), (32799095113349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4461281717/10000000000 : ℝ)|^1051 ≤ (215011289297/625000000000 : ℝ)^795
        have hw : |(4461281717/10000000000 : ℝ)|=(4461281717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268947241/625000000 : ℝ)|^1051 ≤ (32799098579671/100000000000000 : ℝ)^795
        have hw : |(268947241/625000000 : ℝ)|=(268947241/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537894439/1250000000 : ℝ)|^1051 ≤ (32799095113349/100000000000000 : ℝ)^795
        have hw : |(537894439/1250000000 : ℝ)|=(537894439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1129190197/5000000000 : ℝ)*x 0 + (5282001913/10000000000 : ℝ)*x 1 + (1320500491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1129190197/5000000000 : ℝ)^1051 ≤ (13986583134081/100000000000000 : ℝ)^795 := by
    have hnat : (1129190197 : ℕ)^1051*100000000000000^795 ≤ 13986583134081^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129190197 5000000000 13986583134081 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282001913/10000000000 : ℝ)^1051 ≤ (21503354076999/50000000000000 : ℝ)^795 := by
    have hnat : (5282001913 : ℕ)^1051*50000000000000^795 ≤ 21503354076999^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282001913 10000000000 21503354076999 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320500491/2500000000 : ℝ)^1051 ≤ (43006708702961/100000000000000 : ℝ)^795 := by
    have hnat : (1320500491 : ℕ)^1051*100000000000000^795 ≤ 43006708702961^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320500491 2500000000 43006708702961 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1129190197/5000000000 : ℝ), (5282001913/10000000000 : ℝ), (1320500491/2500000000 : ℝ)] ![(13986583134081/100000000000000 : ℝ), (21503354076999/50000000000000 : ℝ), (43006708702961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1129190197/5000000000 : ℝ)|^1051 ≤ (13986583134081/100000000000000 : ℝ)^795
        have hw : |(-1129190197/5000000000 : ℝ)|=(1129190197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282001913/10000000000 : ℝ)|^1051 ≤ (21503354076999/50000000000000 : ℝ)^795
        have hw : |(5282001913/10000000000 : ℝ)|=(5282001913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320500491/2500000000 : ℝ)|^1051 ≤ (43006708702961/100000000000000 : ℝ)^795
        have hw : |(1320500491/2500000000 : ℝ)|=(1320500491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2681184183/5000000000 : ℝ)*x 0 + (-430328951/2000000000 : ℝ)*x 1 + (2641000877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681184183/5000000000 : ℝ)^1051 ≤ (21936941842643/50000000000000 : ℝ)^795 := by
    have hnat : (2681184183 : ℕ)^1051*50000000000000^795 ≤ 21936941842643^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681184183 5000000000 21936941842643 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (430328951/2000000000 : ℝ)^1051 ≤ (13119409850599/100000000000000 : ℝ)^795 := by
    have hnat : (430328951 : ℕ)^1051*100000000000000^795 ≤ 13119409850599^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430328951 2000000000 13119409850599 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641000877/5000000000 : ℝ)^1051 ≤ (10751676610631/25000000000000 : ℝ)^795 := by
    have hnat : (2641000877 : ℕ)^1051*25000000000000^795 ≤ 10751676610631^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641000877 5000000000 10751676610631 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681184183/5000000000 : ℝ), (-430328951/2000000000 : ℝ), (2641000877/5000000000 : ℝ)] ![(21936941842643/50000000000000 : ℝ), (13119409850599/100000000000000 : ℝ), (10751676610631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681184183/5000000000 : ℝ)|^1051 ≤ (21936941842643/50000000000000 : ℝ)^795
        have hw : |(2681184183/5000000000 : ℝ)|=(2681184183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-430328951/2000000000 : ℝ)|^1051 ≤ (13119409850599/100000000000000 : ℝ)^795
        have hw : |(-430328951/2000000000 : ℝ)|=(430328951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641000877/5000000000 : ℝ)|^1051 ≤ (10751676610631/25000000000000 : ℝ)^795
        have hw : |(2641000877/5000000000 : ℝ)|=(2641000877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1072473581/2000000000 : ℝ)*x 0 + (5282002101/10000000000 : ℝ)*x 1 + (-2151644911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072473581/2000000000 : ℝ)^1051 ≤ (438738786989/1000000000000 : ℝ)^795 := by
    have hnat : (1072473581 : ℕ)^1051*1000000000000^795 ≤ 438738786989^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072473581 2000000000 438738786989 1000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282002101/10000000000 : ℝ)^1051 ≤ (10751677544407/25000000000000 : ℝ)^795 := by
    have hnat : (5282002101 : ℕ)^1051*25000000000000^795 ≤ 10751677544407^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282002101 10000000000 10751677544407 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2151644911/10000000000 : ℝ)^1051 ≤ (1639926388511/12500000000000 : ℝ)^795 := by
    have hnat : (2151644911 : ℕ)^1051*12500000000000^795 ≤ 1639926388511^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151644911 10000000000 1639926388511 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072473581/2000000000 : ℝ), (5282002101/10000000000 : ℝ), (-2151644911/10000000000 : ℝ)] ![(438738786989/1000000000000 : ℝ), (10751677544407/25000000000000 : ℝ), (1639926388511/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072473581/2000000000 : ℝ)|^1051 ≤ (438738786989/1000000000000 : ℝ)^795
        have hw : |(1072473581/2000000000 : ℝ)|=(1072473581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282002101/10000000000 : ℝ)|^1051 ≤ (10751677544407/25000000000000 : ℝ)^795
        have hw : |(5282002101/10000000000 : ℝ)|=(5282002101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2151644911/10000000000 : ℝ)|^1051 ≤ (1639926388511/12500000000000 : ℝ)^795
        have hw : |(-2151644911/10000000000 : ℝ)|=(2151644911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2123654969/5000000000 : ℝ)*x 0 + (441012131/1000000000 : ℝ)*x 1 + (2205060627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2123654969/5000000000 : ℝ)^1051 ≤ (32237545576547/100000000000000 : ℝ)^795 := by
    have hnat : (2123654969 : ℕ)^1051*100000000000000^795 ≤ 32237545576547^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123654969 5000000000 32237545576547 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441012131/1000000000 : ℝ)^1051 ≤ (2117576718043/6250000000000 : ℝ)^795 := by
    have hnat : (441012131 : ℕ)^1051*6250000000000^795 ≤ 2117576718043^795*1000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441012131 1000000000 2117576718043 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205060627/5000000000 : ℝ)^1051 ≤ (8470306729981/25000000000000 : ℝ)^795 := by
    have hnat : (2205060627 : ℕ)^1051*25000000000000^795 ≤ 8470306729981^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205060627 5000000000 8470306729981 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2123654969/5000000000 : ℝ), (441012131/1000000000 : ℝ), (2205060627/5000000000 : ℝ)] ![(32237545576547/100000000000000 : ℝ), (2117576718043/6250000000000 : ℝ), (8470306729981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2123654969/5000000000 : ℝ)|^1051 ≤ (32237545576547/100000000000000 : ℝ)^795
        have hw : |(2123654969/5000000000 : ℝ)|=(2123654969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441012131/1000000000 : ℝ)|^1051 ≤ (2117576718043/6250000000000 : ℝ)^795
        have hw : |(441012131/1000000000 : ℝ)|=(441012131/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2205060627/5000000000 : ℝ)|^1051 ≤ (8470306729981/25000000000000 : ℝ)^795
        have hw : |(2205060627/5000000000 : ℝ)|=(2205060627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_8 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2205926557/10000000000 : ℝ)*x 0 + (5218450249/10000000000 : ℝ)*x 1 + (2692428697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2205926557/10000000000 : ℝ)^1051 ≤ (13558733051029/100000000000000 : ℝ)^795 := by
    have hnat : (2205926557 : ℕ)^1051*100000000000000^795 ≤ 13558733051029^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205926557 10000000000 13558733051029 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218450249/10000000000 : ℝ)^1051 ≤ (21161983774441/50000000000000 : ℝ)^795 := by
    have hnat : (5218450249 : ℕ)^1051*50000000000000^795 ≤ 21161983774441^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218450249 10000000000 21161983774441 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692428697/5000000000 : ℝ)^1051 ≤ (44117299383821/100000000000000 : ℝ)^795 := by
    have hnat : (2692428697 : ℕ)^1051*100000000000000^795 ≤ 44117299383821^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692428697 5000000000 44117299383821 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2205926557/10000000000 : ℝ), (5218450249/10000000000 : ℝ), (2692428697/5000000000 : ℝ)] ![(13558733051029/100000000000000 : ℝ), (21161983774441/50000000000000 : ℝ), (44117299383821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2205926557/10000000000 : ℝ)|^1051 ≤ (13558733051029/100000000000000 : ℝ)^795
        have hw : |(-2205926557/10000000000 : ℝ)|=(2205926557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218450249/10000000000 : ℝ)|^1051 ≤ (21161983774441/50000000000000 : ℝ)^795
        have hw : |(5218450249/10000000000 : ℝ)|=(5218450249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692428697/5000000000 : ℝ)|^1051 ≤ (44117299383821/100000000000000 : ℝ)^795
        have hw : |(2692428697/5000000000 : ℝ)|=(2692428697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_9 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5289816327/10000000000 : ℝ)*x 0 + (-2110885083/10000000000 : ℝ)*x 1 + (5384857239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289816327/10000000000 : ℝ)^1051 ≤ (2154542122381/5000000000000 : ℝ)^795 := by
    have hnat : (5289816327 : ℕ)^1051*5000000000000^795 ≤ 2154542122381^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289816327 10000000000 2154542122381 5000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2110885083/10000000000 : ℝ)^1051 ≤ (3197964957211/25000000000000 : ℝ)^795 := by
    have hnat : (2110885083 : ℕ)^1051*25000000000000^795 ≤ 3197964957211^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110885083 10000000000 3197964957211 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384857239/10000000000 : ℝ)^1051 ≤ (4411729770501/10000000000000 : ℝ)^795 := by
    have hnat : (5384857239 : ℕ)^1051*10000000000000^795 ≤ 4411729770501^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384857239 10000000000 4411729770501 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289816327/10000000000 : ℝ), (-2110885083/10000000000 : ℝ), (5384857239/10000000000 : ℝ)] ![(2154542122381/5000000000000 : ℝ), (3197964957211/25000000000000 : ℝ), (4411729770501/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289816327/10000000000 : ℝ)|^1051 ≤ (2154542122381/5000000000000 : ℝ)^795
        have hw : |(5289816327/10000000000 : ℝ)|=(5289816327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2110885083/10000000000 : ℝ)|^1051 ≤ (3197964957211/25000000000000 : ℝ)^795
        have hw : |(-2110885083/10000000000 : ℝ)|=(2110885083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384857239/10000000000 : ℝ)|^1051 ≤ (4411729770501/10000000000000 : ℝ)^795
        have hw : |(5384857239/10000000000 : ℝ)|=(5384857239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_10 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1057963271/2000000000 : ℝ)*x 0 + (2692428119/5000000000 : ℝ)*x 1 + (-164913/781250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057963271/2000000000 : ℝ)^1051 ≤ (8618168549831/20000000000000 : ℝ)^795 := by
    have hnat : (1057963271 : ℕ)^1051*20000000000000^795 ≤ 8618168549831^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057963271 2000000000 8618168549831 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2692428119/5000000000 : ℝ)^1051 ≤ (8823457372627/20000000000000 : ℝ)^795 := by
    have hnat : (2692428119 : ℕ)^1051*20000000000000^795 ≤ 8823457372627^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692428119 5000000000 8823457372627 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164913/781250 : ℝ)^1051 ≤ (1598983797471/12500000000000 : ℝ)^795 := by
    have hnat : (164913 : ℕ)^1051*12500000000000^795 ≤ 1598983797471^795*781250^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164913 781250 1598983797471 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057963271/2000000000 : ℝ), (2692428119/5000000000 : ℝ), (-164913/781250 : ℝ)] ![(8618168549831/20000000000000 : ℝ), (8823457372627/20000000000000 : ℝ), (1598983797471/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057963271/2000000000 : ℝ)|^1051 ≤ (8618168549831/20000000000000 : ℝ)^795
        have hw : |(1057963271/2000000000 : ℝ)|=(1057963271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2692428119/5000000000 : ℝ)|^1051 ≤ (8823457372627/20000000000000 : ℝ)^795
        have hw : |(2692428119/5000000000 : ℝ)|=(2692428119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-164913/781250 : ℝ)|^1051 ≤ (1598983797471/12500000000000 : ℝ)^795
        have hw : |(-164913/781250 : ℝ)|=(164913/781250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_11 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4483067179/10000000000 : ℝ)*x 0 + (858424449/2000000000 : ℝ)*x 1 + (21460613/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4483067179/10000000000 : ℝ)^1051 ≤ (17312034063663/50000000000000 : ℝ)^795 := by
    have hnat : (4483067179 : ℕ)^1051*50000000000000^795 ≤ 17312034063663^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483067179 10000000000 17312034063663 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858424449/2000000000 : ℝ)^1051 ≤ (6537592828413/20000000000000 : ℝ)^795 := by
    have hnat : (858424449 : ℕ)^1051*20000000000000^795 ≤ 6537592828413^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858424449 2000000000 6537592828413 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21460613/50000000 : ℝ)^1051 ≤ (2042997982267/6250000000000 : ℝ)^795 := by
    have hnat : (21460613 : ℕ)^1051*6250000000000^795 ≤ 2042997982267^795*50000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21460613 50000000 2042997982267 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4483067179/10000000000 : ℝ), (858424449/2000000000 : ℝ), (21460613/50000000 : ℝ)] ![(17312034063663/50000000000000 : ℝ), (6537592828413/20000000000000 : ℝ), (2042997982267/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4483067179/10000000000 : ℝ)|^1051 ≤ (17312034063663/50000000000000 : ℝ)^795
        have hw : |(4483067179/10000000000 : ℝ)|=(4483067179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(858424449/2000000000 : ℝ)|^1051 ≤ (6537592828413/20000000000000 : ℝ)^795
        have hw : |(858424449/2000000000 : ℝ)|=(858424449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21460613/50000000 : ℝ)|^1051 ≤ (2042997982267/6250000000000 : ℝ)^795
        have hw : |(21460613/50000000 : ℝ)|=(21460613/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_12 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060655281/10000000000 : ℝ)*x 0 + (5437569349/10000000000 : ℝ)*x 1 + (5273932917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060655281/10000000000 : ℝ)^1051 ≤ (6195501171619/50000000000000 : ℝ)^795 := by
    have hnat : (2060655281 : ℕ)^1051*50000000000000^795 ≤ 6195501171619^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060655281 10000000000 6195501171619 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437569349/10000000000 : ℝ)^1051 ≤ (8937824540503/20000000000000 : ℝ)^795 := by
    have hnat : (5437569349 : ℕ)^1051*20000000000000^795 ≤ 8937824540503^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437569349 10000000000 8937824540503 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273932917/10000000000 : ℝ)^1051 ≤ (21459937470983/50000000000000 : ℝ)^795 := by
    have hnat : (5273932917 : ℕ)^1051*50000000000000^795 ≤ 21459937470983^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273932917 10000000000 21459937470983 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060655281/10000000000 : ℝ), (5437569349/10000000000 : ℝ), (5273932917/10000000000 : ℝ)] ![(6195501171619/50000000000000 : ℝ), (8937824540503/20000000000000 : ℝ), (21459937470983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060655281/10000000000 : ℝ)|^1051 ≤ (6195501171619/50000000000000 : ℝ)^795
        have hw : |(-2060655281/10000000000 : ℝ)|=(2060655281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437569349/10000000000 : ℝ)|^1051 ≤ (8937824540503/20000000000000 : ℝ)^795
        have hw : |(5437569349/10000000000 : ℝ)|=(5437569349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273932917/10000000000 : ℝ)|^1051 ≤ (21459937470983/50000000000000 : ℝ)^795
        have hw : |(5273932917/10000000000 : ℝ)|=(5273932917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_13 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (13420143/25000000 : ℝ)*x 0 + (-2154780949/10000000000 : ℝ)*x 1 + (5273933079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13420143/25000000 : ℝ)^1051 ≤ (43935427220683/100000000000000 : ℝ)^795 := by
    have hnat : (13420143 : ℕ)^1051*100000000000000^795 ≤ 43935427220683^795*25000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13420143 25000000 43935427220683 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2154780949/10000000000 : ℝ)^1051 ≤ (13144696082233/100000000000000 : ℝ)^795 := by
    have hnat : (2154780949 : ℕ)^1051*100000000000000^795 ≤ 13144696082233^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154780949 10000000000 13144696082233 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5273933079/10000000000 : ℝ)^1051 ≤ (21459938342437/50000000000000 : ℝ)^795 := by
    have hnat : (5273933079 : ℕ)^1051*50000000000000^795 ≤ 21459938342437^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273933079 10000000000 21459938342437 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13420143/25000000 : ℝ), (-2154780949/10000000000 : ℝ), (5273933079/10000000000 : ℝ)] ![(43935427220683/100000000000000 : ℝ), (13144696082233/100000000000000 : ℝ), (21459938342437/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13420143/25000000 : ℝ)|^1051 ≤ (43935427220683/100000000000000 : ℝ)^795
        have hw : |(13420143/25000000 : ℝ)|=(13420143/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2154780949/10000000000 : ℝ)|^1051 ≤ (13144696082233/100000000000000 : ℝ)^795
        have hw : |(-2154780949/10000000000 : ℝ)|=(2154780949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5273933079/10000000000 : ℝ)|^1051 ≤ (21459938342437/50000000000000 : ℝ)^795
        have hw : |(5273933079/10000000000 : ℝ)|=(5273933079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_14 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (536805771/1000000000 : ℝ)*x 0 + (5273932887/10000000000 : ℝ)*x 1 + (-2154780521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536805771/1000000000 : ℝ)^1051 ≤ (549192909237/1250000000000 : ℝ)^795 := by
    have hnat : (536805771 : ℕ)^1051*1250000000000^795 ≤ 549192909237^795*1000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536805771 1000000000 549192909237 1250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273932887/10000000000 : ℝ)^1051 ≤ (21459937309603/50000000000000 : ℝ)^795 := by
    have hnat : (5273932887 : ℕ)^1051*50000000000000^795 ≤ 21459937309603^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273932887 10000000000 21459937309603 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2154780521/10000000000 : ℝ)^1051 ≤ (13144692630583/100000000000000 : ℝ)^795 := by
    have hnat : (2154780521 : ℕ)^1051*100000000000000^795 ≤ 13144692630583^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154780521 10000000000 13144692630583 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536805771/1000000000 : ℝ), (5273932887/10000000000 : ℝ), (-2154780521/10000000000 : ℝ)] ![(549192909237/1250000000000 : ℝ), (21459937309603/50000000000000 : ℝ), (13144692630583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536805771/1000000000 : ℝ)|^1051 ≤ (549192909237/1250000000000 : ℝ)^795
        have hw : |(536805771/1000000000 : ℝ)|=(536805771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273932887/10000000000 : ℝ)|^1051 ≤ (21459937309603/50000000000000 : ℝ)^795
        have hw : |(5273932887/10000000000 : ℝ)|=(5273932887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2154780521/10000000000 : ℝ)|^1051 ≤ (13144692630583/100000000000000 : ℝ)^795
        have hw : |(-2154780521/10000000000 : ℝ)|=(2154780521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_box_15 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1057140277/2500000000 : ℝ)*x 0 + (2209686841/5000000000 : ℝ)*x 1 + (2209686277/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057140277/2500000000 : ℝ)^1051 ≤ (32049549541211/100000000000000 : ℝ)^795 := by
    have hnat : (1057140277 : ℕ)^1051*100000000000000^795 ≤ 32049549541211^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057140277 2500000000 32049549541211 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209686841/5000000000 : ℝ)^1051 ≤ (8493807739327/25000000000000 : ℝ)^795 := by
    have hnat : (2209686841 : ℕ)^1051*25000000000000^795 ≤ 8493807739327^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209686841 5000000000 8493807739327 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209686277/5000000000 : ℝ)^1051 ≤ (424690243663/1250000000000 : ℝ)^795 := by
    have hnat : (2209686277 : ℕ)^1051*1250000000000^795 ≤ 424690243663^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209686277 5000000000 424690243663 1250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057140277/2500000000 : ℝ), (2209686841/5000000000 : ℝ), (2209686277/5000000000 : ℝ)] ![(32049549541211/100000000000000 : ℝ), (8493807739327/25000000000000 : ℝ), (424690243663/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057140277/2500000000 : ℝ)|^1051 ≤ (32049549541211/100000000000000 : ℝ)^795
        have hw : |(1057140277/2500000000 : ℝ)|=(1057140277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2209686841/5000000000 : ℝ)|^1051 ≤ (8493807739327/25000000000000 : ℝ)^795
        have hw : |(2209686841/5000000000 : ℝ)|=(2209686841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209686277/5000000000 : ℝ)|^1051 ≤ (424690243663/1250000000000 : ℝ)^795
        have hw : |(2209686277/5000000000 : ℝ)|=(2209686277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31121/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14839/25000 : ℝ) ∧ (80029/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83287/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5723/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5723/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5723/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5723/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5723/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5723/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5723/50000 : ℝ) ^ (8407/2048 : ℝ) ≤ (13670739092454649/100000000000000000000 : ℝ) := by
    have hpowers : (5723/50000 : ℝ)^8407 ≤ (13670739092454649/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5723 : ℕ)^8407*100000000000000000000^2048 ≤ 13670739092454649^2048*50000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5723 50000 13670739092454649 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5723/50000 : ℝ)) (X := (13670739092454649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14089/100000 : ℝ) ^ (8407/2048 : ℝ) ≤ (1603761272808339/5000000000000000000 : ℝ) := by
    have hpowers : (14089/100000 : ℝ)^8407 ≤ (1603761272808339/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14089 : ℕ)^8407*5000000000000000000^2048 ≤ 1603761272808339^2048*100000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14089 100000 1603761272808339 5000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14089/100000 : ℝ)) (X := (1603761272808339/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013670739092454649/50000000000000000000 : ℝ) ≤ (10000665987368551/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50013670739092454649/50000000000000000000 : ℝ)^2048 ≤ (10000665987368551/10000000000000000 : ℝ)^8407 := by
      have hnat : (50013670739092454649 : ℕ)^2048*10000000000000000^8407 ≤ 10000665987368551^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013670739092454649 50000000000000000000 10000665987368551 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665987368551/10000000000000000 : ℝ)) (X := (50013670739092454649/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045745964548621429/100000000000000000000 : ℝ) ≤ (10001114208764649/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (100045745964548621429/100000000000000000000 : ℝ)^2048 ≤ (10001114208764649/10000000000000000 : ℝ)^8407 := by
      have hnat : (100045745964548621429 : ℕ)^2048*10000000000000000^8407 ≤ 10001114208764649^8407*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045745964548621429 100000000000000000000 10001114208764649 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001114208764649/10000000000000000 : ℝ)) (X := (100045745964548621429/100000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501603761272808339/2500000000000000000 : ℝ) ≤ (10001562430160747/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (2501603761272808339/2500000000000000000 : ℝ)^2048 ≤ (10001562430160747/10000000000000000 : ℝ)^8407 := by
      have hnat : (2501603761272808339 : ℕ)^2048*10000000000000000^8407 ≤ 10001562430160747^8407*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501603761272808339 2500000000000000000 10001562430160747 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001562430160747/10000000000000000 : ℝ)) (X := (2501603761272808339/2500000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13670739092454649/100000000000000000000 : ℝ) ≤ ((26421499520415604877/26430000000000000000 : ℝ)+2*(224110698049/132150000000000 : ℝ)*(5723/50000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (26421499520415604877/26430000000000000000 : ℝ)+2*(224110698049/132150000000000 : ℝ)*(5723/50000 : ℝ)=(10000665987368551/10000000000000000 : ℝ) by norm_num, show 1+2*(13670739092454649/100000000000000000000 : ℝ)=(50013670739092454649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1603761272808339/5000000000000000000 : ℝ)+(13670739092454649/100000000000000000000 : ℝ) ≤ ((26421499520415604877/26430000000000000000 : ℝ)+(224110698049/132150000000000 : ℝ)*((14089/100000 : ℝ)+(5723/50000 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (26421499520415604877/26430000000000000000 : ℝ)+(224110698049/132150000000000 : ℝ)*((14089/100000 : ℝ)+(5723/50000 : ℝ))=(10001114208764649/10000000000000000 : ℝ) by norm_num, show 1+(1603761272808339/5000000000000000000 : ℝ)+(13670739092454649/100000000000000000000 : ℝ)=(100045745964548621429/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1603761272808339/5000000000000000000 : ℝ) ≤ ((26421499520415604877/26430000000000000000 : ℝ)+2*(224110698049/132150000000000 : ℝ)*(14089/100000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (26421499520415604877/26430000000000000000 : ℝ)+2*(224110698049/132150000000000 : ℝ)*(14089/100000 : ℝ)=(10001562430160747/10000000000000000 : ℝ) by norm_num, show 1+2*(1603761272808339/5000000000000000000 : ℝ)=(2501603761272808339/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26421499520415604877/26430000000000000000 : ℝ)*(X 1 0+X 2 0)+(224110698049/132150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (5723/50000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (26421499520415604877/26430000000000000000 : ℝ)) (alpha := (224110698049/132150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26421499520415604877/26430000000000000000 : ℝ)*(X 0 1+X 2 1)+(224110698049/132150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (5723/50000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (26421499520415604877/26430000000000000000 : ℝ)) (alpha := (224110698049/132150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26421499520415604877/26430000000000000000 : ℝ)*(X 0 2+X 1 2)+(224110698049/132150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (5723/50000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (26421499520415604877/26430000000000000000 : ℝ)) (alpha := (224110698049/132150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2007925963/10000000000 : ℝ)*X 0 0+(5375244497/10000000000 : ℝ)*X 0 1+(5375245057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648299573/5000000000 : ℝ)*X 1 0+(-1057378157/5000000000 : ℝ)*X 1 1+(5375244793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296599181/10000000000 : ℝ)*X 2 0+(5375244613/10000000000 : ℝ)*X 2 1+(-2114756509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4461281717/10000000000 : ℝ)*X 0 0+(268947241/625000000 : ℝ)*X 0 1+(537894439/1250000000 : ℝ)*X 0 2+(4461281717/10000000000 : ℝ)*X 1 0+(268947241/625000000 : ℝ)*X 1 1+(537894439/1250000000 : ℝ)*X 1 2+(4461281717/10000000000 : ℝ)*X 2 0+(268947241/625000000 : ℝ)*X 2 1+(537894439/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1129190197/5000000000 : ℝ)*X 0 0+(5282001913/10000000000 : ℝ)*X 0 1+(1320500491/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2681184183/5000000000 : ℝ)*X 1 0+(-430328951/2000000000 : ℝ)*X 1 1+(2641000877/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1072473581/2000000000 : ℝ)*X 2 0+(5282002101/10000000000 : ℝ)*X 2 1+(-2151644911/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2123654969/5000000000 : ℝ)*X 0 0+(441012131/1000000000 : ℝ)*X 0 1+(2205060627/5000000000 : ℝ)*X 0 2+(2123654969/5000000000 : ℝ)*X 1 0+(441012131/1000000000 : ℝ)*X 1 1+(2205060627/5000000000 : ℝ)*X 1 2+(2123654969/5000000000 : ℝ)*X 2 0+(441012131/1000000000 : ℝ)*X 2 1+(2205060627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2205926557/10000000000 : ℝ)*X 0 0+(5218450249/10000000000 : ℝ)*X 0 1+(2692428697/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289816327/10000000000 : ℝ)*X 1 0+(-2110885083/10000000000 : ℝ)*X 1 1+(5384857239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1057963271/2000000000 : ℝ)*X 2 0+(2692428119/5000000000 : ℝ)*X 2 1+(-164913/781250 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4483067179/10000000000 : ℝ)*X 0 0+(858424449/2000000000 : ℝ)*X 0 1+(21460613/50000000 : ℝ)*X 0 2+(4483067179/10000000000 : ℝ)*X 1 0+(858424449/2000000000 : ℝ)*X 1 1+(21460613/50000000 : ℝ)*X 1 2+(4483067179/10000000000 : ℝ)*X 2 0+(858424449/2000000000 : ℝ)*X 2 1+(21460613/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2060655281/10000000000 : ℝ)*X 0 0+(5437569349/10000000000 : ℝ)*X 0 1+(5273932917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((13420143/25000000 : ℝ)*X 1 0+(-2154780949/10000000000 : ℝ)*X 1 1+(5273933079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((536805771/1000000000 : ℝ)*X 2 0+(5273932887/10000000000 : ℝ)*X 2 1+(-2154780521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1057140277/2500000000 : ℝ)*X 0 0+(2209686841/5000000000 : ℝ)*X 0 1+(2209686277/5000000000 : ℝ)*X 0 2+(1057140277/2500000000 : ℝ)*X 1 0+(2209686841/5000000000 : ℝ)*X 1 1+(2209686277/5000000000 : ℝ)*X 1 2+(1057140277/2500000000 : ℝ)*X 2 0+(2209686841/5000000000 : ℝ)*X 2 1+(2209686277/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31121/50000 : ℝ) ≤ (-6854091736510956512901969822649/11012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (140722541/100000000000000 : ℝ)*(upper1) + (219379019/100000000000000 : ℝ)*(lower4) + (27689999/100000000000000 : ℝ)*(upper5) + (199053792266363/5000000000000 : ℝ)*(major0) + (199053792266363/5000000000000 : ℝ)*(major1) + (199053792266363/5000000000000 : ℝ)*(major2) + (1370829359/20000000000000 : ℝ)*(sp3) + (167021142956943/3125000000000 : ℝ)*(sp4) + (2672320636124167/50000000000000 : ℝ)*(sp5) + (5344593806431147/100000000000000 : ℝ)*(sp6) + (164888393410731/6250000000000 : ℝ)*(sp7) + (18340949/5000000000000 : ℝ)*(sp12) + (35669192823/100000000000000 : ℝ)*(sp13) + (8313501001/10000000000000 : ℝ)*(sp14) + (263822114871849/10000000000000 : ℝ)*(f.failure) + (5344676941441157/100000000000000 : ℝ)*(f.sum) + (12439599734081/2643000000000000000000000000 : ℝ)*base66 + (226565786410947649/132150000000000000000000000000000 : ℝ)*base68 + (637372878595052351/132150000000000000000000000000000 : ℝ)*base69 + (2057418101776797649/132150000000000000000000000000000 : ℝ)*base72 + (9865040071073/2643000000000000000000000000 : ℝ)*base74 + (1049964775962297649/132150000000000000000000000000000 : ℝ)*base76 + (1891112122632447649/132150000000000000000000000000000 : ℝ)*base78 + (942207197400297649/132150000000000000000000000000000 : ℝ)*base80 + (1965599287/845760000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2308151/200000000000000000000 : ℝ)*base90 + (2308151/200000000000000000000 : ℝ)*base92 + (2308151/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (14839/25000 : ℝ) ≤ (16342071687302920031710471778521/27531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82767351/100000000000000 : ℝ)*(upper1) + (57502811/25000000000000 : ℝ)*(upper2) + (7877181/6250000000000 : ℝ)*(upper3) + (697537/400000000000 : ℝ)*(upper4) + (10785853/20000000000000 : ℝ)*(upper5) + (505802566613677/12500000000000 : ℝ)*(major0) + (505802566613677/12500000000000 : ℝ)*(major1) + (505802566613677/12500000000000 : ℝ)*(major2) + (5391512205749009/100000000000000 : ℝ)*(sp0) + (107830610515199/2000000000000 : ℝ)*(sp1) + (5391420693438957/100000000000000 : ℝ)*(sp2) + (1340762226253543/50000000000000 : ℝ)*(sp3) + (109832320993/100000000000000 : ℝ)*(sp10) + (916000547/5000000000000 : ℝ)*(sp12) + (1340762226253543/50000000000000 : ℝ)*(f.failure) + (107830610515199/2000000000000 : ℝ)*(f.sum) + (112461095094943/13215000000000000000000000000 : ℝ)*base65 + (2726572642919827729/330375000000000000000000000000000 : ℝ)*base67 + (1240895635823827729/330375000000000000000000000000000 : ℝ)*base69 + (2232225191799952729/330375000000000000000000000000000 : ℝ)*base71 + (14807043729457/3303750000000000000000000000 : ℝ)*base73 + (1973464753182547271/330375000000000000000000000000000 : ℝ)*base76 + (6880623896727952729/330375000000000000000000000000000 : ℝ)*base77 + (32740669019077729/330375000000000000000000000000000 : ℝ)*base79 + (70018098457817/13215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (6006457/1000000000000000000000 : ℝ)*base90 + (6006457/1000000000000000000000 : ℝ)*base92 + (6006457/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80029/100000 : ℝ) ≤ (176268788683135108586829987/220250000000000000000000000 : ℝ) := by norm_num
    linear_combination (162370997/25000000000000 : ℝ)*(upper0) + (316292957/100000000000000 : ℝ)*(upper1) + (86863073/25000000000000 : ℝ)*(upper2) + (810531949/100000000000000 : ℝ)*(lower5) + (180541582212257/4000000000000 : ℝ)*(major0) + (180541582212257/4000000000000 : ℝ)*(major1) + (180541582212257/4000000000000 : ℝ)*(major2) + (537060467763/100000000000000 : ℝ)*(sp1) + (71885298027/100000000000000 : ℝ)*(sp3) + (890503579/3125000000000 : ℝ)*(sp4) + (3004646872691561/50000000000000 : ℝ)*(sp8) + (6008785181029887/100000000000000 : ℝ)*(sp9) + (6009322241497649/100000000000000 : ℝ)*(sp10) + (299100790645309/10000000000000 : ℝ)*(sp11) + (2991079791751117/100000000000000 : ℝ)*(f.failure) + (6009322241497649/100000000000000 : ℝ)*(f.sum) + (6091842979361/2643000000000000000000000000 : ℝ)*base65 + (912780103917902611/105720000000000000000000000000000 : ℝ)*base68 + (478751648920497389/105720000000000000000000000000000 : ℝ)*base69 + (788340085062542611/105720000000000000000000000000000 : ℝ)*base72 + (10519313388293/2643000000000000000000000000 : ℝ)*base73 + (1475905544206257389/105720000000000000000000000000000 : ℝ)*base75 + (3935104445102611/105720000000000000000000000000000 : ℝ)*base78 + (977959190567697389/105720000000000000000000000000000 : ℝ)*base79 + (5278906634449/1321500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (2811117/2000000000000000000000 : ℝ)*base89 + (2811117/2000000000000000000000 : ℝ)*base91 + (2811117/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83287/100000 : ℝ) ≤ (-3668661423480932011480914549/4405000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93866123/50000000000000 : ℝ)*(lower0) + (100122511/100000000000000 : ℝ)*(upper1) + (155832457/50000000000000 : ℝ)*(lower2) + (9724741/5000000000000 : ℝ)*(upper3) + (201945633/50000000000000 : ℝ)*(upper5) + (2274460548998623/50000000000000 : ℝ)*(major0) + (2274460548998623/50000000000000 : ℝ)*(major1) + (2274460548998623/50000000000000 : ℝ)*(major2) + (286721141/5000000000000 : ℝ)*(sp4) + (244671867697/100000000000000 : ℝ)*(sp7) + (6111071000140137/100000000000000 : ℝ)*(sp12) + (6111076734562957/100000000000000 : ℝ)*(sp13) + (6111076734562957/100000000000000 : ℝ)*(sp14) + (1507141066077717/50000000000000 : ℝ)*(sp15) + (753631701005783/25000000000000 : ℝ)*(f.failure) + (6111076734562957/100000000000000 : ℝ)*(f.sum) + (69066016840693/13215000000000000000000000000 : ℝ)*base65 + (29057547668226015629/1321500000000000000000000000000000 : ℝ)*base68 + (12031624465055984371/1321500000000000000000000000000000 : ℝ)*base69 + (2108260975156515629/1321500000000000000000000000000000 : ℝ)*base72 + (80440487355133/13215000000000000000000000000 : ℝ)*base73 + (6134701026765015629/1321500000000000000000000000000000 : ℝ)*base76 + (4992015710338484371/1321500000000000000000000000000000 : ℝ)*base77 + (50698213175174984371/1321500000000000000000000000000000 : ℝ)*base79 + (5154301821553/13215000000000000000000000000 : ℝ)*base81 + (1945783/500000000000000000000 : ℝ)*base89 + (1945783/500000000000000000000 : ℝ)*base91 + (1945783/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1215_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14839/25000 : ℝ) else (80029/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83287/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1215_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1215_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14839/25000 : ℝ) else (80029/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83287/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1215_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5723/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31121/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(14839/25000 : ℝ) else (80029/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83287/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
