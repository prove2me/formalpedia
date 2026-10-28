-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:49.538806+00:00
-- url     : https://prove2.me/submissions/2ea8dd3a-0084-49c7-82f0-ca78bf205bb1

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
theorem support_rectangle_w1230_s0_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-372853687/2000000000 : ℝ)*x 0 + (301710697/500000000 : ℝ)*x 1 + (958300003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372853687/2000000000 : ℝ)^8423 ≤ (2173630425251/20000000000000 : ℝ)^6375 := by
    have hnat : (372853687 : ℕ)^8423*20000000000000^6375 ≤ 2173630425251^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372853687 2000000000 2173630425251 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301710697/500000000 : ℝ)^8423 ≤ (12825787441311/25000000000000 : ℝ)^6375 := by
    have hnat : (301710697 : ℕ)^8423*25000000000000^6375 ≤ 12825787441311^6375*500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301710697 500000000 12825787441311 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958300003/2000000000 : ℝ)^8423 ≤ (591073407691/1562500000000 : ℝ)^6375 := by
    have hnat : (958300003 : ℕ)^8423*1562500000000^6375 ≤ 591073407691^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958300003 2000000000 591073407691 1562500000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372853687/2000000000 : ℝ), (301710697/500000000 : ℝ), (958300003/2000000000 : ℝ)] ![(2173630425251/20000000000000 : ℝ), (12825787441311/25000000000000 : ℝ), (591073407691/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372853687/2000000000 : ℝ)|^8423 ≤ (2173630425251/20000000000000 : ℝ)^6375
        have hw : |(-372853687/2000000000 : ℝ)|=(372853687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(301710697/500000000 : ℝ)|^8423 ≤ (12825787441311/25000000000000 : ℝ)^6375
        have hw : |(301710697/500000000 : ℝ)|=(301710697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958300003/2000000000 : ℝ)|^8423 ≤ (591073407691/1562500000000 : ℝ)^6375
        have hw : |(958300003/2000000000 : ℝ)|=(958300003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s0_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2755917777/5000000000 : ℝ)*x 0 + (-2575022437/10000000000 : ℝ)*x 1 + (4791499967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755917777/5000000000 : ℝ)^8423 ≤ (4551833886591/10000000000000 : ℝ)^6375 := by
    have hnat : (2755917777 : ℕ)^8423*10000000000000^6375 ≤ 4551833886591^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755917777 5000000000 4551833886591 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575022437/10000000000 : ℝ)^8423 ≤ (3330592707157/20000000000000 : ℝ)^6375 := by
    have hnat : (2575022437 : ℕ)^8423*20000000000000^6375 ≤ 3330592707157^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575022437 10000000000 3330592707157 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4791499967/10000000000 : ℝ)^8423 ≤ (9457174397881/25000000000000 : ℝ)^6375 := by
    have hnat : (4791499967 : ℕ)^8423*25000000000000^6375 ≤ 9457174397881^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4791499967 10000000000 9457174397881 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755917777/5000000000 : ℝ), (-2575022437/10000000000 : ℝ), (4791499967/10000000000 : ℝ)] ![(4551833886591/10000000000000 : ℝ), (3330592707157/20000000000000 : ℝ), (9457174397881/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755917777/5000000000 : ℝ)|^8423 ≤ (4551833886591/10000000000000 : ℝ)^6375
        have hw : |(2755917777/5000000000 : ℝ)|=(2755917777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2575022437/10000000000 : ℝ)|^8423 ≤ (3330592707157/20000000000000 : ℝ)^6375
        have hw : |(-2575022437/10000000000 : ℝ)|=(2575022437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4791499967/10000000000 : ℝ)|^8423 ≤ (9457174397881/25000000000000 : ℝ)^6375
        have hw : |(4791499967/10000000000 : ℝ)|=(4791499967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s0_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5511835497/10000000000 : ℝ)*x 0 + (479150003/1000000000 : ℝ)*x 1 + (-80469451/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511835497/10000000000 : ℝ)^8423 ≤ (22759169121983/50000000000000 : ℝ)^6375 := by
    have hnat : (5511835497 : ℕ)^8423*50000000000000^6375 ≤ 22759169121983^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511835497 10000000000 22759169121983 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (479150003/1000000000 : ℝ)^8423 ≤ (37828698248693/100000000000000 : ℝ)^6375 := by
    have hnat : (479150003 : ℕ)^8423*100000000000000^6375 ≤ 37828698248693^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479150003 1000000000 37828698248693 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (80469451/312500000 : ℝ)^8423 ≤ (8326481746531/50000000000000 : ℝ)^6375 := by
    have hnat : (80469451 : ℕ)^8423*50000000000000^6375 ≤ 8326481746531^6375*312500000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80469451 312500000 8326481746531 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511835497/10000000000 : ℝ), (479150003/1000000000 : ℝ), (-80469451/312500000 : ℝ)] ![(22759169121983/50000000000000 : ℝ), (37828698248693/100000000000000 : ℝ), (8326481746531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511835497/10000000000 : ℝ)|^8423 ≤ (22759169121983/50000000000000 : ℝ)^6375
        have hw : |(5511835497/10000000000 : ℝ)|=(5511835497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(479150003/1000000000 : ℝ)|^8423 ≤ (37828698248693/100000000000000 : ℝ)^6375
        have hw : |(479150003/1000000000 : ℝ)|=(479150003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-80469451/312500000 : ℝ)|^8423 ≤ (8326481746531/50000000000000 : ℝ)^6375
        have hw : |(-80469451/312500000 : ℝ)|=(80469451/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s0_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048491417/2500000000 : ℝ)*x 0 + (3117347341/10000000000 : ℝ)*x 1 + (352027513/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048491417/2500000000 : ℝ)^8423 ≤ (15862121248251/50000000000000 : ℝ)^6375 := by
    have hnat : (1048491417 : ℕ)^8423*50000000000000^6375 ≤ 15862121248251^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048491417 2500000000 15862121248251 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117347341/10000000000 : ℝ)^8423 ≤ (21436861761107/100000000000000 : ℝ)^6375 := by
    have hnat : (3117347341 : ℕ)^8423*100000000000000^6375 ≤ 21436861761107^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117347341 10000000000 21436861761107 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352027513/625000000 : ℝ)^8423 ≤ (374711165813/800000000000 : ℝ)^6375 := by
    have hnat : (352027513 : ℕ)^8423*800000000000^6375 ≤ 374711165813^6375*625000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352027513 625000000 374711165813 800000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048491417/2500000000 : ℝ), (3117347341/10000000000 : ℝ), (352027513/625000000 : ℝ)] ![(15862121248251/50000000000000 : ℝ), (21436861761107/100000000000000 : ℝ), (374711165813/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048491417/2500000000 : ℝ)|^8423 ≤ (15862121248251/50000000000000 : ℝ)^6375
        have hw : |(1048491417/2500000000 : ℝ)|=(1048491417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117347341/10000000000 : ℝ)|^8423 ≤ (21436861761107/100000000000000 : ℝ)^6375
        have hw : |(3117347341/10000000000 : ℝ)|=(3117347341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352027513/625000000 : ℝ)|^8423 ≤ (374711165813/800000000000 : ℝ)^6375
        have hw : |(352027513/625000000 : ℝ)|=(352027513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s0_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-46729003/250000000 : ℝ)*x 0 + (4823510319/10000000000 : ℝ)*x 1 + (600107263/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (46729003/250000000 : ℝ)^8423 ≤ (2181169277797/20000000000000 : ℝ)^6375 := by
    have hnat : (46729003 : ℕ)^8423*20000000000000^6375 ≤ 2181169277797^6375*250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46729003 250000000 2181169277797 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4823510319/10000000000 : ℝ)^8423 ≤ (38162963472223/100000000000000 : ℝ)^6375 := by
    have hnat : (4823510319 : ℕ)^8423*100000000000000^6375 ≤ 38162963472223^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4823510319 10000000000 38162963472223 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600107263/1000000000 : ℝ)^8423 ≤ (50931190119347/100000000000000 : ℝ)^6375 := by
    have hnat : (600107263 : ℕ)^8423*100000000000000^6375 ≤ 50931190119347^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600107263 1000000000 50931190119347 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-46729003/250000000 : ℝ), (4823510319/10000000000 : ℝ), (600107263/1000000000 : ℝ)] ![(2181169277797/20000000000000 : ℝ), (38162963472223/100000000000000 : ℝ), (50931190119347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-46729003/250000000 : ℝ)|^8423 ≤ (2181169277797/20000000000000 : ℝ)^6375
        have hw : |(-46729003/250000000 : ℝ)|=(46729003/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4823510319/10000000000 : ℝ)|^8423 ≤ (38162963472223/100000000000000 : ℝ)^6375
        have hw : |(4823510319/10000000000 : ℝ)|=(4823510319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600107263/1000000000 : ℝ)|^8423 ≤ (50931190119347/100000000000000 : ℝ)^6375
        have hw : |(600107263/1000000000 : ℝ)|=(600107263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s0_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1293440463/2500000000 : ℝ)*x 0 + (-1365447731/10000000000 : ℝ)*x 1 + (3000537381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293440463/2500000000 : ℝ)^8423 ≤ (1674654958587/4000000000000 : ℝ)^6375 := by
    have hnat : (1293440463 : ℕ)^8423*4000000000000^6375 ≤ 1674654958587^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293440463 2500000000 1674654958587 4000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365447731/10000000000 : ℝ)^8423 ≤ (7202412000459/100000000000000 : ℝ)^6375 := by
    have hnat : (1365447731 : ℕ)^8423*100000000000000^6375 ≤ 7202412000459^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365447731 10000000000 7202412000459 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3000537381/5000000000 : ℝ)^8423 ≤ (50931214026551/100000000000000 : ℝ)^6375 := by
    have hnat : (3000537381 : ℕ)^8423*100000000000000^6375 ≤ 50931214026551^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3000537381 5000000000 50931214026551 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293440463/2500000000 : ℝ), (-1365447731/10000000000 : ℝ), (3000537381/5000000000 : ℝ)] ![(1674654958587/4000000000000 : ℝ), (7202412000459/100000000000000 : ℝ), (50931214026551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293440463/2500000000 : ℝ)|^8423 ≤ (1674654958587/4000000000000 : ℝ)^6375
        have hw : |(1293440463/2500000000 : ℝ)|=(1293440463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1365447731/10000000000 : ℝ)|^8423 ≤ (7202412000459/100000000000000 : ℝ)^6375
        have hw : |(-1365447731/10000000000 : ℝ)|=(1365447731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3000537381/5000000000 : ℝ)|^8423 ≤ (50931214026551/100000000000000 : ℝ)^6375
        have hw : |(3000537381/5000000000 : ℝ)|=(3000537381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s0_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5173762641/10000000000 : ℝ)*x 0 + (375067071/625000000 : ℝ)*x 1 + (-85340571/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173762641/10000000000 : ℝ)^8423 ≤ (20933191200201/50000000000000 : ℝ)^6375 := by
    have hnat : (5173762641 : ℕ)^8423*50000000000000^6375 ≤ 20933191200201^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173762641 10000000000 20933191200201 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (375067071/625000000 : ℝ)^8423 ≤ (50931195793383/100000000000000 : ℝ)^6375 := by
    have hnat : (375067071 : ℕ)^8423*100000000000000^6375 ≤ 50931195793383^6375*625000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375067071 625000000 50931195793383 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85340571/625000000 : ℝ)^8423 ≤ (3601210896167/50000000000000 : ℝ)^6375 := by
    have hnat : (85340571 : ℕ)^8423*50000000000000^6375 ≤ 3601210896167^6375*625000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85340571 625000000 3601210896167 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173762641/10000000000 : ℝ), (375067071/625000000 : ℝ), (-85340571/625000000 : ℝ)] ![(20933191200201/50000000000000 : ℝ), (50931195793383/100000000000000 : ℝ), (3601210896167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173762641/10000000000 : ℝ)|^8423 ≤ (20933191200201/50000000000000 : ℝ)^6375
        have hw : |(5173762641/10000000000 : ℝ)|=(5173762641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(375067071/625000000 : ℝ)|^8423 ≤ (50931195793383/100000000000000 : ℝ)^6375
        have hw : |(375067071/625000000 : ℝ)|=(375067071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85340571/625000000 : ℝ)|^8423 ≤ (3601210896167/50000000000000 : ℝ)^6375
        have hw : |(-85340571/625000000 : ℝ)|=(85340571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s0_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4203865951/10000000000 : ℝ)*x 0 + (5567660271/10000000000 : ℝ)*x 1 + (3184415577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203865951/10000000000 : ℝ)^8423 ≤ (31823226534411/100000000000000 : ℝ)^6375 := by
    have hnat : (4203865951 : ℕ)^8423*100000000000000^6375 ≤ 31823226534411^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203865951 10000000000 31823226534411 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5567660271/10000000000 : ℝ)^8423 ≤ (9225689633703/20000000000000 : ℝ)^6375 := by
    have hnat : (5567660271 : ℕ)^8423*20000000000000^6375 ≤ 9225689633703^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5567660271 10000000000 9225689633703 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184415577/10000000000 : ℝ)^8423 ≤ (5512081319471/25000000000000 : ℝ)^6375 := by
    have hnat : (3184415577 : ℕ)^8423*25000000000000^6375 ≤ 5512081319471^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184415577 10000000000 5512081319471 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203865951/10000000000 : ℝ), (5567660271/10000000000 : ℝ), (3184415577/10000000000 : ℝ)] ![(31823226534411/100000000000000 : ℝ), (9225689633703/20000000000000 : ℝ), (5512081319471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203865951/10000000000 : ℝ)|^8423 ≤ (31823226534411/100000000000000 : ℝ)^6375
        have hw : |(4203865951/10000000000 : ℝ)|=(4203865951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5567660271/10000000000 : ℝ)|^8423 ≤ (9225689633703/20000000000000 : ℝ)^6375
        have hw : |(5567660271/10000000000 : ℝ)|=(5567660271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184415577/10000000000 : ℝ)|^8423 ≤ (5512081319471/25000000000000 : ℝ)^6375
        have hw : |(3184415577/10000000000 : ℝ)|=(3184415577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (77/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27481/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4211/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4211 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4211*1^1024 ≤ 0^1024*1^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4211/1024 : ℝ) ≤ (1154833680028283143/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4211 ≤ (1154833680028283143/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4211*50000000000000000000^1024 ≤ 1154833680028283143^1024*5^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1154833680028283143 50000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1154833680028283143/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4211 := by
      have hnat : (1 : ℕ)^1024*1^4211 ≤ 1^4211*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51154833680028283143/50000000000000000000 : ℝ) ≤ (251392011039101/250000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (51154833680028283143/50000000000000000000 : ℝ)^1024 ≤ (251392011039101/250000000000000 : ℝ)^4211 := by
      have hnat : (51154833680028283143 : ℕ)^1024*250000000000000^4211 ≤ 251392011039101^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51154833680028283143 50000000000000000000 251392011039101 250000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251392011039101/250000000000000 : ℝ)) (X := (51154833680028283143/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26154833680028283143/25000000000000000000 : ℝ) ≤ (126392011039101/125000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (26154833680028283143/25000000000000000000 : ℝ)^1024 ≤ (126392011039101/125000000000000 : ℝ)^4211 := by
      have hnat : (26154833680028283143 : ℕ)^1024*125000000000000^4211 ≤ 126392011039101^4211*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26154833680028283143 25000000000000000000 126392011039101 125000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (126392011039101/125000000000000 : ℝ)) (X := (26154833680028283143/25000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1392011039101/100000000000000 : ℝ)*(0 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1392011039101/100000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1154833680028283143/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1392011039101/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1392011039101/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(251392011039101/250000000000000 : ℝ) by norm_num, show 1+(1154833680028283143/50000000000000000000 : ℝ)+(0 : ℝ)=(51154833680028283143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1154833680028283143/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1392011039101/100000000000000 : ℝ)*(2/5 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1392011039101/100000000000000 : ℝ)*(2/5 : ℝ)=(126392011039101/125000000000000 : ℝ) by norm_num, show 1+2*(1154833680028283143/50000000000000000000 : ℝ)=(26154833680028283143/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1392011039101/100000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1392011039101/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1392011039101/100000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1392011039101/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1392011039101/100000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1392011039101/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-372853687/2000000000 : ℝ)*X 0 0+(301710697/500000000 : ℝ)*X 0 1+(958300003/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755917777/5000000000 : ℝ)*X 1 0+(-2575022437/10000000000 : ℝ)*X 1 1+(4791499967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5511835497/10000000000 : ℝ)*X 2 0+(479150003/1000000000 : ℝ)*X 2 1+(-80469451/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048491417/2500000000 : ℝ)*X 0 0+(3117347341/10000000000 : ℝ)*X 0 1+(352027513/625000000 : ℝ)*X 0 2+(1048491417/2500000000 : ℝ)*X 1 0+(3117347341/10000000000 : ℝ)*X 1 1+(352027513/625000000 : ℝ)*X 1 2+(1048491417/2500000000 : ℝ)*X 2 0+(3117347341/10000000000 : ℝ)*X 2 1+(352027513/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-46729003/250000000 : ℝ)*X 0 0+(4823510319/10000000000 : ℝ)*X 0 1+(600107263/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293440463/2500000000 : ℝ)*X 1 0+(-1365447731/10000000000 : ℝ)*X 1 1+(3000537381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173762641/10000000000 : ℝ)*X 2 0+(375067071/625000000 : ℝ)*X 2 1+(-85340571/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4203865951/10000000000 : ℝ)*X 0 0+(5567660271/10000000000 : ℝ)*X 0 1+(3184415577/10000000000 : ℝ)*X 0 2+(4203865951/10000000000 : ℝ)*X 1 0+(5567660271/10000000000 : ℝ)*X 1 1+(3184415577/10000000000 : ℝ)*X 1 2+(4203865951/10000000000 : ℝ)*X 2 0+(5567660271/10000000000 : ℝ)*X 2 1+(3184415577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32595975375384800251467/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77977307/100000000000000 : ℝ)*(base1) + (1591528379/100000000000000 : ℝ)*(base19) + (1475765789/100000000000000 : ℝ)*(base23) + (107440903/100000000000000 : ℝ)*(base24) + (359811777/100000000000000 : ℝ)*(upper3) + (601151792706863/100000000000000 : ℝ)*(major0) + (601151792706863/100000000000000 : ℝ)*(major1) + (601151792706863/100000000000000 : ℝ)*(major2) + (804695816796591/100000000000000 : ℝ)*(sp0) + (402348842495029/50000000000000 : ℝ)*(sp1) + (160939538662349/20000000000000 : ℝ)*(sp2) + (99400313126407/25000000000000 : ℝ)*(sp3) + (3537699153/100000000000000 : ℝ)*(sp4) + (345138231/12500000000000 : ℝ)*(sp7) + (198802045794391/50000000000000 : ℝ)*(f.failure) + (804699276518437/100000000000000 : ℝ)*(f.sum) + (8485263484837/5000000000000000000000000000 : ℝ)*base66 + (3933741020163/10000000000000000000000000000 : ℝ)*base67 + (43496037699837/10000000000000000000000000000 : ℝ)*base70 + (27879293210163/10000000000000000000000000000 : ℝ)*base71 + (18165718999837/5000000000000000000000000000 : ℝ)*base74 + (3810006009837/10000000000000000000000000000 : ℝ)*base76 + (10308391880163/10000000000000000000000000000 : ℝ)*base77 + (10037399009837/10000000000000000000000000000 : ℝ)*base80 + (52013981349837/5000000000000000000000000000 : ℝ)*base82 + (9294867/5000000000000000000000 : ℝ)*base90 + (9294867/5000000000000000000000 : ℝ)*base92 + (9294867/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2306877271134604737651/625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (717479/1250000000000 : ℝ)*(base1) + (982316709/100000000000000 : ℝ)*(base19) + (549615589/50000000000000 : ℝ)*(base23) + (61694849/25000000000000 : ℝ)*(upper3) + (79300475503821/12500000000000 : ℝ)*(major0) + (79300475503821/12500000000000 : ℝ)*(major1) + (79300475503821/12500000000000 : ℝ)*(major2) + (1209715257/50000000000000 : ℝ)*(sp1) + (278345079/12500000000000 : ℝ)*(sp2) + (30841693/20000000000000 : ℝ)*(sp3) + (424605221776549/50000000000000 : ℝ)*(sp4) + (169841396881511/20000000000000 : ℝ)*(sp5) + (106150882520371/12500000000000 : ℝ)*(sp6) + (419596887266113/100000000000000 : ℝ)*(sp7) + (209798549436449/50000000000000 : ℝ)*(f.failure) + (424605193077389/50000000000000 : ℝ)*(f.sum) + (103442773477/312500000000000000000000000 : ℝ)*base66 + (1120239657579/1250000000000000000000000000 : ℝ)*base68 + (4490567578671/1250000000000000000000000000 : ℝ)*base69 + (1992850031171/1250000000000000000000000000 : ℝ)*base71 + (46443688169/39062500000000000000000000 : ℝ)*base74 + (4838072681329/1250000000000000000000000000 : ℝ)*base76 + (2522832438829/1250000000000000000000000000 : ℝ)*base78 + (4683025090079/1250000000000000000000000000 : ℝ)*base80 + (22141695307/4882812500000000000000000 : ℝ)*base81 + (33622213/5000000000000000000000 : ℝ)*base90 + (33622213/5000000000000000000000 : ℝ)*base92 + (33622213/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1230_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (77/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1230_s1_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2062553959/10000000000 : ℝ)*x 0 + (5678625647/10000000000 : ℝ)*x 1 + (2510081547/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2062553959/10000000000 : ℝ)^8423 ≤ (6210472904979/50000000000000 : ℝ)^6375 := by
    have hnat : (2062553959 : ℕ)^8423*50000000000000^6375 ≤ 6210472904979^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062553959 10000000000 6210472904979 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5678625647/10000000000 : ℝ)^8423 ≤ (23673511399561/50000000000000 : ℝ)^6375 := by
    have hnat : (5678625647 : ℕ)^8423*50000000000000^6375 ≤ 23673511399561^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5678625647 10000000000 23673511399561 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2510081547/5000000000 : ℝ)^8423 ≤ (10058007845669/25000000000000 : ℝ)^6375 := by
    have hnat : (2510081547 : ℕ)^8423*25000000000000^6375 ≤ 10058007845669^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2510081547 5000000000 10058007845669 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2062553959/10000000000 : ℝ), (5678625647/10000000000 : ℝ), (2510081547/5000000000 : ℝ)] ![(6210472904979/50000000000000 : ℝ), (23673511399561/50000000000000 : ℝ), (10058007845669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2062553959/10000000000 : ℝ)|^8423 ≤ (6210472904979/50000000000000 : ℝ)^6375
        have hw : |(-2062553959/10000000000 : ℝ)|=(2062553959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5678625647/10000000000 : ℝ)|^8423 ≤ (23673511399561/50000000000000 : ℝ)^6375
        have hw : |(5678625647/10000000000 : ℝ)|=(5678625647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2510081547/5000000000 : ℝ)|^8423 ≤ (10058007845669/25000000000000 : ℝ)^6375
        have hw : |(2510081547/5000000000 : ℝ)|=(2510081547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s1_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1082861921/2000000000 : ℝ)*x 0 + (-2416345497/10000000000 : ℝ)*x 1 + (251008157/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082861921/2000000000 : ℝ)^8423 ≤ (22228619965309/50000000000000 : ℝ)^6375 := by
    have hnat : (1082861921 : ℕ)^8423*50000000000000^6375 ≤ 22228619965309^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082861921 2000000000 22228619965309 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2416345497/10000000000 : ℝ)^8423 ≤ (478460255633/3125000000000 : ℝ)^6375 := by
    have hnat : (2416345497 : ℕ)^8423*3125000000000^6375 ≤ 478460255633^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416345497 10000000000 478460255633 3125000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251008157/500000000 : ℝ)^8423 ≤ (20116015934877/50000000000000 : ℝ)^6375 := by
    have hnat : (251008157 : ℕ)^8423*50000000000000^6375 ≤ 20116015934877^6375*500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251008157 500000000 20116015934877 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082861921/2000000000 : ℝ), (-2416345497/10000000000 : ℝ), (251008157/500000000 : ℝ)] ![(22228619965309/50000000000000 : ℝ), (478460255633/3125000000000 : ℝ), (20116015934877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082861921/2000000000 : ℝ)|^8423 ≤ (22228619965309/50000000000000 : ℝ)^6375
        have hw : |(1082861921/2000000000 : ℝ)|=(1082861921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2416345497/10000000000 : ℝ)|^8423 ≤ (478460255633/3125000000000 : ℝ)^6375
        have hw : |(-2416345497/10000000000 : ℝ)|=(2416345497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(251008157/500000000 : ℝ)|^8423 ≤ (20116015934877/50000000000000 : ℝ)^6375
        have hw : |(251008157/500000000 : ℝ)|=(251008157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s1_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (108286193/200000000 : ℝ)*x 0 + (5020163117/10000000000 : ℝ)*x 1 + (-2416345469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108286193/200000000 : ℝ)^8423 ≤ (44457240418819/100000000000000 : ℝ)^6375 := by
    have hnat : (108286193 : ℕ)^8423*100000000000000^6375 ≤ 44457240418819^6375*200000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108286193 200000000 44457240418819 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5020163117/10000000000 : ℝ)^8423 ≤ (8046406325243/20000000000000 : ℝ)^6375 := by
    have hnat : (5020163117 : ℕ)^8423*20000000000000^6375 ≤ 8046406325243^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5020163117 10000000000 8046406325243 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2416345469/10000000000 : ℝ)^8423 ≤ (15310727945843/100000000000000 : ℝ)^6375 := by
    have hnat : (2416345469 : ℕ)^8423*100000000000000^6375 ≤ 15310727945843^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2416345469 10000000000 15310727945843 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108286193/200000000 : ℝ), (5020163117/10000000000 : ℝ), (-2416345469/10000000000 : ℝ)] ![(44457240418819/100000000000000 : ℝ), (8046406325243/20000000000000 : ℝ), (15310727945843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108286193/200000000 : ℝ)|^8423 ≤ (44457240418819/100000000000000 : ℝ)^6375
        have hw : |(108286193/200000000 : ℝ)|=(108286193/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5020163117/10000000000 : ℝ)|^8423 ≤ (8046406325243/20000000000000 : ℝ)^6375
        have hw : |(5020163117/10000000000 : ℝ)|=(5020163117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2416345469/10000000000 : ℝ)|^8423 ≤ (15310727945843/100000000000000 : ℝ)^6375
        have hw : |(-2416345469/10000000000 : ℝ)|=(2416345469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s1_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (172395871/400000000 : ℝ)*x 0 + (3693281563/10000000000 : ℝ)*x 1 + (5025925359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172395871/400000000 : ℝ)^8423 ≤ (16444003581147/50000000000000 : ℝ)^6375 := by
    have hnat : (172395871 : ℕ)^8423*50000000000000^6375 ≤ 16444003581147^6375*400000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172395871 400000000 16444003581147 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3693281563/10000000000 : ℝ)^8423 ≤ (13409467780479/50000000000000 : ℝ)^6375 := by
    have hnat : (3693281563 : ℕ)^8423*50000000000000^6375 ≤ 13409467780479^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3693281563 10000000000 13409467780479 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5025925359/10000000000 : ℝ)^8423 ≤ (40293057257947/100000000000000 : ℝ)^6375 := by
    have hnat : (5025925359 : ℕ)^8423*100000000000000^6375 ≤ 40293057257947^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5025925359 10000000000 40293057257947 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172395871/400000000 : ℝ), (3693281563/10000000000 : ℝ), (5025925359/10000000000 : ℝ)] ![(16444003581147/50000000000000 : ℝ), (13409467780479/50000000000000 : ℝ), (40293057257947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172395871/400000000 : ℝ)|^8423 ≤ (16444003581147/50000000000000 : ℝ)^6375
        have hw : |(172395871/400000000 : ℝ)|=(172395871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3693281563/10000000000 : ℝ)|^8423 ≤ (13409467780479/50000000000000 : ℝ)^6375
        have hw : |(3693281563/10000000000 : ℝ)|=(3693281563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5025925359/10000000000 : ℝ)|^8423 ≤ (40293057257947/100000000000000 : ℝ)^6375
        have hw : |(5025925359/10000000000 : ℝ)|=(5025925359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s1_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031622691/5000000000 : ℝ)*x 0 + (5028853509/10000000000 : ℝ)*x 1 + (5669768631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031622691/5000000000 : ℝ)^8423 ≤ (12426447589253/100000000000000 : ℝ)^6375 := by
    have hnat : (1031622691 : ℕ)^8423*100000000000000^6375 ≤ 12426447589253^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031622691 5000000000 12426447589253 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5028853509/10000000000 : ℝ)^8423 ≤ (2016203837757/5000000000000 : ℝ)^6375 := by
    have hnat : (5028853509 : ℕ)^8423*5000000000000^6375 ≤ 2016203837757^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5028853509 10000000000 2016203837757 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5669768631/10000000000 : ℝ)^8423 ≤ (23624737820673/50000000000000 : ℝ)^6375 := by
    have hnat : (5669768631 : ℕ)^8423*50000000000000^6375 ≤ 23624737820673^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5669768631 10000000000 23624737820673 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031622691/5000000000 : ℝ), (5028853509/10000000000 : ℝ), (5669768631/10000000000 : ℝ)] ![(12426447589253/100000000000000 : ℝ), (2016203837757/5000000000000 : ℝ), (23624737820673/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031622691/5000000000 : ℝ)|^8423 ≤ (12426447589253/100000000000000 : ℝ)^6375
        have hw : |(-1031622691/5000000000 : ℝ)|=(1031622691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5028853509/10000000000 : ℝ)|^8423 ≤ (2016203837757/5000000000000 : ℝ)^6375
        have hw : |(5028853509/10000000000 : ℝ)|=(5028853509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5669768631/10000000000 : ℝ)|^8423 ≤ (23624737820673/50000000000000 : ℝ)^6375
        have hw : |(5669768631/10000000000 : ℝ)|=(5669768631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s1_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2622383273/5000000000 : ℝ)*x 0 + (-1766739361/10000000000 : ℝ)*x 1 + (708721119/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622383273/5000000000 : ℝ)^8423 ≤ (42627201047689/100000000000000 : ℝ)^6375 := by
    have hnat : (2622383273 : ℕ)^8423*100000000000000^6375 ≤ 42627201047689^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622383273 5000000000 42627201047689 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1766739361/10000000000 : ℝ)^8423 ≤ (1012331976571/10000000000000 : ℝ)^6375 := by
    have hnat : (1766739361 : ℕ)^8423*10000000000000^6375 ≤ 1012331976571^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1766739361 10000000000 1012331976571 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708721119/1250000000 : ℝ)^8423 ≤ (369136556061/781250000000 : ℝ)^6375 := by
    have hnat : (708721119 : ℕ)^8423*781250000000^6375 ≤ 369136556061^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708721119 1250000000 369136556061 781250000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622383273/5000000000 : ℝ), (-1766739361/10000000000 : ℝ), (708721119/1250000000 : ℝ)] ![(42627201047689/100000000000000 : ℝ), (1012331976571/10000000000000 : ℝ), (369136556061/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622383273/5000000000 : ℝ)|^8423 ≤ (42627201047689/100000000000000 : ℝ)^6375
        have hw : |(2622383273/5000000000 : ℝ)|=(2622383273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1766739361/10000000000 : ℝ)|^8423 ≤ (1012331976571/10000000000000 : ℝ)^6375
        have hw : |(-1766739361/10000000000 : ℝ)|=(1766739361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708721119/1250000000 : ℝ)|^8423 ≤ (369136556061/781250000000 : ℝ)^6375
        have hw : |(708721119/1250000000 : ℝ)|=(708721119/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s1_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (104895337/200000000 : ℝ)*x 0 + (56697697/100000000 : ℝ)*x 1 + (-883368921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104895337/200000000 : ℝ)^8423 ≤ (2131360215611/5000000000000 : ℝ)^6375 := by
    have hnat : (104895337 : ℕ)^8423*5000000000000^6375 ≤ 2131360215611^6375*200000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104895337 200000000 2131360215611 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56697697/100000000 : ℝ)^8423 ≤ (11812371852969/25000000000000 : ℝ)^6375 := by
    have hnat : (56697697 : ℕ)^8423*25000000000000^6375 ≤ 11812371852969^6375*100000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56697697 100000000 11812371852969 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (883368921/5000000000 : ℝ)^8423 ≤ (1012330826579/10000000000000 : ℝ)^6375 := by
    have hnat : (883368921 : ℕ)^8423*10000000000000^6375 ≤ 1012330826579^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883368921 5000000000 1012330826579 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104895337/200000000 : ℝ), (56697697/100000000 : ℝ), (-883368921/5000000000 : ℝ)] ![(2131360215611/5000000000000 : ℝ), (11812371852969/25000000000000 : ℝ), (1012330826579/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104895337/200000000 : ℝ)|^8423 ≤ (2131360215611/5000000000000 : ℝ)^6375
        have hw : |(104895337/200000000 : ℝ)|=(104895337/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56697697/100000000 : ℝ)|^8423 ≤ (11812371852969/25000000000000 : ℝ)^6375
        have hw : |(56697697/100000000 : ℝ)|=(56697697/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-883368921/5000000000 : ℝ)|^8423 ≤ (1012330826579/10000000000000 : ℝ)^6375
        have hw : |(-883368921/5000000000 : ℝ)|=(883368921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s1_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (538911797/1250000000 : ℝ)*x 0 + (5008337877/10000000000 : ℝ)*x 1 + (3711205231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538911797/1250000000 : ℝ)^8423 ≤ (1316083954147/4000000000000 : ℝ)^6375 := by
    have hnat : (538911797 : ℕ)^8423*4000000000000^6375 ≤ 1316083954147^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538911797 1250000000 1316083954147 4000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5008337877/10000000000 : ℝ)^8423 ≤ (10026716414027/25000000000000 : ℝ)^6375 := by
    have hnat : (5008337877 : ℕ)^8423*25000000000000^6375 ≤ 10026716414027^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5008337877 10000000000 10026716414027 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3711205231/10000000000 : ℝ)^8423 ≤ (13495517739863/50000000000000 : ℝ)^6375 := by
    have hnat : (3711205231 : ℕ)^8423*50000000000000^6375 ≤ 13495517739863^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711205231 10000000000 13495517739863 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538911797/1250000000 : ℝ), (5008337877/10000000000 : ℝ), (3711205231/10000000000 : ℝ)] ![(1316083954147/4000000000000 : ℝ), (10026716414027/25000000000000 : ℝ), (13495517739863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538911797/1250000000 : ℝ)|^8423 ≤ (1316083954147/4000000000000 : ℝ)^6375
        have hw : |(538911797/1250000000 : ℝ)|=(538911797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5008337877/10000000000 : ℝ)|^8423 ≤ (10026716414027/25000000000000 : ℝ)^6375
        have hw : |(5008337877/10000000000 : ℝ)|=(5008337877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3711205231/10000000000 : ℝ)|^8423 ≤ (13495517739863/50000000000000 : ℝ)^6375
        have hw : |(3711205231/10000000000 : ℝ)|=(3711205231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (77/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (383/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (401/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (77/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (77/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (77/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (77/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (77/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (77/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (77/10000 : ℝ) ^ (4211/1024 : ℝ) ≤ (203519441443/100000000000000000000 : ℝ) := by
    have hpowers : (77/10000 : ℝ)^4211 ≤ (203519441443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (77 : ℕ)^4211*100000000000000000000^1024 ≤ 203519441443^1024*10000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        77 10000 203519441443 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (77/10000 : ℝ)) (X := (203519441443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27481/100000 : ℝ) ^ (4211/1024 : ℝ) ≤ (493322418901499139/100000000000000000000 : ℝ) := by
    have hpowers : (27481/100000 : ℝ)^4211 ≤ (493322418901499139/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27481 : ℕ)^4211*100000000000000000000^1024 ≤ 493322418901499139^1024*100000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27481 100000 493322418901499139 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27481/100000 : ℝ)) (X := (493322418901499139/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000203519441443/50000000000000000000 : ℝ) ≤ (10000000009898073/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50000000203519441443/50000000000000000000 : ℝ)^1024 ≤ (10000000009898073/10000000000000000 : ℝ)^4211 := by
      have hnat : (50000000203519441443 : ℕ)^1024*10000000000000000^4211 ≤ 10000000009898073^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000203519441443 50000000000000000000 10000000009898073 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000009898073/10000000000000000 : ℝ)) (X := (50000000203519441443/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50246661311210470291/50000000000000000000 : ℝ) ≤ (3128741852019/3125000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50246661311210470291/50000000000000000000 : ℝ)^1024 ≤ (3128741852019/3125000000000 : ℝ)^4211 := by
      have hnat : (50246661311210470291 : ℕ)^1024*3125000000000^4211 ≤ 3128741852019^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50246661311210470291 50000000000000000000 3128741852019 3125000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (3128741852019/3125000000000 : ℝ)) (X := (50246661311210470291/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50493322418901499139/50000000000000000000 : ℝ) ≤ (10023947843023527/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50493322418901499139/50000000000000000000 : ℝ)^1024 ≤ (10023947843023527/10000000000000000 : ℝ)^4211 := by
      have hnat : (50493322418901499139 : ℕ)^1024*10000000000000000^4211 ≤ 10023947843023527^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50493322418901499139 50000000000000000000 10023947843023527 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10023947843023527/10000000000000000 : ℝ)) (X := (50493322418901499139/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(203519441443/100000000000000000000 : ℝ) ≤ ((267091560432880828323/267110000000000000000 : ℝ)+2*(11973916562727/2671100000000000 : ℝ)*(77/10000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (267091560432880828323/267110000000000000000 : ℝ)+2*(11973916562727/2671100000000000 : ℝ)*(77/10000 : ℝ)=(10000000009898073/10000000000000000 : ℝ) by norm_num, show 1+2*(203519441443/100000000000000000000 : ℝ)=(50000000203519441443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(493322418901499139/100000000000000000000 : ℝ)+(203519441443/100000000000000000000 : ℝ) ≤ ((267091560432880828323/267110000000000000000 : ℝ)+(11973916562727/2671100000000000 : ℝ)*((27481/100000 : ℝ)+(77/10000 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (267091560432880828323/267110000000000000000 : ℝ)+(11973916562727/2671100000000000 : ℝ)*((27481/100000 : ℝ)+(77/10000 : ℝ))=(3128741852019/3125000000000 : ℝ) by norm_num, show 1+(493322418901499139/100000000000000000000 : ℝ)+(203519441443/100000000000000000000 : ℝ)=(50246661311210470291/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(493322418901499139/100000000000000000000 : ℝ) ≤ ((267091560432880828323/267110000000000000000 : ℝ)+2*(11973916562727/2671100000000000 : ℝ)*(27481/100000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (267091560432880828323/267110000000000000000 : ℝ)+2*(11973916562727/2671100000000000 : ℝ)*(27481/100000 : ℝ)=(10023947843023527/10000000000000000 : ℝ) by norm_num, show 1+2*(493322418901499139/100000000000000000000 : ℝ)=(50493322418901499139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (267091560432880828323/267110000000000000000 : ℝ)*(X 1 0+X 2 0)+(11973916562727/2671100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (77/10000 : ℝ)) (hi := (27481/100000 : ℝ)) (c := (267091560432880828323/267110000000000000000 : ℝ)) (alpha := (11973916562727/2671100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (267091560432880828323/267110000000000000000 : ℝ)*(X 0 1+X 2 1)+(11973916562727/2671100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (77/10000 : ℝ)) (hi := (27481/100000 : ℝ)) (c := (267091560432880828323/267110000000000000000 : ℝ)) (alpha := (11973916562727/2671100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (267091560432880828323/267110000000000000000 : ℝ)*(X 0 2+X 1 2)+(11973916562727/2671100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (77/10000 : ℝ)) (hi := (27481/100000 : ℝ)) (c := (267091560432880828323/267110000000000000000 : ℝ)) (alpha := (11973916562727/2671100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2062553959/10000000000 : ℝ)*X 0 0+(5678625647/10000000000 : ℝ)*X 0 1+(2510081547/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1082861921/2000000000 : ℝ)*X 1 0+(-2416345497/10000000000 : ℝ)*X 1 1+(251008157/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((108286193/200000000 : ℝ)*X 2 0+(5020163117/10000000000 : ℝ)*X 2 1+(-2416345469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172395871/400000000 : ℝ)*X 0 0+(3693281563/10000000000 : ℝ)*X 0 1+(5025925359/10000000000 : ℝ)*X 0 2+(172395871/400000000 : ℝ)*X 1 0+(3693281563/10000000000 : ℝ)*X 1 1+(5025925359/10000000000 : ℝ)*X 1 2+(172395871/400000000 : ℝ)*X 2 0+(3693281563/10000000000 : ℝ)*X 2 1+(5025925359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1031622691/5000000000 : ℝ)*X 0 0+(5028853509/10000000000 : ℝ)*X 0 1+(5669768631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622383273/5000000000 : ℝ)*X 1 0+(-1766739361/10000000000 : ℝ)*X 1 1+(708721119/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((104895337/200000000 : ℝ)*X 2 0+(56697697/100000000 : ℝ)*X 2 1+(-883368921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((538911797/1250000000 : ℝ)*X 0 0+(5008337877/10000000000 : ℝ)*X 0 1+(3711205231/10000000000 : ℝ)*X 0 2+(538911797/1250000000 : ℝ)*X 1 0+(5008337877/10000000000 : ℝ)*X 1 1+(3711205231/10000000000 : ℝ)*X 1 2+(538911797/1250000000 : ℝ)*X 2 0+(5008337877/10000000000 : ℝ)*X 2 1+(3711205231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33878598922733319926091/6677750000000000000000000000 : ℝ) := by norm_num
    linear_combination (28493289/50000000000000 : ℝ)*(base1) + (222284063/20000000000000 : ℝ)*(base19) + (1124042703/100000000000000 : ℝ)*(base23) + (6061617/5000000000000 : ℝ)*(upper3) + (67576483/50000000000000 : ℝ)*(upper5) + (113454803413793/10000000000000 : ℝ)*(major0) + (113454803413793/10000000000000 : ℝ)*(major1) + (113454803413793/10000000000000 : ℝ)*(major2) + (1518695232370929/100000000000000 : ℝ)*(sp0) + (9491877405931/625000000000 : ℝ)*(sp1) + (1518700372326571/100000000000000 : ℝ)*(sp2) + (187597797096717/25000000000000 : ℝ)*(sp3) + (1580246231/25000000000000 : ℝ)*(sp4) + (3157421287/100000000000000 : ℝ)*(sp7) + (375197201397367/50000000000000 : ℝ)*(f.failure) + (759350748184637/50000000000000 : ℝ)*(f.sum) + (97556604524859/26711000000000000000000000000 : ℝ)*base65 + (3115926781663840861/2671100000000000000000000000000000 : ℝ)*base68 + (2068146450022540861/2671100000000000000000000000000000 : ℝ)*base70 + (3687746921478840861/2671100000000000000000000000000000 : ℝ)*base72 + (94837009903029/26711000000000000000000000000 : ℝ)*base73 + (1217517486744459139/2671100000000000000000000000000000 : ℝ)*base75 + (10324978969736159139/2671100000000000000000000000000000 : ℝ)*base77 + (18832054701405359139/2671100000000000000000000000000000 : ℝ)*base79 + (13080198689453/6677750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4451379/5000000000000000000000 : ℝ)*base90 + (4451379/5000000000000000000000 : ℝ)*base92 + (4451379/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4815659947579882838294504223/834718750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1902791793/100000000000000 : ℝ)*(base19) + (294009121/12500000000000 : ℝ)*(base23) + (937771/1000000000000 : ℝ)*(upper2) + (307875381/100000000000000 : ℝ)*(upper3) + (34998533/25000000000000 : ℝ)*(upper5) + (72849984064017/6250000000000 : ℝ)*(major0) + (72849984064017/6250000000000 : ℝ)*(major1) + (72849984064017/6250000000000 : ℝ)*(major2) + (136179221/1562500000000 : ℝ)*(sp1) + (7142535217/50000000000000 : ℝ)*(sp2) + (390066793693891/25000000000000 : ℝ)*(sp4) + (1560256556513627/100000000000000 : ℝ)*(sp5) + (780125268816081/50000000000000 : ℝ)*(sp6) + (48183257685393/6250000000000 : ℝ)*(sp7) + (48183257685393/6250000000000 : ℝ)*(f.failure) + (390066793693891/25000000000000 : ℝ)*(f.sum) + (68216893990807/16694375000000000000000000000 : ℝ)*base66 + (12666574069531403491/1669437500000000000000000000000000 : ℝ)*base67 + (14525792807991096509/1669437500000000000000000000000000 : ℝ)*base70 + (3806445367635971509/1669437500000000000000000000000000 : ℝ)*base72 + (688870530549889/133555000000000000000000000000 : ℝ)*base73 + (3133999017739846509/1669437500000000000000000000000000 : ℝ)*base76 + (4565475724530846509/1669437500000000000000000000000000 : ℝ)*base78 + (883316747998778491/1669437500000000000000000000000000 : ℝ)*base79 + (370113227727523/66777500000000000000000000000 : ℝ)*base82 + (725259/625000000000000000000 : ℝ)*base89 + (725259/625000000000000000000 : ℝ)*base91 + (725259/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1230_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (77/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (383/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (401/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1230_s2_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2111196913/10000000000 : ℝ)*x 0 + (5494851327/10000000000 : ℝ)*x 1 + (5172926711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111196913/10000000000 : ℝ)^8423 ≤ (12809444297407/100000000000000 : ℝ)^6375 := by
    have hnat : (2111196913 : ℕ)^8423*100000000000000^6375 ≤ 12809444297407^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111196913 10000000000 12809444297407 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5494851327/10000000000 : ℝ)^8423 ≤ (1416659704547/3125000000000 : ℝ)^6375 := by
    have hnat : (5494851327 : ℕ)^8423*3125000000000^6375 ≤ 1416659704547^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494851327 10000000000 1416659704547 3125000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172926711/10000000000 : ℝ)^8423 ≤ (20928722572317/50000000000000 : ℝ)^6375 := by
    have hnat : (5172926711 : ℕ)^8423*50000000000000^6375 ≤ 20928722572317^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172926711 10000000000 20928722572317 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2111196913/10000000000 : ℝ), (5494851327/10000000000 : ℝ), (5172926711/10000000000 : ℝ)] ![(12809444297407/100000000000000 : ℝ), (1416659704547/3125000000000 : ℝ), (20928722572317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2111196913/10000000000 : ℝ)|^8423 ≤ (12809444297407/100000000000000 : ℝ)^6375
        have hw : |(-2111196913/10000000000 : ℝ)|=(2111196913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5494851327/10000000000 : ℝ)|^8423 ≤ (1416659704547/3125000000000 : ℝ)^6375
        have hw : |(5494851327/10000000000 : ℝ)|=(5494851327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172926711/10000000000 : ℝ)|^8423 ≤ (20928722572317/50000000000000 : ℝ)^6375
        have hw : |(5172926711/10000000000 : ℝ)|=(5172926711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s2_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370176163/10000000000 : ℝ)*x 0 + (-2278021787/10000000000 : ℝ)*x 1 + (5172926657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370176163/10000000000 : ℝ)^8423 ≤ (439790683437/1000000000000 : ℝ)^6375 := by
    have hnat : (5370176163 : ℕ)^8423*1000000000000^6375 ≤ 439790683437^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370176163 10000000000 439790683437 1000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278021787/10000000000 : ℝ)^8423 ≤ (17704358859/125000000000 : ℝ)^6375 := by
    have hnat : (2278021787 : ℕ)^8423*125000000000^6375 ≤ 17704358859^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278021787 10000000000 17704358859 125000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172926657/10000000000 : ℝ)^8423 ≤ (20928722283657/50000000000000 : ℝ)^6375 := by
    have hnat : (5172926657 : ℕ)^8423*50000000000000^6375 ≤ 20928722283657^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172926657 10000000000 20928722283657 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370176163/10000000000 : ℝ), (-2278021787/10000000000 : ℝ), (5172926657/10000000000 : ℝ)] ![(439790683437/1000000000000 : ℝ), (17704358859/125000000000 : ℝ), (20928722283657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370176163/10000000000 : ℝ)|^8423 ≤ (439790683437/1000000000000 : ℝ)^6375
        have hw : |(5370176163/10000000000 : ℝ)|=(5370176163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2278021787/10000000000 : ℝ)|^8423 ≤ (17704358859/125000000000 : ℝ)^6375
        have hw : |(-2278021787/10000000000 : ℝ)|=(2278021787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172926657/10000000000 : ℝ)|^8423 ≤ (20928722283657/50000000000000 : ℝ)^6375
        have hw : |(5172926657/10000000000 : ℝ)|=(5172926657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s2_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370175977/10000000000 : ℝ)*x 0 + (5172926819/10000000000 : ℝ)*x 1 + (-113901091/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370175977/10000000000 : ℝ)^8423 ≤ (21989533165551/50000000000000 : ℝ)^6375 := by
    have hnat : (5370175977 : ℕ)^8423*50000000000000^6375 ≤ 21989533165551^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370175977 10000000000 21989533165551 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172926819/10000000000 : ℝ)^8423 ≤ (1674297851971/4000000000000 : ℝ)^6375 := by
    have hnat : (5172926819 : ℕ)^8423*4000000000000^6375 ≤ 1674297851971^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172926819 10000000000 1674297851971 4000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113901091/500000000 : ℝ)^8423 ≤ (1416348735829/10000000000000 : ℝ)^6375 := by
    have hnat : (113901091 : ℕ)^8423*10000000000000^6375 ≤ 1416348735829^6375*500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113901091 500000000 1416348735829 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370175977/10000000000 : ℝ), (5172926819/10000000000 : ℝ), (-113901091/500000000 : ℝ)] ![(21989533165551/50000000000000 : ℝ), (1674297851971/4000000000000 : ℝ), (1416348735829/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370175977/10000000000 : ℝ)|^8423 ≤ (21989533165551/50000000000000 : ℝ)^6375
        have hw : |(5370175977/10000000000 : ℝ)|=(5370175977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172926819/10000000000 : ℝ)|^8423 ≤ (1674297851971/4000000000000 : ℝ)^6375
        have hw : |(5172926819/10000000000 : ℝ)|=(5172926819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113901091/500000000 : ℝ)|^8423 ≤ (1416348735829/10000000000000 : ℝ)^6375
        have hw : |(-113901091/500000000 : ℝ)|=(113901091/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s2_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4343471561/10000000000 : ℝ)*x 0 + (503696167/1250000000 : ℝ)*x 1 + (2340551761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343471561/10000000000 : ℝ)^8423 ≤ (4153367407533/12500000000000 : ℝ)^6375 := by
    have hnat : (4343471561 : ℕ)^8423*12500000000000^6375 ≤ 4153367407533^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343471561 10000000000 4153367407533 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (503696167/1250000000 : ℝ)^8423 ≤ (3761456527101/12500000000000 : ℝ)^6375 := by
    have hnat : (503696167 : ℕ)^8423*12500000000000^6375 ≤ 3761456527101^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503696167 1250000000 3761456527101 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2340551761/5000000000 : ℝ)^8423 ≤ (7336281701947/20000000000000 : ℝ)^6375 := by
    have hnat : (2340551761 : ℕ)^8423*20000000000000^6375 ≤ 7336281701947^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2340551761 5000000000 7336281701947 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343471561/10000000000 : ℝ), (503696167/1250000000 : ℝ), (2340551761/5000000000 : ℝ)] ![(4153367407533/12500000000000 : ℝ), (3761456527101/12500000000000 : ℝ), (7336281701947/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343471561/10000000000 : ℝ)|^8423 ≤ (4153367407533/12500000000000 : ℝ)^6375
        have hw : |(4343471561/10000000000 : ℝ)|=(4343471561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(503696167/1250000000 : ℝ)|^8423 ≤ (3761456527101/12500000000000 : ℝ)^6375
        have hw : |(503696167/1250000000 : ℝ)|=(503696167/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2340551761/5000000000 : ℝ)|^8423 ≤ (7336281701947/20000000000000 : ℝ)^6375
        have hw : |(2340551761/5000000000 : ℝ)|=(2340551761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s2_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2111277871/10000000000 : ℝ)*x 0 + (2587506769/5000000000 : ℝ)*x 1 + (2746372391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2111277871/10000000000 : ℝ)^8423 ≤ (3202523326559/25000000000000 : ℝ)^6375 := by
    have hnat : (2111277871 : ℕ)^8423*25000000000000^6375 ≤ 3202523326559^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111277871 10000000000 3202523326559 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587506769/5000000000 : ℝ)^8423 ≤ (2093987854887/5000000000000 : ℝ)^6375 := by
    have hnat : (2587506769 : ℕ)^8423*5000000000000^6375 ≤ 2093987854887^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587506769 5000000000 2093987854887 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746372391/5000000000 : ℝ)^8423 ≤ (45310149578267/100000000000000 : ℝ)^6375 := by
    have hnat : (2746372391 : ℕ)^8423*100000000000000^6375 ≤ 45310149578267^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746372391 5000000000 45310149578267 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2111277871/10000000000 : ℝ), (2587506769/5000000000 : ℝ), (2746372391/5000000000 : ℝ)] ![(3202523326559/25000000000000 : ℝ), (2093987854887/5000000000000 : ℝ), (45310149578267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2111277871/10000000000 : ℝ)|^8423 ≤ (3202523326559/25000000000000 : ℝ)^6375
        have hw : |(-2111277871/10000000000 : ℝ)|=(2111277871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587506769/5000000000 : ℝ)|^8423 ≤ (2093987854887/5000000000000 : ℝ)^6375
        have hw : |(2587506769/5000000000 : ℝ)|=(2587506769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746372391/5000000000 : ℝ)|^8423 ≤ (45310149578267/100000000000000 : ℝ)^6375
        have hw : |(2746372391/5000000000 : ℝ)|=(2746372391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s2_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322006687/2500000000 : ℝ)*x 0 + (-979101739/5000000000 : ℝ)*x 1 + (2746372411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322006687/2500000000 : ℝ)^8423 ≤ (43092368967591/100000000000000 : ℝ)^6375 := by
    have hnat : (1322006687 : ℕ)^8423*100000000000000^6375 ≤ 43092368967591^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322006687 2500000000 43092368967591 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979101739/5000000000 : ℝ)^8423 ≤ (11597481013713/100000000000000 : ℝ)^6375 := by
    have hnat : (979101739 : ℕ)^8423*100000000000000^6375 ≤ 11597481013713^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979101739 5000000000 11597481013713 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746372411/5000000000 : ℝ)^8423 ≤ (45310150014233/100000000000000 : ℝ)^6375 := by
    have hnat : (2746372411 : ℕ)^8423*100000000000000^6375 ≤ 45310150014233^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746372411 5000000000 45310150014233 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322006687/2500000000 : ℝ), (-979101739/5000000000 : ℝ), (2746372411/5000000000 : ℝ)] ![(43092368967591/100000000000000 : ℝ), (11597481013713/100000000000000 : ℝ), (45310150014233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322006687/2500000000 : ℝ)|^8423 ≤ (43092368967591/100000000000000 : ℝ)^6375
        have hw : |(1322006687/2500000000 : ℝ)|=(1322006687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-979101739/5000000000 : ℝ)|^8423 ≤ (11597481013713/100000000000000 : ℝ)^6375
        have hw : |(-979101739/5000000000 : ℝ)|=(979101739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746372411/5000000000 : ℝ)|^8423 ≤ (45310150014233/100000000000000 : ℝ)^6375
        have hw : |(2746372411/5000000000 : ℝ)|=(2746372411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s2_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644013463/5000000000 : ℝ)*x 0 + (5492744883/10000000000 : ℝ)*x 1 + (-1958203147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644013463/5000000000 : ℝ)^8423 ≤ (43092370884111/100000000000000 : ℝ)^6375 := by
    have hnat : (2644013463 : ℕ)^8423*100000000000000^6375 ≤ 43092370884111^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644013463 5000000000 43092370884111 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492744883/10000000000 : ℝ)^8423 ≤ (22655075339541/50000000000000 : ℝ)^6375 := by
    have hnat : (5492744883 : ℕ)^8423*50000000000000^6375 ≤ 22655075339541^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492744883 10000000000 22655075339541 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1958203147/10000000000 : ℝ)^8423 ≤ (1159747842359/10000000000000 : ℝ)^6375 := by
    have hnat : (1958203147 : ℕ)^8423*10000000000000^6375 ≤ 1159747842359^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958203147 10000000000 1159747842359 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644013463/5000000000 : ℝ), (5492744883/10000000000 : ℝ), (-1958203147/10000000000 : ℝ)] ![(43092370884111/100000000000000 : ℝ), (22655075339541/50000000000000 : ℝ), (1159747842359/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644013463/5000000000 : ℝ)|^8423 ≤ (43092370884111/100000000000000 : ℝ)^6375
        have hw : |(2644013463/5000000000 : ℝ)|=(2644013463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492744883/10000000000 : ℝ)|^8423 ≤ (22655075339541/50000000000000 : ℝ)^6375
        have hw : |(5492744883/10000000000 : ℝ)|=(5492744883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1958203147/10000000000 : ℝ)|^8423 ≤ (1159747842359/10000000000000 : ℝ)^6375
        have hw : |(-1958203147/10000000000 : ℝ)|=(1958203147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s2_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2171817433/5000000000 : ℝ)*x 0 + (4676880213/10000000000 : ℝ)*x 1 + (4033832307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171817433/5000000000 : ℝ)^8423 ≤ (33228589861141/100000000000000 : ℝ)^6375 := by
    have hnat : (2171817433 : ℕ)^8423*100000000000000^6375 ≤ 33228589861141^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171817433 5000000000 33228589861141 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4676880213/10000000000 : ℝ)^8423 ≤ (1144927784429/3125000000000 : ℝ)^6375 := by
    have hnat : (4676880213 : ℕ)^8423*3125000000000^6375 ≤ 1144927784429^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4676880213 10000000000 1144927784429 3125000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4033832307/10000000000 : ℝ)^8423 ≤ (30133721020967/100000000000000 : ℝ)^6375 := by
    have hnat : (4033832307 : ℕ)^8423*100000000000000^6375 ≤ 30133721020967^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033832307 10000000000 30133721020967 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171817433/5000000000 : ℝ), (4676880213/10000000000 : ℝ), (4033832307/10000000000 : ℝ)] ![(33228589861141/100000000000000 : ℝ), (1144927784429/3125000000000 : ℝ), (30133721020967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171817433/5000000000 : ℝ)|^8423 ≤ (33228589861141/100000000000000 : ℝ)^6375
        have hw : |(2171817433/5000000000 : ℝ)|=(2171817433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4676880213/10000000000 : ℝ)|^8423 ≤ (1144927784429/3125000000000 : ℝ)^6375
        have hw : |(4676880213/10000000000 : ℝ)|=(4676880213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4033832307/10000000000 : ℝ)|^8423 ≤ (30133721020967/100000000000000 : ℝ)^6375
        have hw : |(4033832307/10000000000 : ℝ)|=(4033832307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (401/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (383/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (189/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3251/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (401/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (383/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (401/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (383/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (401/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (383/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (401/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (383/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (401/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (383/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (401/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (383/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (383/6250 : ℝ) ^ (4211/1024 : ℝ) ≤ (515294186428977/50000000000000000000 : ℝ) := by
    have hpowers : (383/6250 : ℝ)^4211 ≤ (515294186428977/50000000000000000000 : ℝ)^1024 := by
      have hnat : (383 : ℕ)^4211*50000000000000000000^1024 ≤ 515294186428977^1024*6250^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        383 6250 515294186428977 50000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (383/6250 : ℝ)) (X := (515294186428977/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (401/2000 : ℝ) ^ (4211/1024 : ℝ) ≤ (134921661601110897/100000000000000000000 : ℝ) := by
    have hpowers : (401/2000 : ℝ)^4211 ≤ (134921661601110897/100000000000000000000 : ℝ)^1024 := by
      have hnat : (401 : ℕ)^4211*100000000000000000000^1024 ≤ 134921661601110897^1024*2000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401 2000 134921661601110897 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (401/2000 : ℝ)) (X := (134921661601110897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000515294186428977/25000000000000000000 : ℝ) ≤ (5000025060894387/5000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (25000515294186428977/25000000000000000000 : ℝ)^1024 ≤ (5000025060894387/5000000000000000 : ℝ)^4211 := by
      have hnat : (25000515294186428977 : ℕ)^1024*5000000000000000^4211 ≤ 5000025060894387^4211*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000515294186428977 25000000000000000000 5000025060894387 5000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000025060894387/5000000000000000 : ℝ)) (X := (25000515294186428977/25000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100135952249973968851/100000000000000000000 : ℝ) ≤ (10003304287344397/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (100135952249973968851/100000000000000000000 : ℝ)^1024 ≤ (10003304287344397/10000000000000000 : ℝ)^4211 := by
      have hnat : (100135952249973968851 : ℕ)^1024*10000000000000000^4211 ≤ 10003304287344397^4211*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100135952249973968851 100000000000000000000 10003304287344397 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003304287344397/10000000000000000 : ℝ)) (X := (100135952249973968851/100000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50134921661601110897/50000000000000000000 : ℝ) ≤ (500327922645001/500000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50134921661601110897/50000000000000000000 : ℝ)^1024 ≤ (500327922645001/500000000000000 : ℝ)^4211 := by
      have hnat : (50134921661601110897 : ℕ)^1024*500000000000000^4211 ≤ 500327922645001^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50134921661601110897 50000000000000000000 500327922645001 500000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500327922645001/500000000000000 : ℝ)) (X := (50134921661601110897/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(515294186428977/50000000000000000000 : ℝ) ≤ ((6959040737124679807/6961000000000000000 : ℝ)+2*(3254165555623/1392200000000000 : ℝ)*(383/6250 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (6959040737124679807/6961000000000000000 : ℝ)+2*(3254165555623/1392200000000000 : ℝ)*(383/6250 : ℝ)=(5000025060894387/5000000000000000 : ℝ) by norm_num, show 1+2*(515294186428977/50000000000000000000 : ℝ)=(25000515294186428977/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(134921661601110897/100000000000000000000 : ℝ)+(515294186428977/50000000000000000000 : ℝ) ≤ ((6959040737124679807/6961000000000000000 : ℝ)+(3254165555623/1392200000000000 : ℝ)*((401/2000 : ℝ)+(383/6250 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (6959040737124679807/6961000000000000000 : ℝ)+(3254165555623/1392200000000000 : ℝ)*((401/2000 : ℝ)+(383/6250 : ℝ))=(10003304287344397/10000000000000000 : ℝ) by norm_num, show 1+(134921661601110897/100000000000000000000 : ℝ)+(515294186428977/50000000000000000000 : ℝ)=(100135952249973968851/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(134921661601110897/100000000000000000000 : ℝ) ≤ ((6959040737124679807/6961000000000000000 : ℝ)+2*(3254165555623/1392200000000000 : ℝ)*(401/2000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (6959040737124679807/6961000000000000000 : ℝ)+2*(3254165555623/1392200000000000 : ℝ)*(401/2000 : ℝ)=(500327922645001/500000000000000 : ℝ) by norm_num, show 1+2*(134921661601110897/100000000000000000000 : ℝ)=(50134921661601110897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6959040737124679807/6961000000000000000 : ℝ)*(X 1 0+X 2 0)+(3254165555623/1392200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (383/6250 : ℝ)) (hi := (401/2000 : ℝ)) (c := (6959040737124679807/6961000000000000000 : ℝ)) (alpha := (3254165555623/1392200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6959040737124679807/6961000000000000000 : ℝ)*(X 0 1+X 2 1)+(3254165555623/1392200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (383/6250 : ℝ)) (hi := (401/2000 : ℝ)) (c := (6959040737124679807/6961000000000000000 : ℝ)) (alpha := (3254165555623/1392200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6959040737124679807/6961000000000000000 : ℝ)*(X 0 2+X 1 2)+(3254165555623/1392200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (383/6250 : ℝ)) (hi := (401/2000 : ℝ)) (c := (6959040737124679807/6961000000000000000 : ℝ)) (alpha := (3254165555623/1392200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2111196913/10000000000 : ℝ)*X 0 0+(5494851327/10000000000 : ℝ)*X 0 1+(5172926711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370176163/10000000000 : ℝ)*X 1 0+(-2278021787/10000000000 : ℝ)*X 1 1+(5172926657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370175977/10000000000 : ℝ)*X 2 0+(5172926819/10000000000 : ℝ)*X 2 1+(-113901091/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343471561/10000000000 : ℝ)*X 0 0+(503696167/1250000000 : ℝ)*X 0 1+(2340551761/5000000000 : ℝ)*X 0 2+(4343471561/10000000000 : ℝ)*X 1 0+(503696167/1250000000 : ℝ)*X 1 1+(2340551761/5000000000 : ℝ)*X 1 2+(4343471561/10000000000 : ℝ)*X 2 0+(503696167/1250000000 : ℝ)*X 2 1+(2340551761/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2111277871/10000000000 : ℝ)*X 0 0+(2587506769/5000000000 : ℝ)*X 0 1+(2746372391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1322006687/2500000000 : ℝ)*X 1 0+(-979101739/5000000000 : ℝ)*X 1 1+(2746372411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644013463/5000000000 : ℝ)*X 2 0+(5492744883/10000000000 : ℝ)*X 2 1+(-1958203147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171817433/5000000000 : ℝ)*X 0 0+(4676880213/10000000000 : ℝ)*X 0 1+(4033832307/10000000000 : ℝ)*X 0 2+(2171817433/5000000000 : ℝ)*X 1 0+(4676880213/10000000000 : ℝ)*X 1 1+(4033832307/10000000000 : ℝ)*X 1 2+(2171817433/5000000000 : ℝ)*X 2 0+(4676880213/10000000000 : ℝ)*X 2 1+(4033832307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (336794783195189732243988369/43506250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1541948641/100000000000000 : ℝ)*(base19) + (6624147/500000000000 : ℝ)*(base23) + (2352751/4000000000000 : ℝ)*(lower2) + (245313047/100000000000000 : ℝ)*(upper3) + (106990377/100000000000000 : ℝ)*(upper5) + (580150712019261/25000000000000 : ℝ)*(major0) + (580150712019261/25000000000000 : ℝ)*(major1) + (580150712019261/25000000000000 : ℝ)*(major2) + (1553167386810273/50000000000000 : ℝ)*(sp0) + (1553174154849911/50000000000000 : ℝ)*(sp1) + (1553174263409531/50000000000000 : ℝ)*(sp2) + (767423285495369/50000000000000 : ℝ)*(sp3) + (15078027917/100000000000000 : ℝ)*(sp4) + (9015471659/100000000000000 : ℝ)*(sp7) + (1534855586462397/100000000000000 : ℝ)*(f.failure) + (3106349851648463/100000000000000 : ℝ)*(f.sum) + (204349977238071/34805000000000000000000000000 : ℝ)*base65 + (1422796337057202627/174025000000000000000000000000000 : ℝ)*base67 + (772212292842552627/174025000000000000000000000000000 : ℝ)*base69 + (927571745670327627/174025000000000000000000000000000 : ℝ)*base71 + (192362929401301/34805000000000000000000000000 : ℝ)*base73 + (2074501144147297373/174025000000000000000000000000000 : ℝ)*base76 + (2461022515093627627/174025000000000000000000000000000 : ℝ)*base77 + (1774201732224952627/174025000000000000000000000000000 : ℝ)*base79 + (131050779032539/34805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (32049489/10000000000000000000000 : ℝ)*base90 + (32049489/10000000000000000000000 : ℝ)*base92 + (32049489/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1352109077862974816301375189/174025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387407439/20000000000000 : ℝ)*(base19) + (2177601221/100000000000000 : ℝ)*(base23) + (101913/400000000000 : ℝ)*(upper2) + (128735527/50000000000000 : ℝ)*(upper3) + (154756999/100000000000000 : ℝ)*(upper5) + (1175601977322409/50000000000000 : ℝ)*(major0) + (1175601977322409/50000000000000 : ℝ)*(major1) + (1175601977322409/50000000000000 : ℝ)*(major2) + (19642107799/100000000000000 : ℝ)*(sp1) + (5041307037/20000000000000 : ℝ)*(sp2) + (3147312375085391/100000000000000 : ℝ)*(sp4) + (1573645397970199/50000000000000 : ℝ)*(sp5) + (1573642495474493/50000000000000 : ℝ)*(sp6) + (777547637608361/50000000000000 : ℝ)*(sp7) + (777547637608361/50000000000000 : ℝ)*(f.failure) + (3147312375085391/100000000000000 : ℝ)*(f.sum) + (3010510946111/1087656250000000000000000000 : ℝ)*base65 + (641349408759269937/348050000000000000000000000000000 : ℝ)*base68 + (2618009271971130063/348050000000000000000000000000000 : ℝ)*base69 + (1640198978063719937/348050000000000000000000000000000 : ℝ)*base72 + (41070495241481/17402500000000000000000000000 : ℝ)*base73 + (2474010028171719937/348050000000000000000000000000000 : ℝ)*base76 + (1684135567274280063/348050000000000000000000000000000 : ℝ)*base77 + (2168642160509019937/348050000000000000000000000000000 : ℝ)*base80 + (128736487628147/34805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1819757/5000000000000000000000 : ℝ)*base90 + (1819757/5000000000000000000000 : ℝ)*base92 + (1819757/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1230_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (401/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (383/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1230_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1230_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1230_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1230_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (189/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3251/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
