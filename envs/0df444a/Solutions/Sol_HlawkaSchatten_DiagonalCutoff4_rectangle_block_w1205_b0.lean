-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:43.459614+00:00
-- url     : https://prove2.me/submissions/97a8213b-a3e6-49fe-b72d-de6a22127985

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
theorem support_rectangle_w1205_s0_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-936015241/5000000000 : ℝ)*x 0 + (1207976697/2000000000 : ℝ)*x 1 + (95767761/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936015241/5000000000 : ℝ)^4199 ≤ (10904845249179/100000000000000 : ℝ)^3175 := by
    have hnat : (936015241 : ℕ)^4199*100000000000000^3175 ≤ 10904845249179^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936015241 5000000000 10904845249179 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207976697/2000000000 : ℝ)^4199 ≤ (10266820209283/20000000000000 : ℝ)^3175 := by
    have hnat : (1207976697 : ℕ)^4199*20000000000000^3175 ≤ 10266820209283^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207976697 2000000000 10266820209283 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95767761/200000000 : ℝ)^4199 ≤ (9440263422519/25000000000000 : ℝ)^3175 := by
    have hnat : (95767761 : ℕ)^4199*25000000000000^3175 ≤ 9440263422519^3175*200000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95767761 200000000 9440263422519 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936015241/5000000000 : ℝ), (1207976697/2000000000 : ℝ), (95767761/200000000 : ℝ)] ![(10904845249179/100000000000000 : ℝ), (10266820209283/20000000000000 : ℝ), (9440263422519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936015241/5000000000 : ℝ)|^4199 ≤ (10904845249179/100000000000000 : ℝ)^3175
        have hw : |(-936015241/5000000000 : ℝ)|=(936015241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1207976697/2000000000 : ℝ)|^4199 ≤ (10266820209283/20000000000000 : ℝ)^3175
        have hw : |(1207976697/2000000000 : ℝ)|=(1207976697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95767761/200000000 : ℝ)|^4199 ≤ (9440263422519/25000000000000 : ℝ)^3175
        have hw : |(95767761/200000000 : ℝ)|=(95767761/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s0_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5513244097/10000000000 : ℝ)*x 0 + (-258849211/1000000000 : ℝ)*x 1 + (957677607/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5513244097/10000000000 : ℝ)^4199 ≤ (2843714398207/6250000000000 : ℝ)^3175 := by
    have hnat : (5513244097 : ℕ)^4199*6250000000000^3175 ≤ 2843714398207^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5513244097 10000000000 2843714398207 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258849211/1000000000 : ℝ)^4199 ≤ (16739516085673/100000000000000 : ℝ)^3175 := by
    have hnat : (258849211 : ℕ)^4199*100000000000000^3175 ≤ 16739516085673^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258849211 1000000000 16739516085673 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957677607/2000000000 : ℝ)^4199 ≤ (9440263383409/25000000000000 : ℝ)^3175 := by
    have hnat : (957677607 : ℕ)^4199*25000000000000^3175 ≤ 9440263383409^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957677607 2000000000 9440263383409 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5513244097/10000000000 : ℝ), (-258849211/1000000000 : ℝ), (957677607/2000000000 : ℝ)] ![(2843714398207/6250000000000 : ℝ), (16739516085673/100000000000000 : ℝ), (9440263383409/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5513244097/10000000000 : ℝ)|^4199 ≤ (2843714398207/6250000000000 : ℝ)^3175
        have hw : |(5513244097/10000000000 : ℝ)|=(5513244097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258849211/1000000000 : ℝ)|^4199 ≤ (16739516085673/100000000000000 : ℝ)^3175
        have hw : |(-258849211/1000000000 : ℝ)|=(258849211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957677607/2000000000 : ℝ)|^4199 ≤ (9440263383409/25000000000000 : ℝ)^3175
        have hw : |(957677607/2000000000 : ℝ)|=(957677607/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s0_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1102648817/2000000000 : ℝ)*x 0 + (4788388047/10000000000 : ℝ)*x 1 + (-258849211/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102648817/2000000000 : ℝ)^4199 ≤ (45499430240339/100000000000000 : ℝ)^3175 := by
    have hnat : (1102648817 : ℕ)^4199*100000000000000^3175 ≤ 45499430240339^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102648817 2000000000 45499430240339 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4788388047/10000000000 : ℝ)^4199 ≤ (9440263414697/25000000000000 : ℝ)^3175 := by
    have hnat : (4788388047 : ℕ)^4199*25000000000000^3175 ≤ 9440263414697^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4788388047 10000000000 9440263414697 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258849211/1000000000 : ℝ)^4199 ≤ (16739516085673/100000000000000 : ℝ)^3175 := by
    have hnat : (258849211 : ℕ)^4199*100000000000000^3175 ≤ 16739516085673^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258849211 1000000000 16739516085673 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102648817/2000000000 : ℝ), (4788388047/10000000000 : ℝ), (-258849211/1000000000 : ℝ)] ![(45499430240339/100000000000000 : ℝ), (9440263414697/25000000000000 : ℝ), (16739516085673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102648817/2000000000 : ℝ)|^4199 ≤ (45499430240339/100000000000000 : ℝ)^3175
        have hw : |(1102648817/2000000000 : ℝ)|=(1102648817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4788388047/10000000000 : ℝ)|^4199 ≤ (9440263414697/25000000000000 : ℝ)^3175
        have hw : |(4788388047/10000000000 : ℝ)|=(4788388047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258849211/1000000000 : ℝ)|^4199 ≤ (16739516085673/100000000000000 : ℝ)^3175
        have hw : |(-258849211/1000000000 : ℝ)|=(258849211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s0_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839188613/2000000000 : ℝ)*x 0 + (311833803/1000000000 : ℝ)*x 1 + (2819479837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839188613/2000000000 : ℝ)^4199 ≤ (31709157537339/100000000000000 : ℝ)^3175 := by
    have hnat : (839188613 : ℕ)^4199*100000000000000^3175 ≤ 31709157537339^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839188613 2000000000 31709157537339 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311833803/1000000000 : ℝ)^4199 ≤ (21414279078473/100000000000000 : ℝ)^3175 := by
    have hnat : (311833803 : ℕ)^4199*100000000000000^3175 ≤ 21414279078473^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311833803 1000000000 21414279078473 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2819479837/5000000000 : ℝ)^4199 ≤ (46876563372229/100000000000000 : ℝ)^3175 := by
    have hnat : (2819479837 : ℕ)^4199*100000000000000^3175 ≤ 46876563372229^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819479837 5000000000 46876563372229 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839188613/2000000000 : ℝ), (311833803/1000000000 : ℝ), (2819479837/5000000000 : ℝ)] ![(31709157537339/100000000000000 : ℝ), (21414279078473/100000000000000 : ℝ), (46876563372229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839188613/2000000000 : ℝ)|^4199 ≤ (31709157537339/100000000000000 : ℝ)^3175
        have hw : |(839188613/2000000000 : ℝ)|=(839188613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311833803/1000000000 : ℝ)|^4199 ≤ (21414279078473/100000000000000 : ℝ)^3175
        have hw : |(311833803/1000000000 : ℝ)|=(311833803/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2819479837/5000000000 : ℝ)|^4199 ≤ (46876563372229/100000000000000 : ℝ)^3175
        have hw : |(2819479837/5000000000 : ℝ)|=(2819479837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s0_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1876993733/10000000000 : ℝ)*x 0 + (4820639771/10000000000 : ℝ)*x 1 + (6006493347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1876993733/10000000000 : ℝ)^4199 ≤ (10943097809037/100000000000000 : ℝ)^3175 := by
    have hnat : (1876993733 : ℕ)^4199*100000000000000^3175 ≤ 10943097809037^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876993733 10000000000 10943097809037 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4820639771/10000000000 : ℝ)^4199 ≤ (19048891353943/50000000000000 : ℝ)^3175 := by
    have hnat : (4820639771 : ℕ)^4199*50000000000000^3175 ≤ 19048891353943^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4820639771 10000000000 19048891353943 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6006493347/10000000000 : ℝ)^4199 ≤ (1592472483367/3125000000000 : ℝ)^3175 := by
    have hnat : (6006493347 : ℕ)^4199*3125000000000^3175 ≤ 1592472483367^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006493347 10000000000 1592472483367 3125000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1876993733/10000000000 : ℝ), (4820639771/10000000000 : ℝ), (6006493347/10000000000 : ℝ)] ![(10943097809037/100000000000000 : ℝ), (19048891353943/50000000000000 : ℝ), (1592472483367/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1876993733/10000000000 : ℝ)|^4199 ≤ (10943097809037/100000000000000 : ℝ)^3175
        have hw : |(-1876993733/10000000000 : ℝ)|=(1876993733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4820639771/10000000000 : ℝ)|^4199 ≤ (19048891353943/50000000000000 : ℝ)^3175
        have hw : |(4820639771/10000000000 : ℝ)|=(4820639771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6006493347/10000000000 : ℝ)|^4199 ≤ (1592472483367/3125000000000 : ℝ)^3175
        have hw : |(6006493347/10000000000 : ℝ)|=(6006493347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s0_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034578301/2000000000 : ℝ)*x 0 + (-685192683/5000000000 : ℝ)*x 1 + (6006494931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034578301/2000000000 : ℝ)^4199 ≤ (41822187647199/100000000000000 : ℝ)^3175 := by
    have hnat : (1034578301 : ℕ)^4199*100000000000000^3175 ≤ 41822187647199^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034578301 2000000000 41822187647199 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685192683/5000000000 : ℝ)^4199 ≤ (7218675104409/100000000000000 : ℝ)^3175 := by
    have hnat : (685192683 : ℕ)^4199*100000000000000^3175 ≤ 7218675104409^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685192683 5000000000 7218675104409 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6006494931/10000000000 : ℝ)^4199 ≤ (50959137240643/100000000000000 : ℝ)^3175 := by
    have hnat : (6006494931 : ℕ)^4199*100000000000000^3175 ≤ 50959137240643^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6006494931 10000000000 50959137240643 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034578301/2000000000 : ℝ), (-685192683/5000000000 : ℝ), (6006494931/10000000000 : ℝ)] ![(41822187647199/100000000000000 : ℝ), (7218675104409/100000000000000 : ℝ), (50959137240643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034578301/2000000000 : ℝ)|^4199 ≤ (41822187647199/100000000000000 : ℝ)^3175
        have hw : |(1034578301/2000000000 : ℝ)|=(1034578301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-685192683/5000000000 : ℝ)|^4199 ≤ (7218675104409/100000000000000 : ℝ)^3175
        have hw : |(-685192683/5000000000 : ℝ)|=(685192683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6006494931/10000000000 : ℝ)|^4199 ≤ (50959137240643/100000000000000 : ℝ)^3175
        have hw : |(6006494931/10000000000 : ℝ)|=(6006494931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s0_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2586446139/5000000000 : ℝ)*x 0 + (1501623463/2500000000 : ℝ)*x 1 + (-1370385917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586446139/5000000000 : ℝ)^4199 ≤ (4182219591243/10000000000000 : ℝ)^3175 := by
    have hnat : (2586446139 : ℕ)^4199*10000000000000^3175 ≤ 4182219591243^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586446139 5000000000 4182219591243 10000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1501623463/2500000000 : ℝ)^4199 ≤ (25479562566989/50000000000000 : ℝ)^3175 := by
    have hnat : (1501623463 : ℕ)^4199*50000000000000^3175 ≤ 25479562566989^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501623463 2500000000 25479562566989 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370385917/10000000000 : ℝ)^4199 ≤ (7218678942971/100000000000000 : ℝ)^3175 := by
    have hnat : (1370385917 : ℕ)^4199*100000000000000^3175 ≤ 7218678942971^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370385917 10000000000 7218678942971 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586446139/5000000000 : ℝ), (1501623463/2500000000 : ℝ), (-1370385917/10000000000 : ℝ)] ![(4182219591243/10000000000000 : ℝ), (25479562566989/50000000000000 : ℝ), (7218678942971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586446139/5000000000 : ℝ)|^4199 ≤ (4182219591243/10000000000000 : ℝ)^3175
        have hw : |(2586446139/5000000000 : ℝ)|=(2586446139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1501623463/2500000000 : ℝ)|^4199 ≤ (25479562566989/50000000000000 : ℝ)^3175
        have hw : |(1501623463/2500000000 : ℝ)|=(1501623463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1370385917/10000000000 : ℝ)|^4199 ≤ (7218678942971/100000000000000 : ℝ)^3175
        have hw : |(-1370385917/10000000000 : ℝ)|=(1370385917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s0_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525742303/1250000000 : ℝ)*x 0 + (5574005343/10000000000 : ℝ)*x 1 + (127423379/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525742303/1250000000 : ℝ)^4199 ≤ (7952273407749/25000000000000 : ℝ)^3175 := by
    have hnat : (525742303 : ℕ)^4199*25000000000000^3175 ≤ 7952273407749^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525742303 1250000000 7952273407749 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5574005343/10000000000 : ℝ)^4199 ≤ (4616378016663/10000000000000 : ℝ)^3175 := by
    have hnat : (5574005343 : ℕ)^4199*10000000000000^3175 ≤ 4616378016663^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5574005343 10000000000 4616378016663 10000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127423379/400000000 : ℝ)^4199 ≤ (2753390772347/12500000000000 : ℝ)^3175 := by
    have hnat : (127423379 : ℕ)^4199*12500000000000^3175 ≤ 2753390772347^3175*400000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127423379 400000000 2753390772347 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525742303/1250000000 : ℝ), (5574005343/10000000000 : ℝ), (127423379/400000000 : ℝ)] ![(7952273407749/25000000000000 : ℝ), (4616378016663/10000000000000 : ℝ), (2753390772347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525742303/1250000000 : ℝ)|^4199 ≤ (7952273407749/25000000000000 : ℝ)^3175
        have hw : |(525742303/1250000000 : ℝ)|=(525742303/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5574005343/10000000000 : ℝ)|^4199 ≤ (4616378016663/10000000000000 : ℝ)^3175
        have hw : |(5574005343/10000000000 : ℝ)|=(5574005343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(127423379/400000000 : ℝ)|^4199 ≤ (2753390772347/12500000000000 : ℝ)^3175
        have hw : |(127423379/400000000 : ℝ)|=(127423379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (67/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1103/4000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (8397/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8397 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8397*1^2048 ≤ 0^2048*1^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8397/2048 : ℝ) ≤ (2335646447044305407/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8397 ≤ (2335646447044305407/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8397*100000000000000000000^2048 ≤ 2335646447044305407^2048*5^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2335646447044305407 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2335646447044305407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8397 := by
      have hnat : (1 : ℕ)^2048*1^8397 ≤ 1^8397*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102335646447044305407/100000000000000000000 : ℝ) ≤ (2011293878865381/2000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (102335646447044305407/100000000000000000000 : ℝ)^2048 ≤ (2011293878865381/2000000000000000 : ℝ)^8397 := by
      have hnat : (102335646447044305407 : ℕ)^2048*2000000000000000^8397 ≤ 2011293878865381^8397*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102335646447044305407 100000000000000000000 2011293878865381 2000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011293878865381/2000000000000000 : ℝ)) (X := (102335646447044305407/100000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52335646447044305407/50000000000000000000 : ℝ) ≤ (1011293878865381/1000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (52335646447044305407/50000000000000000000 : ℝ)^2048 ≤ (1011293878865381/1000000000000000 : ℝ)^8397 := by
      have hnat : (52335646447044305407 : ℕ)^2048*1000000000000000^8397 ≤ 1011293878865381^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52335646447044305407 50000000000000000000 1011293878865381 1000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011293878865381/1000000000000000 : ℝ)) (X := (52335646447044305407/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11293878865381/800000000000000 : ℝ)*(0 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11293878865381/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2335646447044305407/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11293878865381/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11293878865381/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011293878865381/2000000000000000 : ℝ) by norm_num, show 1+(2335646447044305407/100000000000000000000 : ℝ)+(0 : ℝ)=(102335646447044305407/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2335646447044305407/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11293878865381/800000000000000 : ℝ)*(2/5 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11293878865381/800000000000000 : ℝ)*(2/5 : ℝ)=(1011293878865381/1000000000000000 : ℝ) by norm_num, show 1+2*(2335646447044305407/100000000000000000000 : ℝ)=(52335646447044305407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11293878865381/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11293878865381/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11293878865381/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11293878865381/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11293878865381/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11293878865381/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-936015241/5000000000 : ℝ)*X 0 0+(1207976697/2000000000 : ℝ)*X 0 1+(95767761/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5513244097/10000000000 : ℝ)*X 1 0+(-258849211/1000000000 : ℝ)*X 1 1+(957677607/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1102648817/2000000000 : ℝ)*X 2 0+(4788388047/10000000000 : ℝ)*X 2 1+(-258849211/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((839188613/2000000000 : ℝ)*X 0 0+(311833803/1000000000 : ℝ)*X 0 1+(2819479837/5000000000 : ℝ)*X 0 2+(839188613/2000000000 : ℝ)*X 1 0+(311833803/1000000000 : ℝ)*X 1 1+(2819479837/5000000000 : ℝ)*X 1 2+(839188613/2000000000 : ℝ)*X 2 0+(311833803/1000000000 : ℝ)*X 2 1+(2819479837/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1876993733/10000000000 : ℝ)*X 0 0+(4820639771/10000000000 : ℝ)*X 0 1+(6006493347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1034578301/2000000000 : ℝ)*X 1 0+(-685192683/5000000000 : ℝ)*X 1 1+(6006494931/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2586446139/5000000000 : ℝ)*X 2 0+(1501623463/2500000000 : ℝ)*X 2 1+(-1370385917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((525742303/1250000000 : ℝ)*X 0 0+(5574005343/10000000000 : ℝ)*X 0 1+(127423379/400000000 : ℝ)*X 0 2+(525742303/1250000000 : ℝ)*X 1 0+(5574005343/10000000000 : ℝ)*X 1 1+(127423379/400000000 : ℝ)*X 1 2+(525742303/1250000000 : ℝ)*X 2 0+(5574005343/10000000000 : ℝ)*X 2 1+(127423379/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (960136981765101087/200000000000000000000000 : ℝ) := by norm_num
    linear_combination (52504251/100000000000000 : ℝ)*(base1) + (1176355423/100000000000000 : ℝ)*(base19) + (218805429/20000000000000 : ℝ)*(base23) + (16117817/20000000000000 : ℝ)*(base24) + (53858633/20000000000000 : ℝ)*(upper3) + (298945400513833/50000000000000 : ℝ)*(major0) + (298945400513833/50000000000000 : ℝ)*(major1) + (298945400513833/50000000000000 : ℝ)*(major2) + (31961921711599/4000000000000 : ℝ)*(sp0) + (199762354982053/25000000000000 : ℝ)*(sp1) + (199762355416851/25000000000000 : ℝ)*(sp2) + (396728734425087/100000000000000 : ℝ)*(sp3) + (2605997911/100000000000000 : ℝ)*(sp4) + (1029409763/50000000000000 : ℝ)*(sp7) + (3099459732413/781250000000 : ℝ)*(f.failure) + (159810119256727/20000000000000 : ℝ)*(f.sum) + (10392144004627/20000000000000000000000000000 : ℝ)*base66 + (99562256044627/40000000000000000000000000000 : ℝ)*base68 + (49392541115373/40000000000000000000000000000 : ℝ)*base69 + (43835694404627/40000000000000000000000000000 : ℝ)*base72 + (36073138844627/20000000000000000000000000000 : ℝ)*base74 + (90678995373/40000000000000000000000000000 : ℝ)*base75 + (77462674555373/40000000000000000000000000000 : ℝ)*base77 + (144936194675373/40000000000000000000000000000 : ℝ)*base79 + (2432074355373/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (33057/7812500000000000000 : ℝ)*base89 + (33057/7812500000000000000 : ℝ)*base91 + (33057/7812500000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5705129266612686045273/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120798403/20000000000000 : ℝ)*(base19) + (43722137/5000000000000 : ℝ)*(base23) + (28819341/20000000000000 : ℝ)*(base39) + (17568569/10000000000000 : ℝ)*(upper3) + (14893739/50000000000000 : ℝ)*(upper5) + (31548993934491/5000000000000 : ℝ)*(major0) + (31548993934491/5000000000000 : ℝ)*(major1) + (157744933648279/25000000000000 : ℝ)*(major2) + (163444751/10000000000000 : ℝ)*(sp1) + (424852829/25000000000000 : ℝ)*(sp2) + (168654482316829/20000000000000 : ℝ)*(sp4) + (843270173144621/100000000000000 : ℝ)*(sp5) + (421634990913397/50000000000000 : ℝ)*(sp6) + (83737425126079/20000000000000 : ℝ)*(sp7) + (83737425126079/20000000000000 : ℝ)*(f.failure) + (16865451113617/2000000000000 : ℝ)*(f.sum) + (1510315895173/10000000000000000000000000000 : ℝ)*base66 + (63103182270701/20000000000000000000000000000 : ℝ)*base68 + (25027082003929/4000000000000000000000000000 : ℝ)*base70 + (154118367770701/20000000000000000000000000000 : ℝ)*base72 + (13255645064827/10000000000000000000000000000 : ℝ)*base73 + (10678184747929/4000000000000000000000000000 : ℝ)*base76 + (28685718531929/4000000000000000000000000000 : ℝ)*base78 + (4069921543929/4000000000000000000000000000 : ℝ)*base80 + (5450959777929/2000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (878681/200000000000000000000 : ℝ)*base89 + (878681/200000000000000000000 : ℝ)*base91 + (1121319/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1205_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (67/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1103/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1205_s1_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072134491/10000000000 : ℝ)*x 0 + (5684990753/10000000000 : ℝ)*x 1 + (5015189791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072134491/10000000000 : ℝ)^4199 ≤ (6236189062651/50000000000000 : ℝ)^3175 := by
    have hnat : (2072134491 : ℕ)^4199*50000000000000^3175 ≤ 6236189062651^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072134491 10000000000 6236189062651 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5684990753/10000000000 : ℝ)^4199 ≤ (47383297721691/100000000000000 : ℝ)^3175 := by
    have hnat : (5684990753 : ℕ)^4199*100000000000000^3175 ≤ 47383297721691^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5684990753 10000000000 47383297721691 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015189791/10000000000 : ℝ)^4199 ≤ (4014432414023/10000000000000 : ℝ)^3175 := by
    have hnat : (5015189791 : ℕ)^4199*10000000000000^3175 ≤ 4014432414023^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015189791 10000000000 4014432414023 10000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072134491/10000000000 : ℝ), (5684990753/10000000000 : ℝ), (5015189791/10000000000 : ℝ)] ![(6236189062651/50000000000000 : ℝ), (47383297721691/100000000000000 : ℝ), (4014432414023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072134491/10000000000 : ℝ)|^4199 ≤ (6236189062651/50000000000000 : ℝ)^3175
        have hw : |(-2072134491/10000000000 : ℝ)|=(2072134491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5684990753/10000000000 : ℝ)|^4199 ≤ (47383297721691/100000000000000 : ℝ)^3175
        have hw : |(5684990753/10000000000 : ℝ)|=(5684990753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015189791/10000000000 : ℝ)|^4199 ≤ (4014432414023/10000000000000 : ℝ)^3175
        have hw : |(5015189791/10000000000 : ℝ)|=(5015189791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s1_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707835463/5000000000 : ℝ)*x 0 + (-1216227339/5000000000 : ℝ)*x 1 + (1253797559/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707835463/5000000000 : ℝ)^4199 ≤ (44437526847621/100000000000000 : ℝ)^3175 := by
    have hnat : (2707835463 : ℕ)^4199*100000000000000^3175 ≤ 44437526847621^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707835463 5000000000 44437526847621 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1216227339/5000000000 : ℝ)^4199 ≤ (963634017947/6250000000000 : ℝ)^3175 := by
    have hnat : (1216227339 : ℕ)^4199*6250000000000^3175 ≤ 963634017947^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216227339 5000000000 963634017947 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253797559/2500000000 : ℝ)^4199 ≤ (40144328851077/100000000000000 : ℝ)^3175 := by
    have hnat : (1253797559 : ℕ)^4199*100000000000000^3175 ≤ 40144328851077^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253797559 2500000000 40144328851077 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707835463/5000000000 : ℝ), (-1216227339/5000000000 : ℝ), (1253797559/2500000000 : ℝ)] ![(44437526847621/100000000000000 : ℝ), (963634017947/6250000000000 : ℝ), (40144328851077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707835463/5000000000 : ℝ)|^4199 ≤ (44437526847621/100000000000000 : ℝ)^3175
        have hw : |(2707835463/5000000000 : ℝ)|=(2707835463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1216227339/5000000000 : ℝ)|^4199 ≤ (963634017947/6250000000000 : ℝ)^3175
        have hw : |(-1216227339/5000000000 : ℝ)|=(1216227339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1253797559/2500000000 : ℝ)|^4199 ≤ (40144328851077/100000000000000 : ℝ)^3175
        have hw : |(1253797559/2500000000 : ℝ)|=(1253797559/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s1_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5415669719/10000000000 : ℝ)*x 0 + (156724719/312500000 : ℝ)*x 1 + (-1216227633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415669719/10000000000 : ℝ)^4199 ≤ (1110937843739/2500000000000 : ℝ)^3175 := by
    have hnat : (5415669719 : ℕ)^4199*2500000000000^3175 ≤ 1110937843739^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415669719 10000000000 1110937843739 2500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156724719/312500000 : ℝ)^4199 ≤ (40144337023601/100000000000000 : ℝ)^3175 := by
    have hnat : (156724719 : ℕ)^4199*100000000000000^3175 ≤ 40144337023601^3175*312500000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156724719 312500000 40144337023601 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216227633/5000000000 : ℝ)^4199 ≤ (15418149216243/100000000000000 : ℝ)^3175 := by
    have hnat : (1216227633 : ℕ)^4199*100000000000000^3175 ≤ 15418149216243^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216227633 5000000000 15418149216243 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415669719/10000000000 : ℝ), (156724719/312500000 : ℝ), (-1216227633/5000000000 : ℝ)] ![(1110937843739/2500000000000 : ℝ), (40144337023601/100000000000000 : ℝ), (15418149216243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415669719/10000000000 : ℝ)|^4199 ≤ (1110937843739/2500000000000 : ℝ)^3175
        have hw : |(5415669719/10000000000 : ℝ)|=(5415669719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156724719/312500000 : ℝ)|^4199 ≤ (40144337023601/100000000000000 : ℝ)^3175
        have hw : |(156724719/312500000 : ℝ)|=(156724719/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1216227633/5000000000 : ℝ)|^4199 ≤ (15418149216243/100000000000000 : ℝ)^3175
        have hw : |(-1216227633/5000000000 : ℝ)|=(1216227633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s1_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156028469/5000000000 : ℝ)*x 0 + (3688738007/10000000000 : ℝ)*x 1 + (503777669/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156028469/5000000000 : ℝ)^4199 ≤ (32874794182789/100000000000000 : ℝ)^3175 := by
    have hnat : (2156028469 : ℕ)^4199*100000000000000^3175 ≤ 32874794182789^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156028469 5000000000 32874794182789 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3688738007/10000000000 : ℝ)^4199 ≤ (6685399846351/25000000000000 : ℝ)^3175 := by
    have hnat : (3688738007 : ℕ)^4199*25000000000000^3175 ≤ 6685399846351^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3688738007 10000000000 6685399846351 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (503777669/1000000000 : ℝ)^4199 ≤ (20191803202739/50000000000000 : ℝ)^3175 := by
    have hnat : (503777669 : ℕ)^4199*50000000000000^3175 ≤ 20191803202739^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503777669 1000000000 20191803202739 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156028469/5000000000 : ℝ), (3688738007/10000000000 : ℝ), (503777669/1000000000 : ℝ)] ![(32874794182789/100000000000000 : ℝ), (6685399846351/25000000000000 : ℝ), (20191803202739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156028469/5000000000 : ℝ)|^4199 ≤ (32874794182789/100000000000000 : ℝ)^3175
        have hw : |(2156028469/5000000000 : ℝ)|=(2156028469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3688738007/10000000000 : ℝ)|^4199 ≤ (6685399846351/25000000000000 : ℝ)^3175
        have hw : |(3688738007/10000000000 : ℝ)|=(3688738007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(503777669/1000000000 : ℝ)|^4199 ≤ (20191803202739/50000000000000 : ℝ)^3175
        have hw : |(503777669/1000000000 : ℝ)|=(503777669/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s1_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072854503/10000000000 : ℝ)*x 0 + (5024115457/10000000000 : ℝ)*x 1 + (1135178791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072854503/10000000000 : ℝ)^4199 ≤ (12478110011263/100000000000000 : ℝ)^3175 := by
    have hnat : (2072854503 : ℕ)^4199*100000000000000^3175 ≤ 12478110011263^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072854503 10000000000 12478110011263 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5024115457/10000000000 : ℝ)^4199 ≤ (20119419938947/50000000000000 : ℝ)^3175 := by
    have hnat : (5024115457 : ℕ)^4199*50000000000000^3175 ≤ 20119419938947^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024115457 10000000000 20119419938947 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135178791/2000000000 : ℝ)^4199 ≤ (2364152504787/5000000000000 : ℝ)^3175 := by
    have hnat : (1135178791 : ℕ)^4199*5000000000000^3175 ≤ 2364152504787^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135178791 2000000000 2364152504787 5000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072854503/10000000000 : ℝ), (5024115457/10000000000 : ℝ), (1135178791/2000000000 : ℝ)] ![(12478110011263/100000000000000 : ℝ), (20119419938947/50000000000000 : ℝ), (2364152504787/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072854503/10000000000 : ℝ)|^4199 ≤ (12478110011263/100000000000000 : ℝ)^3175
        have hw : |(-2072854503/10000000000 : ℝ)|=(2072854503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5024115457/10000000000 : ℝ)|^4199 ≤ (20119419938947/50000000000000 : ℝ)^3175
        have hw : |(5024115457/10000000000 : ℝ)|=(5024115457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135178791/2000000000 : ℝ)|^4199 ≤ (2364152504787/5000000000000 : ℝ)^3175
        have hw : |(1135178791/2000000000 : ℝ)|=(1135178791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s1_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5243414017/10000000000 : ℝ)*x 0 + (-1771753127/10000000000 : ℝ)*x 1 + (5675891819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5243414017/10000000000 : ℝ)^4199 ≤ (42577895811493/100000000000000 : ℝ)^3175 := by
    have hnat : (5243414017 : ℕ)^4199*100000000000000^3175 ≤ 42577895811493^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243414017 10000000000 42577895811493 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1771753127/10000000000 : ℝ)^4199 ≤ (2534769401801/25000000000000 : ℝ)^3175 := by
    have hnat : (1771753127 : ℕ)^4199*25000000000000^3175 ≤ 2534769401801^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771753127 10000000000 2534769401801 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5675891819/10000000000 : ℝ)^4199 ≤ (47283026562887/100000000000000 : ℝ)^3175 := by
    have hnat : (5675891819 : ℕ)^4199*100000000000000^3175 ≤ 47283026562887^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675891819 10000000000 47283026562887 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5243414017/10000000000 : ℝ), (-1771753127/10000000000 : ℝ), (5675891819/10000000000 : ℝ)] ![(42577895811493/100000000000000 : ℝ), (2534769401801/25000000000000 : ℝ), (47283026562887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5243414017/10000000000 : ℝ)|^4199 ≤ (42577895811493/100000000000000 : ℝ)^3175
        have hw : |(5243414017/10000000000 : ℝ)|=(5243414017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1771753127/10000000000 : ℝ)|^4199 ≤ (2534769401801/25000000000000 : ℝ)^3175
        have hw : |(-1771753127/10000000000 : ℝ)|=(1771753127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5675891819/10000000000 : ℝ)|^4199 ≤ (47283026562887/100000000000000 : ℝ)^3175
        have hw : |(5675891819/10000000000 : ℝ)|=(5675891819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s1_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048682827/2000000000 : ℝ)*x 0 + (5675892301/10000000000 : ℝ)*x 1 + (-885876129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048682827/2000000000 : ℝ)^4199 ≤ (42577897078719/100000000000000 : ℝ)^3175 := by
    have hnat : (1048682827 : ℕ)^4199*100000000000000^3175 ≤ 42577897078719^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048682827 2000000000 42577897078719 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5675892301/10000000000 : ℝ)^4199 ≤ (47283031873203/100000000000000 : ℝ)^3175 := by
    have hnat : (5675892301 : ℕ)^4199*100000000000000^3175 ≤ 47283031873203^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5675892301 10000000000 47283031873203 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (885876129/5000000000 : ℝ)^4199 ≤ (5069535515183/50000000000000 : ℝ)^3175 := by
    have hnat : (885876129 : ℕ)^4199*50000000000000^3175 ≤ 5069535515183^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885876129 5000000000 5069535515183 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048682827/2000000000 : ℝ), (5675892301/10000000000 : ℝ), (-885876129/5000000000 : ℝ)] ![(42577897078719/100000000000000 : ℝ), (47283031873203/100000000000000 : ℝ), (5069535515183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048682827/2000000000 : ℝ)|^4199 ≤ (42577897078719/100000000000000 : ℝ)^3175
        have hw : |(1048682827/2000000000 : ℝ)|=(1048682827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5675892301/10000000000 : ℝ)|^4199 ≤ (47283031873203/100000000000000 : ℝ)^3175
        have hw : |(5675892301/10000000000 : ℝ)|=(5675892301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-885876129/5000000000 : ℝ)|^4199 ≤ (5069535515183/50000000000000 : ℝ)^3175
        have hw : |(-885876129/5000000000 : ℝ)|=(885876129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s1_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4313509837/10000000000 : ℝ)*x 0 + (627474737/1250000000 : ℝ)*x 1 + (3707063913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313509837/10000000000 : ℝ)^4199 ≤ (8222361063371/25000000000000 : ℝ)^3175 := by
    have hnat : (4313509837 : ℕ)^4199*25000000000000^3175 ≤ 8222361063371^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313509837 10000000000 8222361063371 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627474737/1250000000 : ℝ)^4199 ≤ (8038622711267/20000000000000 : ℝ)^3175 := by
    have hnat : (627474737 : ℕ)^4199*20000000000000^3175 ≤ 8038622711267^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627474737 1250000000 8038622711267 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3707063913/10000000000 : ℝ)^4199 ≤ (13458721089349/50000000000000 : ℝ)^3175 := by
    have hnat : (3707063913 : ℕ)^4199*50000000000000^3175 ≤ 13458721089349^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3707063913 10000000000 13458721089349 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313509837/10000000000 : ℝ), (627474737/1250000000 : ℝ), (3707063913/10000000000 : ℝ)] ![(8222361063371/25000000000000 : ℝ), (8038622711267/20000000000000 : ℝ), (13458721089349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313509837/10000000000 : ℝ)|^4199 ≤ (8222361063371/25000000000000 : ℝ)^3175
        have hw : |(4313509837/10000000000 : ℝ)|=(4313509837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627474737/1250000000 : ℝ)|^4199 ≤ (8038622711267/20000000000000 : ℝ)^3175
        have hw : |(627474737/1250000000 : ℝ)|=(627474737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3707063913/10000000000 : ℝ)|^4199 ≤ (13458721089349/50000000000000 : ℝ)^3175
        have hw : |(3707063913/10000000000 : ℝ)|=(3707063913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1103/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (1199/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20157/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1103/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (67/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1103/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (67/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1103/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (67/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1103/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (67/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1103/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (67/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1103/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (67/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (67/10000 : ℝ) ^ (8397/2048 : ℝ) ≤ (30523505027/25000000000000000000 : ℝ) := by
    have hpowers : (67/10000 : ℝ)^8397 ≤ (30523505027/25000000000000000000 : ℝ)^2048 := by
      have hnat : (67 : ℕ)^8397*25000000000000000000^2048 ≤ 30523505027^2048*10000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67 10000 30523505027 25000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67/10000 : ℝ)) (X := (30523505027/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1103/4000 : ℝ) ^ (8397/2048 : ℝ) ≤ (254114240646828139/50000000000000000000 : ℝ) := by
    have hpowers : (1103/4000 : ℝ)^8397 ≤ (254114240646828139/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1103 : ℕ)^8397*50000000000000000000^2048 ≤ 254114240646828139^2048*4000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1103 4000 254114240646828139 50000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1103/4000 : ℝ)) (X := (254114240646828139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000030523505027/12500000000000000000 : ℝ) ≤ (625000000372229/625000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (12500000030523505027/12500000000000000000 : ℝ)^2048 ≤ (625000000372229/625000000000000 : ℝ)^8397 := by
      have hnat : (12500000030523505027 : ℕ)^2048*625000000000000^8397 ≤ 625000000372229^8397*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000030523505027 12500000000000000000 625000000372229 625000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625000000372229/625000000000000 : ℝ)) (X := (12500000030523505027/12500000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50254114301693838193/50000000000000000000 : ℝ) ≤ (10012371778608487/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50254114301693838193/50000000000000000000 : ℝ)^2048 ≤ (10012371778608487/10000000000000000 : ℝ)^8397 := by
      have hnat : (50254114301693838193 : ℕ)^2048*10000000000000000^8397 ≤ 10012371778608487^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50254114301693838193 50000000000000000000 10012371778608487 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012371778608487/10000000000000000 : ℝ)) (X := (50254114301693838193/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25254114240646828139/25000000000000000000 : ℝ) ≤ (1002474355126131/1000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (25254114240646828139/25000000000000000000 : ℝ)^2048 ≤ (1002474355126131/1000000000000000 : ℝ)^8397 := by
      have hnat : (25254114240646828139 : ℕ)^2048*1000000000000000^8397 ≤ 1002474355126131^8397*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25254114240646828139 25000000000000000000 1002474355126131 1000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002474355126131/1000000000000000 : ℝ)) (X := (25254114240646828139/25000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(30523505027/25000000000000000000 : ℝ) ≤ ((2690334219848823571/2690500000000000000 : ℝ)+2*(12371772652823/2690500000000000 : ℝ)*(67/10000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (2690334219848823571/2690500000000000000 : ℝ)+2*(12371772652823/2690500000000000 : ℝ)*(67/10000 : ℝ)=(625000000372229/625000000000000 : ℝ) by norm_num, show 1+2*(30523505027/25000000000000000000 : ℝ)=(12500000030523505027/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(254114240646828139/50000000000000000000 : ℝ)+(30523505027/25000000000000000000 : ℝ) ≤ ((2690334219848823571/2690500000000000000 : ℝ)+(12371772652823/2690500000000000 : ℝ)*((1103/4000 : ℝ)+(67/10000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (2690334219848823571/2690500000000000000 : ℝ)+(12371772652823/2690500000000000 : ℝ)*((1103/4000 : ℝ)+(67/10000 : ℝ))=(10012371778608487/10000000000000000 : ℝ) by norm_num, show 1+(254114240646828139/50000000000000000000 : ℝ)+(30523505027/25000000000000000000 : ℝ)=(50254114301693838193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(254114240646828139/50000000000000000000 : ℝ) ≤ ((2690334219848823571/2690500000000000000 : ℝ)+2*(12371772652823/2690500000000000 : ℝ)*(1103/4000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (2690334219848823571/2690500000000000000 : ℝ)+2*(12371772652823/2690500000000000 : ℝ)*(1103/4000 : ℝ)=(1002474355126131/1000000000000000 : ℝ) by norm_num, show 1+2*(254114240646828139/50000000000000000000 : ℝ)=(25254114240646828139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2690334219848823571/2690500000000000000 : ℝ)*(X 1 0+X 2 0)+(12371772652823/2690500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (67/10000 : ℝ)) (hi := (1103/4000 : ℝ)) (c := (2690334219848823571/2690500000000000000 : ℝ)) (alpha := (12371772652823/2690500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2690334219848823571/2690500000000000000 : ℝ)*(X 0 1+X 2 1)+(12371772652823/2690500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (67/10000 : ℝ)) (hi := (1103/4000 : ℝ)) (c := (2690334219848823571/2690500000000000000 : ℝ)) (alpha := (12371772652823/2690500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2690334219848823571/2690500000000000000 : ℝ)*(X 0 2+X 1 2)+(12371772652823/2690500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (67/10000 : ℝ)) (hi := (1103/4000 : ℝ)) (c := (2690334219848823571/2690500000000000000 : ℝ)) (alpha := (12371772652823/2690500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2072134491/10000000000 : ℝ)*X 0 0+(5684990753/10000000000 : ℝ)*X 0 1+(5015189791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2707835463/5000000000 : ℝ)*X 1 0+(-1216227339/5000000000 : ℝ)*X 1 1+(1253797559/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5415669719/10000000000 : ℝ)*X 2 0+(156724719/312500000 : ℝ)*X 2 1+(-1216227633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156028469/5000000000 : ℝ)*X 0 0+(3688738007/10000000000 : ℝ)*X 0 1+(503777669/1000000000 : ℝ)*X 0 2+(2156028469/5000000000 : ℝ)*X 1 0+(3688738007/10000000000 : ℝ)*X 1 1+(503777669/1000000000 : ℝ)*X 1 2+(2156028469/5000000000 : ℝ)*X 2 0+(3688738007/10000000000 : ℝ)*X 2 1+(503777669/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2072854503/10000000000 : ℝ)*X 0 0+(5024115457/10000000000 : ℝ)*X 0 1+(1135178791/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5243414017/10000000000 : ℝ)*X 1 0+(-1771753127/10000000000 : ℝ)*X 1 1+(5675891819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1048682827/2000000000 : ℝ)*X 2 0+(5675892301/10000000000 : ℝ)*X 2 1+(-885876129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313509837/10000000000 : ℝ)*X 0 0+(627474737/1250000000 : ℝ)*X 0 1+(3707063913/10000000000 : ℝ)*X 0 2+(4313509837/10000000000 : ℝ)*X 1 0+(627474737/1250000000 : ℝ)*X 1 1+(3707063913/10000000000 : ℝ)*X 1 2+(4313509837/10000000000 : ℝ)*X 2 0+(627474737/1250000000 : ℝ)*X 2 1+(3707063913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (685548158969841044714810529/134525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1345922953/100000000000000 : ℝ)*(base19) + (504608403/50000000000000 : ℝ)*(base23) + (24959073/100000000000000 : ℝ)*(upper2) + (306084127/100000000000000 : ℝ)*(upper3) + (5420673/20000000000000 : ℝ)*(upper4) + (1117137510407011/100000000000000 : ℝ)*(major0) + (1117137510407011/100000000000000 : ℝ)*(major1) + (1117137510407011/100000000000000 : ℝ)*(major2) + (1492990972248171/100000000000000 : ℝ)*(sp0) + (746498076886929/50000000000000 : ℝ)*(sp1) + (298599298096001/20000000000000 : ℝ)*(sp2) + (185318099389021/25000000000000 : ℝ)*(sp3) + (20398277/312500000000 : ℝ)*(sp4) + (990738457/20000000000000 : ℝ)*(sp7) + (741277351248369/100000000000000 : ℝ)*(f.failure) + (1492997499696811/100000000000000 : ℝ)*(f.sum) + (78677450851347/134525000000000000000000000000 : ℝ)*base66 + (1229074692906040719/269050000000000000000000000000000 : ℝ)*base68 + (2105875935842790719/269050000000000000000000000000000 : ℝ)*base70 + (1129839004964740719/269050000000000000000000000000000 : ℝ)*base72 + (184183090216547/134525000000000000000000000000 : ℝ)*base74 + (1655770628957140719/269050000000000000000000000000000 : ℝ)*base76 + (2987364533172090719/269050000000000000000000000000000 : ℝ)*base78 + (1209166014488890719/269050000000000000000000000000000 : ℝ)*base80 + (48359324793161/67262500000000000000000000000 : ℝ)*base82 + (8863991/1000000000000000000000 : ℝ)*base89 + (8863991/1000000000000000000000 : ℝ)*base91 + (8863991/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100028777825664440882963361/33631250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372695087/100000000000000 : ℝ)*(base19) + (96270029/12500000000000 : ℝ)*(base23) + (54577921/100000000000000 : ℝ)*(lower3) + (138886609/100000000000000 : ℝ)*(lower4) + (574009355854503/50000000000000 : ℝ)*(major0) + (574009355854503/50000000000000 : ℝ)*(major1) + (574009355854503/50000000000000 : ℝ)*(major2) + (78251821/3125000000000 : ℝ)*(sp0) + (161827009/20000000000000 : ℝ)*(sp1) + (75880699/2000000000000 : ℝ)*(sp2) + (306853245388099/20000000000000 : ℝ)*(sp4) + (306853509833727/20000000000000 : ℝ)*(sp5) + (767132083401793/50000000000000 : ℝ)*(sp6) + (15235371865531/2000000000000 : ℝ)*(sp7) + (15235371865531/2000000000000 : ℝ)*(f.failure) + (1534268730998767/100000000000000 : ℝ)*(f.sum) + (278039618480113/134525000000000000000000000000 : ℝ)*base65 + (633527302714584213/134525000000000000000000000000000 : ℝ)*base67 + (220425215847684213/134525000000000000000000000000000 : ℝ)*base69 + (879526177066984213/134525000000000000000000000000000 : ℝ)*base71 + (11594432744687/134525000000000000000000000000 : ℝ)*base74 + (567686865951484213/134525000000000000000000000000000 : ℝ)*base75 + (35542062372109213/134525000000000000000000000000000 : ℝ)*base77 + (280224471506790787/134525000000000000000000000000000 : ℝ)*base80 + (86977392930403/33631250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (61891/20000000000000000000 : ℝ)*base90 + (61891/20000000000000000000 : ℝ)*base92 + (61891/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1205_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1103/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (67/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1199/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20157/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1205_s2_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-424410799/2000000000 : ℝ)*x 0 + (5499216753/10000000000 : ℝ)*x 1 + (5169162071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424410799/2000000000 : ℝ)^4199 ≤ (6435645751289/50000000000000 : ℝ)^3175 := by
    have hnat : (424410799 : ℕ)^4199*50000000000000^3175 ≤ 6435645751289^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424410799 2000000000 6435645751289 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499216753/10000000000 : ℝ)^4199 ≤ (45346392821539/100000000000000 : ℝ)^3175 := by
    have hnat : (5499216753 : ℕ)^4199*100000000000000^3175 ≤ 45346392821539^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499216753 10000000000 45346392821539 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169162071/10000000000 : ℝ)^4199 ≤ (41782315654187/100000000000000 : ℝ)^3175 := by
    have hnat : (5169162071 : ℕ)^4199*100000000000000^3175 ≤ 41782315654187^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169162071 10000000000 41782315654187 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424410799/2000000000 : ℝ), (5499216753/10000000000 : ℝ), (5169162071/10000000000 : ℝ)] ![(6435645751289/50000000000000 : ℝ), (45346392821539/100000000000000 : ℝ), (41782315654187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424410799/2000000000 : ℝ)|^4199 ≤ (6435645751289/50000000000000 : ℝ)^3175
        have hw : |(-424410799/2000000000 : ℝ)|=(424410799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499216753/10000000000 : ℝ)|^4199 ≤ (45346392821539/100000000000000 : ℝ)^3175
        have hw : |(5499216753/10000000000 : ℝ)|=(5499216753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5169162071/10000000000 : ℝ)|^4199 ≤ (41782315654187/100000000000000 : ℝ)^3175
        have hw : |(5169162071/10000000000 : ℝ)|=(5169162071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s2_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371200243/10000000000 : ℝ)*x 0 + (-286655069/1250000000 : ℝ)*x 1 + (2584583361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371200243/10000000000 : ℝ)^4199 ≤ (1373611948653/3125000000000 : ℝ)^3175 := by
    have hnat : (5371200243 : ℕ)^4199*3125000000000^3175 ≤ 1373611948653^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371200243 10000000000 1373611948653 3125000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (286655069/1250000000 : ℝ)^4199 ≤ (14262052260779/100000000000000 : ℝ)^3175 := by
    have hnat : (286655069 : ℕ)^4199*100000000000000^3175 ≤ 14262052260779^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      286655069 1250000000 14262052260779 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584583361/5000000000 : ℝ)^4199 ≤ (20891182686509/50000000000000 : ℝ)^3175 := by
    have hnat : (2584583361 : ℕ)^4199*50000000000000^3175 ≤ 20891182686509^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584583361 5000000000 20891182686509 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371200243/10000000000 : ℝ), (-286655069/1250000000 : ℝ), (2584583361/5000000000 : ℝ)] ![(1373611948653/3125000000000 : ℝ), (14262052260779/100000000000000 : ℝ), (20891182686509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371200243/10000000000 : ℝ)|^4199 ≤ (1373611948653/3125000000000 : ℝ)^3175
        have hw : |(5371200243/10000000000 : ℝ)|=(5371200243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-286655069/1250000000 : ℝ)|^4199 ≤ (14262052260779/100000000000000 : ℝ)^3175
        have hw : |(-286655069/1250000000 : ℝ)|=(286655069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2584583361/5000000000 : ℝ)|^4199 ≤ (20891182686509/50000000000000 : ℝ)^3175
        have hw : |(2584583361/5000000000 : ℝ)|=(2584583361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s2_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5371202327/10000000000 : ℝ)*x 0 + (5169163833/10000000000 : ℝ)*x 1 + (-573310391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371202327/10000000000 : ℝ)^4199 ≤ (43955604911883/100000000000000 : ℝ)^3175 := by
    have hnat : (5371202327 : ℕ)^4199*100000000000000^3175 ≤ 43955604911883^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371202327 10000000000 43955604911883 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5169163833/10000000000 : ℝ)^4199 ≤ (41782334489829/100000000000000 : ℝ)^3175 := by
    have hnat : (5169163833 : ℕ)^4199*100000000000000^3175 ≤ 41782334489829^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169163833 10000000000 41782334489829 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573310391/2500000000 : ℝ)^4199 ≤ (7131030292227/50000000000000 : ℝ)^3175 := by
    have hnat : (573310391 : ℕ)^4199*50000000000000^3175 ≤ 7131030292227^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573310391 2500000000 7131030292227 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371202327/10000000000 : ℝ), (5169163833/10000000000 : ℝ), (-573310391/2500000000 : ℝ)] ![(43955604911883/100000000000000 : ℝ), (41782334489829/100000000000000 : ℝ), (7131030292227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371202327/10000000000 : ℝ)|^4199 ≤ (43955604911883/100000000000000 : ℝ)^3175
        have hw : |(5371202327/10000000000 : ℝ)|=(5371202327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5169163833/10000000000 : ℝ)|^4199 ≤ (41782334489829/100000000000000 : ℝ)^3175
        have hw : |(5169163833/10000000000 : ℝ)|=(5169163833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-573310391/2500000000 : ℝ)|^4199 ≤ (7131030292227/50000000000000 : ℝ)^3175
        have hw : |(-573310391/2500000000 : ℝ)|=(573310391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s2_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2173226863/5000000000 : ℝ)*x 0 + (4026489369/10000000000 : ℝ)*x 1 + (2345622511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173226863/5000000000 : ℝ)^4199 ≤ (2076378442603/6250000000000 : ℝ)^3175 := by
    have hnat : (2173226863 : ℕ)^4199*6250000000000^3175 ≤ 2076378442603^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173226863 5000000000 2076378442603 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4026489369/10000000000 : ℝ)^4199 ≤ (30026699266679/100000000000000 : ℝ)^3175 := by
    have hnat : (4026489369 : ℕ)^4199*100000000000000^3175 ≤ 30026699266679^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026489369 10000000000 30026699266679 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2345622511/5000000000 : ℝ)^4199 ≤ (36751245631859/100000000000000 : ℝ)^3175 := by
    have hnat : (2345622511 : ℕ)^4199*100000000000000^3175 ≤ 36751245631859^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2345622511 5000000000 36751245631859 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2173226863/5000000000 : ℝ), (4026489369/10000000000 : ℝ), (2345622511/5000000000 : ℝ)] ![(2076378442603/6250000000000 : ℝ), (30026699266679/100000000000000 : ℝ), (36751245631859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2173226863/5000000000 : ℝ)|^4199 ≤ (2076378442603/6250000000000 : ℝ)^3175
        have hw : |(2173226863/5000000000 : ℝ)|=(2173226863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4026489369/10000000000 : ℝ)|^4199 ≤ (30026699266679/100000000000000 : ℝ)^3175
        have hw : |(4026489369/10000000000 : ℝ)|=(4026489369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2345622511/5000000000 : ℝ)|^4199 ≤ (36751245631859/100000000000000 : ℝ)^3175
        have hw : |(2345622511/5000000000 : ℝ)|=(2345622511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s2_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2122139271/10000000000 : ℝ)*x 0 + (2585670439/5000000000 : ℝ)*x 1 + (1374254499/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122139271/10000000000 : ℝ)^4199 ≤ (2574395113549/20000000000000 : ℝ)^3175 := by
    have hnat : (2122139271 : ℕ)^4199*20000000000000^3175 ≤ 2574395113549^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122139271 10000000000 2574395113549 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585670439/5000000000 : ℝ)^4199 ≤ (20902804256099/50000000000000 : ℝ)^3175 := by
    have hnat : (2585670439 : ℕ)^4199*50000000000000^3175 ≤ 20902804256099^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585670439 5000000000 20902804256099 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1374254499/2500000000 : ℝ)^4199 ≤ (4532241590769/10000000000000 : ℝ)^3175 := by
    have hnat : (1374254499 : ℕ)^4199*10000000000000^3175 ≤ 4532241590769^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374254499 2500000000 4532241590769 10000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2122139271/10000000000 : ℝ), (2585670439/5000000000 : ℝ), (1374254499/2500000000 : ℝ)] ![(2574395113549/20000000000000 : ℝ), (20902804256099/50000000000000 : ℝ), (4532241590769/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2122139271/10000000000 : ℝ)|^4199 ≤ (2574395113549/20000000000000 : ℝ)^3175
        have hw : |(-2122139271/10000000000 : ℝ)|=(2122139271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585670439/5000000000 : ℝ)|^4199 ≤ (20902804256099/50000000000000 : ℝ)^3175
        have hw : |(2585670439/5000000000 : ℝ)|=(2585670439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1374254499/2500000000 : ℝ)|^4199 ≤ (4532241590769/10000000000000 : ℝ)^3175
        have hw : |(1374254499/2500000000 : ℝ)|=(1374254499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s2_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660889011/1250000000 : ℝ)*x 0 + (-982693791/5000000000 : ℝ)*x 1 + (274850901/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660889011/1250000000 : ℝ)^4199 ≤ (43047807911959/100000000000000 : ℝ)^3175 := by
    have hnat : (660889011 : ℕ)^4199*100000000000000^3175 ≤ 43047807911959^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660889011 1250000000 43047807911959 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982693791/5000000000 : ℝ)^4199 ≤ (1453721987551/12500000000000 : ℝ)^3175 := by
    have hnat : (982693791 : ℕ)^4199*12500000000000^3175 ≤ 1453721987551^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982693791 5000000000 1453721987551 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274850901/500000000 : ℝ)^4199 ≤ (45322416169387/100000000000000 : ℝ)^3175 := by
    have hnat : (274850901 : ℕ)^4199*100000000000000^3175 ≤ 45322416169387^3175*500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274850901 500000000 45322416169387 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660889011/1250000000 : ℝ), (-982693791/5000000000 : ℝ), (274850901/500000000 : ℝ)] ![(43047807911959/100000000000000 : ℝ), (1453721987551/12500000000000 : ℝ), (45322416169387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660889011/1250000000 : ℝ)|^4199 ≤ (43047807911959/100000000000000 : ℝ)^3175
        have hw : |(660889011/1250000000 : ℝ)|=(660889011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982693791/5000000000 : ℝ)|^4199 ≤ (1453721987551/12500000000000 : ℝ)^3175
        have hw : |(-982693791/5000000000 : ℝ)|=(982693791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274850901/500000000 : ℝ)|^4199 ≤ (45322416169387/100000000000000 : ℝ)^3175
        have hw : |(274850901/500000000 : ℝ)|=(274850901/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s2_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057422453/2000000000 : ℝ)*x 0 + (1099403609/2000000000 : ℝ)*x 1 + (-393077461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057422453/2000000000 : ℝ)^4199 ≤ (43047809817893/100000000000000 : ℝ)^3175 := by
    have hnat : (1057422453 : ℕ)^4199*100000000000000^3175 ≤ 43047809817893^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057422453 2000000000 43047809817893 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099403609/2000000000 : ℝ)^4199 ≤ (45322416441989/100000000000000 : ℝ)^3175 := by
    have hnat : (1099403609 : ℕ)^4199*100000000000000^3175 ≤ 45322416441989^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099403609 2000000000 45322416441989 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (393077461/2000000000 : ℝ)^4199 ≤ (5814886866339/50000000000000 : ℝ)^3175 := by
    have hnat : (393077461 : ℕ)^4199*50000000000000^3175 ≤ 5814886866339^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      393077461 2000000000 5814886866339 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057422453/2000000000 : ℝ), (1099403609/2000000000 : ℝ), (-393077461/2000000000 : ℝ)] ![(43047809817893/100000000000000 : ℝ), (45322416441989/100000000000000 : ℝ), (5814886866339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057422453/2000000000 : ℝ)|^4199 ≤ (43047809817893/100000000000000 : ℝ)^3175
        have hw : |(1057422453/2000000000 : ℝ)|=(1057422453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099403609/2000000000 : ℝ)|^4199 ≤ (45322416441989/100000000000000 : ℝ)^3175
        have hw : |(1099403609/2000000000 : ℝ)|=(1099403609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-393077461/2000000000 : ℝ)|^4199 ≤ (5814886866339/50000000000000 : ℝ)^3175
        have hw : |(-393077461/2000000000 : ℝ)|=(393077461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s2_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (543328489/1250000000 : ℝ)*x 0 + (146464357/312500000 : ℝ)*x 1 + (2015458249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543328489/1250000000 : ℝ)^4199 ≤ (16611907940017/50000000000000 : ℝ)^3175 := by
    have hnat : (543328489 : ℕ)^4199*50000000000000^3175 ≤ 16611907940017^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543328489 1250000000 16611907940017 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (146464357/312500000 : ℝ)^4199 ≤ (36705814932547/100000000000000 : ℝ)^3175 := by
    have hnat : (146464357 : ℕ)^4199*100000000000000^3175 ≤ 36705814932547^3175*312500000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146464357 312500000 36705814932547 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015458249/5000000000 : ℝ)^4199 ≤ (30070369180633/100000000000000 : ℝ)^3175 := by
    have hnat : (2015458249 : ℕ)^4199*100000000000000^3175 ≤ 30070369180633^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015458249 5000000000 30070369180633 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543328489/1250000000 : ℝ), (146464357/312500000 : ℝ), (2015458249/5000000000 : ℝ)] ![(16611907940017/50000000000000 : ℝ), (36705814932547/100000000000000 : ℝ), (30070369180633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543328489/1250000000 : ℝ)|^4199 ≤ (16611907940017/50000000000000 : ℝ)^3175
        have hw : |(543328489/1250000000 : ℝ)|=(543328489/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(146464357/312500000 : ℝ)|^4199 ≤ (36705814932547/100000000000000 : ℝ)^3175
        have hw : |(146464357/312500000 : ℝ)|=(146464357/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015458249/5000000000 : ℝ)|^4199 ≤ (30070369180633/100000000000000 : ℝ)^3175
        have hw : |(2015458249/5000000000 : ℝ)|=(2015458249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (4673/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8161/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20157/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1199/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20157/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1199/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20157/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1199/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1199/20000 : ℝ) ^ (8397/2048 : ℝ) ≤ (487288672942167/50000000000000000000 : ℝ) := by
    have hpowers : (1199/20000 : ℝ)^8397 ≤ (487288672942167/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1199 : ℕ)^8397*50000000000000000000^2048 ≤ 487288672942167^2048*20000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1199 20000 487288672942167 50000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1199/20000 : ℝ)) (X := (487288672942167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20157/100000 : ℝ) ^ (8397/2048 : ℝ) ≤ (17578760884047627/12500000000000000000 : ℝ) := by
    have hpowers : (20157/100000 : ℝ)^8397 ≤ (17578760884047627/12500000000000000000 : ℝ)^2048 := by
      have hnat : (20157 : ℕ)^8397*12500000000000000000^2048 ≤ 17578760884047627^2048*100000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20157 100000 17578760884047627 12500000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20157/100000 : ℝ)) (X := (17578760884047627/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000487288672942167/25000000000000000000 : ℝ) ≤ (2000009507775143/2000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (25000487288672942167/25000000000000000000 : ℝ)^2048 ≤ (2000009507775143/2000000000000000 : ℝ)^8397 := by
      have hnat : (25000487288672942167 : ℕ)^2048*2000000000000000^8397 ≤ 2000009507775143^8397*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000487288672942167 25000000000000000000 2000009507775143 2000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000009507775143/2000000000000000 : ℝ)) (X := (25000487288672942167/25000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2002832093288365307/2000000000000000000 : ℝ) ≤ (200069036853551/200000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (2002832093288365307/2000000000000000000 : ℝ)^2048 ≤ (200069036853551/200000000000000 : ℝ)^8397 := by
      have hnat : (2002832093288365307 : ℕ)^2048*200000000000000^8397 ≤ 200069036853551^8397*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2002832093288365307 2000000000000000000 200069036853551 200000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200069036853551/200000000000000 : ℝ)) (X := (2002832093288365307/2000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6267578760884047627/6250000000000000000 : ℝ) ≤ (2001371229295877/2000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (6267578760884047627/6250000000000000000 : ℝ)^2048 ≤ (2001371229295877/2000000000000000 : ℝ)^8397 := by
      have hnat : (6267578760884047627 : ℕ)^2048*2000000000000000^8397 ≤ 2001371229295877^8397*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6267578760884047627 6250000000000000000 2001371229295877 2000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001371229295877/2000000000000000 : ℝ)) (X := (6267578760884047627/6250000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(487288672942167/50000000000000000000 : ℝ) ≤ ((7078992782148693709/7081000000000000000 : ℝ)+2*(680860760367/283240000000000 : ℝ)*(1199/20000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (7078992782148693709/7081000000000000000 : ℝ)+2*(680860760367/283240000000000 : ℝ)*(1199/20000 : ℝ)=(2000009507775143/2000000000000000 : ℝ) by norm_num, show 1+2*(487288672942167/50000000000000000000 : ℝ)=(25000487288672942167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17578760884047627/12500000000000000000 : ℝ)+(487288672942167/50000000000000000000 : ℝ) ≤ ((7078992782148693709/7081000000000000000 : ℝ)+(680860760367/283240000000000 : ℝ)*((20157/100000 : ℝ)+(1199/20000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (7078992782148693709/7081000000000000000 : ℝ)+(680860760367/283240000000000 : ℝ)*((20157/100000 : ℝ)+(1199/20000 : ℝ))=(200069036853551/200000000000000 : ℝ) by norm_num, show 1+(17578760884047627/12500000000000000000 : ℝ)+(487288672942167/50000000000000000000 : ℝ)=(2002832093288365307/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17578760884047627/12500000000000000000 : ℝ) ≤ ((7078992782148693709/7081000000000000000 : ℝ)+2*(680860760367/283240000000000 : ℝ)*(20157/100000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (7078992782148693709/7081000000000000000 : ℝ)+2*(680860760367/283240000000000 : ℝ)*(20157/100000 : ℝ)=(2001371229295877/2000000000000000 : ℝ) by norm_num, show 1+2*(17578760884047627/12500000000000000000 : ℝ)=(6267578760884047627/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7078992782148693709/7081000000000000000 : ℝ)*(X 1 0+X 2 0)+(680860760367/283240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (1199/20000 : ℝ)) (hi := (20157/100000 : ℝ)) (c := (7078992782148693709/7081000000000000000 : ℝ)) (alpha := (680860760367/283240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7078992782148693709/7081000000000000000 : ℝ)*(X 0 1+X 2 1)+(680860760367/283240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (1199/20000 : ℝ)) (hi := (20157/100000 : ℝ)) (c := (7078992782148693709/7081000000000000000 : ℝ)) (alpha := (680860760367/283240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7078992782148693709/7081000000000000000 : ℝ)*(X 0 2+X 1 2)+(680860760367/283240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (1199/20000 : ℝ)) (hi := (20157/100000 : ℝ)) (c := (7078992782148693709/7081000000000000000 : ℝ)) (alpha := (680860760367/283240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-424410799/2000000000 : ℝ)*X 0 0+(5499216753/10000000000 : ℝ)*X 0 1+(5169162071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5371200243/10000000000 : ℝ)*X 1 0+(-286655069/1250000000 : ℝ)*X 1 1+(2584583361/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5371202327/10000000000 : ℝ)*X 2 0+(5169163833/10000000000 : ℝ)*X 2 1+(-573310391/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2173226863/5000000000 : ℝ)*X 0 0+(4026489369/10000000000 : ℝ)*X 0 1+(2345622511/5000000000 : ℝ)*X 0 2+(2173226863/5000000000 : ℝ)*X 1 0+(4026489369/10000000000 : ℝ)*X 1 1+(2345622511/5000000000 : ℝ)*X 1 2+(2173226863/5000000000 : ℝ)*X 2 0+(4026489369/10000000000 : ℝ)*X 2 1+(2345622511/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2122139271/10000000000 : ℝ)*X 0 0+(2585670439/5000000000 : ℝ)*X 0 1+(1374254499/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660889011/1250000000 : ℝ)*X 1 0+(-982693791/5000000000 : ℝ)*X 1 1+(274850901/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057422453/2000000000 : ℝ)*X 2 0+(1099403609/2000000000 : ℝ)*X 2 1+(-393077461/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543328489/1250000000 : ℝ)*X 0 0+(146464357/312500000 : ℝ)*X 0 1+(2015458249/5000000000 : ℝ)*X 0 2+(543328489/1250000000 : ℝ)*X 1 0+(146464357/312500000 : ℝ)*X 1 1+(2015458249/5000000000 : ℝ)*X 1 2+(543328489/1250000000 : ℝ)*X 2 0+(146464357/312500000 : ℝ)*X 2 1+(2015458249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (174462677987465161422453339/35405000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22649851/2500000000000 : ℝ)*(base19) + (912498237/50000000000000 : ℝ)*(base23) + (32528217/25000000000000 : ℝ)*(upper2) + (625568799/100000000000000 : ℝ)*(upper3) + (66981263/25000000000000 : ℝ)*(upper4) + (453422510945857/20000000000000 : ℝ)*(major0) + (453422510945857/20000000000000 : ℝ)*(major1) + (453422510945857/20000000000000 : ℝ)*(major2) + (3029843623748729/100000000000000 : ℝ)*(sp0) + (302987996885551/10000000000000 : ℝ)*(sp1) + (121195161994123/4000000000000 : ℝ)*(sp2) + (1504323988732931/100000000000000 : ℝ)*(sp3) + (1862555041/5000000000000 : ℝ)*(sp4) + (20081621811/100000000000000 : ℝ)*(sp7) + (752172035177371/50000000000000 : ℝ)*(f.failure) + (3029880874849549/100000000000000 : ℝ)*(f.sum) + (10212372658411/14162000000000000000000000000 : ℝ)*base66 + (453212452752511387/141620000000000000000000000000000 : ℝ)*base68 + (42558445974308613/141620000000000000000000000000000 : ℝ)*base69 + (327828359824671387/141620000000000000000000000000000 : ℝ)*base72 + (25917000612549/14162000000000000000000000000 : ℝ)*base73 + (748633370226111387/141620000000000000000000000000000 : ℝ)*base76 + (2699514008571387/141620000000000000000000000000000 : ℝ)*base78 + (327065794188871387/141620000000000000000000000000000 : ℝ)*base80 + (19468132039/4531840000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1164131/500000000000000000000 : ℝ)*base90 + (1164131/500000000000000000000 : ℝ)*base92 + (1164131/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2028906546878110712785221453/354050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1476183243/100000000000000 : ℝ)*(base19) + (851303917/50000000000000 : ℝ)*(base23) + (1366657/5000000000000 : ℝ)*(upper2) + (196415161/100000000000000 : ℝ)*(upper3) + (23535889/20000000000000 : ℝ)*(upper5) + (2297524288742487/100000000000000 : ℝ)*(major0) + (2297524288742487/100000000000000 : ℝ)*(major1) + (2297524288742487/100000000000000 : ℝ)*(major2) + (7254458873/50000000000000 : ℝ)*(sp1) + (9515668821/50000000000000 : ℝ)*(sp2) + (3070524589420481/100000000000000 : ℝ)*(sp4) + (767627151079873/25000000000000 : ℝ)*(sp5) + (1535251927737503/50000000000000 : ℝ)*(sp6) + (1524523797045651/100000000000000 : ℝ)*(sp7) + (1524523797045651/100000000000000 : ℝ)*(f.failure) + (3070524589420481/100000000000000 : ℝ)*(f.sum) + (58637153338247/14162000000000000000000000000 : ℝ)*base65 + (2473959909785939283/708100000000000000000000000000000 : ℝ)*base67 + (6645420252036739283/708100000000000000000000000000000 : ℝ)*base69 + (5464510543939539283/708100000000000000000000000000000 : ℝ)*base71 + (11288847923127/14162000000000000000000000000 : ℝ)*base74 + (1722908469991139283/708100000000000000000000000000000 : ℝ)*base75 + (3972395178344539283/708100000000000000000000000000000 : ℝ)*base77 + (391676625008139283/708100000000000000000000000000000 : ℝ)*base79 + (34948405409369/14162000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6389211/1000000000000000000000 : ℝ)*base90 + (6389211/1000000000000000000000 : ℝ)*base92 + (6389211/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1205_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20157/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1205_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1205_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1205_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1205_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4673/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
