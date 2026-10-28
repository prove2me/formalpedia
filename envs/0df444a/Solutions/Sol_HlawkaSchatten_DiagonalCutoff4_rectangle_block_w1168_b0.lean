-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1168_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:43:47.623517+00:00
-- url     : https://prove2.me/submissions/276d2275-b83a-4ca3-be3d-d17b4d79c1de

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
theorem support_rectangle_w1168_s0_0 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1883609041/10000000000 : ℝ)*x 0 + (1512085079/2500000000 : ℝ)*x 1 + (4783751813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1883609041/10000000000 : ℝ)^8361 ≤ (2191899080033/20000000000000 : ℝ)^6313 := by
    have hnat : (1883609041 : ℕ)^8361*20000000000000^6313 ≤ 2191899080033^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883609041 10000000000 2191899080033 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512085079/2500000000 : ℝ)^8361 ≤ (51380323754129/100000000000000 : ℝ)^6313 := by
    have hnat : (1512085079 : ℕ)^8361*100000000000000^6313 ≤ 51380323754129^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512085079 2500000000 51380323754129 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783751813/10000000000 : ℝ)^8361 ≤ (18830090415339/50000000000000 : ℝ)^6313 := by
    have hnat : (4783751813 : ℕ)^8361*50000000000000^6313 ≤ 18830090415339^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783751813 10000000000 18830090415339 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1883609041/10000000000 : ℝ), (1512085079/2500000000 : ℝ), (4783751813/10000000000 : ℝ)] ![(2191899080033/20000000000000 : ℝ), (51380323754129/100000000000000 : ℝ), (18830090415339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1883609041/10000000000 : ℝ)|^8361 ≤ (2191899080033/20000000000000 : ℝ)^6313
        have hw : |(-1883609041/10000000000 : ℝ)|=(1883609041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1512085079/2500000000 : ℝ)|^8361 ≤ (51380323754129/100000000000000 : ℝ)^6313
        have hw : |(1512085079/2500000000 : ℝ)|=(1512085079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783751813/10000000000 : ℝ)|^8361 ≤ (18830090415339/50000000000000 : ℝ)^6313
        have hw : |(4783751813/10000000000 : ℝ)|=(4783751813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s0_1 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (689416113/1250000000 : ℝ)*x 0 + (-2608600559/10000000000 : ℝ)*x 1 + (4783751791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (689416113/1250000000 : ℝ)^8361 ≤ (22735505648291/50000000000000 : ℝ)^6313 := by
    have hnat : (689416113 : ℕ)^8361*50000000000000^6313 ≤ 22735505648291^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689416113 1250000000 22735505648291 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608600559/10000000000 : ℝ)^8361 ≤ (16868808092493/100000000000000 : ℝ)^6313 := by
    have hnat : (2608600559 : ℕ)^8361*100000000000000^6313 ≤ 16868808092493^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608600559 10000000000 16868808092493 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4783751791/10000000000 : ℝ)^8361 ≤ (2353761287581/6250000000000 : ℝ)^6313 := by
    have hnat : (4783751791 : ℕ)^8361*6250000000000^6313 ≤ 2353761287581^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4783751791 10000000000 2353761287581 6250000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(689416113/1250000000 : ℝ), (-2608600559/10000000000 : ℝ), (4783751791/10000000000 : ℝ)] ![(22735505648291/50000000000000 : ℝ), (16868808092493/100000000000000 : ℝ), (2353761287581/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(689416113/1250000000 : ℝ)|^8361 ≤ (22735505648291/50000000000000 : ℝ)^6313
        have hw : |(689416113/1250000000 : ℝ)|=(689416113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2608600559/10000000000 : ℝ)|^8361 ≤ (16868808092493/100000000000000 : ℝ)^6313
        have hw : |(-2608600559/10000000000 : ℝ)|=(2608600559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4783751791/10000000000 : ℝ)|^8361 ≤ (2353761287581/6250000000000 : ℝ)^6313
        have hw : |(4783751791/10000000000 : ℝ)|=(4783751791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s0_2 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5515328871/10000000000 : ℝ)*x 0 + (2391875909/5000000000 : ℝ)*x 1 + (-2608600567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5515328871/10000000000 : ℝ)^8361 ≤ (45471010936253/100000000000000 : ℝ)^6313 := by
    have hnat : (5515328871 : ℕ)^8361*100000000000000^6313 ≤ 45471010936253^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515328871 10000000000 45471010936253 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2391875909/5000000000 : ℝ)^8361 ≤ (3766018088281/10000000000000 : ℝ)^6313 := by
    have hnat : (2391875909 : ℕ)^8361*10000000000000^6313 ≤ 3766018088281^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2391875909 5000000000 3766018088281 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608600567/10000000000 : ℝ)^8361 ≤ (16868808161009/100000000000000 : ℝ)^6313 := by
    have hnat : (2608600567 : ℕ)^8361*100000000000000^6313 ≤ 16868808161009^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608600567 10000000000 16868808161009 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5515328871/10000000000 : ℝ), (2391875909/5000000000 : ℝ), (-2608600567/10000000000 : ℝ)] ![(45471010936253/100000000000000 : ℝ), (3766018088281/10000000000000 : ℝ), (16868808161009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5515328871/10000000000 : ℝ)|^8361 ≤ (45471010936253/100000000000000 : ℝ)^6313
        have hw : |(5515328871/10000000000 : ℝ)|=(5515328871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2391875909/5000000000 : ℝ)|^8361 ≤ (3766018088281/10000000000000 : ℝ)^6313
        have hw : |(2391875909/5000000000 : ℝ)|=(2391875909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2608600567/10000000000 : ℝ)|^8361 ≤ (16868808161009/100000000000000 : ℝ)^6313
        have hw : |(-2608600567/10000000000 : ℝ)|=(2608600567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s0_3 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4198896191/10000000000 : ℝ)*x 0 + (1559952323/5000000000 : ℝ)*x 1 + (1129721491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4198896191/10000000000 : ℝ)^8361 ≤ (3960832168101/12500000000000 : ℝ)^6313 := by
    have hnat : (4198896191 : ℕ)^8361*12500000000000^6313 ≤ 3960832168101^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4198896191 10000000000 3960832168101 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559952323/5000000000 : ℝ)^8361 ≤ (21381380053697/100000000000000 : ℝ)^6313 := by
    have hnat : (1559952323 : ℕ)^8361*100000000000000^6313 ≤ 21381380053697^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559952323 5000000000 21381380053697 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1129721491/2000000000 : ℝ)^8361 ≤ (2933247661409/6250000000000 : ℝ)^6313 := by
    have hnat : (1129721491 : ℕ)^8361*6250000000000^6313 ≤ 2933247661409^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129721491 2000000000 2933247661409 6250000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4198896191/10000000000 : ℝ), (1559952323/5000000000 : ℝ), (1129721491/2000000000 : ℝ)] ![(3960832168101/12500000000000 : ℝ), (21381380053697/100000000000000 : ℝ), (2933247661409/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4198896191/10000000000 : ℝ)|^8361 ≤ (3960832168101/12500000000000 : ℝ)^6313
        have hw : |(4198896191/10000000000 : ℝ)|=(4198896191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559952323/5000000000 : ℝ)|^8361 ≤ (21381380053697/100000000000000 : ℝ)^6313
        have hw : |(1559952323/5000000000 : ℝ)|=(1559952323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1129721491/2000000000 : ℝ)|^8361 ≤ (2933247661409/6250000000000 : ℝ)^6313
        have hw : |(1129721491/2000000000 : ℝ)|=(1129721491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s0_4 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888678543/10000000000 : ℝ)*x 0 + (4816361173/10000000000 : ℝ)*x 1 + (3007291287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888678543/10000000000 : ℝ)^8361 ≤ (10998577416547/100000000000000 : ℝ)^6313 := by
    have hnat : (1888678543 : ℕ)^8361*100000000000000^6313 ≤ 10998577416547^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888678543 10000000000 10998577416547 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4816361173/10000000000 : ℝ)^8361 ≤ (1216017787/3200000000 : ℝ)^6313 := by
    have hnat : (4816361173 : ℕ)^8361*3200000000^6313 ≤ 1216017787^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4816361173 10000000000 1216017787 3200000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3007291287/5000000000 : ℝ)^8361 ≤ (6375108341691/12500000000000 : ℝ)^6313 := by
    have hnat : (3007291287 : ℕ)^8361*12500000000000^6313 ≤ 6375108341691^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007291287 5000000000 6375108341691 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888678543/10000000000 : ℝ), (4816361173/10000000000 : ℝ), (3007291287/5000000000 : ℝ)] ![(10998577416547/100000000000000 : ℝ), (1216017787/3200000000 : ℝ), (6375108341691/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888678543/10000000000 : ℝ)|^8361 ≤ (10998577416547/100000000000000 : ℝ)^6313
        have hw : |(-1888678543/10000000000 : ℝ)|=(1888678543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4816361173/10000000000 : ℝ)|^8361 ≤ (1216017787/3200000000 : ℝ)^6313
        have hw : |(4816361173/10000000000 : ℝ)|=(4816361173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3007291287/5000000000 : ℝ)|^8361 ≤ (6375108341691/12500000000000 : ℝ)^6313
        have hw : |(3007291287/5000000000 : ℝ)|=(3007291287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s0_5 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1034317373/2000000000 : ℝ)*x 0 + (-1377769999/10000000000 : ℝ)*x 1 + (1503645587/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034317373/2000000000 : ℝ)^8361 ≤ (10439039767889/25000000000000 : ℝ)^6313 := by
    have hnat : (1034317373 : ℕ)^8361*25000000000000^6313 ≤ 10439039767889^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034317373 2000000000 10439039767889 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377769999/10000000000 : ℝ)^8361 ≤ (7242976726139/100000000000000 : ℝ)^6313 := by
    have hnat : (1377769999 : ℕ)^8361*100000000000000^6313 ≤ 7242976726139^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377769999 10000000000 7242976726139 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1503645587/2500000000 : ℝ)^8361 ≤ (25500432097731/50000000000000 : ℝ)^6313 := by
    have hnat : (1503645587 : ℕ)^8361*50000000000000^6313 ≤ 25500432097731^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503645587 2500000000 25500432097731 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034317373/2000000000 : ℝ), (-1377769999/10000000000 : ℝ), (1503645587/2500000000 : ℝ)] ![(10439039767889/25000000000000 : ℝ), (7242976726139/100000000000000 : ℝ), (25500432097731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034317373/2000000000 : ℝ)|^8361 ≤ (10439039767889/25000000000000 : ℝ)^6313
        have hw : |(1034317373/2000000000 : ℝ)|=(1034317373/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1377769999/10000000000 : ℝ)|^8361 ≤ (7242976726139/100000000000000 : ℝ)^6313
        have hw : |(-1377769999/10000000000 : ℝ)|=(1377769999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1503645587/2500000000 : ℝ)|^8361 ≤ (25500432097731/50000000000000 : ℝ)^6313
        have hw : |(1503645587/2500000000 : ℝ)|=(1503645587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s0_6 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5171586829/10000000000 : ℝ)*x 0 + (3007291223/5000000000 : ℝ)*x 1 + (-172221237/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5171586829/10000000000 : ℝ)^8361 ≤ (4175615868659/10000000000000 : ℝ)^6313 := by
    have hnat : (5171586829 : ℕ)^8361*10000000000000^6313 ≤ 4175615868659^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5171586829 10000000000 4175615868659 10000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3007291223/5000000000 : ℝ)^8361 ≤ (51000865296039/100000000000000 : ℝ)^6313 := by
    have hnat : (3007291223 : ℕ)^8361*100000000000000^6313 ≤ 51000865296039^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3007291223 5000000000 51000865296039 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172221237/1250000000 : ℝ)^8361 ≤ (1448595201801/20000000000000 : ℝ)^6313 := by
    have hnat : (172221237 : ℕ)^8361*20000000000000^6313 ≤ 1448595201801^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172221237 1250000000 1448595201801 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5171586829/10000000000 : ℝ), (3007291223/5000000000 : ℝ), (-172221237/1250000000 : ℝ)] ![(4175615868659/10000000000000 : ℝ), (51000865296039/100000000000000 : ℝ), (1448595201801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5171586829/10000000000 : ℝ)|^8361 ≤ (4175615868659/10000000000000 : ℝ)^6313
        have hw : |(5171586829/10000000000 : ℝ)|=(5171586829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3007291223/5000000000 : ℝ)|^8361 ≤ (51000865296039/100000000000000 : ℝ)^6313
        have hw : |(3007291223/5000000000 : ℝ)|=(3007291223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-172221237/1250000000 : ℝ)|^8361 ≤ (1448595201801/20000000000000 : ℝ)^6313
        have hw : |(-172221237/1250000000 : ℝ)|=(172221237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s0_7 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (263064593/625000000 : ℝ)*x 0 + (2791700347/5000000000 : ℝ)*x 1 + (1593703859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263064593/625000000 : ℝ)^8361 ≤ (3973501854193/12500000000000 : ℝ)^6313 := by
    have hnat : (263064593 : ℕ)^8361*12500000000000^6313 ≤ 3973501854193^6313*625000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263064593 625000000 3973501854193 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2791700347/5000000000 : ℝ)^8361 ≤ (46215775822413/100000000000000 : ℝ)^6313 := by
    have hnat : (2791700347 : ℕ)^8361*100000000000000^6313 ≤ 46215775822413^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2791700347 5000000000 46215775822413 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1593703859/5000000000 : ℝ)^8361 ≤ (21996209334253/100000000000000 : ℝ)^6313 := by
    have hnat : (1593703859 : ℕ)^8361*100000000000000^6313 ≤ 21996209334253^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593703859 5000000000 21996209334253 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263064593/625000000 : ℝ), (2791700347/5000000000 : ℝ), (1593703859/5000000000 : ℝ)] ![(3973501854193/12500000000000 : ℝ), (46215775822413/100000000000000 : ℝ), (21996209334253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263064593/625000000 : ℝ)|^8361 ≤ (3973501854193/12500000000000 : ℝ)^6313
        have hw : |(263064593/625000000 : ℝ)|=(263064593/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2791700347/5000000000 : ℝ)|^8361 ≤ (46215775822413/100000000000000 : ℝ)^6313
        have hw : |(2791700347/5000000000 : ℝ)|=(2791700347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1593703859/5000000000 : ℝ)|^8361 ≤ (21996209334253/100000000000000 : ℝ)^6313
        have hw : |(1593703859/5000000000 : ℝ)|=(1593703859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1168_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (13/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6929/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1045/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1045 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1045*1^256 ≤ 0^256*1^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1045/256 : ℝ) ≤ (296829090912746467/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1045 ≤ (296829090912746467/12500000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1045*12500000000000000000^256 ≤ 296829090912746467^256*5^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 296829090912746467 12500000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (296829090912746467/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1045 := by
      have hnat : (1 : ℕ)^256*1^1045 ≤ 1^1045*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12796829090912746467/12500000000000000000 : ℝ) ≤ (10057658457352021/10000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (12796829090912746467/12500000000000000000 : ℝ)^256 ≤ (10057658457352021/10000000000000000 : ℝ)^1045 := by
      have hnat : (12796829090912746467 : ℕ)^256*10000000000000000^1045 ≤ 10057658457352021^1045*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12796829090912746467 12500000000000000000 10057658457352021 10000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10057658457352021/10000000000000000 : ℝ)) (X := (12796829090912746467/12500000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6546829090912746467/6250000000000000000 : ℝ) ≤ (5057658457352021/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (6546829090912746467/6250000000000000000 : ℝ)^256 ≤ (5057658457352021/5000000000000000 : ℝ)^1045 := by
      have hnat : (6546829090912746467 : ℕ)^256*5000000000000000^1045 ≤ 5057658457352021^1045*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6546829090912746467 6250000000000000000 5057658457352021 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5057658457352021/5000000000000000 : ℝ)) (X := (6546829090912746467/6250000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(57658457352021/4000000000000000 : ℝ)*(0 : ℝ))^(1045/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(57658457352021/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(296829090912746467/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(57658457352021/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1045/256 : ℝ) := by
    rw [show (1 : ℝ)+(57658457352021/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10057658457352021/10000000000000000 : ℝ) by norm_num, show 1+(296829090912746467/12500000000000000000 : ℝ)+(0 : ℝ)=(12796829090912746467/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(296829090912746467/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(57658457352021/4000000000000000 : ℝ)*(2/5 : ℝ))^(1045/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(57658457352021/4000000000000000 : ℝ)*(2/5 : ℝ)=(5057658457352021/5000000000000000 : ℝ) by norm_num, show 1+2*(296829090912746467/12500000000000000000 : ℝ)=(6546829090912746467/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(57658457352021/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57658457352021/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(57658457352021/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57658457352021/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(57658457352021/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (57658457352021/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1883609041/10000000000 : ℝ)*X 0 0+(1512085079/2500000000 : ℝ)*X 0 1+(4783751813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((689416113/1250000000 : ℝ)*X 1 0+(-2608600559/10000000000 : ℝ)*X 1 1+(4783751791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5515328871/10000000000 : ℝ)*X 2 0+(2391875909/5000000000 : ℝ)*X 2 1+(-2608600567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4198896191/10000000000 : ℝ)*X 0 0+(1559952323/5000000000 : ℝ)*X 0 1+(1129721491/2000000000 : ℝ)*X 0 2+(4198896191/10000000000 : ℝ)*X 1 0+(1559952323/5000000000 : ℝ)*X 1 1+(1129721491/2000000000 : ℝ)*X 1 2+(4198896191/10000000000 : ℝ)*X 2 0+(1559952323/5000000000 : ℝ)*X 2 1+(1129721491/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1888678543/10000000000 : ℝ)*X 0 0+(4816361173/10000000000 : ℝ)*X 0 1+(3007291287/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1034317373/2000000000 : ℝ)*X 1 0+(-1377769999/10000000000 : ℝ)*X 1 1+(1503645587/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5171586829/10000000000 : ℝ)*X 2 0+(3007291223/5000000000 : ℝ)*X 2 1+(-172221237/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((263064593/625000000 : ℝ)*X 0 0+(2791700347/5000000000 : ℝ)*X 0 1+(1593703859/5000000000 : ℝ)*X 0 2+(263064593/625000000 : ℝ)*X 1 0+(2791700347/5000000000 : ℝ)*X 1 1+(1593703859/5000000000 : ℝ)*X 1 2+(263064593/625000000 : ℝ)*X 2 0+(2791700347/5000000000 : ℝ)*X 2 1+(1593703859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (192642957217133966498907/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48758333/100000000000000 : ℝ)*(base1) + (600348783/50000000000000 : ℝ)*(base19) + (69690569/6250000000000 : ℝ)*(base23) + (80916989/100000000000000 : ℝ)*(base24) + (273389681/100000000000000 : ℝ)*(upper3) + (118624096638811/20000000000000 : ℝ)*(major0) + (118624096638811/20000000000000 : ℝ)*(major1) + (118624096638811/20000000000000 : ℝ)*(major2) + (395387555223497/50000000000000 : ℝ)*(sp0) + (790776524716241/100000000000000 : ℝ)*(sp1) + (790776529447713/100000000000000 : ℝ)*(sp2) + (197730461447697/50000000000000 : ℝ)*(sp3) + (532745029/20000000000000 : ℝ)*(sp4) + (210878477/10000000000000 : ℝ)*(sp7) + (12358221263703/3125000000000 : ℝ)*(f.failure) + (790777725413807/100000000000000 : ℝ)*(f.sum) + (26769903112969/40000000000000000000000000000 : ℝ)*base66 + (314478630447031/80000000000000000000000000000 : ℝ)*base67 + (16662279327031/80000000000000000000000000000 : ℝ)*base69 + (113061367647031/80000000000000000000000000000 : ℝ)*base71 + (12167430487031/40000000000000000000000000000 : ℝ)*base73 + (128938862992969/80000000000000000000000000000 : ℝ)*base76 + (208397994927031/80000000000000000000000000000 : ℝ)*base77 + (547543666847031/80000000000000000000000000000 : ℝ)*base79 + (214453036472969/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2515141/312500000000000000000 : ℝ)*base90 + (2515141/312500000000000000000 : ℝ)*base92 + (2515141/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (376373558205899608808799/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17722109/20000000000000 : ℝ)*(base1) + (1871191809/100000000000000 : ℝ)*(base19) + (1866263477/100000000000000 : ℝ)*(base23) + (203316113/100000000000000 : ℝ)*(upper3) + (11071477/5000000000000 : ℝ)*(upper5) + (312983528342527/50000000000000 : ℝ)*(major0) + (312983528342527/50000000000000 : ℝ)*(major1) + (312983528342527/50000000000000 : ℝ)*(major2) + (3820795131/100000000000000 : ℝ)*(sp1) + (3834052613/100000000000000 : ℝ)*(sp2) + (834570417847191/100000000000000 : ℝ)*(sp4) + (166912927449941/20000000000000 : ℝ)*(sp5) + (208641157230139/25000000000000 : ℝ)*(sp6) + (83472688921441/20000000000000 : ℝ)*(sp7) + (417363533217751/100000000000000 : ℝ)*(f.failure) + (417285164618323/50000000000000 : ℝ)*(f.sum) + (153275670997067/100000000000000000000000000000 : ℝ)*base65 + (1862148441097067/200000000000000000000000000000 : ℝ)*base67 + (206840061102933/200000000000000000000000000000 : ℝ)*base70 + (1604737045897067/200000000000000000000000000000 : ℝ)*base71 + (350659329097067/100000000000000000000000000000 : ℝ)*base73 + (524542473497067/200000000000000000000000000000 : ℝ)*base75 + (1016945926297067/200000000000000000000000000000 : ℝ)*base77 + (300460632302933/200000000000000000000000000000 : ℝ)*base80 + (99407940602933/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (16822003/10000000000000000000000 : ℝ)*base89 + (16822003/10000000000000000000000 : ℝ)*base91 + (16822003/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1168_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (13/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6929/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1168_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1168_s1_0 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2086388189/10000000000 : ℝ)*x 0 + (355913919/625000000 : ℝ)*x 1 + (62595739/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086388189/10000000000 : ℝ)^8361 ≤ (6274369991013/50000000000000 : ℝ)^6313 := by
    have hnat : (2086388189 : ℕ)^8361*50000000000000^6313 ≤ 6274369991013^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086388189 10000000000 6274369991013 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (355913919/625000000 : ℝ)^8361 ≤ (2371949063617/5000000000000 : ℝ)^6313 := by
    have hnat : (355913919 : ℕ)^8361*5000000000000^6313 ≤ 2371949063617^6313*625000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      355913919 625000000 2371949063617 5000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62595739/125000000 : ℝ)^8361 ≤ (40012278739271/100000000000000 : ℝ)^6313 := by
    have hnat : (62595739 : ℕ)^8361*100000000000000^6313 ≤ 40012278739271^6313*125000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62595739 125000000 40012278739271 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2086388189/10000000000 : ℝ), (355913919/625000000 : ℝ), (62595739/125000000 : ℝ)] ![(6274369991013/50000000000000 : ℝ), (2371949063617/5000000000000 : ℝ), (40012278739271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2086388189/10000000000 : ℝ)|^8361 ≤ (6274369991013/50000000000000 : ℝ)^6313
        have hw : |(-2086388189/10000000000 : ℝ)|=(2086388189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(355913919/625000000 : ℝ)|^8361 ≤ (2371949063617/5000000000000 : ℝ)^6313
        have hw : |(355913919/625000000 : ℝ)|=(355913919/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62595739/125000000 : ℝ)|^8361 ≤ (40012278739271/100000000000000 : ℝ)^6313
        have hw : |(62595739/125000000 : ℝ)|=(62595739/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_1 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (270884903/500000000 : ℝ)*x 0 + (-76769523/312500000 : ℝ)*x 1 + (5007658159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270884903/500000000 : ℝ)^8361 ≤ (44408046541027/100000000000000 : ℝ)^6313 := by
    have hnat : (270884903 : ℕ)^8361*100000000000000^6313 ≤ 44408046541027^6313*500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270884903 500000000 44408046541027 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76769523/312500000 : ℝ)^8361 ≤ (15579684875491/100000000000000 : ℝ)^6313 := by
    have hnat : (76769523 : ℕ)^8361*100000000000000^6313 ≤ 15579684875491^6313*312500000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76769523 312500000 15579684875491 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5007658159/10000000000 : ℝ)^8361 ≤ (2000613428483/5000000000000 : ℝ)^6313 := by
    have hnat : (5007658159 : ℕ)^8361*5000000000000^6313 ≤ 2000613428483^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007658159 10000000000 2000613428483 5000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270884903/500000000 : ℝ), (-76769523/312500000 : ℝ), (5007658159/10000000000 : ℝ)] ![(44408046541027/100000000000000 : ℝ), (15579684875491/100000000000000 : ℝ), (2000613428483/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270884903/500000000 : ℝ)|^8361 ≤ (44408046541027/100000000000000 : ℝ)^6313
        have hw : |(270884903/500000000 : ℝ)|=(270884903/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76769523/312500000 : ℝ)|^8361 ≤ (15579684875491/100000000000000 : ℝ)^6313
        have hw : |(-76769523/312500000 : ℝ)|=(76769523/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5007658159/10000000000 : ℝ)|^8361 ≤ (2000613428483/5000000000000 : ℝ)^6313
        have hw : |(5007658159/10000000000 : ℝ)|=(5007658159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_2 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5417700177/10000000000 : ℝ)*x 0 + (5007656203/10000000000 : ℝ)*x 1 + (-491324893/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5417700177/10000000000 : ℝ)^8361 ≤ (44408069523153/100000000000000 : ℝ)^6313 := by
    have hnat : (5417700177 : ℕ)^8361*100000000000000^6313 ≤ 44408069523153^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417700177 10000000000 44408069523153 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5007656203/10000000000 : ℝ)^8361 ≤ (20006123935321/50000000000000 : ℝ)^6313 := by
    have hnat : (5007656203 : ℕ)^8361*50000000000000^6313 ≤ 20006123935321^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5007656203 10000000000 20006123935321 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (491324893/2000000000 : ℝ)^8361 ≤ (3115936519857/20000000000000 : ℝ)^6313 := by
    have hnat : (491324893 : ℕ)^8361*20000000000000^6313 ≤ 3115936519857^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491324893 2000000000 3115936519857 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5417700177/10000000000 : ℝ), (5007656203/10000000000 : ℝ), (-491324893/2000000000 : ℝ)] ![(44408069523153/100000000000000 : ℝ), (20006123935321/50000000000000 : ℝ), (3115936519857/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5417700177/10000000000 : ℝ)|^8361 ≤ (44408069523153/100000000000000 : ℝ)^6313
        have hw : |(5417700177/10000000000 : ℝ)|=(5417700177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5007656203/10000000000 : ℝ)|^8361 ≤ (20006123935321/50000000000000 : ℝ)^6313
        have hw : |(5007656203/10000000000 : ℝ)|=(5007656203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-491324893/2000000000 : ℝ)|^8361 ≤ (3115936519857/20000000000000 : ℝ)^6313
        have hw : |(-491324893/2000000000 : ℝ)|=(491324893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_3 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4315228043/10000000000 : ℝ)*x 0 + (3681886399/10000000000 : ℝ)*x 1 + (5055550979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315228043/10000000000 : ℝ)^8361 ≤ (32854535956207/100000000000000 : ℝ)^6313 := by
    have hnat : (4315228043 : ℕ)^8361*100000000000000^6313 ≤ 32854535956207^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315228043 10000000000 32854535956207 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3681886399/10000000000 : ℝ)^8361 ≤ (26625593719293/100000000000000 : ℝ)^6313 := by
    have hnat : (3681886399 : ℕ)^8361*100000000000000^6313 ≤ 26625593719293^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3681886399 10000000000 26625593719293 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5055550979/10000000000 : ℝ)^8361 ≤ (2025993515747/5000000000000 : ℝ)^6313 := by
    have hnat : (5055550979 : ℕ)^8361*5000000000000^6313 ≤ 2025993515747^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5055550979 10000000000 2025993515747 5000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315228043/10000000000 : ℝ), (3681886399/10000000000 : ℝ), (5055550979/10000000000 : ℝ)] ![(32854535956207/100000000000000 : ℝ), (26625593719293/100000000000000 : ℝ), (2025993515747/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315228043/10000000000 : ℝ)|^8361 ≤ (32854535956207/100000000000000 : ℝ)^6313
        have hw : |(4315228043/10000000000 : ℝ)|=(4315228043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3681886399/10000000000 : ℝ)|^8361 ≤ (26625593719293/100000000000000 : ℝ)^6313
        have hw : |(3681886399/10000000000 : ℝ)|=(3681886399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5055550979/10000000000 : ℝ)|^8361 ≤ (2025993515747/5000000000000 : ℝ)^6313
        have hw : |(5055550979/10000000000 : ℝ)|=(5055550979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_4 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2087162889/10000000000 : ℝ)*x 0 + (627118299/1250000000 : ℝ)*x 1 + (710643773/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087162889/10000000000 : ℝ)^8361 ≤ (3138727857773/25000000000000 : ℝ)^6313 := by
    have hnat : (2087162889 : ℕ)^8361*25000000000000^6313 ≤ 3138727857773^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087162889 10000000000 3138727857773 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627118299/1250000000 : ℝ)^8361 ≤ (10027647298241/25000000000000 : ℝ)^6313 := by
    have hnat : (627118299 : ℕ)^8361*25000000000000^6313 ≤ 10027647298241^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627118299 1250000000 10027647298241 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710643773/1250000000 : ℝ)^8361 ≤ (47334499357003/100000000000000 : ℝ)^6313 := by
    have hnat : (710643773 : ℕ)^8361*100000000000000^6313 ≤ 47334499357003^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710643773 1250000000 47334499357003 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2087162889/10000000000 : ℝ), (627118299/1250000000 : ℝ), (710643773/1250000000 : ℝ)] ![(3138727857773/25000000000000 : ℝ), (10027647298241/25000000000000 : ℝ), (47334499357003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2087162889/10000000000 : ℝ)|^8361 ≤ (3138727857773/25000000000000 : ℝ)^6313
        have hw : |(-2087162889/10000000000 : ℝ)|=(2087162889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627118299/1250000000 : ℝ)|^8361 ≤ (10027647298241/25000000000000 : ℝ)^6313
        have hw : |(627118299/1250000000 : ℝ)|=(627118299/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(710643773/1250000000 : ℝ)|^8361 ≤ (47334499357003/100000000000000 : ℝ)^6313
        have hw : |(710643773/1250000000 : ℝ)|=(710643773/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_5 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5241344883/10000000000 : ℝ)*x 0 + (-222391193/1250000000 : ℝ)*x 1 + (710644147/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5241344883/10000000000 : ℝ)^8361 ≤ (10625935593539/25000000000000 : ℝ)^6313 := by
    have hnat : (5241344883 : ℕ)^8361*25000000000000^6313 ≤ 10625935593539^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241344883 10000000000 10625935593539 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222391193/1250000000 : ℝ)^8361 ≤ (10161725265731/100000000000000 : ℝ)^6313 := by
    have hnat : (222391193 : ℕ)^8361*100000000000000^6313 ≤ 10161725265731^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222391193 1250000000 10161725265731 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (710644147/1250000000 : ℝ)^8361 ≤ (23667266174929/50000000000000 : ℝ)^6313 := by
    have hnat : (710644147 : ℕ)^8361*50000000000000^6313 ≤ 23667266174929^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      710644147 1250000000 23667266174929 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5241344883/10000000000 : ℝ), (-222391193/1250000000 : ℝ), (710644147/1250000000 : ℝ)] ![(10625935593539/25000000000000 : ℝ), (10161725265731/100000000000000 : ℝ), (23667266174929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5241344883/10000000000 : ℝ)|^8361 ≤ (10625935593539/25000000000000 : ℝ)^6313
        have hw : |(5241344883/10000000000 : ℝ)|=(5241344883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222391193/1250000000 : ℝ)|^8361 ≤ (10161725265731/100000000000000 : ℝ)^6313
        have hw : |(-222391193/1250000000 : ℝ)|=(222391193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(710644147/1250000000 : ℝ)|^8361 ≤ (23667266174929/50000000000000 : ℝ)^6313
        have hw : |(710644147/1250000000 : ℝ)|=(710644147/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_6 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2620672057/5000000000 : ℝ)*x 0 + (2842577239/5000000000 : ℝ)*x 1 + (-1779128737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2620672057/5000000000 : ℝ)^8361 ≤ (42503734115047/100000000000000 : ℝ)^6313 := by
    have hnat : (2620672057 : ℕ)^8361*100000000000000^6313 ≤ 42503734115047^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620672057 5000000000 42503734115047 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2842577239/5000000000 : ℝ)^8361 ≤ (9466909341409/20000000000000 : ℝ)^6313 := by
    have hnat : (2842577239 : ℕ)^8361*20000000000000^6313 ≤ 9466909341409^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2842577239 5000000000 9466909341409 20000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1779128737/10000000000 : ℝ)^8361 ≤ (10161719161151/100000000000000 : ℝ)^6313 := by
    have hnat : (1779128737 : ℕ)^8361*100000000000000^6313 ≤ 10161719161151^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1779128737 10000000000 10161719161151 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2620672057/5000000000 : ℝ), (2842577239/5000000000 : ℝ), (-1779128737/10000000000 : ℝ)] ![(42503734115047/100000000000000 : ℝ), (9466909341409/20000000000000 : ℝ), (10161719161151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2620672057/5000000000 : ℝ)|^8361 ≤ (42503734115047/100000000000000 : ℝ)^6313
        have hw : |(2620672057/5000000000 : ℝ)|=(2620672057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2842577239/5000000000 : ℝ)|^8361 ≤ (9466909341409/20000000000000 : ℝ)^6313
        have hw : |(2842577239/5000000000 : ℝ)|=(2842577239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1779128737/10000000000 : ℝ)|^8361 ≤ (10161719161151/100000000000000 : ℝ)^6313
        have hw : |(-1779128737/10000000000 : ℝ)|=(1779128737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_7 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1079191357/2500000000 : ℝ)*x 0 + (5036982689/10000000000 : ℝ)*x 1 + (740163901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079191357/2500000000 : ℝ)^8361 ≤ (16435019585323/50000000000000 : ℝ)^6313 := by
    have hnat : (1079191357 : ℕ)^8361*50000000000000^6313 ≤ 16435019585323^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079191357 2500000000 16435019585323 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5036982689/10000000000 : ℝ)^8361 ≤ (40322884536751/100000000000000 : ℝ)^6313 := by
    have hnat : (5036982689 : ℕ)^8361*100000000000000^6313 ≤ 40322884536751^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5036982689 10000000000 40322884536751 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (740163901/2000000000 : ℝ)^8361 ≤ (26807076276607/100000000000000 : ℝ)^6313 := by
    have hnat : (740163901 : ℕ)^8361*100000000000000^6313 ≤ 26807076276607^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740163901 2000000000 26807076276607 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079191357/2500000000 : ℝ), (5036982689/10000000000 : ℝ), (740163901/2000000000 : ℝ)] ![(16435019585323/50000000000000 : ℝ), (40322884536751/100000000000000 : ℝ), (26807076276607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079191357/2500000000 : ℝ)|^8361 ≤ (16435019585323/50000000000000 : ℝ)^6313
        have hw : |(1079191357/2500000000 : ℝ)|=(1079191357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5036982689/10000000000 : ℝ)|^8361 ≤ (40322884536751/100000000000000 : ℝ)^6313
        have hw : |(5036982689/10000000000 : ℝ)|=(5036982689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(740163901/2000000000 : ℝ)|^8361 ≤ (26807076276607/100000000000000 : ℝ)^6313
        have hw : |(740163901/2000000000 : ℝ)|=(740163901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_8 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1071887/2000000000 : ℝ)*x 0 + (54905459/100000000 : ℝ)*x 1 + (6349418567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071887/2000000000 : ℝ)^8361 ≤ (1163999209/25000000000000 : ℝ)^6313 := by
    have hnat : (1071887 : ℕ)^8361*25000000000000^6313 ≤ 1163999209^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071887 2000000000 1163999209 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54905459/100000000 : ℝ)^8361 ≤ (11300150347287/25000000000000 : ℝ)^6313 := by
    have hnat : (54905459 : ℕ)^8361*25000000000000^6313 ≤ 11300150347287^6313*100000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54905459 100000000 11300150347287 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6349418567/10000000000 : ℝ)^8361 ≤ (13698685648901/25000000000000 : ℝ)^6313 := by
    have hnat : (6349418567 : ℕ)^8361*25000000000000^6313 ≤ 13698685648901^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6349418567 10000000000 13698685648901 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071887/2000000000 : ℝ), (54905459/100000000 : ℝ), (6349418567/10000000000 : ℝ)] ![(1163999209/25000000000000 : ℝ), (11300150347287/25000000000000 : ℝ), (13698685648901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071887/2000000000 : ℝ)|^8361 ≤ (1163999209/25000000000000 : ℝ)^6313
        have hw : |(1071887/2000000000 : ℝ)|=(1071887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54905459/100000000 : ℝ)|^8361 ≤ (11300150347287/25000000000000 : ℝ)^6313
        have hw : |(54905459/100000000 : ℝ)|=(54905459/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6349418567/10000000000 : ℝ)|^8361 ≤ (13698685648901/25000000000000 : ℝ)^6313
        have hw : |(6349418567/10000000000 : ℝ)|=(6349418567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_9 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (492614111/5000000000 : ℝ)*x 0 + (-4392679567/10000000000 : ℝ)*x 1 + (6946132673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (492614111/5000000000 : ℝ)^8361 ≤ (4645475605881/100000000000000 : ℝ)^6313 := by
    have hnat : (492614111 : ℕ)^8361*100000000000000^6313 ≤ 4645475605881^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492614111 5000000000 4645475605881 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392679567/10000000000 : ℝ)^8361 ≤ (33637787870023/100000000000000 : ℝ)^6313 := by
    have hnat : (4392679567 : ℕ)^8361*100000000000000^6313 ≤ 33637787870023^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392679567 10000000000 33637787870023 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6946132673/10000000000 : ℝ)^8361 ≤ (7714592064121/12500000000000 : ℝ)^6313 := by
    have hnat : (6946132673 : ℕ)^8361*12500000000000^6313 ≤ 7714592064121^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6946132673 10000000000 7714592064121 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(492614111/5000000000 : ℝ), (-4392679567/10000000000 : ℝ), (6946132673/10000000000 : ℝ)] ![(4645475605881/100000000000000 : ℝ), (33637787870023/100000000000000 : ℝ), (7714592064121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(492614111/5000000000 : ℝ)|^8361 ≤ (4645475605881/100000000000000 : ℝ)^6313
        have hw : |(492614111/5000000000 : ℝ)|=(492614111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4392679567/10000000000 : ℝ)|^8361 ≤ (33637787870023/100000000000000 : ℝ)^6313
        have hw : |(-4392679567/10000000000 : ℝ)|=(4392679567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6946132673/10000000000 : ℝ)|^8361 ≤ (7714592064121/12500000000000 : ℝ)^6313
        have hw : |(6946132673/10000000000 : ℝ)|=(6946132673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_10 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (246305441/2500000000 : ℝ)*x 0 + (3473058427/5000000000 : ℝ)*x 1 + (-2196350949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246305441/2500000000 : ℝ)^8361 ≤ (4645435277261/100000000000000 : ℝ)^6313 := by
    have hnat : (246305441 : ℕ)^8361*100000000000000^6313 ≤ 4645435277261^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246305441 2500000000 4645435277261 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3473058427/5000000000 : ℝ)^8361 ≤ (30858275181883/50000000000000 : ℝ)^6313 := by
    have hnat : (3473058427 : ℕ)^8361*50000000000000^6313 ≤ 30858275181883^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3473058427 5000000000 30858275181883 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2196350949/5000000000 : ℝ)^8361 ≤ (33638014349507/100000000000000 : ℝ)^6313 := by
    have hnat : (2196350949 : ℕ)^8361*100000000000000^6313 ≤ 33638014349507^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196350949 5000000000 33638014349507 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(246305441/2500000000 : ℝ), (3473058427/5000000000 : ℝ), (-2196350949/5000000000 : ℝ)] ![(4645435277261/100000000000000 : ℝ), (30858275181883/50000000000000 : ℝ), (33638014349507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(246305441/2500000000 : ℝ)|^8361 ≤ (4645435277261/100000000000000 : ℝ)^6313
        have hw : |(246305441/2500000000 : ℝ)|=(246305441/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3473058427/5000000000 : ℝ)|^8361 ≤ (30858275181883/50000000000000 : ℝ)^6313
        have hw : |(3473058427/5000000000 : ℝ)|=(3473058427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2196350949/5000000000 : ℝ)|^8361 ≤ (33638014349507/100000000000000 : ℝ)^6313
        have hw : |(-2196350949/5000000000 : ℝ)|=(2196350949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s1_11 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (478223041/2500000000 : ℝ)*x 0 + (5805646071/10000000000 : ℝ)*x 1 + (15688563/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478223041/2500000000 : ℝ)^8361 ≤ (11185714668653/100000000000000 : ℝ)^6313 := by
    have hnat : (478223041 : ℕ)^8361*100000000000000^6313 ≤ 11185714668653^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478223041 2500000000 11185714668653 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5805646071/10000000000 : ℝ)^8361 ≤ (24333878325151/50000000000000 : ℝ)^6313 := by
    have hnat : (5805646071 : ℕ)^8361*50000000000000^6313 ≤ 24333878325151^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5805646071 10000000000 24333878325151 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15688563/31250000 : ℝ)^8361 ≤ (40146528674587/100000000000000 : ℝ)^6313 := by
    have hnat : (15688563 : ℕ)^8361*100000000000000^6313 ≤ 40146528674587^6313*31250000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15688563 31250000 40146528674587 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(478223041/2500000000 : ℝ), (5805646071/10000000000 : ℝ), (15688563/31250000 : ℝ)] ![(11185714668653/100000000000000 : ℝ), (24333878325151/50000000000000 : ℝ), (40146528674587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(478223041/2500000000 : ℝ)|^8361 ≤ (11185714668653/100000000000000 : ℝ)^6313
        have hw : |(478223041/2500000000 : ℝ)|=(478223041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5805646071/10000000000 : ℝ)|^8361 ≤ (24333878325151/50000000000000 : ℝ)^6313
        have hw : |(5805646071/10000000000 : ℝ)|=(5805646071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15688563/31250000 : ℝ)|^8361 ≤ (40146528674587/100000000000000 : ℝ)^6313
        have hw : |(15688563/31250000 : ℝ)|=(15688563/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1168_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6929/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2897/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (127/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6929/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (13/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6929/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (13/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6929/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (13/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6929/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (13/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6929/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (13/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6929/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (13/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (13/2500 : ℝ) ^ (1045/256 : ℝ) ≤ (47495697929/100000000000000000000 : ℝ) := by
    have hpowers : (13/2500 : ℝ)^1045 ≤ (47495697929/100000000000000000000 : ℝ)^256 := by
      have hnat : (13 : ℕ)^1045*100000000000000000000^256 ≤ 47495697929^256*2500^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 2500 47495697929 100000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/2500 : ℝ)) (X := (47495697929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hpowhi : (6929/25000 : ℝ) ^ (1045/256 : ℝ) ≤ (265569811689848117/50000000000000000000 : ℝ) := by
    have hpowers : (6929/25000 : ℝ)^1045 ≤ (265569811689848117/50000000000000000000 : ℝ)^256 := by
      have hnat : (6929 : ℕ)^1045*50000000000000000000^256 ≤ 265569811689848117^256*25000^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6929 25000 265569811689848117 50000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6929/25000 : ℝ)) (X := (265569811689848117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000047495697929/50000000000000000000 : ℝ) ≤ (5000000001163531/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (50000000047495697929/50000000000000000000 : ℝ)^256 ≤ (5000000001163531/5000000000000000 : ℝ)^1045 := by
      have hnat : (50000000047495697929 : ℕ)^256*5000000000000000^1045 ≤ 5000000001163531^1045*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000047495697929 50000000000000000000 5000000001163531 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000001163531/5000000000000000 : ℝ)) (X := (50000000047495697929/50000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100531139670875394163/100000000000000000000 : ℝ) ≤ (10012985642171253/10000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (100531139670875394163/100000000000000000000 : ℝ)^256 ≤ (10012985642171253/10000000000000000 : ℝ)^1045 := by
      have hnat : (100531139670875394163 : ℕ)^256*10000000000000000^1045 ≤ 10012985642171253^1045*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100531139670875394163 100000000000000000000 10012985642171253 10000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012985642171253/10000000000000000 : ℝ)) (X := (100531139670875394163/100000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25265569811689848117/25000000000000000000 : ℝ) ≤ (2506492820503861/2500000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (25265569811689848117/25000000000000000000 : ℝ)^256 ≤ (2506492820503861/2500000000000000 : ℝ)^1045 := by
      have hnat : (25265569811689848117 : ℕ)^256*2500000000000000^1045 ≤ 2506492820503861^1045*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25265569811689848117 25000000000000000000 2506492820503861 2500000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506492820503861/2500000000000000 : ℝ)) (X := (25265569811689848117/25000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(47495697929/100000000000000000000 : ℝ) ≤ ((2614870144210084803/2615000000000000000 : ℝ)+2*(12985639844191/2719600000000000 : ℝ)*(13/2500 : ℝ))^(1045/256 : ℝ) := by
    rw [show (2614870144210084803/2615000000000000000 : ℝ)+2*(12985639844191/2719600000000000 : ℝ)*(13/2500 : ℝ)=(5000000001163531/5000000000000000 : ℝ) by norm_num, show 1+2*(47495697929/100000000000000000000 : ℝ)=(50000000047495697929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(265569811689848117/50000000000000000000 : ℝ)+(47495697929/100000000000000000000 : ℝ) ≤ ((2614870144210084803/2615000000000000000 : ℝ)+(12985639844191/2719600000000000 : ℝ)*((6929/25000 : ℝ)+(13/2500 : ℝ)))^(1045/256 : ℝ) := by
    rw [show (2614870144210084803/2615000000000000000 : ℝ)+(12985639844191/2719600000000000 : ℝ)*((6929/25000 : ℝ)+(13/2500 : ℝ))=(10012985642171253/10000000000000000 : ℝ) by norm_num, show 1+(265569811689848117/50000000000000000000 : ℝ)+(47495697929/100000000000000000000 : ℝ)=(100531139670875394163/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(265569811689848117/50000000000000000000 : ℝ) ≤ ((2614870144210084803/2615000000000000000 : ℝ)+2*(12985639844191/2719600000000000 : ℝ)*(6929/25000 : ℝ))^(1045/256 : ℝ) := by
    rw [show (2614870144210084803/2615000000000000000 : ℝ)+2*(12985639844191/2719600000000000 : ℝ)*(6929/25000 : ℝ)=(2506492820503861/2500000000000000 : ℝ) by norm_num, show 1+2*(265569811689848117/50000000000000000000 : ℝ)=(25265569811689848117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2614870144210084803/2615000000000000000 : ℝ)*(X 1 0+X 2 0)+(12985639844191/2719600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (13/2500 : ℝ)) (hi := (6929/25000 : ℝ)) (c := (2614870144210084803/2615000000000000000 : ℝ)) (alpha := (12985639844191/2719600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2614870144210084803/2615000000000000000 : ℝ)*(X 0 1+X 2 1)+(12985639844191/2719600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (13/2500 : ℝ)) (hi := (6929/25000 : ℝ)) (c := (2614870144210084803/2615000000000000000 : ℝ)) (alpha := (12985639844191/2719600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2614870144210084803/2615000000000000000 : ℝ)*(X 0 2+X 1 2)+(12985639844191/2719600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (13/2500 : ℝ)) (hi := (6929/25000 : ℝ)) (c := (2614870144210084803/2615000000000000000 : ℝ)) (alpha := (12985639844191/2719600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2086388189/10000000000 : ℝ)*X 0 0+(355913919/625000000 : ℝ)*X 0 1+(62595739/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((270884903/500000000 : ℝ)*X 1 0+(-76769523/312500000 : ℝ)*X 1 1+(5007658159/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5417700177/10000000000 : ℝ)*X 2 0+(5007656203/10000000000 : ℝ)*X 2 1+(-491324893/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315228043/10000000000 : ℝ)*X 0 0+(3681886399/10000000000 : ℝ)*X 0 1+(5055550979/10000000000 : ℝ)*X 0 2+(4315228043/10000000000 : ℝ)*X 1 0+(3681886399/10000000000 : ℝ)*X 1 1+(5055550979/10000000000 : ℝ)*X 1 2+(4315228043/10000000000 : ℝ)*X 2 0+(3681886399/10000000000 : ℝ)*X 2 1+(5055550979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2087162889/10000000000 : ℝ)*X 0 0+(627118299/1250000000 : ℝ)*X 0 1+(710643773/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5241344883/10000000000 : ℝ)*X 1 0+(-222391193/1250000000 : ℝ)*X 1 1+(710644147/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2620672057/5000000000 : ℝ)*X 2 0+(2842577239/5000000000 : ℝ)*X 2 1+(-1779128737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1079191357/2500000000 : ℝ)*X 0 0+(5036982689/10000000000 : ℝ)*X 0 1+(740163901/2000000000 : ℝ)*X 0 2+(1079191357/2500000000 : ℝ)*X 1 0+(5036982689/10000000000 : ℝ)*X 1 1+(740163901/2000000000 : ℝ)*X 1 2+(1079191357/2500000000 : ℝ)*X 2 0+(5036982689/10000000000 : ℝ)*X 2 1+(740163901/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1071887/2000000000 : ℝ)*X 0 0+(54905459/100000000 : ℝ)*X 0 1+(6349418567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((492614111/5000000000 : ℝ)*X 1 0+(-4392679567/10000000000 : ℝ)*X 1 1+(6946132673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((246305441/2500000000 : ℝ)*X 2 0+(3473058427/5000000000 : ℝ)*X 2 1+(-2196350949/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((478223041/2500000000 : ℝ)*X 0 0+(5805646071/10000000000 : ℝ)*X 0 1+(15688563/31250000 : ℝ)*X 0 2+(478223041/2500000000 : ℝ)*X 1 0+(5805646071/10000000000 : ℝ)*X 1 1+(15688563/31250000 : ℝ)*X 1 2+(478223041/2500000000 : ℝ)*X 2 0+(5805646071/10000000000 : ℝ)*X 2 1+(15688563/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5455385436757289180503059/1327929687500000000000000000000 : ℝ) := by norm_num
    linear_combination (368537949/100000000000000 : ℝ)*(lower2) + (27295811905057/2500000000000 : ℝ)*(major0) + (27295811905057/2500000000000 : ℝ)*(major1) + (27295811905057/2500000000000 : ℝ)*(major2) + (727840923309957/50000000000000 : ℝ)*(sp0) + (291136235778081/20000000000000 : ℝ)*(sp1) + (363919897530147/25000000000000 : ℝ)*(sp2) + (72797865489121/10000000000000 : ℝ)*(sp3) + (1834261943/50000000000000 : ℝ)*(sp4) + (717126769/20000000000000 : ℝ)*(sp5) + (2691040391/50000000000000 : ℝ)*(sp6) + (750619549/100000000000000 : ℝ)*(sp9) + (542942429/100000000000000 : ℝ)*(sp10) + (645429931/100000000000000 : ℝ)*(sp11) + (727979300321141/100000000000000 : ℝ)*(f.failure) + (1455685515143799/100000000000000 : ℝ)*(f.sum) + (2858095489111/849875000000000000000000000 : ℝ)*base65 + (439296602799040977/84987500000000000000000000000000 : ℝ)*base68 + (685104554829103477/84987500000000000000000000000000 : ℝ)*base70 + (138976560286940977/84987500000000000000000000000000 : ℝ)*base72 + (6852078772389/3399500000000000000000000000 : ℝ)*base74 + (32767691310503477/84987500000000000000000000000000 : ℝ)*base76 + (388312434548603477/84987500000000000000000000000000 : ℝ)*base78 + (84787250280434023/84987500000000000000000000000000 : ℝ)*base79 + (147379766749/53117187500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (29569673/10000000000000000000000 : ℝ)*base89 + (29569673/10000000000000000000000 : ℝ)*base91 + (29569673/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22102899278943791409927/10460000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2146609/25000000000000 : ℝ)*(lower4) + (1122481599246449/100000000000000 : ℝ)*(major0) + (1122481599246449/100000000000000 : ℝ)*(major1) + (1122481599246449/100000000000000 : ℝ)*(major2) + (423040803/10000000000000 : ℝ)*(sp1) + (3353369543/50000000000000 : ℝ)*(sp2) + (134908497/10000000000000 : ℝ)*(sp3) + (1496545818706921/100000000000000 : ℝ)*(sp4) + (149654414701537/10000000000000 : ℝ)*(sp5) + (1496541818296163/100000000000000 : ℝ)*(sp6) + (374206202777013/50000000000000 : ℝ)*(sp7) + (338291041/12500000000000 : ℝ)*(sp8) + (147611849/100000000000000 : ℝ)*(sp9) + (848382389/100000000000000 : ℝ)*(sp11) + (149682920604277/20000000000000 : ℝ)*(f.failure) + (1496548525035249/100000000000000 : ℝ)*(f.sum) + (37342513166257/10460000000000000000000000000 : ℝ)*base66 + (157453809525347953/261500000000000000000000000000000 : ℝ)*base68 + (113793153692847953/261500000000000000000000000000000 : ℝ)*base70 + (164309956714152047/261500000000000000000000000000000 : ℝ)*base71 + (17615635942757/10460000000000000000000000000 : ℝ)*base74 + (17143864046652047/261500000000000000000000000000000 : ℝ)*base75 + (473879719330152047/261500000000000000000000000000000 : ℝ)*base77 + (301143912135347953/261500000000000000000000000000000 : ℝ)*base80 + (8883816839897/10460000000000000000000000000 : ℝ)*base82 + (1619081/2000000000000000000000 : ℝ)*base89 + (1619081/2000000000000000000000 : ℝ)*base91 + (1619081/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1168_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6929/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2897/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (127/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1168_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1168_s2_0 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-53456047/250000000 : ℝ)*x 0 + (2752961781/5000000000 : ℝ)*x 1 + (2581679987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53456047/250000000 : ℝ)^8361 ≤ (12963450186037/100000000000000 : ℝ)^6313 := by
    have hnat : (53456047 : ℕ)^8361*100000000000000^6313 ≤ 12963450186037^6313*250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53456047 250000000 12963450186037 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2752961781/5000000000 : ℝ)^8361 ≤ (5671042766443/12500000000000 : ℝ)^6313 := by
    have hnat : (2752961781 : ℕ)^8361*12500000000000^6313 ≤ 5671042766443^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752961781 5000000000 5671042766443 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2581679987/5000000000 : ℝ)^8361 ≤ (10417051916727/25000000000000 : ℝ)^6313 := by
    have hnat : (2581679987 : ℕ)^8361*25000000000000^6313 ≤ 10417051916727^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2581679987 5000000000 10417051916727 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53456047/250000000 : ℝ), (2752961781/5000000000 : ℝ), (2581679987/5000000000 : ℝ)] ![(12963450186037/100000000000000 : ℝ), (5671042766443/12500000000000 : ℝ), (10417051916727/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53456047/250000000 : ℝ)|^8361 ≤ (12963450186037/100000000000000 : ℝ)^6313
        have hw : |(-53456047/250000000 : ℝ)|=(53456047/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2752961781/5000000000 : ℝ)|^8361 ≤ (5671042766443/12500000000000 : ℝ)^6313
        have hw : |(2752961781/5000000000 : ℝ)|=(2752961781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2581679987/5000000000 : ℝ)|^8361 ≤ (10417051916727/25000000000000 : ℝ)^6313
        have hw : |(2581679987/5000000000 : ℝ)|=(2581679987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s2_1 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5372752589/10000000000 : ℝ)*x 0 + (-2316162147/10000000000 : ℝ)*x 1 + (5163362741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372752589/10000000000 : ℝ)^8361 ≤ (10980194229171/25000000000000 : ℝ)^6313 := by
    have hnat : (5372752589 : ℕ)^8361*25000000000000^6313 ≤ 10980194229171^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372752589 10000000000 10980194229171 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2316162147/10000000000 : ℝ)^8361 ≤ (7205492913891/50000000000000 : ℝ)^6313 := by
    have hnat : (2316162147 : ℕ)^8361*50000000000000^6313 ≤ 7205492913891^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316162147 10000000000 7205492913891 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5163362741/10000000000 : ℝ)^8361 ≤ (20834118620249/50000000000000 : ℝ)^6313 := by
    have hnat : (5163362741 : ℕ)^8361*50000000000000^6313 ≤ 20834118620249^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5163362741 10000000000 20834118620249 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372752589/10000000000 : ℝ), (-2316162147/10000000000 : ℝ), (5163362741/10000000000 : ℝ)] ![(10980194229171/25000000000000 : ℝ), (7205492913891/50000000000000 : ℝ), (20834118620249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372752589/10000000000 : ℝ)|^8361 ≤ (10980194229171/25000000000000 : ℝ)^6313
        have hw : |(5372752589/10000000000 : ℝ)|=(5372752589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2316162147/10000000000 : ℝ)|^8361 ≤ (7205492913891/50000000000000 : ℝ)^6313
        have hw : |(-2316162147/10000000000 : ℝ)|=(2316162147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5163362741/10000000000 : ℝ)|^8361 ≤ (20834118620249/50000000000000 : ℝ)^6313
        have hw : |(5163362741/10000000000 : ℝ)|=(5163362741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s2_2 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53727531/100000000 : ℝ)*x 0 + (1290840467/2500000000 : ℝ)*x 1 + (-2316162607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53727531/100000000 : ℝ)^8361 ≤ (43920782449121/100000000000000 : ℝ)^6313 := by
    have hnat : (53727531 : ℕ)^8361*100000000000000^6313 ≤ 43920782449121^6313*100000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53727531 100000000 43920782449121 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1290840467/2500000000 : ℝ)^8361 ≤ (41668227909907/100000000000000 : ℝ)^6313 := by
    have hnat : (1290840467 : ℕ)^8361*100000000000000^6313 ≤ 41668227909907^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1290840467 2500000000 41668227909907 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2316162607/10000000000 : ℝ)^8361 ≤ (3602747404589/25000000000000 : ℝ)^6313 := by
    have hnat : (2316162607 : ℕ)^8361*25000000000000^6313 ≤ 3602747404589^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316162607 10000000000 3602747404589 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53727531/100000000 : ℝ), (1290840467/2500000000 : ℝ), (-2316162607/10000000000 : ℝ)] ![(43920782449121/100000000000000 : ℝ), (41668227909907/100000000000000 : ℝ), (3602747404589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53727531/100000000 : ℝ)|^8361 ≤ (43920782449121/100000000000000 : ℝ)^6313
        have hw : |(53727531/100000000 : ℝ)|=(53727531/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1290840467/2500000000 : ℝ)|^8361 ≤ (41668227909907/100000000000000 : ℝ)^6313
        have hw : |(1290840467/2500000000 : ℝ)|=(1290840467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2316162607/10000000000 : ℝ)|^8361 ≤ (3602747404589/25000000000000 : ℝ)^6313
        have hw : |(-2316162607/10000000000 : ℝ)|=(2316162607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s2_3 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870172643/2000000000 : ℝ)*x 0 + (1005411479/2500000000 : ℝ)*x 1 + (1176659979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870172643/2000000000 : ℝ)^8361 ≤ (4151793235947/12500000000000 : ℝ)^6313 := by
    have hnat : (870172643 : ℕ)^8361*12500000000000^6313 ≤ 4151793235947^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870172643 2000000000 4151793235947 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005411479/2500000000 : ℝ)^8361 ≤ (3740920777139/12500000000000 : ℝ)^6313 := by
    have hnat : (1005411479 : ℕ)^8361*12500000000000^6313 ≤ 3740920777139^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005411479 2500000000 3740920777139 12500000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1176659979/2500000000 : ℝ)^8361 ≤ (9214571969179/25000000000000 : ℝ)^6313 := by
    have hnat : (1176659979 : ℕ)^8361*25000000000000^6313 ≤ 9214571969179^6313*2500000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176659979 2500000000 9214571969179 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870172643/2000000000 : ℝ), (1005411479/2500000000 : ℝ), (1176659979/2500000000 : ℝ)] ![(4151793235947/12500000000000 : ℝ), (3740920777139/12500000000000 : ℝ), (9214571969179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870172643/2000000000 : ℝ)|^8361 ≤ (4151793235947/12500000000000 : ℝ)^6313
        have hw : |(870172643/2000000000 : ℝ)|=(870172643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005411479/2500000000 : ℝ)|^8361 ≤ (3740920777139/12500000000000 : ℝ)^6313
        have hw : |(1005411479/2500000000 : ℝ)|=(1005411479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1176659979/2500000000 : ℝ)|^8361 ≤ (9214571969179/25000000000000 : ℝ)^6313
        have hw : |(1176659979/2500000000 : ℝ)|=(1176659979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s2_4 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267292107/1250000000 : ℝ)*x 0 + (645710011/1250000000 : ℝ)*x 1 + (5503581089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267292107/1250000000 : ℝ)^8361 ≤ (12964212797291/100000000000000 : ℝ)^6313 := by
    have hnat : (267292107 : ℕ)^8361*100000000000000^6313 ≤ 12964212797291^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267292107 1250000000 12964212797291 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645710011/1250000000 : ℝ)^8361 ≤ (20846503380727/50000000000000 : ℝ)^6313 := by
    have hnat : (645710011 : ℕ)^8361*50000000000000^6313 ≤ 20846503380727^6313*1250000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645710011 1250000000 20846503380727 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5503581089/10000000000 : ℝ)^8361 ≤ (11335695107127/25000000000000 : ℝ)^6313 := by
    have hnat : (5503581089 : ℕ)^8361*25000000000000^6313 ≤ 11335695107127^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503581089 10000000000 11335695107127 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267292107/1250000000 : ℝ), (645710011/1250000000 : ℝ), (5503581089/10000000000 : ℝ)] ![(12964212797291/100000000000000 : ℝ), (20846503380727/50000000000000 : ℝ), (11335695107127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267292107/1250000000 : ℝ)|^8361 ≤ (12964212797291/100000000000000 : ℝ)^6313
        have hw : |(-267292107/1250000000 : ℝ)|=(267292107/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(645710011/1250000000 : ℝ)|^8361 ≤ (20846503380727/50000000000000 : ℝ)^6313
        have hw : |(645710011/1250000000 : ℝ)|=(645710011/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5503581089/10000000000 : ℝ)|^8361 ≤ (11335695107127/25000000000000 : ℝ)^6313
        have hw : |(5503581089/10000000000 : ℝ)|=(5503581089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s2_5 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528568557/1000000000 : ℝ)*x 0 + (-1975942637/10000000000 : ℝ)*x 1 + (2751790543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528568557/1000000000 : ℝ)^8361 ≤ (42980616428711/100000000000000 : ℝ)^6313 := by
    have hnat : (528568557 : ℕ)^8361*100000000000000^6313 ≤ 42980616428711^6313*1000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528568557 1000000000 42980616428711 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975942637/10000000000 : ℝ)^8361 ≤ (467064126437/4000000000000 : ℝ)^6313 := by
    have hnat : (1975942637 : ℕ)^8361*4000000000000^6313 ≤ 467064126437^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975942637 10000000000 467064126437 4000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2751790543/5000000000 : ℝ)^8361 ≤ (45342780395773/100000000000000 : ℝ)^6313 := by
    have hnat : (2751790543 : ℕ)^8361*100000000000000^6313 ≤ 45342780395773^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751790543 5000000000 45342780395773 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528568557/1000000000 : ℝ), (-1975942637/10000000000 : ℝ), (2751790543/5000000000 : ℝ)] ![(42980616428711/100000000000000 : ℝ), (467064126437/4000000000000 : ℝ), (45342780395773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528568557/1000000000 : ℝ)|^8361 ≤ (42980616428711/100000000000000 : ℝ)^6313
        have hw : |(528568557/1000000000 : ℝ)|=(528568557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1975942637/10000000000 : ℝ)|^8361 ≤ (467064126437/4000000000000 : ℝ)^6313
        have hw : |(-1975942637/10000000000 : ℝ)|=(1975942637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2751790543/5000000000 : ℝ)|^8361 ≤ (45342780395773/100000000000000 : ℝ)^6313
        have hw : |(2751790543/5000000000 : ℝ)|=(2751790543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s2_6 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5285685699/10000000000 : ℝ)*x 0 + (2751790541/5000000000 : ℝ)*x 1 + (-395188493/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285685699/10000000000 : ℝ)^8361 ≤ (42980617817971/100000000000000 : ℝ)^6313 := by
    have hnat : (5285685699 : ℕ)^8361*100000000000000^6313 ≤ 42980617817971^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285685699 10000000000 42980617817971 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2751790541/5000000000 : ℝ)^8361 ≤ (45342780352127/100000000000000 : ℝ)^6313 := by
    have hnat : (2751790541 : ℕ)^8361*100000000000000^6313 ≤ 45342780352127^6313*5000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2751790541 5000000000 45342780352127 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395188493/2000000000 : ℝ)^8361 ≤ (11676601814777/100000000000000 : ℝ)^6313 := by
    have hnat : (395188493 : ℕ)^8361*100000000000000^6313 ≤ 11676601814777^6313*2000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395188493 2000000000 11676601814777 100000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285685699/10000000000 : ℝ), (2751790541/5000000000 : ℝ), (-395188493/2000000000 : ℝ)] ![(42980617817971/100000000000000 : ℝ), (45342780352127/100000000000000 : ℝ), (11676601814777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285685699/10000000000 : ℝ)|^8361 ≤ (42980617817971/100000000000000 : ℝ)^6313
        have hw : |(5285685699/10000000000 : ℝ)|=(5285685699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2751790541/5000000000 : ℝ)|^8361 ≤ (45342780352127/100000000000000 : ℝ)^6313
        have hw : |(2751790541/5000000000 : ℝ)|=(2751790541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395188493/2000000000 : ℝ)|^8361 ≤ (11676601814777/100000000000000 : ℝ)^6313
        have hw : |(-395188493/2000000000 : ℝ)|=(395188493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1168_s2_7 (p : ℝ) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4351054761/10000000000 : ℝ)*x 0 + (4702003013/10000000000 : ℝ)*x 1 + (4026327391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351054761/10000000000 : ℝ)^8361 ≤ (8304070631893/25000000000000 : ℝ)^6313 := by
    have hnat : (4351054761 : ℕ)^8361*25000000000000^6313 ≤ 8304070631893^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351054761 10000000000 8304070631893 25000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4702003013/10000000000 : ℝ)^8361 ≤ (18405101682671/50000000000000 : ℝ)^6313 := by
    have hnat : (4702003013 : ℕ)^8361*50000000000000^6313 ≤ 18405101682671^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4702003013 10000000000 18405101682671 50000000000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4026327391/10000000000 : ℝ)^8361 ≤ (93667231563/312500000000 : ℝ)^6313 := by
    have hnat : (4026327391 : ℕ)^8361*312500000000^6313 ≤ 93667231563^6313*10000000000^8361 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026327391 10000000000 93667231563 312500000000 8361 6313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8361/2048 : ℝ)) 8361 6313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351054761/10000000000 : ℝ), (4702003013/10000000000 : ℝ), (4026327391/10000000000 : ℝ)] ![(8304070631893/25000000000000 : ℝ), (18405101682671/50000000000000 : ℝ), (93667231563/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351054761/10000000000 : ℝ)|^8361 ≤ (8304070631893/25000000000000 : ℝ)^6313
        have hw : |(4351054761/10000000000 : ℝ)|=(4351054761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4702003013/10000000000 : ℝ)|^8361 ≤ (18405101682671/50000000000000 : ℝ)^6313
        have hw : |(4702003013/10000000000 : ℝ)|=(4702003013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4026327391/10000000000 : ℝ)|^8361 ≤ (93667231563/312500000000 : ℝ)^6313
        have hw : |(4026327391/10000000000 : ℝ)|=(4026327391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1168_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (127/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2897/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4593/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8213/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (127/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2897/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (127/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2897/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (127/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2897/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (127/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2897/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (127/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2897/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (127/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2897/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2897/50000 : ℝ) ^ (1045/256 : ℝ) ≤ (446076708093111/50000000000000000000 : ℝ) := by
    have hpowers : (2897/50000 : ℝ)^1045 ≤ (446076708093111/50000000000000000000 : ℝ)^256 := by
      have hnat : (2897 : ℕ)^1045*50000000000000000000^256 ≤ 446076708093111^256*50000^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2897 50000 446076708093111 50000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2897/50000 : ℝ)) (X := (446076708093111/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hpowhi : (127/625 : ℝ) ^ (1045/256 : ℝ) ≤ (29919403198810001/20000000000000000000 : ℝ) := by
    have hpowers : (127/625 : ℝ)^1045 ≤ (29919403198810001/20000000000000000000 : ℝ)^256 := by
      have hnat : (127 : ℕ)^1045*20000000000000000000^256 ≤ 29919403198810001^256*625^1045 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        127 625 29919403198810001 20000000000000000000 1045 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (127/625 : ℝ)) (X := (29919403198810001/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000446076708093111/25000000000000000000 : ℝ) ≤ (5000021855477141/5000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (25000446076708093111/25000000000000000000 : ℝ)^256 ≤ (5000021855477141/5000000000000000 : ℝ)^1045 := by
      have hnat : (25000446076708093111 : ℕ)^256*5000000000000000^1045 ≤ 5000021855477141^1045*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000446076708093111 25000000000000000000 5000021855477141 5000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000021855477141/5000000000000000 : ℝ)) (X := (25000446076708093111/25000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100150489169410236227/100000000000000000000 : ℝ) ≤ (10003684532045249/10000000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (100150489169410236227/100000000000000000000 : ℝ)^256 ≤ (10003684532045249/10000000000000000 : ℝ)^1045 := by
      have hnat : (100150489169410236227 : ℕ)^256*10000000000000000^1045 ≤ 10003684532045249^1045*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100150489169410236227 100000000000000000000 10003684532045249 10000000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003684532045249/10000000000000000 : ℝ)) (X := (100150489169410236227/100000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10029919403198810001/10000000000000000000 : ℝ) ≤ (1250915669142027/1250000000000000 : ℝ) ^ (1045/256 : ℝ) := by
    have hpowers : (10029919403198810001/10000000000000000000 : ℝ)^256 ≤ (1250915669142027/1250000000000000 : ℝ)^1045 := by
      have hnat : (10029919403198810001 : ℕ)^256*1250000000000000^1045 ≤ 1250915669142027^1045*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10029919403198810001 10000000000000000000 1250915669142027 1250000000000000 256 1045 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250915669142027/1250000000000000 : ℝ)) (X := (10029919403198810001/10000000000000000000 : ℝ)) (by norm_num) 1045 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(446076708093111/50000000000000000000 : ℝ) ≤ ((9076152819407485921/9078750000000000000 : ℝ)+2*(3640821090967/1452600000000000 : ℝ)*(2897/50000 : ℝ))^(1045/256 : ℝ) := by
    rw [show (9076152819407485921/9078750000000000000 : ℝ)+2*(3640821090967/1452600000000000 : ℝ)*(2897/50000 : ℝ)=(5000021855477141/5000000000000000 : ℝ) by norm_num, show 1+2*(446076708093111/50000000000000000000 : ℝ)=(25000446076708093111/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29919403198810001/20000000000000000000 : ℝ)+(446076708093111/50000000000000000000 : ℝ) ≤ ((9076152819407485921/9078750000000000000 : ℝ)+(3640821090967/1452600000000000 : ℝ)*((127/625 : ℝ)+(2897/50000 : ℝ)))^(1045/256 : ℝ) := by
    rw [show (9076152819407485921/9078750000000000000 : ℝ)+(3640821090967/1452600000000000 : ℝ)*((127/625 : ℝ)+(2897/50000 : ℝ))=(10003684532045249/10000000000000000 : ℝ) by norm_num, show 1+(29919403198810001/20000000000000000000 : ℝ)+(446076708093111/50000000000000000000 : ℝ)=(100150489169410236227/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29919403198810001/20000000000000000000 : ℝ) ≤ ((9076152819407485921/9078750000000000000 : ℝ)+2*(3640821090967/1452600000000000 : ℝ)*(127/625 : ℝ))^(1045/256 : ℝ) := by
    rw [show (9076152819407485921/9078750000000000000 : ℝ)+2*(3640821090967/1452600000000000 : ℝ)*(127/625 : ℝ)=(1250915669142027/1250000000000000 : ℝ) by norm_num, show 1+2*(29919403198810001/20000000000000000000 : ℝ)=(10029919403198810001/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9076152819407485921/9078750000000000000 : ℝ)*(X 1 0+X 2 0)+(3640821090967/1452600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (2897/50000 : ℝ)) (hi := (127/625 : ℝ)) (c := (9076152819407485921/9078750000000000000 : ℝ)) (alpha := (3640821090967/1452600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9076152819407485921/9078750000000000000 : ℝ)*(X 0 1+X 2 1)+(3640821090967/1452600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (2897/50000 : ℝ)) (hi := (127/625 : ℝ)) (c := (9076152819407485921/9078750000000000000 : ℝ)) (alpha := (3640821090967/1452600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9076152819407485921/9078750000000000000 : ℝ)*(X 0 2+X 1 2)+(3640821090967/1452600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1045/256 : ℝ)) (lo := (2897/50000 : ℝ)) (hi := (127/625 : ℝ)) (c := (9076152819407485921/9078750000000000000 : ℝ)) (alpha := (3640821090967/1452600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-53456047/250000000 : ℝ)*X 0 0+(2752961781/5000000000 : ℝ)*X 0 1+(2581679987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5372752589/10000000000 : ℝ)*X 1 0+(-2316162147/10000000000 : ℝ)*X 1 1+(5163362741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((53727531/100000000 : ℝ)*X 2 0+(1290840467/2500000000 : ℝ)*X 2 1+(-2316162607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870172643/2000000000 : ℝ)*X 0 0+(1005411479/2500000000 : ℝ)*X 0 1+(1176659979/2500000000 : ℝ)*X 0 2+(870172643/2000000000 : ℝ)*X 1 0+(1005411479/2500000000 : ℝ)*X 1 1+(1176659979/2500000000 : ℝ)*X 1 2+(870172643/2000000000 : ℝ)*X 2 0+(1005411479/2500000000 : ℝ)*X 2 1+(1176659979/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267292107/1250000000 : ℝ)*X 0 0+(645710011/1250000000 : ℝ)*X 0 1+(5503581089/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528568557/1000000000 : ℝ)*X 1 0+(-1975942637/10000000000 : ℝ)*X 1 1+(2751790543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5285685699/10000000000 : ℝ)*X 2 0+(2751790541/5000000000 : ℝ)*X 2 1+(-395188493/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351054761/10000000000 : ℝ)*X 0 0+(4702003013/10000000000 : ℝ)*X 0 1+(4026327391/10000000000 : ℝ)*X 0 2+(4351054761/10000000000 : ℝ)*X 1 0+(4702003013/10000000000 : ℝ)*X 1 1+(4026327391/10000000000 : ℝ)*X 1 2+(4351054761/10000000000 : ℝ)*X 2 0+(4702003013/10000000000 : ℝ)*X 2 1+(4026327391/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1168_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22005775940336188671122407/2101562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (348190571/25000000000000 : ℝ)*(base19) + (322542137/25000000000000 : ℝ)*(base23) + (537819/25000000000000 : ℝ)*(upper2) + (528368147/100000000000000 : ℝ)*(upper3) + (206444849/100000000000000 : ℝ)*(upper4) + (136847392738993/6250000000000 : ℝ)*(major0) + (136847392738993/6250000000000 : ℝ)*(major1) + (136847392738993/6250000000000 : ℝ)*(major2) + (729800056936269/25000000000000 : ℝ)*(sp0) + (9122583895307/312500000000 : ℝ)*(sp1) + (116769077963679/4000000000000 : ℝ)*(sp2) + (1459874596423933/100000000000000 : ℝ)*(sp3) + (28011515447/100000000000000 : ℝ)*(sp4) + (2676584997/20000000000000 : ℝ)*(sp7) + (729943989674459/50000000000000 : ℝ)*(f.failure) + (2919228239260523/100000000000000 : ℝ)*(f.sum) + (54062959775357/9078750000000000000000000000 : ℝ)*base65 + (214777675526713231/113484375000000000000000000000000 : ℝ)*base67 + (47507529647756491/7092773437500000000000000000000 : ℝ)*base69 + (398017552446817553/56742187500000000000000000000000 : ℝ)*base71 + (40202348036347/36315000000000000000000000000 : ℝ)*base74 + (454560218099630519/113484375000000000000000000000000 : ℝ)*base76 + (606690967729473803/56742187500000000000000000000000 : ℝ)*base77 + (34381863069275731/113484375000000000000000000000000 : ℝ)*base79 + (20709972931811/18157500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (22917127/5000000000000000000000 : ℝ)*base89 + (22917127/5000000000000000000000 : ℝ)*base91 + (22917127/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119018321838398660009549/24210000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1209250989/100000000000000 : ℝ)*(base19) + (671204847/50000000000000 : ℝ)*(base23) + (2724479/25000000000000 : ℝ)*(upper2) + (148442321/100000000000000 : ℝ)*(upper3) + (53614561/50000000000000 : ℝ)*(upper5) + (2219723501257183/100000000000000 : ℝ)*(major0) + (2219723501257183/100000000000000 : ℝ)*(major1) + (2219723501257183/100000000000000 : ℝ)*(major2) + (11592547931/100000000000000 : ℝ)*(sp1) + (438746331/3125000000000 : ℝ)*(sp2) + (369930775082559/12500000000000 : ℝ)*(sp4) + (184964587428847/6250000000000 : ℝ)*(sp5) + (1479715409184093/50000000000000 : ℝ)*(sp6) + (370000159496131/25000000000000 : ℝ)*(sp7) + (370000159496131/25000000000000 : ℝ)*(f.failure) + (369930775082559/12500000000000 : ℝ)*(f.sum) + (258119613940801/72630000000000000000000000000 : ℝ)*base65 + (4100637736719376793/907875000000000000000000000000000 : ℝ)*base67 + (1301090088914623207/907875000000000000000000000000000 : ℝ)*base70 + (116545512798748207/907875000000000000000000000000000 : ℝ)*base72 + (301795838825431/72630000000000000000000000000 : ℝ)*base73 + (114343429302748207/907875000000000000000000000000000 : ℝ)*base76 + (1844683089883126793/907875000000000000000000000000000 : ℝ)*base77 + (3509631473539876793/907875000000000000000000000000000 : ℝ)*base79 + (123745562295539/72630000000000000000000000000 : ℝ)*base82 + (1032143/2500000000000000000000 : ℝ)*base89 + (1032143/2500000000000000000000 : ℝ)*base91 + (1032143/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1168_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (127/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2897/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1168_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1168_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1168_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1168_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1168_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1045/256 : ℝ) ≤ p) (hpb : p ≤ (8361/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (149981253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4593/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8213/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1168_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
