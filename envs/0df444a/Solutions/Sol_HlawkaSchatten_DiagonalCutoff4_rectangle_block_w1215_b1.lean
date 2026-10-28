-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:53.119875+00:00
-- url     : https://prove2.me/submissions/8f74948b-437b-41d7-9c98-737a9458111d

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
theorem support_rectangle_w1215_s3_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064689889/5000000000 : ℝ)*x 0 + (5422079067/10000000000 : ℝ)*x 1 + (5238480567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064689889/5000000000 : ℝ)^1051 ≤ (6470117779567/50000000000000 : ℝ)^795 := by
    have hnat : (1064689889 : ℕ)^1051*50000000000000^795 ≤ 6470117779567^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064689889 5000000000 6470117779567 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422079067/10000000000 : ℝ)^1051 ≤ (44520896918467/100000000000000 : ℝ)^795 := by
    have hnat : (5422079067 : ℕ)^1051*100000000000000^795 ≤ 44520896918467^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422079067 10000000000 44520896918467 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238480567/10000000000 : ℝ)^1051 ≤ (2658679219349/6250000000000 : ℝ)^795 := by
    have hnat : (5238480567 : ℕ)^1051*6250000000000^795 ≤ 2658679219349^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238480567 10000000000 2658679219349 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064689889/5000000000 : ℝ), (5422079067/10000000000 : ℝ), (5238480567/10000000000 : ℝ)] ![(6470117779567/50000000000000 : ℝ), (44520896918467/100000000000000 : ℝ), (2658679219349/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064689889/5000000000 : ℝ)|^1051 ≤ (6470117779567/50000000000000 : ℝ)^795
        have hw : |(-1064689889/5000000000 : ℝ)|=(1064689889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422079067/10000000000 : ℝ)|^1051 ≤ (44520896918467/100000000000000 : ℝ)^795
        have hw : |(5422079067/10000000000 : ℝ)|=(5422079067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238480567/10000000000 : ℝ)|^1051 ≤ (2658679219349/6250000000000 : ℝ)^795
        have hw : |(5238480567/10000000000 : ℝ)|=(5238480567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s3_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5352092933/10000000000 : ℝ)*x 0 + (-555772007/2500000000 : ℝ)*x 1 + (5238480657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352092933/10000000000 : ℝ)^1051 ≤ (43762774212689/100000000000000 : ℝ)^795 := by
    have hnat : (5352092933 : ℕ)^1051*100000000000000^795 ≤ 43762774212689^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352092933 10000000000 43762774212689 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (555772007/2500000000 : ℝ)^1051 ≤ (1712294662751/12500000000000 : ℝ)^795 := by
    have hnat : (555772007 : ℕ)^1051*12500000000000^795 ≤ 1712294662751^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555772007 2500000000 1712294662751 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238480657/10000000000 : ℝ)^1051 ≤ (21269434237883/50000000000000 : ℝ)^795 := by
    have hnat : (5238480657 : ℕ)^1051*50000000000000^795 ≤ 21269434237883^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238480657 10000000000 21269434237883 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352092933/10000000000 : ℝ), (-555772007/2500000000 : ℝ), (5238480657/10000000000 : ℝ)] ![(43762774212689/100000000000000 : ℝ), (1712294662751/12500000000000 : ℝ), (21269434237883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352092933/10000000000 : ℝ)|^1051 ≤ (43762774212689/100000000000000 : ℝ)^795
        have hw : |(5352092933/10000000000 : ℝ)|=(5352092933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-555772007/2500000000 : ℝ)|^1051 ≤ (1712294662751/12500000000000 : ℝ)^795
        have hw : |(-555772007/2500000000 : ℝ)|=(555772007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238480657/10000000000 : ℝ)|^1051 ≤ (21269434237883/50000000000000 : ℝ)^795
        have hw : |(5238480657/10000000000 : ℝ)|=(5238480657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s3_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2676046433/5000000000 : ℝ)*x 0 + (5238480871/10000000000 : ℝ)*x 1 + (-1111543917/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676046433/5000000000 : ℝ)^1051 ≤ (21881386744217/50000000000000 : ℝ)^795 := by
    have hnat : (2676046433 : ℕ)^1051*50000000000000^795 ≤ 21881386744217^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676046433 5000000000 21881386744217 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238480871/10000000000 : ℝ)^1051 ≤ (4253887077313/10000000000000 : ℝ)^795 := by
    have hnat : (5238480871 : ℕ)^1051*10000000000000^795 ≤ 4253887077313^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238480871 10000000000 4253887077313 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1111543917/5000000000 : ℝ)^1051 ≤ (13698355721673/100000000000000 : ℝ)^795 := by
    have hnat : (1111543917 : ℕ)^1051*100000000000000^795 ≤ 13698355721673^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111543917 5000000000 13698355721673 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676046433/5000000000 : ℝ), (5238480871/10000000000 : ℝ), (-1111543917/5000000000 : ℝ)] ![(21881386744217/50000000000000 : ℝ), (4253887077313/10000000000000 : ℝ), (13698355721673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676046433/5000000000 : ℝ)|^1051 ≤ (21881386744217/50000000000000 : ℝ)^795
        have hw : |(2676046433/5000000000 : ℝ)|=(2676046433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238480871/10000000000 : ℝ)|^1051 ≤ (4253887077313/10000000000000 : ℝ)^795
        have hw : |(5238480871/10000000000 : ℝ)|=(5238480871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1111543917/5000000000 : ℝ)|^1051 ≤ (13698355721673/100000000000000 : ℝ)^795
        have hw : |(-1111543917/5000000000 : ℝ)|=(1111543917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s3_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4352655029/10000000000 : ℝ)*x 0 + (2085628437/5000000000 : ℝ)*x 1 + (1135439523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352655029/10000000000 : ℝ)^1051 ≤ (16649399594159/50000000000000 : ℝ)^795 := by
    have hnat : (4352655029 : ℕ)^1051*50000000000000^795 ≤ 16649399594159^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352655029 10000000000 16649399594159 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085628437/5000000000 : ℝ)^1051 ≤ (1967288844833/6250000000000 : ℝ)^795 := by
    have hnat : (2085628437 : ℕ)^1051*6250000000000^795 ≤ 1967288844833^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085628437 5000000000 1967288844833 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135439523/2500000000 : ℝ)^1051 ≤ (8806144818507/25000000000000 : ℝ)^795 := by
    have hnat : (1135439523 : ℕ)^1051*25000000000000^795 ≤ 8806144818507^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135439523 2500000000 8806144818507 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352655029/10000000000 : ℝ), (2085628437/5000000000 : ℝ), (1135439523/2500000000 : ℝ)] ![(16649399594159/50000000000000 : ℝ), (1967288844833/6250000000000 : ℝ), (8806144818507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352655029/10000000000 : ℝ)|^1051 ≤ (16649399594159/50000000000000 : ℝ)^795
        have hw : |(4352655029/10000000000 : ℝ)|=(4352655029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085628437/5000000000 : ℝ)|^1051 ≤ (1967288844833/6250000000000 : ℝ)^795
        have hw : |(2085628437/5000000000 : ℝ)|=(2085628437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1135439523/2500000000 : ℝ)|^1051 ≤ (8806144818507/25000000000000 : ℝ)^795
        have hw : |(1135439523/2500000000 : ℝ)|=(1135439523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s3_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-532348713/2500000000 : ℝ)*x 0 + (654894919/1250000000 : ℝ)*x 1 + (2710698293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532348713/2500000000 : ℝ)^1051 ≤ (2588071332357/20000000000000 : ℝ)^795 := by
    have hnat : (532348713 : ℕ)^1051*20000000000000^795 ≤ 2588071332357^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532348713 2500000000 2588071332357 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654894919/1250000000 : ℝ)^1051 ≤ (21273077327791/50000000000000 : ℝ)^795 := by
    have hnat : (654894919 : ℕ)^1051*50000000000000^795 ≤ 21273077327791^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654894919 1250000000 21273077327791 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710698293/5000000000 : ℝ)^1051 ≤ (44513488672221/100000000000000 : ℝ)^795 := by
    have hnat : (2710698293 : ℕ)^1051*100000000000000^795 ≤ 44513488672221^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710698293 5000000000 44513488672221 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532348713/2500000000 : ℝ), (654894919/1250000000 : ℝ), (2710698293/5000000000 : ℝ)] ![(2588071332357/20000000000000 : ℝ), (21273077327791/50000000000000 : ℝ), (44513488672221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532348713/2500000000 : ℝ)|^1051 ≤ (2588071332357/20000000000000 : ℝ)^795
        have hw : |(-532348713/2500000000 : ℝ)|=(532348713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654894919/1250000000 : ℝ)|^1051 ≤ (21273077327791/50000000000000 : ℝ)^795
        have hw : |(654894919/1250000000 : ℝ)|=(654894919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710698293/5000000000 : ℝ)|^1051 ≤ (44513488672221/100000000000000 : ℝ)^795
        have hw : |(2710698293/5000000000 : ℝ)|=(2710698293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s3_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305338017/10000000000 : ℝ)*x 0 + (-2040172023/10000000000 : ℝ)*x 1 + (677674597/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305338017/10000000000 : ℝ)^1051 ≤ (43258076216033/100000000000000 : ℝ)^795 := by
    have hnat : (5305338017 : ℕ)^1051*100000000000000^795 ≤ 43258076216033^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305338017 10000000000 43258076216033 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2040172023/10000000000 : ℝ)^1051 ≤ (12228433045237/100000000000000 : ℝ)^795 := by
    have hnat : (2040172023 : ℕ)^1051*100000000000000^795 ≤ 12228433045237^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2040172023 10000000000 12228433045237 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677674597/1250000000 : ℝ)^1051 ≤ (22256745367303/50000000000000 : ℝ)^795 := by
    have hnat : (677674597 : ℕ)^1051*50000000000000^795 ≤ 22256745367303^795*1250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677674597 1250000000 22256745367303 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305338017/10000000000 : ℝ), (-2040172023/10000000000 : ℝ), (677674597/1250000000 : ℝ)] ![(43258076216033/100000000000000 : ℝ), (12228433045237/100000000000000 : ℝ), (22256745367303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305338017/10000000000 : ℝ)|^1051 ≤ (43258076216033/100000000000000 : ℝ)^795
        have hw : |(5305338017/10000000000 : ℝ)|=(5305338017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2040172023/10000000000 : ℝ)|^1051 ≤ (12228433045237/100000000000000 : ℝ)^795
        have hw : |(-2040172023/10000000000 : ℝ)|=(2040172023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677674597/1250000000 : ℝ)|^1051 ≤ (22256745367303/50000000000000 : ℝ)^795
        have hw : |(677674597/1250000000 : ℝ)|=(677674597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s3_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305338099/10000000000 : ℝ)*x 0 + (5421396673/10000000000 : ℝ)*x 1 + (-510043013/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305338099/10000000000 : ℝ)^1051 ≤ (21629038549967/50000000000000 : ℝ)^795 := by
    have hnat : (5305338099 : ℕ)^1051*50000000000000^795 ≤ 21629038549967^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305338099 10000000000 21629038549967 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421396673/10000000000 : ℝ)^1051 ≤ (695523275259/1562500000000 : ℝ)^795 := by
    have hnat : (5421396673 : ℕ)^1051*1562500000000^795 ≤ 695523275259^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421396673 10000000000 695523275259 1562500000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510043013/2500000000 : ℝ)^1051 ≤ (1222843327503/10000000000000 : ℝ)^795 := by
    have hnat : (510043013 : ℕ)^1051*10000000000000^795 ≤ 1222843327503^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510043013 2500000000 1222843327503 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305338099/10000000000 : ℝ), (5421396673/10000000000 : ℝ), (-510043013/2500000000 : ℝ)] ![(21629038549967/50000000000000 : ℝ), (695523275259/1562500000000 : ℝ), (1222843327503/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305338099/10000000000 : ℝ)|^1051 ≤ (21629038549967/50000000000000 : ℝ)^795
        have hw : |(5305338099/10000000000 : ℝ)|=(5305338099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421396673/10000000000 : ℝ)|^1051 ≤ (695523275259/1562500000000 : ℝ)^795
        have hw : |(5421396673/10000000000 : ℝ)|=(5421396673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510043013/2500000000 : ℝ)|^1051 ≤ (1222843327503/10000000000000 : ℝ)^795
        have hw : |(-510043013/2500000000 : ℝ)|=(510043013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s3_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4352685349/10000000000 : ℝ)*x 0 + (4540388677/10000000000 : ℝ)*x 1 + (2086316727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352685349/10000000000 : ℝ)^1051 ≤ (1040597057373/3125000000000 : ℝ)^795 := by
    have hnat : (4352685349 : ℕ)^1051*3125000000000^795 ≤ 1040597057373^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352685349 10000000000 1040597057373 3125000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540388677/10000000000 : ℝ)^1051 ≤ (3521053913531/10000000000000 : ℝ)^795 := by
    have hnat : (4540388677 : ℕ)^1051*10000000000000^795 ≤ 3521053913531^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540388677 10000000000 3521053913531 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086316727/5000000000 : ℝ)^1051 ≤ (3149035501927/10000000000000 : ℝ)^795 := by
    have hnat : (2086316727 : ℕ)^1051*10000000000000^795 ≤ 3149035501927^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086316727 5000000000 3149035501927 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352685349/10000000000 : ℝ), (4540388677/10000000000 : ℝ), (2086316727/5000000000 : ℝ)] ![(1040597057373/3125000000000 : ℝ), (3521053913531/10000000000000 : ℝ), (3149035501927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352685349/10000000000 : ℝ)|^1051 ≤ (1040597057373/3125000000000 : ℝ)^795
        have hw : |(4352685349/10000000000 : ℝ)|=(4352685349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540388677/10000000000 : ℝ)|^1051 ≤ (3521053913531/10000000000000 : ℝ)^795
        have hw : |(4540388677/10000000000 : ℝ)|=(4540388677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086316727/5000000000 : ℝ)|^1051 ≤ (3149035501927/10000000000000 : ℝ)^795
        have hw : |(2086316727/5000000000 : ℝ)|=(2086316727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2347/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (271/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7363/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2347/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2347/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2347/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3259/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2347/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2347/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3259/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2347/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2347/25000 : ℝ) ^ (8407/2048 : ℝ) ≤ (6059441041504253/100000000000000000000 : ℝ) := by
    have hpowers : (2347/25000 : ℝ)^8407 ≤ (6059441041504253/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2347 : ℕ)^8407*100000000000000000000^2048 ≤ 6059441041504253^2048*25000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2347 25000 6059441041504253 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2347/25000 : ℝ)) (X := (6059441041504253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3259/20000 : ℝ) ^ (8407/2048 : ℝ) ≤ (2913859192771767/5000000000000000000 : ℝ) := by
    have hpowers : (3259/20000 : ℝ)^8407 ≤ (2913859192771767/5000000000000000000 : ℝ)^2048 := by
      have hnat : (3259 : ℕ)^8407*5000000000000000000^2048 ≤ 2913859192771767^2048*20000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3259 20000 2913859192771767 5000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3259/20000 : ℝ)) (X := (2913859192771767/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006059441041504253/50000000000000000000 : ℝ) ≤ (2500073802584247/2500000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50006059441041504253/50000000000000000000 : ℝ)^2048 ≤ (2500073802584247/2500000000000000 : ℝ)^8407 := by
      have hnat : (50006059441041504253 : ℕ)^2048*2500000000000000^8407 ≤ 2500073802584247^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006059441041504253 50000000000000000000 2500073802584247 2500000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500073802584247/2500000000000000 : ℝ)) (X := (50006059441041504253/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100064336624896939593/100000000000000000000 : ℝ) ≤ (10001566900913563/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (100064336624896939593/100000000000000000000 : ℝ)^2048 ≤ (10001566900913563/10000000000000000 : ℝ)^8407 := by
      have hnat : (100064336624896939593 : ℕ)^2048*10000000000000000^8407 ≤ 10001566900913563^8407*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100064336624896939593 100000000000000000000 10001566900913563 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001566900913563/10000000000000000 : ℝ)) (X := (100064336624896939593/100000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502913859192771767/2500000000000000000 : ℝ) ≤ (5001419295745069/5000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (2502913859192771767/2500000000000000000 : ℝ)^2048 ≤ (5001419295745069/5000000000000000 : ℝ)^8407 := by
      have hnat : (2502913859192771767 : ℕ)^2048*5000000000000000^8407 ≤ 5001419295745069^8407*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502913859192771767 2500000000000000000 5001419295745069 5000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001419295745069/5000000000000000 : ℝ)) (X := (2502913859192771767/2500000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6059441041504253/100000000000000000000 : ℝ) ≤ ((17262040438882950979/17267500000000000000 : ℝ)+2*(50867623063/27628000000000 : ℝ)*(2347/25000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (17262040438882950979/17267500000000000000 : ℝ)+2*(50867623063/27628000000000 : ℝ)*(2347/25000 : ℝ)=(2500073802584247/2500000000000000 : ℝ) by norm_num, show 1+2*(6059441041504253/100000000000000000000 : ℝ)=(50006059441041504253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2913859192771767/5000000000000000000 : ℝ)+(6059441041504253/100000000000000000000 : ℝ) ≤ ((17262040438882950979/17267500000000000000 : ℝ)+(50867623063/27628000000000 : ℝ)*((3259/20000 : ℝ)+(2347/25000 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (17262040438882950979/17267500000000000000 : ℝ)+(50867623063/27628000000000 : ℝ)*((3259/20000 : ℝ)+(2347/25000 : ℝ))=(10001566900913563/10000000000000000 : ℝ) by norm_num, show 1+(2913859192771767/5000000000000000000 : ℝ)+(6059441041504253/100000000000000000000 : ℝ)=(100064336624896939593/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2913859192771767/5000000000000000000 : ℝ) ≤ ((17262040438882950979/17267500000000000000 : ℝ)+2*(50867623063/27628000000000 : ℝ)*(3259/20000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (17262040438882950979/17267500000000000000 : ℝ)+2*(50867623063/27628000000000 : ℝ)*(3259/20000 : ℝ)=(5001419295745069/5000000000000000 : ℝ) by norm_num, show 1+2*(2913859192771767/5000000000000000000 : ℝ)=(2502913859192771767/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17262040438882950979/17267500000000000000 : ℝ)*(X 1 0+X 2 0)+(50867623063/27628000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (2347/25000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (17262040438882950979/17267500000000000000 : ℝ)) (alpha := (50867623063/27628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17262040438882950979/17267500000000000000 : ℝ)*(X 0 1+X 2 1)+(50867623063/27628000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (2347/25000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (17262040438882950979/17267500000000000000 : ℝ)) (alpha := (50867623063/27628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17262040438882950979/17267500000000000000 : ℝ)*(X 0 2+X 1 2)+(50867623063/27628000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (2347/25000 : ℝ)) (hi := (3259/20000 : ℝ)) (c := (17262040438882950979/17267500000000000000 : ℝ)) (alpha := (50867623063/27628000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1064689889/5000000000 : ℝ)*X 0 0+(5422079067/10000000000 : ℝ)*X 0 1+(5238480567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352092933/10000000000 : ℝ)*X 1 0+(-555772007/2500000000 : ℝ)*X 1 1+(5238480657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676046433/5000000000 : ℝ)*X 2 0+(5238480871/10000000000 : ℝ)*X 2 1+(-1111543917/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352655029/10000000000 : ℝ)*X 0 0+(2085628437/5000000000 : ℝ)*X 0 1+(1135439523/2500000000 : ℝ)*X 0 2+(4352655029/10000000000 : ℝ)*X 1 0+(2085628437/5000000000 : ℝ)*X 1 1+(1135439523/2500000000 : ℝ)*X 1 2+(4352655029/10000000000 : ℝ)*X 2 0+(2085628437/5000000000 : ℝ)*X 2 1+(1135439523/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-532348713/2500000000 : ℝ)*X 0 0+(654894919/1250000000 : ℝ)*X 0 1+(2710698293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305338017/10000000000 : ℝ)*X 1 0+(-2040172023/10000000000 : ℝ)*X 1 1+(677674597/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305338099/10000000000 : ℝ)*X 2 0+(5421396673/10000000000 : ℝ)*X 2 1+(-510043013/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4352685349/10000000000 : ℝ)*X 0 0+(4540388677/10000000000 : ℝ)*X 0 1+(2086316727/5000000000 : ℝ)*X 0 2+(4352685349/10000000000 : ℝ)*X 1 0+(4540388677/10000000000 : ℝ)*X 1 1+(2086316727/5000000000 : ℝ)*X 1 2+(4352685349/10000000000 : ℝ)*X 2 0+(4540388677/10000000000 : ℝ)*X 2 1+(2086316727/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4999950087775793180155911999/431687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1022736697/50000000000000 : ℝ)*(base19) + (1746140919/100000000000000 : ℝ)*(base23) + (61856133/50000000000000 : ℝ)*(lower2) + (178770279/100000000000000 : ℝ)*(upper3) + (41672393/20000000000000 : ℝ)*(upper5) + (2036460864947127/50000000000000 : ℝ)*(major0) + (2036460864947127/50000000000000 : ℝ)*(major1) + (2036460864947127/50000000000000 : ℝ)*(major2) + (2723355188495461/50000000000000 : ℝ)*(sp0) + (1089350896841619/20000000000000 : ℝ)*(sp1) + (544675478354057/10000000000000 : ℝ)*(sp2) + (1349533148593687/50000000000000 : ℝ)*(sp3) + (5769086321/12500000000000 : ℝ)*(sp4) + (2530855217/12500000000000 : ℝ)*(sp7) + (269908654402911/10000000000000 : ℝ)*(f.failure) + (544675652968149/10000000000000 : ℝ)*(f.sum) + (7889793237651/1726750000000000000000000000 : ℝ)*base65 + (14243959952332237667/863375000000000000000000000000000 : ℝ)*base68 + (5344658522908737667/863375000000000000000000000000000 : ℝ)*base70 + (3254606405204137333/863375000000000000000000000000000 : ℝ)*base71 + (19421756092803/3453500000000000000000000000 : ℝ)*base74 + (4238074923565112667/863375000000000000000000000000000 : ℝ)*base76 + (8808109834779762333/863375000000000000000000000000000 : ℝ)*base77 + (10507976395747237667/863375000000000000000000000000000 : ℝ)*base80 + (22238415787497/3453500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (382911/200000000000000000000 : ℝ)*base89 + (382911/200000000000000000000 : ℝ)*base91 + (382911/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (842182606371648361342071159/215843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (403434299/100000000000000 : ℝ)*(base19) + (301790239/50000000000000 : ℝ)*(base23) + (136276909/100000000000000 : ℝ)*(upper3) + (21251697/50000000000000 : ℝ)*(lower4) + (2857821/10000000000000 : ℝ)*(upper5) + (2051637684217557/50000000000000 : ℝ)*(major0) + (2051637684217557/50000000000000 : ℝ)*(major1) + (2051637684217557/50000000000000 : ℝ)*(major2) + (1043506173/12500000000000 : ℝ)*(sp1) + (12344388001/100000000000000 : ℝ)*(sp2) + (5487348994831533/100000000000000 : ℝ)*(sp4) + (109746804866957/2000000000000 : ℝ)*(sp5) + (2743668023431527/50000000000000 : ℝ)*(sp6) + (2719201611978153/100000000000000 : ℝ)*(sp7) + (2719201611978153/100000000000000 : ℝ)*(f.failure) + (5487348994831533/100000000000000 : ℝ)*(f.sum) + (28169556446043/6907000000000000000000000000 : ℝ)*base65 + (4968610026100861697/863375000000000000000000000000000 : ℝ)*base68 + (5011741308215986697/863375000000000000000000000000000 : ℝ)*base70 + (7244453636367388303/863375000000000000000000000000000 : ℝ)*base71 + (18856656342143/6907000000000000000000000000 : ℝ)*base74 + (10666804864322236697/863375000000000000000000000000000 : ℝ)*base76 + (3727469967436361697/863375000000000000000000000000000 : ℝ)*base78 + (393759954910736697/863375000000000000000000000000000 : ℝ)*base80 + (1718486022617/690700000000000000000000000 : ℝ)*base81 + (10481847/2000000000000000000000 : ℝ)*base90 + (10481847/2000000000000000000000 : ℝ)*base92 + (10481847/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1215_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2347/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1215_s4_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-532962203/2500000000 : ℝ)*x 0 + (1349652027/2500000000 : ℝ)*x 1 + (5260334047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (532962203/2500000000 : ℝ)^1051 ≤ (2592015030471/20000000000000 : ℝ)^795 := by
    have hnat : (532962203 : ℕ)^1051*20000000000000^795 ≤ 2592015030471^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532962203 2500000000 2592015030471 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1349652027/2500000000 : ℝ)^1051 ≤ (22133147581837/50000000000000 : ℝ)^795 := by
    have hnat : (1349652027 : ℕ)^1051*50000000000000^795 ≤ 22133147581837^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349652027 2500000000 22133147581837 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5260334047/10000000000 : ℝ)^1051 ≤ (42773629677077/100000000000000 : ℝ)^795 := by
    have hnat : (5260334047 : ℕ)^1051*100000000000000^795 ≤ 42773629677077^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260334047 10000000000 42773629677077 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-532962203/2500000000 : ℝ), (1349652027/2500000000 : ℝ), (5260334047/10000000000 : ℝ)] ![(2592015030471/20000000000000 : ℝ), (22133147581837/50000000000000 : ℝ), (42773629677077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-532962203/2500000000 : ℝ)|^1051 ≤ (2592015030471/20000000000000 : ℝ)^795
        have hw : |(-532962203/2500000000 : ℝ)|=(532962203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1349652027/2500000000 : ℝ)|^1051 ≤ (22133147581837/50000000000000 : ℝ)^795
        have hw : |(1349652027/2500000000 : ℝ)|=(1349652027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5260334047/10000000000 : ℝ)|^1051 ≤ (42773629677077/100000000000000 : ℝ)^795
        have hw : |(5260334047/10000000000 : ℝ)|=(5260334047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s4_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334136851/625000000 : ℝ)*x 0 + (-1101034597/5000000000 : ℝ)*x 1 + (1052066817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334136851/625000000 : ℝ)^1051 ≤ (2731185750009/6250000000000 : ℝ)^795 := by
    have hnat : (334136851 : ℕ)^1051*6250000000000^795 ≤ 2731185750009^795*625000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334136851 625000000 2731185750009 6250000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1101034597/5000000000 : ℝ)^1051 ≤ (1690924737237/12500000000000 : ℝ)^795 := by
    have hnat : (1101034597 : ℕ)^1051*12500000000000^795 ≤ 1690924737237^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101034597 5000000000 1690924737237 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052066817/2000000000 : ℝ)^1051 ≤ (668337970087/1562500000000 : ℝ)^795 := by
    have hnat : (1052066817 : ℕ)^1051*1562500000000^795 ≤ 668337970087^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052066817 2000000000 668337970087 1562500000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334136851/625000000 : ℝ), (-1101034597/5000000000 : ℝ), (1052066817/2000000000 : ℝ)] ![(2731185750009/6250000000000 : ℝ), (1690924737237/12500000000000 : ℝ), (668337970087/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334136851/625000000 : ℝ)|^1051 ≤ (2731185750009/6250000000000 : ℝ)^795
        have hw : |(334136851/625000000 : ℝ)|=(334136851/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1101034597/5000000000 : ℝ)|^1051 ≤ (1690924737237/12500000000000 : ℝ)^795
        have hw : |(-1101034597/5000000000 : ℝ)|=(1101034597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052066817/2000000000 : ℝ)|^1051 ≤ (668337970087/1562500000000 : ℝ)^795
        have hw : |(1052066817/2000000000 : ℝ)|=(1052066817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s4_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336547417/2500000000 : ℝ)*x 0 + (2630167027/5000000000 : ℝ)*x 1 + (-440413833/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336547417/2500000000 : ℝ)^1051 ≤ (10924743140513/25000000000000 : ℝ)^795 := by
    have hnat : (1336547417 : ℕ)^1051*25000000000000^795 ≤ 10924743140513^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336547417 2500000000 10924743140513 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630167027/5000000000 : ℝ)^1051 ≤ (1710945190093/4000000000000 : ℝ)^795 := by
    have hnat : (2630167027 : ℕ)^1051*4000000000000^795 ≤ 1710945190093^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630167027 5000000000 1710945190093 4000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440413833/2000000000 : ℝ)^1051 ≤ (6763698831191/50000000000000 : ℝ)^795 := by
    have hnat : (440413833 : ℕ)^1051*50000000000000^795 ≤ 6763698831191^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440413833 2000000000 6763698831191 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336547417/2500000000 : ℝ), (2630167027/5000000000 : ℝ), (-440413833/2000000000 : ℝ)] ![(10924743140513/25000000000000 : ℝ), (1710945190093/4000000000000 : ℝ), (6763698831191/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336547417/2500000000 : ℝ)|^1051 ≤ (10924743140513/25000000000000 : ℝ)^795
        have hw : |(1336547417/2500000000 : ℝ)|=(1336547417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630167027/5000000000 : ℝ)|^1051 ≤ (1710945190093/4000000000000 : ℝ)^795
        have hw : |(2630167027/5000000000 : ℝ)|=(2630167027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-440413833/2000000000 : ℝ)|^1051 ≤ (6763698831191/50000000000000 : ℝ)^795
        have hw : |(-440413833/2000000000 : ℝ)|=(440413833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s4_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1088532991/2500000000 : ℝ)*x 0 + (1054199923/2500000000 : ℝ)*x 1 + (1123959187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088532991/2500000000 : ℝ)^1051 ≤ (33313737276467/100000000000000 : ℝ)^795 := by
    have hnat : (1088532991 : ℕ)^1051*100000000000000^795 ≤ 33313737276467^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088532991 2500000000 33313737276467 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054199923/2500000000 : ℝ)^1051 ≤ (1596587686291/5000000000000 : ℝ)^795 := by
    have hnat : (1054199923 : ℕ)^1051*5000000000000^795 ≤ 1596587686291^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054199923 2500000000 1596587686291 5000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123959187/2500000000 : ℝ)^1051 ≤ (3475450899277/10000000000000 : ℝ)^795 := by
    have hnat : (1123959187 : ℕ)^1051*10000000000000^795 ≤ 3475450899277^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123959187 2500000000 3475450899277 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088532991/2500000000 : ℝ), (1054199923/2500000000 : ℝ), (1123959187/2500000000 : ℝ)] ![(33313737276467/100000000000000 : ℝ), (1596587686291/5000000000000 : ℝ), (3475450899277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088532991/2500000000 : ℝ)|^1051 ≤ (33313737276467/100000000000000 : ℝ)^795
        have hw : |(1088532991/2500000000 : ℝ)|=(1088532991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054199923/2500000000 : ℝ)|^1051 ≤ (1596587686291/5000000000000 : ℝ)^795
        have hw : |(1054199923/2500000000 : ℝ)|=(1054199923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123959187/2500000000 : ℝ)|^1051 ≤ (3475450899277/10000000000000 : ℝ)^795
        have hw : |(1123959187/2500000000 : ℝ)|=(1123959187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s4_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131854779/10000000000 : ℝ)*x 0 + (210428787/400000000 : ℝ)*x 1 + (1079644251/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131854779/10000000000 : ℝ)^1051 ≤ (6480061554177/50000000000000 : ℝ)^795 := by
    have hnat : (2131854779 : ℕ)^1051*50000000000000^795 ≤ 6480061554177^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131854779 10000000000 6480061554177 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210428787/400000000 : ℝ)^1051 ≤ (21388887565319/50000000000000 : ℝ)^795 := by
    have hnat : (210428787 : ℕ)^1051*50000000000000^795 ≤ 21388887565319^795*400000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210428787 400000000 21388887565319 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079644251/2000000000 : ℝ)^1051 ≤ (11065525436989/25000000000000 : ℝ)^795 := by
    have hnat : (1079644251 : ℕ)^1051*25000000000000^795 ≤ 11065525436989^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079644251 2000000000 11065525436989 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131854779/10000000000 : ℝ), (210428787/400000000 : ℝ), (1079644251/2000000000 : ℝ)] ![(6480061554177/50000000000000 : ℝ), (21388887565319/50000000000000 : ℝ), (11065525436989/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131854779/10000000000 : ℝ)|^1051 ≤ (6480061554177/50000000000000 : ℝ)^795
        have hw : |(-2131854779/10000000000 : ℝ)|=(2131854779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210428787/400000000 : ℝ)|^1051 ≤ (21388887565319/50000000000000 : ℝ)^795
        have hw : |(210428787/400000000 : ℝ)|=(210428787/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079644251/2000000000 : ℝ)|^1051 ≤ (11065525436989/25000000000000 : ℝ)^795
        have hw : |(1079644251/2000000000 : ℝ)|=(1079644251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s4_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1327743867/2500000000 : ℝ)*x 0 + (-8256729/40000000 : ℝ)*x 1 + (5398220929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327743867/2500000000 : ℝ)^1051 ≤ (21659427134757/50000000000000 : ℝ)^795 := by
    have hnat : (1327743867 : ℕ)^1051*50000000000000^795 ≤ 21659427134757^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327743867 2500000000 21659427134757 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8256729/40000000 : ℝ)^1051 ≤ (12419047504419/100000000000000 : ℝ)^795 := by
    have hnat : (8256729 : ℕ)^1051*100000000000000^795 ≤ 12419047504419^795*40000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8256729 40000000 12419047504419 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398220929/10000000000 : ℝ)^1051 ≤ (5532762276777/12500000000000 : ℝ)^795 := by
    have hnat : (5398220929 : ℕ)^1051*12500000000000^795 ≤ 5532762276777^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398220929 10000000000 5532762276777 12500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327743867/2500000000 : ℝ), (-8256729/40000000 : ℝ), (5398220929/10000000000 : ℝ)] ![(21659427134757/50000000000000 : ℝ), (12419047504419/100000000000000 : ℝ), (5532762276777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327743867/2500000000 : ℝ)|^1051 ≤ (21659427134757/50000000000000 : ℝ)^795
        have hw : |(1327743867/2500000000 : ℝ)|=(1327743867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8256729/40000000 : ℝ)|^1051 ≤ (12419047504419/100000000000000 : ℝ)^795
        have hw : |(-8256729/40000000 : ℝ)|=(8256729/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398220929/10000000000 : ℝ)|^1051 ≤ (5532762276777/12500000000000 : ℝ)^795
        have hw : |(5398220929/10000000000 : ℝ)|=(5398220929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s4_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5310975561/10000000000 : ℝ)*x 0 + (5398220869/10000000000 : ℝ)*x 1 + (-412836441/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310975561/10000000000 : ℝ)^1051 ≤ (4331885527233/10000000000000 : ℝ)^795 := by
    have hnat : (5310975561 : ℕ)^1051*10000000000000^795 ≤ 4331885527233^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310975561 10000000000 4331885527233 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398220869/10000000000 : ℝ)^1051 ≤ (8852419512767/20000000000000 : ℝ)^795 := by
    have hnat : (5398220869 : ℕ)^1051*20000000000000^795 ≤ 8852419512767^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398220869 10000000000 8852419512767 20000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412836441/2000000000 : ℝ)^1051 ≤ (12419047146497/100000000000000 : ℝ)^795 := by
    have hnat : (412836441 : ℕ)^1051*100000000000000^795 ≤ 12419047146497^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412836441 2000000000 12419047146497 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310975561/10000000000 : ℝ), (5398220869/10000000000 : ℝ), (-412836441/2000000000 : ℝ)] ![(4331885527233/10000000000000 : ℝ), (8852419512767/20000000000000 : ℝ), (12419047146497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310975561/10000000000 : ℝ)|^1051 ≤ (4331885527233/10000000000000 : ℝ)^795
        have hw : |(5310975561/10000000000 : ℝ)|=(5310975561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398220869/10000000000 : ℝ)|^1051 ≤ (8852419512767/20000000000000 : ℝ)^795
        have hw : |(5398220869/10000000000 : ℝ)|=(5398220869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-412836441/2000000000 : ℝ)|^1051 ≤ (12419047146497/100000000000000 : ℝ)^795
        have hw : |(-412836441/2000000000 : ℝ)|=(412836441/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s4_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (272134049/625000000 : ℝ)*x 0 + (2247529269/5000000000 : ℝ)*x 1 + (2108790563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272134049/625000000 : ℝ)^1051 ≤ (33313866948281/100000000000000 : ℝ)^795 := by
    have hnat : (272134049 : ℕ)^1051*100000000000000^795 ≤ 33313866948281^795*625000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272134049 625000000 33313866948281 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247529269/5000000000 : ℝ)^1051 ≤ (8686639044283/25000000000000 : ℝ)^795 := by
    have hnat : (2247529269 : ℕ)^1051*25000000000000^795 ≤ 8686639044283^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247529269 5000000000 8686639044283 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108790563/5000000000 : ℝ)^1051 ≤ (31939576857629/100000000000000 : ℝ)^795 := by
    have hnat : (2108790563 : ℕ)^1051*100000000000000^795 ≤ 31939576857629^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108790563 5000000000 31939576857629 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272134049/625000000 : ℝ), (2247529269/5000000000 : ℝ), (2108790563/5000000000 : ℝ)] ![(33313866948281/100000000000000 : ℝ), (8686639044283/25000000000000 : ℝ), (31939576857629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272134049/625000000 : ℝ)|^1051 ≤ (33313866948281/100000000000000 : ℝ)^795
        have hw : |(272134049/625000000 : ℝ)|=(272134049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247529269/5000000000 : ℝ)|^1051 ≤ (8686639044283/25000000000000 : ℝ)^795
        have hw : |(2247529269/5000000000 : ℝ)|=(2247529269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2108790563/5000000000 : ℝ)|^1051 ≤ (31939576857629/100000000000000 : ℝ)^795
        have hw : |(2108790563/5000000000 : ℝ)|=(2108790563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11307/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (271/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (271/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (271/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7363/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (271/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (271/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7363/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (271/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (271/2500 : ℝ) ^ (8407/2048 : ℝ) ≤ (2186976146527689/20000000000000000000 : ℝ) := by
    have hpowers : (271/2500 : ℝ)^8407 ≤ (2186976146527689/20000000000000000000 : ℝ)^2048 := by
      have hnat : (271 : ℕ)^8407*20000000000000000000^2048 ≤ 2186976146527689^2048*2500^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        271 2500 2186976146527689 20000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (271/2500 : ℝ)) (X := (2186976146527689/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7363/50000 : ℝ) ^ (8407/2048 : ℝ) ≤ (38459562227627939/100000000000000000000 : ℝ) := by
    have hpowers : (7363/50000 : ℝ)^8407 ≤ (38459562227627939/100000000000000000000 : ℝ)^2048 := by
      have hnat : (7363 : ℕ)^8407*100000000000000000000^2048 ≤ 38459562227627939^2048*50000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7363 50000 38459562227627939 100000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7363/50000 : ℝ)) (X := (38459562227627939/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002186976146527689/10000000000000000000 : ℝ) ≤ (1000053271758537/1000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (10002186976146527689/10000000000000000000 : ℝ)^2048 ≤ (1000053271758537/1000000000000000 : ℝ)^8407 := by
      have hnat : (10002186976146527689 : ℕ)^2048*1000000000000000^8407 ≤ 1000053271758537^8407*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002186976146527689 10000000000000000000 1000053271758537 1000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000053271758537/1000000000000000 : ℝ)) (X := (10002186976146527689/10000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253087152685016649/6250000000000000000 : ℝ) ≤ (2500300764027491/2500000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (6253087152685016649/6250000000000000000 : ℝ)^2048 ≤ (2500300764027491/2500000000000000 : ℝ)^8407 := by
      have hnat : (6253087152685016649 : ℕ)^2048*2500000000000000^8407 ≤ 2500300764027491^8407*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253087152685016649 6250000000000000000 2500300764027491 2500000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500300764027491/2500000000000000 : ℝ)) (X := (6253087152685016649/6250000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038459562227627939/50000000000000000000 : ℝ) ≤ (5000936697317279/5000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (50038459562227627939/50000000000000000000 : ℝ)^2048 ≤ (5000936697317279/5000000000000000 : ℝ)^8407 := by
      have hnat : (50038459562227627939 : ℕ)^2048*5000000000000000^8407 ≤ 5000936697317279^8407*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038459562227627939 50000000000000000000 5000936697317279 5000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000936697317279/5000000000000000 : ℝ)) (X := (50038459562227627939/50000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2186976146527689/20000000000000000000 : ℝ) ≤ ((388475372013235499/388600000000000000 : ℝ)+2*(335169262297/194300000000000 : ℝ)*(271/2500 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (388475372013235499/388600000000000000 : ℝ)+2*(335169262297/194300000000000 : ℝ)*(271/2500 : ℝ)=(1000053271758537/1000000000000000 : ℝ) by norm_num, show 1+2*(2186976146527689/20000000000000000000 : ℝ)=(10002186976146527689/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38459562227627939/100000000000000000000 : ℝ)+(2186976146527689/20000000000000000000 : ℝ) ≤ ((388475372013235499/388600000000000000 : ℝ)+(335169262297/194300000000000 : ℝ)*((7363/50000 : ℝ)+(271/2500 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (388475372013235499/388600000000000000 : ℝ)+(335169262297/194300000000000 : ℝ)*((7363/50000 : ℝ)+(271/2500 : ℝ))=(2500300764027491/2500000000000000 : ℝ) by norm_num, show 1+(38459562227627939/100000000000000000000 : ℝ)+(2186976146527689/20000000000000000000 : ℝ)=(6253087152685016649/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38459562227627939/100000000000000000000 : ℝ) ≤ ((388475372013235499/388600000000000000 : ℝ)+2*(335169262297/194300000000000 : ℝ)*(7363/50000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (388475372013235499/388600000000000000 : ℝ)+2*(335169262297/194300000000000 : ℝ)*(7363/50000 : ℝ)=(5000936697317279/5000000000000000 : ℝ) by norm_num, show 1+2*(38459562227627939/100000000000000000000 : ℝ)=(50038459562227627939/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (388475372013235499/388600000000000000 : ℝ)*(X 1 0+X 2 0)+(335169262297/194300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (388475372013235499/388600000000000000 : ℝ)) (alpha := (335169262297/194300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (388475372013235499/388600000000000000 : ℝ)*(X 0 1+X 2 1)+(335169262297/194300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (388475372013235499/388600000000000000 : ℝ)) (alpha := (335169262297/194300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (388475372013235499/388600000000000000 : ℝ)*(X 0 2+X 1 2)+(335169262297/194300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (271/2500 : ℝ)) (hi := (7363/50000 : ℝ)) (c := (388475372013235499/388600000000000000 : ℝ)) (alpha := (335169262297/194300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-532962203/2500000000 : ℝ)*X 0 0+(1349652027/2500000000 : ℝ)*X 0 1+(5260334047/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334136851/625000000 : ℝ)*X 1 0+(-1101034597/5000000000 : ℝ)*X 1 1+(1052066817/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336547417/2500000000 : ℝ)*X 2 0+(2630167027/5000000000 : ℝ)*X 2 1+(-440413833/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088532991/2500000000 : ℝ)*X 0 0+(1054199923/2500000000 : ℝ)*X 0 1+(1123959187/2500000000 : ℝ)*X 0 2+(1088532991/2500000000 : ℝ)*X 1 0+(1054199923/2500000000 : ℝ)*X 1 1+(1123959187/2500000000 : ℝ)*X 1 2+(1088532991/2500000000 : ℝ)*X 2 0+(1054199923/2500000000 : ℝ)*X 2 1+(1123959187/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2131854779/10000000000 : ℝ)*X 0 0+(210428787/400000000 : ℝ)*X 0 1+(1079644251/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327743867/2500000000 : ℝ)*X 1 0+(-8256729/40000000 : ℝ)*X 1 1+(5398220929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310975561/10000000000 : ℝ)*X 2 0+(5398220869/10000000000 : ℝ)*X 2 1+(-412836441/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272134049/625000000 : ℝ)*X 0 0+(2247529269/5000000000 : ℝ)*X 0 1+(2108790563/5000000000 : ℝ)*X 0 2+(272134049/625000000 : ℝ)*X 1 0+(2247529269/5000000000 : ℝ)*X 1 1+(2108790563/5000000000 : ℝ)*X 1 2+(272134049/625000000 : ℝ)*X 2 0+(2247529269/5000000000 : ℝ)*X 2 1+(2108790563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4009599141313863635168571/1214375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35973087/5000000000000 : ℝ)*(base19) + (348576711/50000000000000 : ℝ)*(base23) + (49533139/100000000000000 : ℝ)*(lower2) + (32675683/50000000000000 : ℝ)*(upper3) + (5179171/10000000000000 : ℝ)*(upper5) + (337994727293991/6250000000000 : ℝ)*(major0) + (337994727293991/6250000000000 : ℝ)*(major1) + (337994727293991/6250000000000 : ℝ)*(major2) + (3616017426811509/50000000000000 : ℝ)*(sp0) + (7232056118164193/100000000000000 : ℝ)*(sp1) + (7232056140472511/100000000000000 : ℝ)*(sp2) + (1791881652294951/50000000000000 : ℝ)*(sp3) + (4396800583/20000000000000 : ℝ)*(sp4) + (2755283131/25000000000000 : ℝ)*(sp7) + (447971790715303/12500000000000 : ℝ)*(f.failure) + (7232056837625933/100000000000000 : ℝ)*(f.sum) + (94627370234013/9715000000000000000000000000 : ℝ)*base66 + (15237573032621759/2428750000000000000000000000000 : ℝ)*base67 + (28601453621224259/2428750000000000000000000000000 : ℝ)*base69 + (39212445384270509/2428750000000000000000000000000 : ℝ)*base71 + (25411619385689/4857500000000000000000000000 : ℝ)*base74 + (20243721130396759/2428750000000000000000000000000 : ℝ)*base75 + (27205600767954491/2428750000000000000000000000000 : ℝ)*base78 + (42157578095653009/2428750000000000000000000000000 : ℝ)*base79 + (9134306072343/9715000000000000000000000000 : ℝ)*base82 + (4744697/250000000000000000000 : ℝ)*base90 + (4744697/250000000000000000000 : ℝ)*base92 + (4744697/250000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10194930021954727997132919/1943000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31870197/20000000000000 : ℝ)*(base19) + (103040677/10000000000000 : ℝ)*(base23) + (4696167/3125000000000 : ℝ)*(lower3) + (172050811/50000000000000 : ℝ)*(lower4) + (1087654647074473/20000000000000 : ℝ)*(major0) + (1087654647074473/20000000000000 : ℝ)*(major1) + (1087654647074473/20000000000000 : ℝ)*(major2) + (5551770387/100000000000000 : ℝ)*(sp0) + (457407163/10000000000000 : ℝ)*(sp1) + (19022347073/100000000000000 : ℝ)*(sp2) + (454540545378983/6250000000000 : ℝ)*(sp4) + (14545299088823/200000000000 : ℝ)*(sp5) + (7272634225080273/100000000000000 : ℝ)*(sp6) + (1801946009005223/50000000000000 : ℝ)*(sp7) + (1801946009005223/50000000000000 : ℝ)*(f.failure) + (1818163569458529/25000000000000 : ℝ)*(f.sum) + (1409875914963/1943000000000000000000000000 : ℝ)*base66 + (25760617462111027/7772000000000000000000000000000 : ℝ)*base67 + (72100290150979027/7772000000000000000000000000000 : ℝ)*base69 + (91944982938911027/7772000000000000000000000000000 : ℝ)*base71 + (257520348023/1943000000000000000000000000 : ℝ)*base74 + (150036451069367027/7772000000000000000000000000000 : ℝ)*base75 + (77912063077747027/7772000000000000000000000000000 : ℝ)*base77 + (3866207545764973/7772000000000000000000000000000 : ℝ)*base80 + (5535049455083/1943000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (10854777/1000000000000000000000 : ℝ)*base90 + (10854777/1000000000000000000000 : ℝ)*base92 + (10854777/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1215_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7363/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (271/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1215_s5_0 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1066170037/5000000000 : ℝ)*x 0 + (2696530779/5000000000 : ℝ)*x 1 + (210622323/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066170037/5000000000 : ℝ)^1051 ≤ (25928047011/200000000000 : ℝ)^795 := by
    have hnat : (1066170037 : ℕ)^1051*200000000000^795 ≤ 25928047011^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066170037 5000000000 25928047011 200000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696530779/5000000000 : ℝ)^1051 ≤ (44206180831099/100000000000000 : ℝ)^795 := by
    have hnat : (2696530779 : ℕ)^1051*100000000000000^795 ≤ 44206180831099^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696530779 5000000000 44206180831099 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210622323/400000000 : ℝ)^1051 ≤ (21414897824911/50000000000000 : ℝ)^795 := by
    have hnat : (210622323 : ℕ)^1051*50000000000000^795 ≤ 21414897824911^795*400000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210622323 400000000 21414897824911 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1066170037/5000000000 : ℝ), (2696530779/5000000000 : ℝ), (210622323/400000000 : ℝ)] ![(25928047011/200000000000 : ℝ), (44206180831099/100000000000000 : ℝ), (21414897824911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1066170037/5000000000 : ℝ)|^1051 ≤ (25928047011/200000000000 : ℝ)^795
        have hw : |(-1066170037/5000000000 : ℝ)|=(1066170037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696530779/5000000000 : ℝ)|^1051 ≤ (44206180831099/100000000000000 : ℝ)^795
        have hw : |(2696530779/5000000000 : ℝ)|=(2696530779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210622323/400000000 : ℝ)|^1051 ≤ (21414897824911/50000000000000 : ℝ)^795
        have hw : |(210622323/400000000 : ℝ)|=(210622323/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s5_1 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336197591/2500000000 : ℝ)*x 0 + (-1098506569/5000000000 : ℝ)*x 1 + (5265558071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336197591/2500000000 : ℝ)^1051 ≤ (2184192620387/5000000000000 : ℝ)^795 := by
    have hnat : (1336197591 : ℕ)^1051*5000000000000^795 ≤ 2184192620387^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336197591 2500000000 2184192620387 5000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098506569/5000000000 : ℝ)^1051 ≤ (13486351967547/100000000000000 : ℝ)^795 := by
    have hnat : (1098506569 : ℕ)^1051*100000000000000^795 ≤ 13486351967547^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098506569 5000000000 13486351967547 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265558071/10000000000 : ℝ)^1051 ≤ (42829795606809/100000000000000 : ℝ)^795 := by
    have hnat : (5265558071 : ℕ)^1051*100000000000000^795 ≤ 42829795606809^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265558071 10000000000 42829795606809 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336197591/2500000000 : ℝ), (-1098506569/5000000000 : ℝ), (5265558071/10000000000 : ℝ)] ![(2184192620387/5000000000000 : ℝ), (13486351967547/100000000000000 : ℝ), (42829795606809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336197591/2500000000 : ℝ)|^1051 ≤ (2184192620387/5000000000000 : ℝ)^795
        have hw : |(1336197591/2500000000 : ℝ)|=(1336197591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1098506569/5000000000 : ℝ)|^1051 ≤ (13486351967547/100000000000000 : ℝ)^795
        have hw : |(-1098506569/5000000000 : ℝ)|=(1098506569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265558071/10000000000 : ℝ)|^1051 ≤ (42829795606809/100000000000000 : ℝ)^795
        have hw : |(5265558071/10000000000 : ℝ)|=(5265558071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s5_2 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (133619759/250000000 : ℝ)*x 0 + (2632779033/5000000000 : ℝ)*x 1 + (-2197013151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133619759/250000000 : ℝ)^1051 ≤ (1092096309113/2500000000000 : ℝ)^795 := by
    have hnat : (133619759 : ℕ)^1051*2500000000000^795 ≤ 1092096309113^795*250000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133619759 250000000 1092096309113 2500000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632779033/5000000000 : ℝ)^1051 ≤ (42829795553043/100000000000000 : ℝ)^795 := by
    have hnat : (2632779033 : ℕ)^1051*100000000000000^795 ≤ 42829795553043^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632779033 5000000000 42829795553043 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2197013151/10000000000 : ℝ)^1051 ≤ (3371588018261/25000000000000 : ℝ)^795 := by
    have hnat : (2197013151 : ℕ)^1051*25000000000000^795 ≤ 3371588018261^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197013151 10000000000 3371588018261 25000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133619759/250000000 : ℝ), (2632779033/5000000000 : ℝ), (-2197013151/10000000000 : ℝ)] ![(1092096309113/2500000000000 : ℝ), (42829795553043/100000000000000 : ℝ), (3371588018261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133619759/250000000 : ℝ)|^1051 ≤ (1092096309113/2500000000000 : ℝ)^795
        have hw : |(133619759/250000000 : ℝ)|=(133619759/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632779033/5000000000 : ℝ)|^1051 ≤ (42829795553043/100000000000000 : ℝ)^795
        have hw : |(2632779033/5000000000 : ℝ)|=(2632779033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2197013151/10000000000 : ℝ)|^1051 ≤ (3371588018261/25000000000000 : ℝ)^795
        have hw : |(-2197013151/10000000000 : ℝ)|=(2197013151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s5_3 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4354421821/10000000000 : ℝ)*x 0 + (4227630023/10000000000 : ℝ)*x 1 + (4484932057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354421821/10000000000 : ℝ)^1051 ≤ (520572955529/1562500000000 : ℝ)^795 := by
    have hnat : (4354421821 : ℕ)^1051*1562500000000^795 ≤ 520572955529^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354421821 10000000000 520572955529 1562500000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227630023/10000000000 : ℝ)^1051 ≤ (32040220460753/100000000000000 : ℝ)^795 := by
    have hnat : (4227630023 : ℕ)^1051*100000000000000^795 ≤ 32040220460753^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227630023 10000000000 32040220460753 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484932057/10000000000 : ℝ)^1051 ≤ (17321555181663/50000000000000 : ℝ)^795 := by
    have hnat : (4484932057 : ℕ)^1051*50000000000000^795 ≤ 17321555181663^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484932057 10000000000 17321555181663 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354421821/10000000000 : ℝ), (4227630023/10000000000 : ℝ), (4484932057/10000000000 : ℝ)] ![(520572955529/1562500000000 : ℝ), (32040220460753/100000000000000 : ℝ), (17321555181663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354421821/10000000000 : ℝ)|^1051 ≤ (520572955529/1562500000000 : ℝ)^795
        have hw : |(4354421821/10000000000 : ℝ)|=(4354421821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227630023/10000000000 : ℝ)|^1051 ≤ (32040220460753/100000000000000 : ℝ)^795
        have hw : |(4227630023/10000000000 : ℝ)|=(4227630023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484932057/10000000000 : ℝ)|^1051 ≤ (17321555181663/50000000000000 : ℝ)^795
        have hw : |(4484932057/10000000000 : ℝ)|=(4484932057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s5_4 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132345129/10000000000 : ℝ)*x 0 + (1316471529/2500000000 : ℝ)*x 1 + (2696366139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132345129/10000000000 : ℝ)^1051 ≤ (6482032067443/50000000000000 : ℝ)^795 := by
    have hnat : (2132345129 : ℕ)^1051*50000000000000^795 ≤ 6482032067443^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132345129 10000000000 6482032067443 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316471529/2500000000 : ℝ)^1051 ≤ (42833323171293/100000000000000 : ℝ)^795 := by
    have hnat : (1316471529 : ℕ)^1051*100000000000000^795 ≤ 42833323171293^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316471529 2500000000 42833323171293 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696366139/5000000000 : ℝ)^1051 ≤ (44202612671353/100000000000000 : ℝ)^795 := by
    have hnat : (2696366139 : ℕ)^1051*100000000000000^795 ≤ 44202612671353^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696366139 5000000000 44202612671353 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132345129/10000000000 : ℝ), (1316471529/2500000000 : ℝ), (2696366139/5000000000 : ℝ)] ![(6482032067443/50000000000000 : ℝ), (42833323171293/100000000000000 : ℝ), (44202612671353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132345129/10000000000 : ℝ)|^1051 ≤ (6482032067443/50000000000000 : ℝ)^795
        have hw : |(-2132345129/10000000000 : ℝ)|=(2132345129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316471529/2500000000 : ℝ)|^1051 ≤ (42833323171293/100000000000000 : ℝ)^795
        have hw : |(1316471529/2500000000 : ℝ)|=(1316471529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696366139/5000000000 : ℝ)|^1051 ≤ (44202612671353/100000000000000 : ℝ)^795
        have hw : |(2696366139/5000000000 : ℝ)|=(2696366139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s5_5 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062463547/2000000000 : ℝ)*x 0 + (-2069838787/10000000000 : ℝ)*x 1 + (1348183079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062463547/2000000000 : ℝ)^1051 ≤ (43333328478453/100000000000000 : ℝ)^795 := by
    have hnat : (1062463547 : ℕ)^1051*100000000000000^795 ≤ 43333328478453^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062463547 2000000000 43333328478453 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2069838787/10000000000 : ℝ)^1051 ≤ (1246405842787/10000000000000 : ℝ)^795 := by
    have hnat : (2069838787 : ℕ)^1051*10000000000000^795 ≤ 1246405842787^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069838787 10000000000 1246405842787 10000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348183079/2500000000 : ℝ)^1051 ≤ (22101306541563/50000000000000 : ℝ)^795 := by
    have hnat : (1348183079 : ℕ)^1051*50000000000000^795 ≤ 22101306541563^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348183079 2500000000 22101306541563 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062463547/2000000000 : ℝ), (-2069838787/10000000000 : ℝ), (1348183079/2500000000 : ℝ)] ![(43333328478453/100000000000000 : ℝ), (1246405842787/10000000000000 : ℝ), (22101306541563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062463547/2000000000 : ℝ)|^1051 ≤ (43333328478453/100000000000000 : ℝ)^795
        have hw : |(1062463547/2000000000 : ℝ)|=(1062463547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2069838787/10000000000 : ℝ)|^1051 ≤ (1246405842787/10000000000000 : ℝ)^795
        have hw : |(-2069838787/10000000000 : ℝ)|=(2069838787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348183079/2500000000 : ℝ)|^1051 ≤ (22101306541563/50000000000000 : ℝ)^795
        have hw : |(1348183079/2500000000 : ℝ)|=(1348183079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s5_6 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328079409/2500000000 : ℝ)*x 0 + (2696366213/5000000000 : ℝ)*x 1 + (-517459693/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328079409/2500000000 : ℝ)^1051 ≤ (43333327410853/100000000000000 : ℝ)^795 := by
    have hnat : (1328079409 : ℕ)^1051*100000000000000^795 ≤ 43333327410853^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328079409 2500000000 43333327410853 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696366213/5000000000 : ℝ)^1051 ≤ (22101307137551/50000000000000 : ℝ)^795 := by
    have hnat : (2696366213 : ℕ)^1051*50000000000000^795 ≤ 22101307137551^795*5000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696366213 5000000000 22101307137551 50000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517459693/2500000000 : ℝ)^1051 ≤ (12464058308457/100000000000000 : ℝ)^795 := by
    have hnat : (517459693 : ℕ)^1051*100000000000000^795 ≤ 12464058308457^795*2500000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517459693 2500000000 12464058308457 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328079409/2500000000 : ℝ), (2696366213/5000000000 : ℝ), (-517459693/2500000000 : ℝ)] ![(43333327410853/100000000000000 : ℝ), (22101307137551/50000000000000 : ℝ), (12464058308457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328079409/2500000000 : ℝ)|^1051 ≤ (43333327410853/100000000000000 : ℝ)^795
        have hw : |(1328079409/2500000000 : ℝ)|=(1328079409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696366213/5000000000 : ℝ)|^1051 ≤ (22101307137551/50000000000000 : ℝ)^795
        have hw : |(2696366213/5000000000 : ℝ)|=(2696366213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517459693/2500000000 : ℝ)|^1051 ≤ (12464058308457/100000000000000 : ℝ)^795
        have hw : |(-517459693/2500000000 : ℝ)|=(517459693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1215_s5_7 (p : ℝ) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4354432103/10000000000 : ℝ)*x 0 + (4484270087/10000000000 : ℝ)*x 1 + (845658859/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4354432103/10000000000 : ℝ)^1051 ≤ (1041149161141/3125000000000 : ℝ)^795 := by
    have hnat : (4354432103 : ℕ)^1051*3125000000000^795 ≤ 1041149161141^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354432103 10000000000 1041149161141 3125000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4484270087/10000000000 : ℝ)^1051 ≤ (34636350707511/100000000000000 : ℝ)^795 := by
    have hnat : (4484270087 : ℕ)^1051*100000000000000^795 ≤ 34636350707511^795*10000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484270087 10000000000 34636350707511 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (845658859/2000000000 : ℝ)^1051 ≤ (32046876119443/100000000000000 : ℝ)^795 := by
    have hnat : (845658859 : ℕ)^1051*100000000000000^795 ≤ 32046876119443^795*2000000000^1051 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845658859 2000000000 32046876119443 100000000000000 1051 795 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1051/256 : ℝ)) 1051 795 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4354432103/10000000000 : ℝ), (4484270087/10000000000 : ℝ), (845658859/2000000000 : ℝ)] ![(1041149161141/3125000000000 : ℝ), (34636350707511/100000000000000 : ℝ), (32046876119443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4354432103/10000000000 : ℝ)|^1051 ≤ (1041149161141/3125000000000 : ℝ)^795
        have hw : |(4354432103/10000000000 : ℝ)|=(4354432103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4484270087/10000000000 : ℝ)|^1051 ≤ (34636350707511/100000000000000 : ℝ)^795
        have hw : |(4484270087/10000000000 : ℝ)|=(4484270087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(845658859/2000000000 : ℝ)|^1051 ≤ (32046876119443/100000000000000 : ℝ)^795
        have hw : |(845658859/2000000000 : ℝ)|=(845658859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1215_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5709/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14119/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11307/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11307/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11307/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11307/100000 : ℝ) ^ (8407/2048 : ℝ) ≤ (1300198121259223/10000000000000000000 : ℝ) := by
    have hpowers : (11307/100000 : ℝ)^8407 ≤ (1300198121259223/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11307 : ℕ)^8407*10000000000000000000^2048 ≤ 1300198121259223^2048*100000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11307 100000 1300198121259223 10000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11307/100000 : ℝ)) (X := (1300198121259223/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8407/2048 : ℝ) ≤ (16730886797888103/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8407 ≤ (16730886797888103/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8407*50000000000000000000^2048 ≤ 16730886797888103^2048*20000^8407 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 16730886797888103 50000000000000000000 8407 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (16730886797888103/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001300198121259223/5000000000000000000 : ℝ) ≤ (2000126682236971/2000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (5001300198121259223/5000000000000000000 : ℝ)^2048 ≤ (2000126682236971/2000000000000000 : ℝ)^8407 := by
      have hnat : (5001300198121259223 : ℕ)^2048*2000000000000000^8407 ≤ 2000126682236971^8407*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001300198121259223 5000000000000000000 2000126682236971 2000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000126682236971/2000000000000000 : ℝ)) (X := (5001300198121259223/5000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011615938702092109/25000000000000000000 : ℝ) ≤ (5000565844253909/5000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (25011615938702092109/25000000000000000000 : ℝ)^2048 ≤ (5000565844253909/5000000000000000 : ℝ)^8407 := by
      have hnat : (25011615938702092109 : ℕ)^2048*5000000000000000^8407 ≤ 5000565844253909^8407*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011615938702092109 25000000000000000000 5000565844253909 5000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000565844253909/5000000000000000 : ℝ)) (X := (25011615938702092109/25000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016730886797888103/25000000000000000000 : ℝ) ≤ (10001629965830781/10000000000000000 : ℝ) ^ (8407/2048 : ℝ) := by
    have hpowers : (25016730886797888103/25000000000000000000 : ℝ)^2048 ≤ (10001629965830781/10000000000000000 : ℝ)^8407 := by
      have hnat : (25016730886797888103 : ℕ)^2048*10000000000000000^8407 ≤ 10001629965830781^8407*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016730886797888103 25000000000000000000 10001629965830781 10000000000000000 2048 8407 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001629965830781/10000000000000000 : ℝ)) (X := (25016730886797888103/25000000000000000000 : ℝ)) (by norm_num) 8407 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1300198121259223/10000000000000000000 : ℝ) ≤ ((4878431097427961693/4880000000000000000 : ℝ)+2*(498277322963/292800000000000 : ℝ)*(11307/100000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (4878431097427961693/4880000000000000000 : ℝ)+2*(498277322963/292800000000000 : ℝ)*(11307/100000 : ℝ)=(2000126682236971/2000000000000000 : ℝ) by norm_num, show 1+2*(1300198121259223/10000000000000000000 : ℝ)=(5001300198121259223/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16730886797888103/50000000000000000000 : ℝ)+(1300198121259223/10000000000000000000 : ℝ) ≤ ((4878431097427961693/4880000000000000000 : ℝ)+(498277322963/292800000000000 : ℝ)*((2847/20000 : ℝ)+(11307/100000 : ℝ)))^(8407/2048 : ℝ) := by
    rw [show (4878431097427961693/4880000000000000000 : ℝ)+(498277322963/292800000000000 : ℝ)*((2847/20000 : ℝ)+(11307/100000 : ℝ))=(5000565844253909/5000000000000000 : ℝ) by norm_num, show 1+(16730886797888103/50000000000000000000 : ℝ)+(1300198121259223/10000000000000000000 : ℝ)=(25011615938702092109/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16730886797888103/50000000000000000000 : ℝ) ≤ ((4878431097427961693/4880000000000000000 : ℝ)+2*(498277322963/292800000000000 : ℝ)*(2847/20000 : ℝ))^(8407/2048 : ℝ) := by
    rw [show (4878431097427961693/4880000000000000000 : ℝ)+2*(498277322963/292800000000000 : ℝ)*(2847/20000 : ℝ)=(10001629965830781/10000000000000000 : ℝ) by norm_num, show 1+2*(16730886797888103/50000000000000000000 : ℝ)=(25016730886797888103/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4878431097427961693/4880000000000000000 : ℝ)*(X 1 0+X 2 0)+(498277322963/292800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4878431097427961693/4880000000000000000 : ℝ)) (alpha := (498277322963/292800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4878431097427961693/4880000000000000000 : ℝ)*(X 0 1+X 2 1)+(498277322963/292800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4878431097427961693/4880000000000000000 : ℝ)) (alpha := (498277322963/292800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4878431097427961693/4880000000000000000 : ℝ)*(X 0 2+X 1 2)+(498277322963/292800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8407/2048 : ℝ)) (lo := (11307/100000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (4878431097427961693/4880000000000000000 : ℝ)) (alpha := (498277322963/292800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1066170037/5000000000 : ℝ)*X 0 0+(2696530779/5000000000 : ℝ)*X 0 1+(210622323/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336197591/2500000000 : ℝ)*X 1 0+(-1098506569/5000000000 : ℝ)*X 1 1+(5265558071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133619759/250000000 : ℝ)*X 2 0+(2632779033/5000000000 : ℝ)*X 2 1+(-2197013151/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4354421821/10000000000 : ℝ)*X 0 0+(4227630023/10000000000 : ℝ)*X 0 1+(4484932057/10000000000 : ℝ)*X 0 2+(4354421821/10000000000 : ℝ)*X 1 0+(4227630023/10000000000 : ℝ)*X 1 1+(4484932057/10000000000 : ℝ)*X 1 2+(4354421821/10000000000 : ℝ)*X 2 0+(4227630023/10000000000 : ℝ)*X 2 1+(4484932057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132345129/10000000000 : ℝ)*X 0 0+(1316471529/2500000000 : ℝ)*X 0 1+(2696366139/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062463547/2000000000 : ℝ)*X 1 0+(-2069838787/10000000000 : ℝ)*X 1 1+(1348183079/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328079409/2500000000 : ℝ)*X 2 0+(2696366213/5000000000 : ℝ)*X 2 1+(-517459693/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4354432103/10000000000 : ℝ)*X 0 0+(4484270087/10000000000 : ℝ)*X 0 1+(845658859/2000000000 : ℝ)*X 0 2+(4354432103/10000000000 : ℝ)*X 1 0+(4484270087/10000000000 : ℝ)*X 1 1+(845658859/2000000000 : ℝ)*X 1 2+(4354432103/10000000000 : ℝ)*X 2 0+(4484270087/10000000000 : ℝ)*X 2 1+(845658859/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1215_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1586095551580853361071593713/244000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1268078877/100000000000000 : ℝ)*(base19) + (582679109/50000000000000 : ℝ)*(base23) + (51764843/100000000000000 : ℝ)*(lower2) + (44181433/25000000000000 : ℝ)*(upper3) + (84071739/100000000000000 : ℝ)*(upper5) + (5864754819394953/100000000000000 : ℝ)*(major0) + (5864754819394953/100000000000000 : ℝ)*(major1) + (5864754819394953/100000000000000 : ℝ)*(major2) + (61273117533301/781250000000 : ℝ)*(sp0) + (1960747710298897/25000000000000 : ℝ)*(sp1) + (7842990943916247/100000000000000 : ℝ)*(sp2) + (971624745568311/25000000000000 : ℝ)*(sp3) + (33065011937/100000000000000 : ℝ)*(sp4) + (9165281233/50000000000000 : ℝ)*(sp7) + (388651731283571/10000000000000 : ℝ)*(f.failure) + (1568598421854893/20000000000000 : ℝ)*(f.sum) + (5305253682153/4880000000000000000000000000 : ℝ)*base65 + (2647011906942814571/488000000000000000000000000000000 : ℝ)*base68 + (6964253232014814571/488000000000000000000000000000000 : ℝ)*base70 + (3000664365665185429/488000000000000000000000000000000 : ℝ)*base71 + (27784619233113/4880000000000000000000000000 : ℝ)*base73 + (4827059132929185429/488000000000000000000000000000000 : ℝ)*base75 + (5620607100321185429/488000000000000000000000000000000 : ℝ)*base77 + (583531995889185429/488000000000000000000000000000000 : ℝ)*base79 + (23162156006633/4880000000000000000000000000 : ℝ)*base81 + (1936429/200000000000000000000 : ℝ)*base90 + (1936429/200000000000000000000 : ℝ)*base92 + (1936429/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (782435003351403818916349733/122000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (777314817/50000000000000 : ℝ)*(base19) + (804136799/50000000000000 : ℝ)*(base23) + (207167383/100000000000000 : ℝ)*(upper3) + (82820591/100000000000000 : ℝ)*(lower4) + (136250857/100000000000000 : ℝ)*(upper5) + (2947544477399809/50000000000000 : ℝ)*(major0) + (2947544477399809/50000000000000 : ℝ)*(major1) + (2947544477399809/50000000000000 : ℝ)*(major2) + (10596674371/25000000000000 : ℝ)*(sp1) + (12423099093/25000000000000 : ℝ)*(sp2) + (315342329583101/4000000000000 : ℝ)*(sp4) + (7883514298250407/100000000000000 : ℝ)*(sp5) + (1970876734726889/25000000000000 : ℝ)*(sp6) + (3906619456241647/100000000000000 : ℝ)*(sp7) + (3906619456241647/100000000000000 : ℝ)*(f.failure) + (315342329583101/4000000000000 : ℝ)*(f.sum) + (19822453631053/7320000000000000000000000000 : ℝ)*base66 + (3698694468152100089/732000000000000000000000000000000 : ℝ)*base68 + (1955216594384100089/732000000000000000000000000000000 : ℝ)*base70 + (2437714501988100089/732000000000000000000000000000000 : ℝ)*base72 + (19059451897907/7320000000000000000000000000 : ℝ)*base73 + (6237265821416100089/732000000000000000000000000000000 : ℝ)*base76 + (851996967368100089/732000000000000000000000000000000 : ℝ)*base78 + (27933900168008100089/732000000000000000000000000000000 : ℝ)*base80 + (64654104859547/7320000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2701647/2000000000000000000000 : ℝ)*base89 + (2701647/2000000000000000000000 : ℝ)*base91 + (2701647/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1215_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11307/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1215_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1215_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2347/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1215_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1215_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1215_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8407/2048 : ℝ) ≤ p) (hpb : p ≤ (1051/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30180001/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2347/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5709/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1215_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
