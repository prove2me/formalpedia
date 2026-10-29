-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1661_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:24.443062+00:00
-- url     : https://prove2.me/submissions/045d6da1-ca6a-441a-aac7-2a55aa6aa113

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
theorem support_rectangle_w1661_s3_0 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1583836803/10000000000 : ℝ)*x 0 + (5444348011/10000000000 : ℝ)*x 1 + (5184537123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583836803/10000000000 : ℝ)^4963 ≤ (9809877541943/100000000000000 : ℝ)^3939 := by
    have hnat : (1583836803 : ℕ)^4963*100000000000000^3939 ≤ 9809877541943^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583836803 10000000000 9809877541943 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444348011/10000000000 : ℝ)^4963 ≤ (181577162961/390625000000 : ℝ)^3939 := by
    have hnat : (5444348011 : ℕ)^4963*390625000000^3939 ≤ 181577162961^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444348011 10000000000 181577162961 390625000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184537123/10000000000 : ℝ)^4963 ≤ (5463296090619/12500000000000 : ℝ)^3939 := by
    have hnat : (5184537123 : ℕ)^4963*12500000000000^3939 ≤ 5463296090619^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184537123 10000000000 5463296090619 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1583836803/10000000000 : ℝ), (5444348011/10000000000 : ℝ), (5184537123/10000000000 : ℝ)] ![(9809877541943/100000000000000 : ℝ), (181577162961/390625000000 : ℝ), (5463296090619/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1583836803/10000000000 : ℝ)|^4963 ≤ (9809877541943/100000000000000 : ℝ)^3939
        have hw : |(-1583836803/10000000000 : ℝ)|=(1583836803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444348011/10000000000 : ℝ)|^4963 ≤ (181577162961/390625000000 : ℝ)^3939
        have hw : |(5444348011/10000000000 : ℝ)|=(5444348011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184537123/10000000000 : ℝ)|^4963 ≤ (5463296090619/12500000000000 : ℝ)^3939
        have hw : |(5184537123/10000000000 : ℝ)|=(5184537123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s3_1 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069217861/2000000000 : ℝ)*x 0 + (-858764257/5000000000 : ℝ)*x 1 + (207381483/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069217861/2000000000 : ℝ)^4963 ≤ (45429221001251/100000000000000 : ℝ)^3939 := by
    have hnat : (1069217861 : ℕ)^4963*100000000000000^3939 ≤ 45429221001251^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069217861 2000000000 45429221001251 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (858764257/5000000000 : ℝ)^4963 ≤ (10864410770847/100000000000000 : ℝ)^3939 := by
    have hnat : (858764257 : ℕ)^4963*100000000000000^3939 ≤ 10864410770847^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858764257 5000000000 10864410770847 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207381483/400000000 : ℝ)^4963 ≤ (5463296026889/12500000000000 : ℝ)^3939 := by
    have hnat : (207381483 : ℕ)^4963*12500000000000^3939 ≤ 5463296026889^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207381483 400000000 5463296026889 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069217861/2000000000 : ℝ), (-858764257/5000000000 : ℝ), (207381483/400000000 : ℝ)] ![(45429221001251/100000000000000 : ℝ), (10864410770847/100000000000000 : ℝ), (5463296026889/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069217861/2000000000 : ℝ)|^4963 ≤ (45429221001251/100000000000000 : ℝ)^3939
        have hw : |(1069217861/2000000000 : ℝ)|=(1069217861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-858764257/5000000000 : ℝ)|^4963 ≤ (10864410770847/100000000000000 : ℝ)^3939
        have hw : |(-858764257/5000000000 : ℝ)|=(858764257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207381483/400000000 : ℝ)|^4963 ≤ (5463296026889/12500000000000 : ℝ)^3939
        have hw : |(207381483/400000000 : ℝ)|=(207381483/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s3_2 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346089311/10000000000 : ℝ)*x 0 + (5184537091/10000000000 : ℝ)*x 1 + (-343505697/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346089311/10000000000 : ℝ)^4963 ≤ (45429221065491/100000000000000 : ℝ)^3939 := by
    have hnat : (5346089311 : ℕ)^4963*100000000000000^3939 ≤ 45429221065491^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346089311 10000000000 45429221065491 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184537091/10000000000 : ℝ)^4963 ≤ (43706368385059/100000000000000 : ℝ)^3939 := by
    have hnat : (5184537091 : ℕ)^4963*100000000000000^3939 ≤ 43706368385059^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184537091 10000000000 43706368385059 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343505697/2000000000 : ℝ)^4963 ≤ (2716102634929/25000000000000 : ℝ)^3939 := by
    have hnat : (343505697 : ℕ)^4963*25000000000000^3939 ≤ 2716102634929^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343505697 2000000000 2716102634929 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346089311/10000000000 : ℝ), (5184537091/10000000000 : ℝ), (-343505697/2000000000 : ℝ)] ![(45429221065491/100000000000000 : ℝ), (43706368385059/100000000000000 : ℝ), (2716102634929/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346089311/10000000000 : ℝ)|^4963 ≤ (45429221065491/100000000000000 : ℝ)^3939
        have hw : |(5346089311/10000000000 : ℝ)|=(5346089311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184537091/10000000000 : ℝ)|^4963 ≤ (43706368385059/100000000000000 : ℝ)^3939
        have hw : |(5184537091/10000000000 : ℝ)|=(5184537091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343505697/2000000000 : ℝ)|^4963 ≤ (2716102634929/25000000000000 : ℝ)^3939
        have hw : |(-343505697/2000000000 : ℝ)|=(343505697/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s3_3 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4172369641/10000000000 : ℝ)*x 0 + (3841541633/10000000000 : ℝ)*x 1 + (452306123/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172369641/10000000000 : ℝ)^4963 ≤ (33242661783991/100000000000000 : ℝ)^3939 := by
    have hnat : (4172369641 : ℕ)^4963*100000000000000^3939 ≤ 33242661783991^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172369641 10000000000 33242661783991 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3841541633/10000000000 : ℝ)^4963 ≤ (5991309415937/20000000000000 : ℝ)^3939 := by
    have hnat : (3841541633 : ℕ)^4963*20000000000000^3939 ≤ 5991309415937^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841541633 10000000000 5991309415937 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452306123/1000000000 : ℝ)^4963 ≤ (36800791122537/100000000000000 : ℝ)^3939 := by
    have hnat : (452306123 : ℕ)^4963*100000000000000^3939 ≤ 36800791122537^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452306123 1000000000 36800791122537 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172369641/10000000000 : ℝ), (3841541633/10000000000 : ℝ), (452306123/1000000000 : ℝ)] ![(33242661783991/100000000000000 : ℝ), (5991309415937/20000000000000 : ℝ), (36800791122537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172369641/10000000000 : ℝ)|^4963 ≤ (33242661783991/100000000000000 : ℝ)^3939
        have hw : |(4172369641/10000000000 : ℝ)|=(4172369641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3841541633/10000000000 : ℝ)|^4963 ≤ (5991309415937/20000000000000 : ℝ)^3939
        have hw : |(3841541633/10000000000 : ℝ)|=(3841541633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452306123/1000000000 : ℝ)|^4963 ≤ (36800791122537/100000000000000 : ℝ)^3939
        have hw : |(452306123/1000000000 : ℝ)|=(452306123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s3_4 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1583899841/10000000000 : ℝ)*x 0 + (5186513127/10000000000 : ℝ)*x 1 + (1360587761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583899841/10000000000 : ℝ)^4963 ≤ (9810369486459/100000000000000 : ℝ)^3939 := by
    have hnat : (1583899841 : ℕ)^4963*100000000000000^3939 ≤ 9810369486459^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583899841 10000000000 9810369486459 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186513127/10000000000 : ℝ)^4963 ≤ (8745471647601/20000000000000 : ℝ)^3939 := by
    have hnat : (5186513127 : ℕ)^4963*20000000000000^3939 ≤ 8745471647601^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186513127 10000000000 8745471647601 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360587761/2500000000 : ℝ)^4963 ≤ (46462272258383/100000000000000 : ℝ)^3939 := by
    have hnat : (1360587761 : ℕ)^4963*100000000000000^3939 ≤ 46462272258383^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360587761 2500000000 46462272258383 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1583899841/10000000000 : ℝ), (5186513127/10000000000 : ℝ), (1360587761/2500000000 : ℝ)] ![(9810369486459/100000000000000 : ℝ), (8745471647601/20000000000000 : ℝ), (46462272258383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1583899841/10000000000 : ℝ)|^4963 ≤ (9810369486459/100000000000000 : ℝ)^3939
        have hw : |(-1583899841/10000000000 : ℝ)|=(1583899841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186513127/10000000000 : ℝ)|^4963 ≤ (8745471647601/20000000000000 : ℝ)^3939
        have hw : |(5186513127/10000000000 : ℝ)|=(5186513127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360587761/2500000000 : ℝ)|^4963 ≤ (46462272258383/100000000000000 : ℝ)^3939
        have hw : |(1360587761/2500000000 : ℝ)|=(1360587761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s3_5 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276594837/10000000000 : ℝ)*x 0 + (-1459714541/10000000000 : ℝ)*x 1 + (2721175521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276594837/10000000000 : ℝ)^4963 ≤ (44686422855931/100000000000000 : ℝ)^3939 := by
    have hnat : (5276594837 : ℕ)^4963*100000000000000^3939 ≤ 44686422855931^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276594837 10000000000 44686422855931 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459714541/10000000000 : ℝ)^4963 ≤ (69150819483/781250000000 : ℝ)^3939 := by
    have hnat : (1459714541 : ℕ)^4963*781250000000^3939 ≤ 69150819483^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459714541 10000000000 69150819483 781250000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721175521/5000000000 : ℝ)^4963 ≤ (4646227223687/10000000000000 : ℝ)^3939 := by
    have hnat : (2721175521 : ℕ)^4963*10000000000000^3939 ≤ 4646227223687^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721175521 5000000000 4646227223687 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276594837/10000000000 : ℝ), (-1459714541/10000000000 : ℝ), (2721175521/5000000000 : ℝ)] ![(44686422855931/100000000000000 : ℝ), (69150819483/781250000000 : ℝ), (4646227223687/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276594837/10000000000 : ℝ)|^4963 ≤ (44686422855931/100000000000000 : ℝ)^3939
        have hw : |(5276594837/10000000000 : ℝ)|=(5276594837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1459714541/10000000000 : ℝ)|^4963 ≤ (69150819483/781250000000 : ℝ)^3939
        have hw : |(-1459714541/10000000000 : ℝ)|=(1459714541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721175521/5000000000 : ℝ)|^4963 ≤ (4646227223687/10000000000000 : ℝ)^3939
        have hw : |(2721175521/5000000000 : ℝ)|=(2721175521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s3_6 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276594703/10000000000 : ℝ)*x 0 + (4353881/8000000 : ℝ)*x 1 + (-364928609/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276594703/10000000000 : ℝ)^4963 ≤ (44686421426099/100000000000000 : ℝ)^3939 := by
    have hnat : (5276594703 : ℕ)^4963*100000000000000^3939 ≤ 44686421426099^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276594703 10000000000 44686421426099 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4353881/8000000 : ℝ)^4963 ≤ (11615568618557/25000000000000 : ℝ)^3939 := by
    have hnat : (4353881 : ℕ)^4963*25000000000000^3939 ≤ 11615568618557^3939*8000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353881 8000000 11615568618557 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364928609/2500000000 : ℝ)^4963 ≤ (8851304091617/100000000000000 : ℝ)^3939 := by
    have hnat : (364928609 : ℕ)^4963*100000000000000^3939 ≤ 8851304091617^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364928609 2500000000 8851304091617 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276594703/10000000000 : ℝ), (4353881/8000000 : ℝ), (-364928609/2500000000 : ℝ)] ![(44686421426099/100000000000000 : ℝ), (11615568618557/25000000000000 : ℝ), (8851304091617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276594703/10000000000 : ℝ)|^4963 ≤ (44686421426099/100000000000000 : ℝ)^3939
        have hw : |(5276594703/10000000000 : ℝ)|=(5276594703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4353881/8000000 : ℝ)|^4963 ≤ (11615568618557/25000000000000 : ℝ)^3939
        have hw : |(4353881/8000000 : ℝ)|=(4353881/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-364928609/2500000000 : ℝ)|^4963 ≤ (8851304091617/100000000000000 : ℝ)^3939
        have hw : |(-364928609/2500000000 : ℝ)|=(364928609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s3_7 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521566811/1250000000 : ℝ)*x 0 + (4517877897/10000000000 : ℝ)*x 1 + (3846779609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521566811/1250000000 : ℝ)^4963 ≤ (33244316618569/100000000000000 : ℝ)^3939 := by
    have hnat : (521566811 : ℕ)^4963*100000000000000^3939 ≤ 33244316618569^3939*1250000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521566811 1250000000 33244316618569 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517877897/10000000000 : ℝ)^4963 ≤ (36747662644019/100000000000000 : ℝ)^3939 := by
    have hnat : (4517877897 : ℕ)^4963*100000000000000^3939 ≤ 36747662644019^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517877897 10000000000 36747662644019 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3846779609/10000000000 : ℝ)^4963 ≤ (30008020727381/100000000000000 : ℝ)^3939 := by
    have hnat : (3846779609 : ℕ)^4963*100000000000000^3939 ≤ 30008020727381^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846779609 10000000000 30008020727381 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521566811/1250000000 : ℝ), (4517877897/10000000000 : ℝ), (3846779609/10000000000 : ℝ)] ![(33244316618569/100000000000000 : ℝ), (36747662644019/100000000000000 : ℝ), (30008020727381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521566811/1250000000 : ℝ)|^4963 ≤ (33244316618569/100000000000000 : ℝ)^3939
        have hw : |(521566811/1250000000 : ℝ)|=(521566811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517877897/10000000000 : ℝ)|^4963 ≤ (36747662644019/100000000000000 : ℝ)^3939
        have hw : |(4517877897/10000000000 : ℝ)|=(4517877897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3846779609/10000000000 : ℝ)|^4963 ≤ (30008020727381/100000000000000 : ℝ)^3939
        have hw : |(3846779609/10000000000 : ℝ)|=(3846779609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1661_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2667/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10723/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13/80 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1631/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2667/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1631/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2667/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1631/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2667/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1631/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2667/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1631/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2667/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1631/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2667/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2667/25000 : ℝ) ^ (4959/1024 : ℝ) ≤ (1964383162338331/100000000000000000000 : ℝ) := by
    have hpowers : (2667/25000 : ℝ)^4959 ≤ (1964383162338331/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2667 : ℕ)^4959*100000000000000000000^1024 ≤ 1964383162338331^1024*25000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2667 25000 1964383162338331 100000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2667/25000 : ℝ)) (X := (1964383162338331/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1631/10000 : ℝ) ^ (4959/1024 : ℝ) ≤ (15349455061996309/100000000000000000000 : ℝ) := by
    have hpowers : (1631/10000 : ℝ)^4959 ≤ (15349455061996309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1631 : ℕ)^4959*100000000000000000000^1024 ≤ 15349455061996309^1024*10000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1631 10000 15349455061996309 100000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1631/10000 : ℝ)) (X := (15349455061996309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001964383162338331/50000000000000000000 : ℝ) ≤ (250002028127651/250000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (50001964383162338331/50000000000000000000 : ℝ)^1024 ≤ (250002028127651/250000000000000 : ℝ)^4959 := by
      have hnat : (50001964383162338331 : ℕ)^1024*250000000000000^4959 ≤ 250002028127651^4959*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001964383162338331 50000000000000000000 250002028127651 250000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250002028127651/250000000000000 : ℝ)) (X := (50001964383162338331/50000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250216422977804183/1250000000000000000 : ℝ) ≤ (1250044686813319/1250000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (1250216422977804183/1250000000000000000 : ℝ)^1024 ≤ (1250044686813319/1250000000000000 : ℝ)^4959 := by
      have hnat : (1250216422977804183 : ℕ)^1024*1250000000000000^4959 ≤ 1250044686813319^4959*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250216422977804183 1250000000000000000 1250044686813319 1250000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250044686813319/1250000000000000 : ℝ)) (X := (1250216422977804183/1250000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015349455061996309/50000000000000000000 : ℝ) ≤ (1250079232988383/1250000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (50015349455061996309/50000000000000000000 : ℝ)^1024 ≤ (1250079232988383/1250000000000000 : ℝ)^4959 := by
      have hnat : (50015349455061996309 : ℕ)^1024*1250000000000000^4959 ≤ 1250079232988383^4959*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015349455061996309 50000000000000000000 1250079232988383 1250000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250079232988383/1250000000000000 : ℝ)) (X := (50015349455061996309/50000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1964383162338331/100000000000000000000 : ℝ) ≤ ((16248433493755459/16250000000000000 : ℝ)+2*(139299093/284375000000 : ℝ)*(2667/25000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (16248433493755459/16250000000000000 : ℝ)+2*(139299093/284375000000 : ℝ)*(2667/25000 : ℝ)=(250002028127651/250000000000000 : ℝ) by norm_num, show 1+2*(1964383162338331/100000000000000000000 : ℝ)=(50001964383162338331/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15349455061996309/100000000000000000000 : ℝ)+(1964383162338331/100000000000000000000 : ℝ) ≤ ((16248433493755459/16250000000000000 : ℝ)+(139299093/284375000000 : ℝ)*((1631/10000 : ℝ)+(2667/25000 : ℝ)))^(4959/1024 : ℝ) := by
    rw [show (16248433493755459/16250000000000000 : ℝ)+(139299093/284375000000 : ℝ)*((1631/10000 : ℝ)+(2667/25000 : ℝ))=(1250044686813319/1250000000000000 : ℝ) by norm_num, show 1+(15349455061996309/100000000000000000000 : ℝ)+(1964383162338331/100000000000000000000 : ℝ)=(1250216422977804183/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15349455061996309/100000000000000000000 : ℝ) ≤ ((16248433493755459/16250000000000000 : ℝ)+2*(139299093/284375000000 : ℝ)*(1631/10000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (16248433493755459/16250000000000000 : ℝ)+2*(139299093/284375000000 : ℝ)*(1631/10000 : ℝ)=(1250079232988383/1250000000000000 : ℝ) by norm_num, show 1+2*(15349455061996309/100000000000000000000 : ℝ)=(50015349455061996309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16248433493755459/16250000000000000 : ℝ)*(X 1 0+X 2 0)+(139299093/284375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (2667/25000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (16248433493755459/16250000000000000 : ℝ)) (alpha := (139299093/284375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16248433493755459/16250000000000000 : ℝ)*(X 0 1+X 2 1)+(139299093/284375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (2667/25000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (16248433493755459/16250000000000000 : ℝ)) (alpha := (139299093/284375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16248433493755459/16250000000000000 : ℝ)*(X 0 2+X 1 2)+(139299093/284375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (2667/25000 : ℝ)) (hi := (1631/10000 : ℝ)) (c := (16248433493755459/16250000000000000 : ℝ)) (alpha := (139299093/284375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1583836803/10000000000 : ℝ)*X 0 0+(5444348011/10000000000 : ℝ)*X 0 1+(5184537123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069217861/2000000000 : ℝ)*X 1 0+(-858764257/5000000000 : ℝ)*X 1 1+(207381483/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346089311/10000000000 : ℝ)*X 2 0+(5184537091/10000000000 : ℝ)*X 2 1+(-343505697/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4172369641/10000000000 : ℝ)*X 0 0+(3841541633/10000000000 : ℝ)*X 0 1+(452306123/1000000000 : ℝ)*X 0 2+(4172369641/10000000000 : ℝ)*X 1 0+(3841541633/10000000000 : ℝ)*X 1 1+(452306123/1000000000 : ℝ)*X 1 2+(4172369641/10000000000 : ℝ)*X 2 0+(3841541633/10000000000 : ℝ)*X 2 1+(452306123/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1583899841/10000000000 : ℝ)*X 0 0+(5186513127/10000000000 : ℝ)*X 0 1+(1360587761/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276594837/10000000000 : ℝ)*X 1 0+(-1459714541/10000000000 : ℝ)*X 1 1+(2721175521/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276594703/10000000000 : ℝ)*X 2 0+(4353881/8000000 : ℝ)*X 2 1+(-364928609/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((521566811/1250000000 : ℝ)*X 0 0+(4517877897/10000000000 : ℝ)*X 0 1+(3846779609/10000000000 : ℝ)*X 0 2+(521566811/1250000000 : ℝ)*X 1 0+(4517877897/10000000000 : ℝ)*X 1 1+(3846779609/10000000000 : ℝ)*X 1 2+(521566811/1250000000 : ℝ)*X 2 0+(4517877897/10000000000 : ℝ)*X 2 1+(3846779609/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1661241145789050143543091/355468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (665512501/100000000000000 : ℝ)*(base19) + (77184369/12500000000000 : ℝ)*(base23) + (6997671/25000000000000 : ℝ)*(lower2) + (1118313/1250000000000 : ℝ)*(upper3) + (76229907/100000000000000 : ℝ)*(upper5) + (166133905800097/6250000000000 : ℝ)*(major0) + (166133905800097/6250000000000 : ℝ)*(major1) + (166133905800097/6250000000000 : ℝ)*(major2) + (1503500535539/39062500000 : ℝ)*(sp0) + (24056055932519/625000000000 : ℝ)*(sp1) + (962242249310147/25000000000000 : ℝ)*(sp2) + (146731208374483/10000000000000 : ℝ)*(sp3) + (82437357/1000000000000 : ℝ)*(sp4) + (3131363339/100000000000000 : ℝ)*(sp7) + (1467315215108169/100000000000000 : ℝ)*(f.failure) + (192448480735777/5000000000000 : ℝ)*(f.sum) + (726869157321/227500000000000000000000000 : ℝ)*base65 + (1977125298471053/1421875000000000000000000000000 : ℝ)*base68 + (3742253518439803/1421875000000000000000000000000 : ℝ)*base70 + (487787860470991/177734375000000000000000000000 : ℝ)*base72 + (779302429337/455000000000000000000000000 : ℝ)*base73 + (23453759082189803/1421875000000000000000000000000 : ℝ)*base76 + (593936943948643/355468750000000000000000000000 : ℝ)*base77 + (11280478118596053/1421875000000000000000000000000 : ℝ)*base80 + (754458553053/455000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5615471/5000000000000000000000 : ℝ)*base90 + (5615471/5000000000000000000000 : ℝ)*base92 + (5615471/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9474066722102379782620161/812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (361343993/20000000000000 : ℝ)*(base19) + (1759523139/100000000000000 : ℝ)*(base23) + (444579/4000000000000 : ℝ)*(upper2) + (281646349/100000000000000 : ℝ)*(upper3) + (246703751/100000000000000 : ℝ)*(upper5) + (2699409318592393/100000000000000 : ℝ)*(major0) + (2699409318592393/100000000000000 : ℝ)*(major1) + (2699409318592393/100000000000000 : ℝ)*(major2) + (5246141713/25000000000000 : ℝ)*(sp1) + (2917306769/12500000000000 : ℝ)*(sp2) + (3908723426387133/100000000000000 : ℝ)*(sp4) + (977175158775079/25000000000000 : ℝ)*(sp5) + (1954349164204921/50000000000000 : ℝ)*(sp6) + (372523705529497/25000000000000 : ℝ)*(sp7) + (372523705529497/25000000000000 : ℝ)*(f.failure) + (3908723426387133/100000000000000 : ℝ)*(f.sum) + (1525940133163/455000000000000000000000000 : ℝ)*base65 + (18898415302338709/11375000000000000000000000000000 : ℝ)*base67 + (57592970316036291/11375000000000000000000000000000 : ℝ)*base70 + (1540757645036291/11375000000000000000000000000000 : ℝ)*base72 + (60359745963/28437500000000000000000000 : ℝ)*base73 + (93270092706036291/11375000000000000000000000000000 : ℝ)*base76 + (134235225356713709/11375000000000000000000000000000 : ℝ)*base77 + (75281573339036291/11375000000000000000000000000000 : ℝ)*base80 + (328324472683/113750000000000000000000000 : ℝ)*base82 + (5274177/1250000000000000000000 : ℝ)*base89 + (5274177/1250000000000000000000 : ℝ)*base91 + (5274177/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1661_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2667/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13/80 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1661_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1661_s4_0 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-197983803/1250000000 : ℝ)*x 0 + (2722086131/5000000000 : ℝ)*x 1 + (5184690417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (197983803/1250000000 : ℝ)^4963 ≤ (9810139917441/100000000000000 : ℝ)^3939 := by
    have hnat : (197983803 : ℕ)^4963*100000000000000^3939 ≤ 9810139917441^3939*1250000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197983803 1250000000 9810139917441 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722086131/5000000000 : ℝ)^4963 ≤ (46481863096273/100000000000000 : ℝ)^3939 := by
    have hnat : (2722086131 : ℕ)^4963*100000000000000^3939 ≤ 46481863096273^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722086131 5000000000 46481863096273 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184690417/10000000000 : ℝ)^4963 ≤ (43707996970341/100000000000000 : ℝ)^3939 := by
    have hnat : (5184690417 : ℕ)^4963*100000000000000^3939 ≤ 43707996970341^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184690417 10000000000 43707996970341 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-197983803/1250000000 : ℝ), (2722086131/5000000000 : ℝ), (5184690417/10000000000 : ℝ)] ![(9810139917441/100000000000000 : ℝ), (46481863096273/100000000000000 : ℝ), (43707996970341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-197983803/1250000000 : ℝ)|^4963 ≤ (9810139917441/100000000000000 : ℝ)^3939
        have hw : |(-197983803/1250000000 : ℝ)|=(197983803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722086131/5000000000 : ℝ)|^4963 ≤ (46481863096273/100000000000000 : ℝ)^3939
        have hw : |(2722086131/5000000000 : ℝ)|=(2722086131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184690417/10000000000 : ℝ)|^4963 ≤ (43707996970341/100000000000000 : ℝ)^3939
        have hw : |(5184690417/10000000000 : ℝ)|=(5184690417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s4_1 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346041793/10000000000 : ℝ)*x 0 + (-1717387617/10000000000 : ℝ)*x 1 + (10126349/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346041793/10000000000 : ℝ)^4963 ≤ (45428712303069/100000000000000 : ℝ)^3939 := by
    have hnat : (5346041793 : ℕ)^4963*100000000000000^3939 ≤ 45428712303069^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346041793 10000000000 45428712303069 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1717387617/10000000000 : ℝ)^4963 ≤ (10863287828057/100000000000000 : ℝ)^3939 := by
    have hnat : (1717387617 : ℕ)^4963*100000000000000^3939 ≤ 10863287828057^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1717387617 10000000000 10863287828057 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10126349/19531250 : ℝ)^4963 ≤ (43707999848837/100000000000000 : ℝ)^3939 := by
    have hnat : (10126349 : ℕ)^4963*100000000000000^3939 ≤ 43707999848837^3939*19531250^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10126349 19531250 43707999848837 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346041793/10000000000 : ℝ), (-1717387617/10000000000 : ℝ), (10126349/19531250 : ℝ)] ![(45428712303069/100000000000000 : ℝ), (10863287828057/100000000000000 : ℝ), (43707999848837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346041793/10000000000 : ℝ)|^4963 ≤ (45428712303069/100000000000000 : ℝ)^3939
        have hw : |(5346041793/10000000000 : ℝ)|=(5346041793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1717387617/10000000000 : ℝ)|^4963 ≤ (10863287828057/100000000000000 : ℝ)^3939
        have hw : |(-1717387617/10000000000 : ℝ)|=(1717387617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10126349/19531250 : ℝ)|^4963 ≤ (43707999848837/100000000000000 : ℝ)^3939
        have hw : |(10126349/19531250 : ℝ)|=(10126349/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s4_2 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346041723/10000000000 : ℝ)*x 0 + (5184690343/10000000000 : ℝ)*x 1 + (-429347043/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346041723/10000000000 : ℝ)^4963 ≤ (45428711553599/100000000000000 : ℝ)^3939 := by
    have hnat : (5346041723 : ℕ)^4963*100000000000000^3939 ≤ 45428711553599^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346041723 10000000000 45428711553599 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184690343/10000000000 : ℝ)^4963 ≤ (43707996184331/100000000000000 : ℝ)^3939 := by
    have hnat : (5184690343 : ℕ)^4963*100000000000000^3939 ≤ 43707996184331^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184690343 10000000000 43707996184331 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (429347043/2500000000 : ℝ)^4963 ≤ (2172658450267/20000000000000 : ℝ)^3939 := by
    have hnat : (429347043 : ℕ)^4963*20000000000000^3939 ≤ 2172658450267^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429347043 2500000000 2172658450267 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346041723/10000000000 : ℝ), (5184690343/10000000000 : ℝ), (-429347043/2500000000 : ℝ)] ![(45428711553599/100000000000000 : ℝ), (43707996184331/100000000000000 : ℝ), (2172658450267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346041723/10000000000 : ℝ)|^4963 ≤ (45428711553599/100000000000000 : ℝ)^3939
        have hw : |(5346041723/10000000000 : ℝ)|=(5346041723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184690343/10000000000 : ℝ)|^4963 ≤ (43707996184331/100000000000000 : ℝ)^3939
        have hw : |(5184690343/10000000000 : ℝ)|=(5184690343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-429347043/2500000000 : ℝ)|^4963 ≤ (2172658450267/20000000000000 : ℝ)^3939
        have hw : |(-429347043/2500000000 : ℝ)|=(429347043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s4_3 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (521549021/1250000000 : ℝ)*x 0 + (384197069/1000000000 : ℝ)*x 1 + (4522627937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (521549021/1250000000 : ℝ)^4963 ≤ (16621443961367/50000000000000 : ℝ)^3939 := by
    have hnat : (521549021 : ℕ)^4963*50000000000000^3939 ≤ 16621443961367^3939*1250000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521549021 1250000000 16621443961367 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384197069/1000000000 : ℝ)^4963 ≤ (3745095342731/12500000000000 : ℝ)^3939 := by
    have hnat : (384197069 : ℕ)^4963*12500000000000^3939 ≤ 3745095342731^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384197069 1000000000 3745095342731 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522627937/10000000000 : ℝ)^4963 ≤ (9199087330001/25000000000000 : ℝ)^3939 := by
    have hnat : (4522627937 : ℕ)^4963*25000000000000^3939 ≤ 9199087330001^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522627937 10000000000 9199087330001 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(521549021/1250000000 : ℝ), (384197069/1000000000 : ℝ), (4522627937/10000000000 : ℝ)] ![(16621443961367/50000000000000 : ℝ), (3745095342731/12500000000000 : ℝ), (9199087330001/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(521549021/1250000000 : ℝ)|^4963 ≤ (16621443961367/50000000000000 : ℝ)^3939
        have hw : |(521549021/1250000000 : ℝ)|=(521549021/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(384197069/1000000000 : ℝ)|^4963 ≤ (3745095342731/12500000000000 : ℝ)^3939
        have hw : |(384197069/1000000000 : ℝ)|=(384197069/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522627937/10000000000 : ℝ)|^4963 ≤ (9199087330001/25000000000000 : ℝ)^3939
        have hw : |(4522627937/10000000000 : ℝ)|=(4522627937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s4_4 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-158393303/1000000000 : ℝ)*x 0 + (2593330741/5000000000 : ℝ)*x 1 + (2721090227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158393303/1000000000 : ℝ)^4963 ≤ (4905314246667/50000000000000 : ℝ)^3939 := by
    have hnat : (158393303 : ℕ)^4963*50000000000000^3939 ≤ 4905314246667^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158393303 1000000000 4905314246667 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593330741/5000000000 : ℝ)^4963 ≤ (5466116772331/12500000000000 : ℝ)^3939 := by
    have hnat : (2593330741 : ℕ)^4963*12500000000000^3939 ≤ 5466116772331^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593330741 5000000000 5466116772331 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721090227/5000000000 : ℝ)^4963 ≤ (1858417492377/4000000000000 : ℝ)^3939 := by
    have hnat : (2721090227 : ℕ)^4963*4000000000000^3939 ≤ 1858417492377^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721090227 5000000000 1858417492377 4000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-158393303/1000000000 : ℝ), (2593330741/5000000000 : ℝ), (2721090227/5000000000 : ℝ)] ![(4905314246667/50000000000000 : ℝ), (5466116772331/12500000000000 : ℝ), (1858417492377/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-158393303/1000000000 : ℝ)|^4963 ≤ (4905314246667/50000000000000 : ℝ)^3939
        have hw : |(-158393303/1000000000 : ℝ)|=(158393303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593330741/5000000000 : ℝ)|^4963 ≤ (5466116772331/12500000000000 : ℝ)^3939
        have hw : |(2593330741/5000000000 : ℝ)|=(2593330741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721090227/5000000000 : ℝ)|^4963 ≤ (1858417492377/4000000000000 : ℝ)^3939
        have hw : |(2721090227/5000000000 : ℝ)|=(2721090227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s4_5 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276635521/10000000000 : ℝ)*x 0 + (-1459897903/10000000000 : ℝ)*x 1 + (5442180443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276635521/10000000000 : ℝ)^4963 ≤ (44686856970357/100000000000000 : ℝ)^3939 := by
    have hnat : (5276635521 : ℕ)^4963*100000000000000^3939 ≤ 44686856970357^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276635521 10000000000 44686856970357 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459897903/10000000000 : ℝ)^4963 ≤ (1770541163251/20000000000000 : ℝ)^3939 := by
    have hnat : (1459897903 : ℕ)^4963*20000000000000^3939 ≤ 1770541163251^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459897903 10000000000 1770541163251 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442180443/10000000000 : ℝ)^4963 ≤ (725944331111/1562500000000 : ℝ)^3939 := by
    have hnat : (5442180443 : ℕ)^4963*1562500000000^3939 ≤ 725944331111^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442180443 10000000000 725944331111 1562500000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276635521/10000000000 : ℝ), (-1459897903/10000000000 : ℝ), (5442180443/10000000000 : ℝ)] ![(44686856970357/100000000000000 : ℝ), (1770541163251/20000000000000 : ℝ), (725944331111/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276635521/10000000000 : ℝ)|^4963 ≤ (44686856970357/100000000000000 : ℝ)^3939
        have hw : |(5276635521/10000000000 : ℝ)|=(5276635521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1459897903/10000000000 : ℝ)|^4963 ≤ (1770541163251/20000000000000 : ℝ)^3939
        have hw : |(-1459897903/10000000000 : ℝ)|=(1459897903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442180443/10000000000 : ℝ)|^4963 ≤ (725944331111/1562500000000 : ℝ)^3939
        have hw : |(5442180443/10000000000 : ℝ)|=(5442180443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s4_6 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055327103/2000000000 : ℝ)*x 0 + (5442180457/10000000000 : ℝ)*x 1 + (-364974473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055327103/2000000000 : ℝ)^4963 ≤ (8937371381267/20000000000000 : ℝ)^3939 := by
    have hnat : (1055327103 : ℕ)^4963*20000000000000^3939 ≤ 8937371381267^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055327103 2000000000 8937371381267 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442180457/10000000000 : ℝ)^4963 ≤ (23230218670847/50000000000000 : ℝ)^3939 := by
    have hnat : (5442180457 : ℕ)^4963*50000000000000^3939 ≤ 23230218670847^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442180457 10000000000 23230218670847 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (364974473/2500000000 : ℝ)^4963 ≤ (2213176433053/25000000000000 : ℝ)^3939 := by
    have hnat : (364974473 : ℕ)^4963*25000000000000^3939 ≤ 2213176433053^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364974473 2500000000 2213176433053 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055327103/2000000000 : ℝ), (5442180457/10000000000 : ℝ), (-364974473/2500000000 : ℝ)] ![(8937371381267/20000000000000 : ℝ), (23230218670847/50000000000000 : ℝ), (2213176433053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055327103/2000000000 : ℝ)|^4963 ≤ (8937371381267/20000000000000 : ℝ)^3939
        have hw : |(1055327103/2000000000 : ℝ)|=(1055327103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442180457/10000000000 : ℝ)|^4963 ≤ (23230218670847/50000000000000 : ℝ)^3939
        have hw : |(5442180457/10000000000 : ℝ)|=(5442180457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-364974473/2500000000 : ℝ)|^4963 ≤ (2213176433053/25000000000000 : ℝ)^3939
        have hw : |(-364974473/2500000000 : ℝ)|=(364974473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s4_7 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4172556763/10000000000 : ℝ)*x 0 + (4517457127/10000000000 : ℝ)*x 1 + (3847195579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172556763/10000000000 : ℝ)^4963 ≤ (129861485273/390625000000 : ℝ)^3939 := by
    have hnat : (4172556763 : ℕ)^4963*390625000000^3939 ≤ 129861485273^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172556763 10000000000 129861485273 390625000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4517457127/10000000000 : ℝ)^4963 ≤ (36743350502193/100000000000000 : ℝ)^3939 := by
    have hnat : (4517457127 : ℕ)^4963*100000000000000^3939 ≤ 36743350502193^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517457127 10000000000 36743350502193 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3847195579/10000000000 : ℝ)^4963 ≤ (7503027312617/25000000000000 : ℝ)^3939 := by
    have hnat : (3847195579 : ℕ)^4963*25000000000000^3939 ≤ 7503027312617^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3847195579 10000000000 7503027312617 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172556763/10000000000 : ℝ), (4517457127/10000000000 : ℝ), (3847195579/10000000000 : ℝ)] ![(129861485273/390625000000 : ℝ), (36743350502193/100000000000000 : ℝ), (7503027312617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172556763/10000000000 : ℝ)|^4963 ≤ (129861485273/390625000000 : ℝ)^3939
        have hw : |(4172556763/10000000000 : ℝ)|=(4172556763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4517457127/10000000000 : ℝ)|^4963 ≤ (36743350502193/100000000000000 : ℝ)^3939
        have hw : |(4517457127/10000000000 : ℝ)|=(4517457127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3847195579/10000000000 : ℝ)|^4963 ≤ (7503027312617/25000000000000 : ℝ)^3939
        have hw : |(3847195579/10000000000 : ℝ)|=(3847195579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1661_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5363/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8123/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13/80 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10723/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13/80 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10723/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13/80 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10723/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13/80 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10723/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13/80 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10723/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13/80 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10723/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10723/100000 : ℝ) ^ (4959/1024 : ℝ) ≤ (402783396245067/20000000000000000000 : ℝ) := by
    have hpowers : (10723/100000 : ℝ)^4959 ≤ (402783396245067/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10723 : ℕ)^4959*20000000000000000000^1024 ≤ 402783396245067^1024*100000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10723 100000 402783396245067 20000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10723/100000 : ℝ)) (X := (402783396245067/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13/80 : ℝ) ^ (4959/1024 : ℝ) ≤ (3015585420248403/20000000000000000000 : ℝ) := by
    have hpowers : (13/80 : ℝ)^4959 ≤ (3015585420248403/20000000000000000000 : ℝ)^1024 := by
      have hnat : (13 : ℕ)^4959*20000000000000000000^1024 ≤ 3015585420248403^1024*80^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 80 3015585420248403 20000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/80 : ℝ)) (X := (3015585420248403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000402783396245067/10000000000000000000 : ℝ) ≤ (500004158536063/500000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (10000402783396245067/10000000000000000000 : ℝ)^1024 ≤ (500004158536063/500000000000000 : ℝ)^4959 := by
      have hnat : (10000402783396245067 : ℕ)^1024*500000000000000^4959 ≤ 500004158536063^4959*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000402783396245067 10000000000000000000 500004158536063 500000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500004158536063/500000000000000 : ℝ)) (X := (10000402783396245067/10000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2000341836881649347/2000000000000000000 : ℝ) ≤ (5000176455551569/5000000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (2000341836881649347/2000000000000000000 : ℝ)^1024 ≤ (5000176455551569/5000000000000000 : ℝ)^4959 := by
      have hnat : (2000341836881649347 : ℕ)^1024*5000000000000000^4959 ≤ 5000176455551569^4959*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000341836881649347 2000000000000000000 5000176455551569 5000000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000176455551569/5000000000000000 : ℝ)) (X := (2000341836881649347/2000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003015585420248403/10000000000000000000 : ℝ) ≤ (1250077831435627/1250000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (10003015585420248403/10000000000000000000 : ℝ)^1024 ≤ (1250077831435627/1250000000000000 : ℝ)^4959 := by
      have hnat : (10003015585420248403 : ℕ)^1024*1250000000000000^4959 ≤ 1250077831435627^4959*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003015585420248403 10000000000000000000 1250077831435627 1250000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250077831435627/1250000000000000 : ℝ)) (X := (10003015585420248403/10000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(402783396245067/20000000000000000000 : ℝ) ≤ ((3454042177021665527/3454375000000000000 : ℝ)+2*(134870190939/276350000000000 : ℝ)*(10723/100000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (3454042177021665527/3454375000000000000 : ℝ)+2*(134870190939/276350000000000 : ℝ)*(10723/100000 : ℝ)=(500004158536063/500000000000000 : ℝ) by norm_num, show 1+2*(402783396245067/20000000000000000000 : ℝ)=(10000402783396245067/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3015585420248403/20000000000000000000 : ℝ)+(402783396245067/20000000000000000000 : ℝ) ≤ ((3454042177021665527/3454375000000000000 : ℝ)+(134870190939/276350000000000 : ℝ)*((13/80 : ℝ)+(10723/100000 : ℝ)))^(4959/1024 : ℝ) := by
    rw [show (3454042177021665527/3454375000000000000 : ℝ)+(134870190939/276350000000000 : ℝ)*((13/80 : ℝ)+(10723/100000 : ℝ))=(5000176455551569/5000000000000000 : ℝ) by norm_num, show 1+(3015585420248403/20000000000000000000 : ℝ)+(402783396245067/20000000000000000000 : ℝ)=(2000341836881649347/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3015585420248403/20000000000000000000 : ℝ) ≤ ((3454042177021665527/3454375000000000000 : ℝ)+2*(134870190939/276350000000000 : ℝ)*(13/80 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (3454042177021665527/3454375000000000000 : ℝ)+2*(134870190939/276350000000000 : ℝ)*(13/80 : ℝ)=(1250077831435627/1250000000000000 : ℝ) by norm_num, show 1+2*(3015585420248403/20000000000000000000 : ℝ)=(10003015585420248403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3454042177021665527/3454375000000000000 : ℝ)*(X 1 0+X 2 0)+(134870190939/276350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (13/80 : ℝ)) (c := (3454042177021665527/3454375000000000000 : ℝ)) (alpha := (134870190939/276350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3454042177021665527/3454375000000000000 : ℝ)*(X 0 1+X 2 1)+(134870190939/276350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (13/80 : ℝ)) (c := (3454042177021665527/3454375000000000000 : ℝ)) (alpha := (134870190939/276350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3454042177021665527/3454375000000000000 : ℝ)*(X 0 2+X 1 2)+(134870190939/276350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (10723/100000 : ℝ)) (hi := (13/80 : ℝ)) (c := (3454042177021665527/3454375000000000000 : ℝ)) (alpha := (134870190939/276350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-197983803/1250000000 : ℝ)*X 0 0+(2722086131/5000000000 : ℝ)*X 0 1+(5184690417/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346041793/10000000000 : ℝ)*X 1 0+(-1717387617/10000000000 : ℝ)*X 1 1+(10126349/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346041723/10000000000 : ℝ)*X 2 0+(5184690343/10000000000 : ℝ)*X 2 1+(-429347043/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((521549021/1250000000 : ℝ)*X 0 0+(384197069/1000000000 : ℝ)*X 0 1+(4522627937/10000000000 : ℝ)*X 0 2+(521549021/1250000000 : ℝ)*X 1 0+(384197069/1000000000 : ℝ)*X 1 1+(4522627937/10000000000 : ℝ)*X 1 2+(521549021/1250000000 : ℝ)*X 2 0+(384197069/1000000000 : ℝ)*X 2 1+(4522627937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-158393303/1000000000 : ℝ)*X 0 0+(2593330741/5000000000 : ℝ)*X 0 1+(2721090227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276635521/10000000000 : ℝ)*X 1 0+(-1459897903/10000000000 : ℝ)*X 1 1+(5442180443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055327103/2000000000 : ℝ)*X 2 0+(5442180457/10000000000 : ℝ)*X 2 1+(-364974473/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4172556763/10000000000 : ℝ)*X 0 0+(4517457127/10000000000 : ℝ)*X 0 1+(3847195579/10000000000 : ℝ)*X 0 2+(4172556763/10000000000 : ℝ)*X 1 0+(4517457127/10000000000 : ℝ)*X 1 1+(3847195579/10000000000 : ℝ)*X 1 2+(4172556763/10000000000 : ℝ)*X 2 0+(4517457127/10000000000 : ℝ)*X 2 1+(3847195579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70908497328227307396229113/8635937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (562802801/50000000000000 : ℝ)*(base19) + (526097187/50000000000000 : ℝ)*(base23) + (9957427/100000000000000 : ℝ)*(upper2) + (138214269/50000000000000 : ℝ)*(upper3) + (33269085739419/1250000000000 : ℝ)*(major0) + (33269085739419/1250000000000 : ℝ)*(major1) + (33269085739419/1250000000000 : ℝ)*(major2) + (963463915658101/25000000000000 : ℝ)*(sp0) + (3853868907495581/100000000000000 : ℝ)*(sp1) + (1926932889278671/50000000000000 : ℝ)*(sp2) + (1469174780271287/100000000000000 : ℝ)*(sp3) + (14370468779/100000000000000 : ℝ)*(sp4) + (1601174733/50000000000000 : ℝ)*(sp6) + (8631239141/100000000000000 : ℝ)*(sp7) + (367295852877607/25000000000000 : ℝ)*(f.failure) + (3853870033101183/100000000000000 : ℝ)*(f.sum) + (6860261829979/5527000000000000000000000000 : ℝ)*base66 + (88526642850032127/17271875000000000000000000000000 : ℝ)*base67 + (299465891044031/2158984375000000000000000000000 : ℝ)*base70 + (760131250829547/1079492187500000000000000000000 : ℝ)*base71 + (2599819778827/1381750000000000000000000000 : ℝ)*base74 + (13411279060764501/8635937500000000000000000000000 : ℝ)*base75 + (84219524430082127/17271875000000000000000000000000 : ℝ)*base77 + (264584289095550877/17271875000000000000000000000000 : ℝ)*base79 + (6233333923281/2763500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5870687/1250000000000000000000 : ℝ)*base89 + (5870687/1250000000000000000000 : ℝ)*base91 + (5870687/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (690462449960613859177014417/86359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73141689/6250000000000 : ℝ)*(base19) + (1267839381/100000000000000 : ℝ)*(base23) + (11305929/3125000000000 : ℝ)*(lower1) + (167291919/100000000000000 : ℝ)*(upper3) + (43355003/100000000000000 : ℝ)*(lower4) + (150698123/100000000000000 : ℝ)*(upper5) + (675692274062991/25000000000000 : ℝ)*(major0) + (675692274062991/25000000000000 : ℝ)*(major1) + (675692274062991/25000000000000 : ℝ)*(major2) + (1509739061/100000000000000 : ℝ)*(sp2) + (3913588480624629/100000000000000 : ℝ)*(sp4) + (1956793655178803/50000000000000 : ℝ)*(sp5) + (3913585703046187/100000000000000 : ℝ)*(sp6) + (298389889074373/20000000000000 : ℝ)*(sp7) + (298389889074373/20000000000000 : ℝ)*(f.failure) + (3913588480624629/100000000000000 : ℝ)*(f.sum) + (86422648840983/27635000000000000000000000000 : ℝ)*base66 + (76753213850357191/43179687500000000000000000000000 : ℝ)*base67 + (254275844836642809/43179687500000000000000000000000 : ℝ)*base70 + (262329258990080309/43179687500000000000000000000000 : ℝ)*base72 + (88604556780103/27635000000000000000000000000 : ℝ)*base74 + (131979504779888441/43179687500000000000000000000000 : ℝ)*base75 + (32393098310687773/5397460937500000000000000000000 : ℝ)*base78 + (257522993434861559/43179687500000000000000000000000 : ℝ)*base80 + (59898117486873/27635000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (607507/1000000000000000000000 : ℝ)*base90 + (607507/1000000000000000000000 : ℝ)*base92 + (607507/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1661_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13/80 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10723/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8123/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1661_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1661_box_0 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-664884573/5000000000 : ℝ)*x 0 + (5405374029/10000000000 : ℝ)*x 1 + (216214879/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664884573/5000000000 : ℝ)^4963 ≤ (1574052509011/20000000000000 : ℝ)^3939 := by
    have hnat : (664884573 : ℕ)^4963*20000000000000^3939 ≤ 1574052509011^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664884573 5000000000 1574052509011 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405374029/10000000000 : ℝ)^4963 ≤ (9212975949091/20000000000000 : ℝ)^3939 := by
    have hnat : (5405374029 : ℕ)^4963*20000000000000^3939 ≤ 9212975949091^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405374029 10000000000 9212975949091 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216214879/400000000 : ℝ)^4963 ≤ (23032428845333/50000000000000 : ℝ)^3939 := by
    have hnat : (216214879 : ℕ)^4963*50000000000000^3939 ≤ 23032428845333^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216214879 400000000 23032428845333 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-664884573/5000000000 : ℝ), (5405374029/10000000000 : ℝ), (216214879/400000000 : ℝ)] ![(1574052509011/20000000000000 : ℝ), (9212975949091/20000000000000 : ℝ), (23032428845333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-664884573/5000000000 : ℝ)|^4963 ≤ (1574052509011/20000000000000 : ℝ)^3939
        have hw : |(-664884573/5000000000 : ℝ)|=(664884573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405374029/10000000000 : ℝ)|^4963 ≤ (9212975949091/20000000000000 : ℝ)^3939
        have hw : |(5405374029/10000000000 : ℝ)|=(5405374029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216214879/400000000 : ℝ)|^4963 ≤ (23032428845333/50000000000000 : ℝ)^3939
        have hw : |(216214879/400000000 : ℝ)|=(216214879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_1 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250891553/10000000000 : ℝ)*x 0 + (-1546938077/10000000000 : ℝ)*x 1 + (540537279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250891553/10000000000 : ℝ)^4963 ≤ (44412332754147/100000000000000 : ℝ)^3939 := by
    have hnat : (5250891553 : ℕ)^4963*100000000000000^3939 ≤ 44412332754147^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250891553 10000000000 44412332754147 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1546938077/10000000000 : ℝ)^4963 ≤ (4761400390979/50000000000000 : ℝ)^3939 := by
    have hnat : (1546938077 : ℕ)^4963*50000000000000^3939 ≤ 4761400390979^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546938077 10000000000 4761400390979 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540537279/1000000000 : ℝ)^4963 ≤ (23032433220857/50000000000000 : ℝ)^3939 := by
    have hnat : (540537279 : ℕ)^4963*50000000000000^3939 ≤ 23032433220857^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540537279 1000000000 23032433220857 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250891553/10000000000 : ℝ), (-1546938077/10000000000 : ℝ), (540537279/1000000000 : ℝ)] ![(44412332754147/100000000000000 : ℝ), (4761400390979/50000000000000 : ℝ), (23032433220857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250891553/10000000000 : ℝ)|^4963 ≤ (44412332754147/100000000000000 : ℝ)^3939
        have hw : |(5250891553/10000000000 : ℝ)|=(5250891553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1546938077/10000000000 : ℝ)|^4963 ≤ (4761400390979/50000000000000 : ℝ)^3939
        have hw : |(-1546938077/10000000000 : ℝ)|=(1546938077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540537279/1000000000 : ℝ)|^4963 ≤ (23032433220857/50000000000000 : ℝ)^3939
        have hw : |(540537279/1000000000 : ℝ)|=(540537279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_2 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328180719/625000000 : ℝ)*x 0 + (5405372473/10000000000 : ℝ)*x 1 + (-309387717/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328180719/625000000 : ℝ)^4963 ≤ (44412332231961/100000000000000 : ℝ)^3939 := by
    have hnat : (328180719 : ℕ)^4963*100000000000000^3939 ≤ 44412332231961^3939*625000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328180719 625000000 44412332231961 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405372473/10000000000 : ℝ)^4963 ≤ (11516215759483/25000000000000 : ℝ)^3939 := by
    have hnat : (5405372473 : ℕ)^4963*25000000000000^3939 ≤ 11516215759483^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405372473 10000000000 11516215759483 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (309387717/2000000000 : ℝ)^4963 ≤ (9522804722117/100000000000000 : ℝ)^3939 := by
    have hnat : (309387717 : ℕ)^4963*100000000000000^3939 ≤ 9522804722117^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309387717 2000000000 9522804722117 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328180719/625000000 : ℝ), (5405372473/10000000000 : ℝ), (-309387717/2000000000 : ℝ)] ![(44412332231961/100000000000000 : ℝ), (11516215759483/25000000000000 : ℝ), (9522804722117/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328180719/625000000 : ℝ)|^4963 ≤ (44412332231961/100000000000000 : ℝ)^3939
        have hw : |(328180719/625000000 : ℝ)|=(328180719/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405372473/10000000000 : ℝ)|^4963 ≤ (11516215759483/25000000000000 : ℝ)^3939
        have hw : |(5405372473/10000000000 : ℝ)|=(5405372473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-309387717/2000000000 : ℝ)|^4963 ≤ (9522804722117/100000000000000 : ℝ)^3939
        have hw : |(-309387717/2000000000 : ℝ)|=(309387717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_3 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4448487969/10000000000 : ℝ)*x 0 + (404619109/1000000000 : ℝ)*x 1 + (4046189903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4448487969/10000000000 : ℝ)^4963 ≤ (36037956180921/100000000000000 : ℝ)^3939 := by
    have hnat : (4448487969 : ℕ)^4963*100000000000000^3939 ≤ 36037956180921^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4448487969 10000000000 36037956180921 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404619109/1000000000 : ℝ)^4963 ≤ (31981027807687/100000000000000 : ℝ)^3939 := by
    have hnat : (404619109 : ℕ)^4963*100000000000000^3939 ≤ 31981027807687^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404619109 1000000000 31981027807687 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4046189903/10000000000 : ℝ)^4963 ≤ (6396203197333/20000000000000 : ℝ)^3939 := by
    have hnat : (4046189903 : ℕ)^4963*20000000000000^3939 ≤ 6396203197333^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046189903 10000000000 6396203197333 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4448487969/10000000000 : ℝ), (404619109/1000000000 : ℝ), (4046189903/10000000000 : ℝ)] ![(36037956180921/100000000000000 : ℝ), (31981027807687/100000000000000 : ℝ), (6396203197333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4448487969/10000000000 : ℝ)|^4963 ≤ (36037956180921/100000000000000 : ℝ)^3939
        have hw : |(4448487969/10000000000 : ℝ)|=(4448487969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404619109/1000000000 : ℝ)|^4963 ≤ (31981027807687/100000000000000 : ℝ)^3939
        have hw : |(404619109/1000000000 : ℝ)|=(404619109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4046189903/10000000000 : ℝ)|^4963 ≤ (6396203197333/20000000000000 : ℝ)^3939
        have hw : |(4046189903/10000000000 : ℝ)|=(4046189903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_4 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1848532831/10000000000 : ℝ)*x 0 + (5215984929/10000000000 : ℝ)*x 1 + (208639383/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1848532831/10000000000 : ℝ)^4963 ≤ (1191868358869/10000000000000 : ℝ)^3939 := by
    have hnat : (1848532831 : ℕ)^4963*10000000000000^3939 ≤ 1191868358869^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848532831 10000000000 1191868358869 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215984929/10000000000 : ℝ)^4963 ≤ (44040660082657/100000000000000 : ℝ)^3939 := by
    have hnat : (5215984929 : ℕ)^4963*100000000000000^3939 ≤ 44040660082657^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215984929 10000000000 44040660082657 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208639383/400000000 : ℝ)^4963 ≤ (11010164079167/25000000000000 : ℝ)^3939 := by
    have hnat : (208639383 : ℕ)^4963*25000000000000^3939 ≤ 11010164079167^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208639383 400000000 11010164079167 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1848532831/10000000000 : ℝ), (5215984929/10000000000 : ℝ), (208639383/400000000 : ℝ)] ![(1191868358869/10000000000000 : ℝ), (44040660082657/100000000000000 : ℝ), (11010164079167/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1848532831/10000000000 : ℝ)|^4963 ≤ (1191868358869/10000000000000 : ℝ)^3939
        have hw : |(-1848532831/10000000000 : ℝ)|=(1848532831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215984929/10000000000 : ℝ)|^4963 ≤ (44040660082657/100000000000000 : ℝ)^3939
        have hw : |(5215984929/10000000000 : ℝ)|=(5215984929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208639383/400000000 : ℝ)|^4963 ≤ (11010164079167/25000000000000 : ℝ)^3939
        have hw : |(208639383/400000000 : ℝ)|=(208639383/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_5 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345173157/2500000000 : ℝ)*x 0 + (-814226163/5000000000 : ℝ)*x 1 + (1303996239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345173157/2500000000 : ℝ)^4963 ≤ (45800021091339/100000000000000 : ℝ)^3939 := by
    have hnat : (1345173157 : ℕ)^4963*100000000000000^3939 ≤ 45800021091339^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345173157 2500000000 45800021091339 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (814226163/5000000000 : ℝ)^4963 ≤ (10159318517199/100000000000000 : ℝ)^3939 := by
    have hnat : (814226163 : ℕ)^4963*100000000000000^3939 ≤ 10159318517199^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814226163 5000000000 10159318517199 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303996239/2500000000 : ℝ)^4963 ≤ (22020330184947/50000000000000 : ℝ)^3939 := by
    have hnat : (1303996239 : ℕ)^4963*50000000000000^3939 ≤ 22020330184947^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303996239 2500000000 22020330184947 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345173157/2500000000 : ℝ), (-814226163/5000000000 : ℝ), (1303996239/2500000000 : ℝ)] ![(45800021091339/100000000000000 : ℝ), (10159318517199/100000000000000 : ℝ), (22020330184947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345173157/2500000000 : ℝ)|^4963 ≤ (45800021091339/100000000000000 : ℝ)^3939
        have hw : |(1345173157/2500000000 : ℝ)|=(1345173157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-814226163/5000000000 : ℝ)|^4963 ≤ (10159318517199/100000000000000 : ℝ)^3939
        have hw : |(-814226163/5000000000 : ℝ)|=(814226163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303996239/2500000000 : ℝ)|^4963 ≤ (22020330184947/50000000000000 : ℝ)^3939
        have hw : |(1303996239/2500000000 : ℝ)|=(1303996239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_6 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380693043/10000000000 : ℝ)*x 0 + (1303996131/2500000000 : ℝ)*x 1 + (-814226173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380693043/10000000000 : ℝ)^4963 ≤ (2862501596381/6250000000000 : ℝ)^3939 := by
    have hnat : (5380693043 : ℕ)^4963*6250000000000^3939 ≤ 2862501596381^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380693043 10000000000 2862501596381 6250000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303996131/2500000000 : ℝ)^4963 ≤ (4404065577411/10000000000000 : ℝ)^3939 := by
    have hnat : (1303996131 : ℕ)^4963*10000000000000^3939 ≤ 4404065577411^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303996131 2500000000 4404065577411 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (814226173/5000000000 : ℝ)^4963 ≤ (1269914834301/12500000000000 : ℝ)^3939 := by
    have hnat : (814226173 : ℕ)^4963*12500000000000^3939 ≤ 1269914834301^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      814226173 5000000000 1269914834301 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380693043/10000000000 : ℝ), (1303996131/2500000000 : ℝ), (-814226173/5000000000 : ℝ)] ![(2862501596381/6250000000000 : ℝ), (4404065577411/10000000000000 : ℝ), (1269914834301/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380693043/10000000000 : ℝ)|^4963 ≤ (2862501596381/6250000000000 : ℝ)^3939
        have hw : |(5380693043/10000000000 : ℝ)|=(5380693043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303996131/2500000000 : ℝ)|^4963 ≤ (4404065577411/10000000000000 : ℝ)^3939
        have hw : |(1303996131/2500000000 : ℝ)|=(1303996131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-814226173/5000000000 : ℝ)|^4963 ≤ (1269914834301/12500000000000 : ℝ)^3939
        have hw : |(-814226173/5000000000 : ℝ)|=(814226173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_7 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (777923063/2000000000 : ℝ)*x 0 + (2162653159/5000000000 : ℝ)*x 1 + (173012253/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (777923063/2000000000 : ℝ)^4963 ≤ (15214824974511/50000000000000 : ℝ)^3939 := by
    have hnat : (777923063 : ℕ)^4963*50000000000000^3939 ≤ 15214824974511^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777923063 2000000000 15214824974511 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2162653159/5000000000 : ℝ)^4963 ≤ (3478517498521/10000000000000 : ℝ)^3939 := by
    have hnat : (2162653159 : ℕ)^4963*10000000000000^3939 ≤ 3478517498521^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162653159 5000000000 3478517498521 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173012253/400000000 : ℝ)^4963 ≤ (34785175056141/100000000000000 : ℝ)^3939 := by
    have hnat : (173012253 : ℕ)^4963*100000000000000^3939 ≤ 34785175056141^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173012253 400000000 34785175056141 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(777923063/2000000000 : ℝ), (2162653159/5000000000 : ℝ), (173012253/400000000 : ℝ)] ![(15214824974511/50000000000000 : ℝ), (3478517498521/10000000000000 : ℝ), (34785175056141/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(777923063/2000000000 : ℝ)|^4963 ≤ (15214824974511/50000000000000 : ℝ)^3939
        have hw : |(777923063/2000000000 : ℝ)|=(777923063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2162653159/5000000000 : ℝ)|^4963 ≤ (3478517498521/10000000000000 : ℝ)^3939
        have hw : |(2162653159/5000000000 : ℝ)|=(2162653159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(173012253/400000000 : ℝ)|^4963 ≤ (34785175056141/100000000000000 : ℝ)^3939
        have hw : |(173012253/400000000 : ℝ)|=(173012253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_8 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-69511693/400000000 : ℝ)*x 0 + (2539763203/5000000000 : ℝ)*x 1 + (1358673139/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69511693/400000000 : ℝ)^4963 ≤ (11026161118823/100000000000000 : ℝ)^3939 := by
    have hnat : (69511693 : ℕ)^4963*100000000000000^3939 ≤ 11026161118823^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69511693 400000000 11026161118823 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539763203/5000000000 : ℝ)^4963 ≤ (21296965145801/50000000000000 : ℝ)^3939 := by
    have hnat : (2539763203 : ℕ)^4963*50000000000000^3939 ≤ 21296965145801^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539763203 5000000000 21296965145801 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358673139/2500000000 : ℝ)^4963 ≤ (23189954288263/50000000000000 : ℝ)^3939 := by
    have hnat : (1358673139 : ℕ)^4963*50000000000000^3939 ≤ 23189954288263^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358673139 2500000000 23189954288263 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69511693/400000000 : ℝ), (2539763203/5000000000 : ℝ), (1358673139/2500000000 : ℝ)] ![(11026161118823/100000000000000 : ℝ), (21296965145801/50000000000000 : ℝ), (23189954288263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69511693/400000000 : ℝ)|^4963 ≤ (11026161118823/100000000000000 : ℝ)^3939
        have hw : |(-69511693/400000000 : ℝ)|=(69511693/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539763203/5000000000 : ℝ)|^4963 ≤ (21296965145801/50000000000000 : ℝ)^3939
        have hw : |(2539763203/5000000000 : ℝ)|=(2539763203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358673139/2500000000 : ℝ)|^4963 ≤ (23189954288263/50000000000000 : ℝ)^3939
        have hw : |(1358673139/2500000000 : ℝ)|=(1358673139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_9 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523079857/1000000000 : ℝ)*x 0 + (-306779741/2000000000 : ℝ)*x 1 + (33966831/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523079857/1000000000 : ℝ)^4963 ≤ (22099155732321/50000000000000 : ℝ)^3939 := by
    have hnat : (523079857 : ℕ)^4963*50000000000000^3939 ≤ 22099155732321^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523079857 1000000000 22099155732321 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (306779741/2000000000 : ℝ)^4963 ≤ (9421775597033/100000000000000 : ℝ)^3939 := by
    have hnat : (306779741 : ℕ)^4963*100000000000000^3939 ≤ 9421775597033^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      306779741 2000000000 9421775597033 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33966831/62500000 : ℝ)^4963 ≤ (23189956460287/50000000000000 : ℝ)^3939 := by
    have hnat : (33966831 : ℕ)^4963*50000000000000^3939 ≤ 23189956460287^3939*62500000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33966831 62500000 23189956460287 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523079857/1000000000 : ℝ), (-306779741/2000000000 : ℝ), (33966831/62500000 : ℝ)] ![(22099155732321/50000000000000 : ℝ), (9421775597033/100000000000000 : ℝ), (23189956460287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523079857/1000000000 : ℝ)|^4963 ≤ (22099155732321/50000000000000 : ℝ)^3939
        have hw : |(523079857/1000000000 : ℝ)|=(523079857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-306779741/2000000000 : ℝ)|^4963 ≤ (9421775597033/100000000000000 : ℝ)^3939
        have hw : |(-306779741/2000000000 : ℝ)|=(306779741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33966831/62500000 : ℝ)|^4963 ≤ (23189956460287/50000000000000 : ℝ)^3939
        have hw : |(33966831/62500000 : ℝ)|=(33966831/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_10 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615399567/5000000000 : ℝ)*x 0 + (1086938527/2000000000 : ℝ)*x 1 + (-766949191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615399567/5000000000 : ℝ)^4963 ≤ (22099158734559/50000000000000 : ℝ)^3939 := by
    have hnat : (2615399567 : ℕ)^4963*50000000000000^3939 ≤ 22099158734559^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615399567 5000000000 22099158734559 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086938527/2000000000 : ℝ)^4963 ≤ (46379909425981/100000000000000 : ℝ)^3939 := by
    have hnat : (1086938527 : ℕ)^4963*100000000000000^3939 ≤ 46379909425981^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086938527 2000000000 46379909425981 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766949191/5000000000 : ℝ)^4963 ≤ (9421773097281/100000000000000 : ℝ)^3939 := by
    have hnat : (766949191 : ℕ)^4963*100000000000000^3939 ≤ 9421773097281^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766949191 5000000000 9421773097281 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615399567/5000000000 : ℝ), (1086938527/2000000000 : ℝ), (-766949191/5000000000 : ℝ)] ![(22099158734559/50000000000000 : ℝ), (46379909425981/100000000000000 : ℝ), (9421773097281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615399567/5000000000 : ℝ)|^4963 ≤ (22099158734559/50000000000000 : ℝ)^3939
        have hw : |(2615399567/5000000000 : ℝ)|=(2615399567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086938527/2000000000 : ℝ)|^4963 ≤ (46379909425981/100000000000000 : ℝ)^3939
        have hw : |(1086938527/2000000000 : ℝ)|=(1086938527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-766949191/5000000000 : ℝ)|^4963 ≤ (9421773097281/100000000000000 : ℝ)^3939
        have hw : |(-766949191/5000000000 : ℝ)|=(766949191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_11 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4532636381/10000000000 : ℝ)*x 0 + (400290107/1000000000 : ℝ)*x 1 + (800580079/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4532636381/10000000000 : ℝ)^4963 ≤ (36898976776911/100000000000000 : ℝ)^3939 := by
    have hnat : (4532636381 : ℕ)^4963*100000000000000^3939 ≤ 36898976776911^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532636381 10000000000 36898976776911 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400290107/1000000000 : ℝ)^4963 ≤ (6310102990849/20000000000000 : ℝ)^3939 := by
    have hnat : (400290107 : ℕ)^4963*20000000000000^3939 ≤ 6310102990849^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400290107 1000000000 6310102990849 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (800580079/2000000000 : ℝ)^4963 ≤ (7887627062717/25000000000000 : ℝ)^3939 := by
    have hnat : (800580079 : ℕ)^4963*25000000000000^3939 ≤ 7887627062717^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      800580079 2000000000 7887627062717 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4532636381/10000000000 : ℝ), (400290107/1000000000 : ℝ), (800580079/2000000000 : ℝ)] ![(36898976776911/100000000000000 : ℝ), (6310102990849/20000000000000 : ℝ), (7887627062717/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4532636381/10000000000 : ℝ)|^4963 ≤ (36898976776911/100000000000000 : ℝ)^3939
        have hw : |(4532636381/10000000000 : ℝ)|=(4532636381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400290107/1000000000 : ℝ)|^4963 ≤ (6310102990849/20000000000000 : ℝ)^3939
        have hw : |(400290107/1000000000 : ℝ)|=(400290107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(800580079/2000000000 : ℝ)|^4963 ≤ (7887627062717/25000000000000 : ℝ)^3939
        have hw : |(800580079/2000000000 : ℝ)|=(800580079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_12 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-359654019/2500000000 : ℝ)*x 0 + (5536696353/10000000000 : ℝ)*x 1 + (2598096397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (359654019/2500000000 : ℝ)^4963 ≤ (1738082990501/20000000000000 : ℝ)^3939 := by
    have hnat : (359654019 : ℕ)^4963*20000000000000^3939 ≤ 1738082990501^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359654019 2500000000 1738082990501 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5536696353/10000000000 : ℝ)^4963 ≤ (11869844348681/25000000000000 : ℝ)^3939 := by
    have hnat : (5536696353 : ℕ)^4963*25000000000000^3939 ≤ 11869844348681^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536696353 10000000000 11869844348681 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598096397/5000000000 : ℝ)^4963 ≤ (1369693988697/3125000000000 : ℝ)^3939 := by
    have hnat : (2598096397 : ℕ)^4963*3125000000000^3939 ≤ 1369693988697^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598096397 5000000000 1369693988697 3125000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-359654019/2500000000 : ℝ), (5536696353/10000000000 : ℝ), (2598096397/5000000000 : ℝ)] ![(1738082990501/20000000000000 : ℝ), (11869844348681/25000000000000 : ℝ), (1369693988697/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-359654019/2500000000 : ℝ)|^4963 ≤ (1738082990501/20000000000000 : ℝ)^3939
        have hw : |(-359654019/2500000000 : ℝ)|=(359654019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5536696353/10000000000 : ℝ)|^4963 ≤ (11869844348681/25000000000000 : ℝ)^3939
        have hw : |(5536696353/10000000000 : ℝ)|=(5536696353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598096397/5000000000 : ℝ)|^4963 ≤ (1369693988697/3125000000000 : ℝ)^3939
        have hw : |(2598096397/5000000000 : ℝ)|=(2598096397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_13 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394268477/10000000000 : ℝ)*x 0 + (-818346297/5000000000 : ℝ)*x 1 + (2598096071/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394268477/10000000000 : ℝ)^4963 ≤ (22972832965911/50000000000000 : ℝ)^3939 := by
    have hnat : (5394268477 : ℕ)^4963*50000000000000^3939 ≤ 22972832965911^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394268477 10000000000 22972832965911 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (818346297/5000000000 : ℝ)^4963 ≤ (10224133343211/100000000000000 : ℝ)^3939 := by
    have hnat : (818346297 : ℕ)^4963*100000000000000^3939 ≤ 10224133343211^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818346297 5000000000 10224133343211 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598096071/5000000000 : ℝ)^4963 ≤ (43830200708927/100000000000000 : ℝ)^3939 := by
    have hnat : (2598096071 : ℕ)^4963*100000000000000^3939 ≤ 43830200708927^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598096071 5000000000 43830200708927 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394268477/10000000000 : ℝ), (-818346297/5000000000 : ℝ), (2598096071/5000000000 : ℝ)] ![(22972832965911/50000000000000 : ℝ), (10224133343211/100000000000000 : ℝ), (43830200708927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394268477/10000000000 : ℝ)|^4963 ≤ (22972832965911/50000000000000 : ℝ)^3939
        have hw : |(5394268477/10000000000 : ℝ)|=(5394268477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-818346297/5000000000 : ℝ)|^4963 ≤ (10224133343211/100000000000000 : ℝ)^3939
        have hw : |(-818346297/5000000000 : ℝ)|=(818346297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598096071/5000000000 : ℝ)|^4963 ≤ (43830200708927/100000000000000 : ℝ)^3939
        have hw : |(2598096071/5000000000 : ℝ)|=(2598096071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_14 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394268831/10000000000 : ℝ)*x 0 + (2598095691/5000000000 : ℝ)*x 1 + (-1636693137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394268831/10000000000 : ℝ)^4963 ≤ (45945669730859/100000000000000 : ℝ)^3939 := by
    have hnat : (5394268831 : ℕ)^4963*100000000000000^3939 ≤ 45945669730859^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394268831 10000000000 45945669730859 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598095691/5000000000 : ℝ)^4963 ≤ (2191509631587/5000000000000 : ℝ)^3939 := by
    have hnat : (2598095691 : ℕ)^4963*5000000000000^3939 ≤ 2191509631587^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598095691 5000000000 2191509631587 5000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1636693137/10000000000 : ℝ)^4963 ≤ (2556034404261/25000000000000 : ℝ)^3939 := by
    have hnat : (1636693137 : ℕ)^4963*25000000000000^3939 ≤ 2556034404261^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636693137 10000000000 2556034404261 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394268831/10000000000 : ℝ), (2598095691/5000000000 : ℝ), (-1636693137/10000000000 : ℝ)] ![(45945669730859/100000000000000 : ℝ), (2191509631587/5000000000000 : ℝ), (2556034404261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394268831/10000000000 : ℝ)|^4963 ≤ (45945669730859/100000000000000 : ℝ)^3939
        have hw : |(5394268831/10000000000 : ℝ)|=(5394268831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598095691/5000000000 : ℝ)|^4963 ≤ (2191509631587/5000000000000 : ℝ)^3939
        have hw : |(2598095691/5000000000 : ℝ)|=(2598095691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1636693137/10000000000 : ℝ)|^4963 ≤ (2556034404261/25000000000000 : ℝ)^3939
        have hw : |(-1636693137/10000000000 : ℝ)|=(1636693137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_box_15 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1914789247/5000000000 : ℝ)*x 0 + (4354423663/10000000000 : ℝ)*x 1 + (4354422883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914789247/5000000000 : ℝ)^4963 ≤ (29839053621707/100000000000000 : ℝ)^3939 := by
    have hnat : (1914789247 : ℕ)^4963*100000000000000^3939 ≤ 29839053621707^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914789247 5000000000 29839053621707 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4354423663/10000000000 : ℝ)^4963 ≤ (17540238568569/50000000000000 : ℝ)^3939 := by
    have hnat : (4354423663 : ℕ)^4963*50000000000000^3939 ≤ 17540238568569^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354423663 10000000000 17540238568569 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4354422883/10000000000 : ℝ)^4963 ≤ (7016093843929/20000000000000 : ℝ)^3939 := by
    have hnat : (4354422883 : ℕ)^4963*20000000000000^3939 ≤ 7016093843929^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4354422883 10000000000 7016093843929 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1914789247/5000000000 : ℝ), (4354423663/10000000000 : ℝ), (4354422883/10000000000 : ℝ)] ![(29839053621707/100000000000000 : ℝ), (17540238568569/50000000000000 : ℝ), (7016093843929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1914789247/5000000000 : ℝ)|^4963 ≤ (29839053621707/100000000000000 : ℝ)^3939
        have hw : |(1914789247/5000000000 : ℝ)|=(1914789247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4354423663/10000000000 : ℝ)|^4963 ≤ (17540238568569/50000000000000 : ℝ)^3939
        have hw : |(4354423663/10000000000 : ℝ)|=(4354423663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4354422883/10000000000 : ℝ)|^4963 ≤ (7016093843929/20000000000000 : ℝ)^3939
        have hw : |(4354422883/10000000000 : ℝ)|=(4354422883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1661_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13023/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7343/12500 : ℝ) ∧ (40697/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88329/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5363/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5363/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5363/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5363/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5363/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5363/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5363/50000 : ℝ) ^ (4959/1024 : ℝ) ≤ (1008323526669379/50000000000000000000 : ℝ) := by
    have hpowers : (5363/50000 : ℝ)^4959 ≤ (1008323526669379/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5363 : ℕ)^4959*50000000000000000000^1024 ≤ 1008323526669379^1024*50000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5363 50000 1008323526669379 50000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5363/50000 : ℝ)) (X := (1008323526669379/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8123/50000 : ℝ) ^ (4959/1024 : ℝ) ≤ (15059961696173083/100000000000000000000 : ℝ) := by
    have hpowers : (8123/50000 : ℝ)^4959 ≤ (15059961696173083/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8123 : ℕ)^4959*100000000000000000000^1024 ≤ 15059961696173083^1024*50000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8123 50000 15059961696173083 100000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8123/50000 : ℝ)) (X := (15059961696173083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001008323526669379/25000000000000000000 : ℝ) ≤ (1250010410433243/1250000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (25001008323526669379/25000000000000000000 : ℝ)^1024 ≤ (1250010410433243/1250000000000000 : ℝ)^4959 := by
      have hnat : (25001008323526669379 : ℕ)^1024*1250000000000000^4959 ≤ 1250010410433243^4959*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001008323526669379 25000000000000000000 1250010410433243 1250000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250010410433243/1250000000000000 : ℝ)) (X := (25001008323526669379/25000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017076608749511841/100000000000000000000 : ℝ) ≤ (10000352596546447/10000000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (100017076608749511841/100000000000000000000 : ℝ)^1024 ≤ (10000352596546447/10000000000000000 : ℝ)^4959 := by
      have hnat : (100017076608749511841 : ℕ)^1024*10000000000000000^4959 ≤ 10000352596546447^4959*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017076608749511841 100000000000000000000 10000352596546447 10000000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000352596546447/10000000000000000 : ℝ)) (X := (100017076608749511841/100000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015059961696173083/50000000000000000000 : ℝ) ≤ (200012438192539/200000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (50015059961696173083/50000000000000000000 : ℝ)^1024 ≤ (200012438192539/200000000000000 : ℝ)^4959 := by
      have hnat : (50015059961696173083 : ℕ)^1024*200000000000000^4959 ≤ 200012438192539^4959*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015059961696173083 50000000000000000000 200012438192539 200000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200012438192539/200000000000000 : ℝ)) (X := (50015059961696173083/50000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1008323526669379/50000000000000000000 : ℝ) ≤ ((13798670605132265131/13800000000000000000 : ℝ)+2*(269313080503/552000000000000 : ℝ)*(5363/50000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (13798670605132265131/13800000000000000000 : ℝ)+2*(269313080503/552000000000000 : ℝ)*(5363/50000 : ℝ)=(1250010410433243/1250000000000000 : ℝ) by norm_num, show 1+2*(1008323526669379/50000000000000000000 : ℝ)=(25001008323526669379/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15059961696173083/100000000000000000000 : ℝ)+(1008323526669379/50000000000000000000 : ℝ) ≤ ((13798670605132265131/13800000000000000000 : ℝ)+(269313080503/552000000000000 : ℝ)*((8123/50000 : ℝ)+(5363/50000 : ℝ)))^(4959/1024 : ℝ) := by
    rw [show (13798670605132265131/13800000000000000000 : ℝ)+(269313080503/552000000000000 : ℝ)*((8123/50000 : ℝ)+(5363/50000 : ℝ))=(10000352596546447/10000000000000000 : ℝ) by norm_num, show 1+(15059961696173083/100000000000000000000 : ℝ)+(1008323526669379/50000000000000000000 : ℝ)=(100017076608749511841/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15059961696173083/100000000000000000000 : ℝ) ≤ ((13798670605132265131/13800000000000000000 : ℝ)+2*(269313080503/552000000000000 : ℝ)*(8123/50000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (13798670605132265131/13800000000000000000 : ℝ)+2*(269313080503/552000000000000 : ℝ)*(8123/50000 : ℝ)=(200012438192539/200000000000000 : ℝ) by norm_num, show 1+2*(15059961696173083/100000000000000000000 : ℝ)=(50015059961696173083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13798670605132265131/13800000000000000000 : ℝ)*(X 1 0+X 2 0)+(269313080503/552000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (5363/50000 : ℝ)) (hi := (8123/50000 : ℝ)) (c := (13798670605132265131/13800000000000000000 : ℝ)) (alpha := (269313080503/552000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13798670605132265131/13800000000000000000 : ℝ)*(X 0 1+X 2 1)+(269313080503/552000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (5363/50000 : ℝ)) (hi := (8123/50000 : ℝ)) (c := (13798670605132265131/13800000000000000000 : ℝ)) (alpha := (269313080503/552000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13798670605132265131/13800000000000000000 : ℝ)*(X 0 2+X 1 2)+(269313080503/552000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (5363/50000 : ℝ)) (hi := (8123/50000 : ℝ)) (c := (13798670605132265131/13800000000000000000 : ℝ)) (alpha := (269313080503/552000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-664884573/5000000000 : ℝ)*X 0 0+(5405374029/10000000000 : ℝ)*X 0 1+(216214879/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5250891553/10000000000 : ℝ)*X 1 0+(-1546938077/10000000000 : ℝ)*X 1 1+(540537279/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((328180719/625000000 : ℝ)*X 2 0+(5405372473/10000000000 : ℝ)*X 2 1+(-309387717/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4448487969/10000000000 : ℝ)*X 0 0+(404619109/1000000000 : ℝ)*X 0 1+(4046189903/10000000000 : ℝ)*X 0 2+(4448487969/10000000000 : ℝ)*X 1 0+(404619109/1000000000 : ℝ)*X 1 1+(4046189903/10000000000 : ℝ)*X 1 2+(4448487969/10000000000 : ℝ)*X 2 0+(404619109/1000000000 : ℝ)*X 2 1+(4046189903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1848532831/10000000000 : ℝ)*X 0 0+(5215984929/10000000000 : ℝ)*X 0 1+(208639383/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345173157/2500000000 : ℝ)*X 1 0+(-814226163/5000000000 : ℝ)*X 1 1+(1303996239/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380693043/10000000000 : ℝ)*X 2 0+(1303996131/2500000000 : ℝ)*X 2 1+(-814226173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((777923063/2000000000 : ℝ)*X 0 0+(2162653159/5000000000 : ℝ)*X 0 1+(173012253/400000000 : ℝ)*X 0 2+(777923063/2000000000 : ℝ)*X 1 0+(2162653159/5000000000 : ℝ)*X 1 1+(173012253/400000000 : ℝ)*X 1 2+(777923063/2000000000 : ℝ)*X 2 0+(2162653159/5000000000 : ℝ)*X 2 1+(173012253/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-69511693/400000000 : ℝ)*X 0 0+(2539763203/5000000000 : ℝ)*X 0 1+(1358673139/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((523079857/1000000000 : ℝ)*X 1 0+(-306779741/2000000000 : ℝ)*X 1 1+(33966831/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615399567/5000000000 : ℝ)*X 2 0+(1086938527/2000000000 : ℝ)*X 2 1+(-766949191/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4532636381/10000000000 : ℝ)*X 0 0+(400290107/1000000000 : ℝ)*X 0 1+(800580079/2000000000 : ℝ)*X 0 2+(4532636381/10000000000 : ℝ)*X 1 0+(400290107/1000000000 : ℝ)*X 1 1+(800580079/2000000000 : ℝ)*X 1 2+(4532636381/10000000000 : ℝ)*X 2 0+(400290107/1000000000 : ℝ)*X 2 1+(800580079/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-359654019/2500000000 : ℝ)*X 0 0+(5536696353/10000000000 : ℝ)*X 0 1+(2598096397/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5394268477/10000000000 : ℝ)*X 1 0+(-818346297/5000000000 : ℝ)*X 1 1+(2598096071/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5394268831/10000000000 : ℝ)*X 2 0+(2598095691/5000000000 : ℝ)*X 2 1+(-1636693137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1914789247/5000000000 : ℝ)*X 0 0+(4354423663/10000000000 : ℝ)*X 0 1+(4354422883/10000000000 : ℝ)*X 0 2+(1914789247/5000000000 : ℝ)*X 1 0+(4354423663/10000000000 : ℝ)*X 1 1+(4354422883/10000000000 : ℝ)*X 1 2+(1914789247/5000000000 : ℝ)*X 2 0+(4354423663/10000000000 : ℝ)*X 2 1+(4354422883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13023/20000 : ℝ) ≤ (-4679937553802439378642526483777/7187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3442679/100000000000000 : ℝ)*(lower2) + (2218021/6250000000000 : ℝ)*(upper4) + (19303649/50000000000000 : ℝ)*(upper5) + (111237117820067/6250000000000 : ℝ)*(major0) + (111237117820067/6250000000000 : ℝ)*(major1) + (111237117820067/6250000000000 : ℝ)*(major2) + (2354353419/50000000000000 : ℝ)*(sp2) + (231628917/25000000000000 : ℝ)*(sp3) + (649706957748741/25000000000000 : ℝ)*(sp4) + (2598826092212299/100000000000000 : ℝ)*(sp5) + (1299413564784197/50000000000000 : ℝ)*(sp6) + (245614765917943/25000000000000 : ℝ)*(sp7) + (1001820067/25000000000000 : ℝ)*(sp8) + (5746062933/100000000000000 : ℝ)*(sp13) + (12280749877343/1250000000000 : ℝ)*(f.failure) + (81213494946101/3125000000000 : ℝ)*(f.sum) + (18142616143099/1725000000000000000000000000 : ℝ)*base66 + (519570001663708777/86250000000000000000000000000000 : ℝ)*base67 + (367415045653708777/86250000000000000000000000000000 : ℝ)*base69 + (499281695892541223/86250000000000000000000000000000 : ℝ)*base72 + (4234109592799/1725000000000000000000000000 : ℝ)*base74 + (470718307506208777/86250000000000000000000000000000 : ℝ)*base75 + (717784077621208777/86250000000000000000000000000000 : ℝ)*base77 + (294634273971208777/86250000000000000000000000000000 : ℝ)*base79 + (2907038820049/1725000000000000000000000000 : ℝ)*base82 + (162263/62500000000000000000 : ℝ)*base89 + (162263/62500000000000000000 : ℝ)*base91 + (162263/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (7343/12500 : ℝ) ≤ (67558658088168296688174438199461/115000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21443593/100000000000000 : ℝ)*(lower1) + (38726919/25000000000000 : ℝ)*(upper3) + (134147717/100000000000000 : ℝ)*(lower5) + (935880608488431/50000000000000 : ℝ)*(major0) + (935880608488431/50000000000000 : ℝ)*(major1) + (935880608488431/50000000000000 : ℝ)*(major2) + (2690703783792337/100000000000000 : ℝ)*(sp0) + (269071278942159/10000000000000 : ℝ)*(sp1) + (2690711773681639/100000000000000 : ℝ)*(sp2) + (258306467729913/25000000000000 : ℝ)*(sp3) + (756114379/100000000000000 : ℝ)*(sp5) + (177185433/10000000000000 : ℝ)*(sp6) + (99720299/12500000000000 : ℝ)*(sp7) + (610108977/6250000000000 : ℝ)*(sp8) + (258306667170511/25000000000000 : ℝ)*(f.failure) + (269071354553597/10000000000000 : ℝ)*(f.sum) + (6891810723331/4600000000000000000000000000 : ℝ)*base65 + (1037915139210658513/230000000000000000000000000000000 : ℝ)*base68 + (3255461616270658513/230000000000000000000000000000000 : ℝ)*base70 + (397634664480658513/230000000000000000000000000000000 : ℝ)*base72 + (1342491767731/4600000000000000000000000000 : ℝ)*base73 + (1013757291380658513/230000000000000000000000000000000 : ℝ)*base76 + (529404723799341487/230000000000000000000000000000000 : ℝ)*base77 + (230960406329341487/230000000000000000000000000000000 : ℝ)*base79 + (3488836753669/4600000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7446649/1250000000000000000000 : ℝ)*base90 + (7446649/1250000000000000000000 : ℝ)*base92 + (7446649/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40697/50000 : ℝ) ≤ (3744254724656311993544764581/4600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1815343/4000000000000 : ℝ)*(lower3) + (33127777/20000000000000 : ℝ)*(upper4) + (32037259/100000000000000 : ℝ)*(lower5) + (981607579608573/50000000000000 : ℝ)*(major0) + (981607579608573/50000000000000 : ℝ)*(major1) + (981607579608573/50000000000000 : ℝ)*(major2) + (304073863/25000000000000 : ℝ)*(sp0) + (55490668219/100000000000000 : ℝ)*(sp1) + (5889649777/10000000000000 : ℝ)*(sp2) + (8544960031/50000000000000 : ℝ)*(sp3) + (703896717346811/25000000000000 : ℝ)*(sp8) + (2815532595014477/100000000000000 : ℝ)*(sp9) + (2815529189184927/100000000000000 : ℝ)*(sp10) + (541846431109039/50000000000000 : ℝ)*(sp11) + (54185497606907/5000000000000 : ℝ)*(f.failure) + (351948510710337/12500000000000 : ℝ)*(f.sum) + (112850134327/4600000000000000000000000000 : ℝ)*base66 + (862628936120681021/230000000000000000000000000000000 : ℝ)*base67 + (127821268080681021/230000000000000000000000000000000 : ℝ)*base69 + (190911267509318979/230000000000000000000000000000000 : ℝ)*base72 + (19698612080873/4600000000000000000000000000 : ℝ)*base73 + (49292467900681021/230000000000000000000000000000000 : ℝ)*base75 + (1863436146739318979/230000000000000000000000000000000 : ℝ)*base78 + (1371732900969318979/230000000000000000000000000000000 : ℝ)*base80 + (15395002316873/4600000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1891987/250000000000000000000 : ℝ)*base89 + (1891987/250000000000000000000 : ℝ)*base91 + (1891987/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-88329/100000 : ℝ) ≤ (-4063039718277976266745978632231/4600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122923797/50000000000000 : ℝ)*(upper3) + (320521/3125000000000 : ℝ)*(lower4) + (13856007/20000000000000 : ℝ)*(upper5) + (40157667338633/2000000000000 : ℝ)*(major0) + (40157667338633/2000000000000 : ℝ)*(major1) + (40157667338633/2000000000000 : ℝ)*(major2) + (2878753679/25000000000000 : ℝ)*(sp4) + (232468182987/100000000000000 : ℝ)*(sp5) + (316604951889/100000000000000 : ℝ)*(sp6) + (10270384273/10000000000000 : ℝ)*(sp7) + (367103798421287/12500000000000 : ℝ)*(sp12) + (367076179275253/12500000000000 : ℝ)*(sp13) + (1468262648716561/50000000000000 : ℝ)*(sp14) + (277066111108667/25000000000000 : ℝ)*(sp15) + (554183574138699/50000000000000 : ℝ)*(f.failure) + (2936841902385011/100000000000000 : ℝ)*(f.sum) + (1617411516001/552000000000000000000000000 : ℝ)*base66 + (398214251832519077/27600000000000000000000000000000 : ℝ)*base68 + (239579529751719077/27600000000000000000000000000000 : ℝ)*base70 + (155728781412519077/27600000000000000000000000000000 : ℝ)*base72 + (3513039438913/552000000000000000000000000 : ℝ)*base74 + (12088910417319077/27600000000000000000000000000000 : ℝ)*base76 + (55952333982519077/27600000000000000000000000000000 : ℝ)*base78 + (96087395981319077/27600000000000000000000000000000 : ℝ)*base80 + (2447227229473/552000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (23188259/2500000000000000000000 : ℝ)*base89 + (23188259/2500000000000000000000 : ℝ)*base91 + (23188259/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1661_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13023/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(7343/12500 : ℝ) else (40697/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88329/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1661_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1661_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2667/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13023/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(7343/12500 : ℝ) else (40697/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88329/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1661_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1661_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1661_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2667/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13023/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(7343/12500 : ℝ) else (40697/50000 : ℝ) ≤ X j i ∧ X j i ≤ (88329/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1661_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
