-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1706_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:57.496236+00:00
-- url     : https://prove2.me/submissions/5ae86671-2dfe-42c6-bef1-83be97e5cab9

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
theorem support_rectangle_w1706_s0_0 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1348450541/10000000000 : ℝ)*x 0 + (1426480753/2500000000 : ℝ)*x 1 + (4955928251/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348450541/10000000000 : ℝ)^5271 ≤ (1039772584973/12500000000000 : ℝ)^4247 := by
    have hnat : (1348450541 : ℕ)^5271*12500000000000^4247 ≤ 1039772584973^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348450541 10000000000 1039772584973 12500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426480753/2500000000 : ℝ)^5271 ≤ (49839458217521/100000000000000 : ℝ)^4247 := by
    have hnat : (1426480753 : ℕ)^5271*100000000000000^4247 ≤ 49839458217521^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426480753 2500000000 49839458217521 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4955928251/10000000000 : ℝ)^5271 ≤ (10460590272357/25000000000000 : ℝ)^4247 := by
    have hnat : (4955928251 : ℕ)^5271*25000000000000^4247 ≤ 10460590272357^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4955928251 10000000000 10460590272357 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1348450541/10000000000 : ℝ), (1426480753/2500000000 : ℝ), (4955928251/10000000000 : ℝ)] ![(1039772584973/12500000000000 : ℝ), (49839458217521/100000000000000 : ℝ), (10460590272357/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1348450541/10000000000 : ℝ)|^5271 ≤ (1039772584973/12500000000000 : ℝ)^4247
        have hw : |(-1348450541/10000000000 : ℝ)|=(1348450541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426480753/2500000000 : ℝ)|^5271 ≤ (49839458217521/100000000000000 : ℝ)^4247
        have hw : |(1426480753/2500000000 : ℝ)|=(1426480753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4955928251/10000000000 : ℝ)|^5271 ≤ (10460590272357/25000000000000 : ℝ)^4247
        have hw : |(4955928251/10000000000 : ℝ)|=(4955928251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s0_1 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351771081/2500000000 : ℝ)*x 0 + (-1755104919/10000000000 : ℝ)*x 1 + (4955927657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351771081/2500000000 : ℝ)^5271 ≤ (46620563575197/100000000000000 : ℝ)^4247 := by
    have hnat : (1351771081 : ℕ)^5271*100000000000000^4247 ≤ 46620563575197^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351771081 2500000000 46620563575197 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1755104919/10000000000 : ℝ)^5271 ≤ (2884270387673/25000000000000 : ℝ)^4247 := by
    have hnat : (1755104919 : ℕ)^5271*25000000000000^4247 ≤ 2884270387673^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755104919 10000000000 2884270387673 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4955927657/10000000000 : ℝ)^5271 ≤ (41842354865159/100000000000000 : ℝ)^4247 := by
    have hnat : (4955927657 : ℕ)^5271*100000000000000^4247 ≤ 41842354865159^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4955927657 10000000000 41842354865159 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351771081/2500000000 : ℝ), (-1755104919/10000000000 : ℝ), (4955927657/10000000000 : ℝ)] ![(46620563575197/100000000000000 : ℝ), (2884270387673/25000000000000 : ℝ), (41842354865159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351771081/2500000000 : ℝ)|^5271 ≤ (46620563575197/100000000000000 : ℝ)^4247
        have hw : |(1351771081/2500000000 : ℝ)|=(1351771081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1755104919/10000000000 : ℝ)|^5271 ≤ (2884270387673/25000000000000 : ℝ)^4247
        have hw : |(-1755104919/10000000000 : ℝ)|=(1755104919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4955927657/10000000000 : ℝ)|^5271 ≤ (41842354865159/100000000000000 : ℝ)^4247
        have hw : |(4955927657/10000000000 : ℝ)|=(4955927657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s0_2 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2703541611/5000000000 : ℝ)*x 0 + (2477964191/5000000000 : ℝ)*x 1 + (-1755105433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2703541611/5000000000 : ℝ)^5271 ≤ (1864822071307/4000000000000 : ℝ)^4247 := by
    have hnat : (2703541611 : ℕ)^5271*4000000000000^4247 ≤ 1864822071307^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703541611 5000000000 1864822071307 4000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2477964191/5000000000 : ℝ)^5271 ≤ (1046059061553/2500000000000 : ℝ)^4247 := by
    have hnat : (2477964191 : ℕ)^5271*2500000000000^4247 ≤ 1046059061553^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2477964191 5000000000 1046059061553 2500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1755105433/10000000000 : ℝ)^5271 ≤ (360533929503/3125000000000 : ℝ)^4247 := by
    have hnat : (1755105433 : ℕ)^5271*3125000000000^4247 ≤ 360533929503^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755105433 10000000000 360533929503 3125000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2703541611/5000000000 : ℝ), (2477964191/5000000000 : ℝ), (-1755105433/10000000000 : ℝ)] ![(1864822071307/4000000000000 : ℝ), (1046059061553/2500000000000 : ℝ), (360533929503/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2703541611/5000000000 : ℝ)|^5271 ≤ (1864822071307/4000000000000 : ℝ)^4247
        have hw : |(2703541611/5000000000 : ℝ)|=(2703541611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2477964191/5000000000 : ℝ)|^5271 ≤ (1046059061553/2500000000000 : ℝ)^4247
        have hw : |(2477964191/5000000000 : ℝ)|=(2477964191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1755105433/10000000000 : ℝ)|^5271 ≤ (360533929503/3125000000000 : ℝ)^4247
        have hw : |(-1755105433/10000000000 : ℝ)|=(1755105433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s0_3 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (505366967/1250000000 : ℝ)*x 0 + (1528294953/5000000000 : ℝ)*x 1 + (5211166697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (505366967/1250000000 : ℝ)^5271 ≤ (6499754726723/20000000000000 : ℝ)^4247 := by
    have hnat : (505366967 : ℕ)^5271*20000000000000^4247 ≤ 6499754726723^4247*1250000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505366967 1250000000 6499754726723 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1528294953/5000000000 : ℝ)^5271 ≤ (1148396889307/5000000000000 : ℝ)^4247 := by
    have hnat : (1528294953 : ℕ)^5271*5000000000000^4247 ≤ 1148396889307^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1528294953 5000000000 1148396889307 5000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5211166697/10000000000 : ℝ)^5271 ≤ (695832633793/1562500000000 : ℝ)^4247 := by
    have hnat : (5211166697 : ℕ)^5271*1562500000000^4247 ≤ 695832633793^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5211166697 10000000000 695832633793 1562500000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(505366967/1250000000 : ℝ), (1528294953/5000000000 : ℝ), (5211166697/10000000000 : ℝ)] ![(6499754726723/20000000000000 : ℝ), (1148396889307/5000000000000 : ℝ), (695832633793/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(505366967/1250000000 : ℝ)|^5271 ≤ (6499754726723/20000000000000 : ℝ)^4247
        have hw : |(505366967/1250000000 : ℝ)|=(505366967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1528294953/5000000000 : ℝ)|^5271 ≤ (1148396889307/5000000000000 : ℝ)^4247
        have hw : |(1528294953/5000000000 : ℝ)|=(1528294953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5211166697/10000000000 : ℝ)|^5271 ≤ (695832633793/1562500000000 : ℝ)^4247
        have hw : |(5211166697/10000000000 : ℝ)|=(5211166697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s0_4 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1350183669/10000000000 : ℝ)*x 0 + (4974439019/10000000000 : ℝ)*x 1 + (5686790663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350183669/10000000000 : ℝ)^5271 ≤ (1666290325799/20000000000000 : ℝ)^4247 := by
    have hnat : (1350183669 : ℕ)^5271*20000000000000^4247 ≤ 1666290325799^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350183669 10000000000 1666290325799 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4974439019/10000000000 : ℝ)^5271 ≤ (5254551835587/12500000000000 : ℝ)^4247 := by
    have hnat : (4974439019 : ℕ)^5271*12500000000000^4247 ≤ 5254551835587^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974439019 10000000000 5254551835587 12500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5686790663/10000000000 : ℝ)^5271 ≤ (49632133675581/100000000000000 : ℝ)^4247 := by
    have hnat : (5686790663 : ℕ)^5271*100000000000000^4247 ≤ 49632133675581^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5686790663 10000000000 49632133675581 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1350183669/10000000000 : ℝ), (4974439019/10000000000 : ℝ), (5686790663/10000000000 : ℝ)] ![(1666290325799/20000000000000 : ℝ), (5254551835587/12500000000000 : ℝ), (49632133675581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1350183669/10000000000 : ℝ)|^5271 ≤ (1666290325799/20000000000000 : ℝ)^4247
        have hw : |(-1350183669/10000000000 : ℝ)|=(1350183669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4974439019/10000000000 : ℝ)|^5271 ≤ (5254551835587/12500000000000 : ℝ)^4247
        have hw : |(4974439019/10000000000 : ℝ)|=(4974439019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5686790663/10000000000 : ℝ)|^5271 ≤ (49632133675581/100000000000000 : ℝ)^4247
        have hw : |(5686790663/10000000000 : ℝ)|=(5686790663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s0_5 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10163637/19531250 : ℝ)*x 0 + (-256060569/2500000000 : ℝ)*x 1 + (2843395339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10163637/19531250 : ℝ)^5271 ≤ (44454979767529/100000000000000 : ℝ)^4247 := by
    have hnat : (10163637 : ℕ)^5271*100000000000000^4247 ≤ 44454979767529^4247*19531250^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10163637 19531250 44454979767529 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256060569/2500000000 : ℝ)^5271 ≤ (2956443187743/50000000000000 : ℝ)^4247 := by
    have hnat : (256060569 : ℕ)^5271*50000000000000^4247 ≤ 2956443187743^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256060569 2500000000 2956443187743 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2843395339/5000000000 : ℝ)^5271 ≤ (2481606691903/5000000000000 : ℝ)^4247 := by
    have hnat : (2843395339 : ℕ)^5271*5000000000000^4247 ≤ 2481606691903^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2843395339 5000000000 2481606691903 5000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10163637/19531250 : ℝ), (-256060569/2500000000 : ℝ), (2843395339/5000000000 : ℝ)] ![(44454979767529/100000000000000 : ℝ), (2956443187743/50000000000000 : ℝ), (2481606691903/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10163637/19531250 : ℝ)|^5271 ≤ (44454979767529/100000000000000 : ℝ)^4247
        have hw : |(10163637/19531250 : ℝ)|=(10163637/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256060569/2500000000 : ℝ)|^5271 ≤ (2956443187743/50000000000000 : ℝ)^4247
        have hw : |(-256060569/2500000000 : ℝ)|=(256060569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2843395339/5000000000 : ℝ)|^5271 ≤ (2481606691903/5000000000000 : ℝ)^4247
        have hw : |(2843395339/5000000000 : ℝ)|=(2843395339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s0_6 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (260189097/500000000 : ℝ)*x 0 + (1137358257/2000000000 : ℝ)*x 1 + (-1024241661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (260189097/500000000 : ℝ)^5271 ≤ (222274888023/500000000000 : ℝ)^4247 := by
    have hnat : (260189097 : ℕ)^5271*500000000000^4247 ≤ 222274888023^4247*500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260189097 500000000 222274888023 500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1137358257/2000000000 : ℝ)^5271 ≤ (49632140413051/100000000000000 : ℝ)^4247 := by
    have hnat : (1137358257 : ℕ)^5271*100000000000000^4247 ≤ 49632140413051^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137358257 2000000000 49632140413051 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1024241661/10000000000 : ℝ)^5271 ≤ (5912881969099/100000000000000 : ℝ)^4247 := by
    have hnat : (1024241661 : ℕ)^5271*100000000000000^4247 ≤ 5912881969099^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024241661 10000000000 5912881969099 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(260189097/500000000 : ℝ), (1137358257/2000000000 : ℝ), (-1024241661/10000000000 : ℝ)] ![(222274888023/500000000000 : ℝ), (49632140413051/100000000000000 : ℝ), (5912881969099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(260189097/500000000 : ℝ)|^5271 ≤ (222274888023/500000000000 : ℝ)^4247
        have hw : |(260189097/500000000 : ℝ)|=(260189097/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1137358257/2000000000 : ℝ)|^5271 ≤ (49632140413051/100000000000000 : ℝ)^4247
        have hw : |(1137358257/2000000000 : ℝ)|=(1137358257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1024241661/10000000000 : ℝ)|^5271 ≤ (5912881969099/100000000000000 : ℝ)^4247
        have hw : |(-1024241661/10000000000 : ℝ)|=(1024241661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s0_7 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4047910673/10000000000 : ℝ)*x 0 + (1031597921/2000000000 : ℝ)*x 1 + (3111550851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4047910673/10000000000 : ℝ)^5271 ≤ (16274206879901/50000000000000 : ℝ)^4247 := by
    have hnat : (4047910673 : ℕ)^5271*50000000000000^4247 ≤ 16274206879901^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4047910673 10000000000 16274206879901 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031597921/2000000000 : ℝ)^5271 ≤ (43969976367567/100000000000000 : ℝ)^4247 := by
    have hnat : (1031597921 : ℕ)^5271*100000000000000^4247 ≤ 43969976367567^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031597921 2000000000 43969976367567 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3111550851/10000000000 : ℝ)^5271 ≤ (23481609852047/100000000000000 : ℝ)^4247 := by
    have hnat : (3111550851 : ℕ)^5271*100000000000000^4247 ≤ 23481609852047^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3111550851 10000000000 23481609852047 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4047910673/10000000000 : ℝ), (1031597921/2000000000 : ℝ), (3111550851/10000000000 : ℝ)] ![(16274206879901/50000000000000 : ℝ), (43969976367567/100000000000000 : ℝ), (23481609852047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4047910673/10000000000 : ℝ)|^5271 ≤ (16274206879901/50000000000000 : ℝ)^4247
        have hw : |(4047910673/10000000000 : ℝ)|=(4047910673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031597921/2000000000 : ℝ)|^5271 ≤ (43969976367567/100000000000000 : ℝ)^4247
        have hw : |(1031597921/2000000000 : ℝ)|=(1031597921/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3111550851/10000000000 : ℝ)|^5271 ≤ (23481609852047/100000000000000 : ℝ)^4247
        have hw : |(3111550851/10000000000 : ℝ)|=(3111550851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1706_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5933/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (441/2000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (5263/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5263 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5263*1^1024 ≤ 0^1024*1^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5263/1024 : ℝ) ≤ (112625898637239021/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5263 ≤ (112625898637239021/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5263*12500000000000000000^1024 ≤ 112625898637239021^1024*5^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 112625898637239021 12500000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (112625898637239021/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5263 := by
      have hnat : (1 : ℕ)^1024*1^5263 ≤ 1^5263*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12612625898637239021/12500000000000000000 : ℝ) ≤ (10017467254865661/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (12612625898637239021/12500000000000000000 : ℝ)^1024 ≤ (10017467254865661/10000000000000000 : ℝ)^5263 := by
      have hnat : (12612625898637239021 : ℕ)^1024*10000000000000000^5263 ≤ 10017467254865661^5263*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12612625898637239021 12500000000000000000 10017467254865661 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10017467254865661/10000000000000000 : ℝ)) (X := (12612625898637239021/12500000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6362625898637239021/6250000000000000000 : ℝ) ≤ (5017467254865661/5000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (6362625898637239021/6250000000000000000 : ℝ)^1024 ≤ (5017467254865661/5000000000000000 : ℝ)^5263 := by
      have hnat : (6362625898637239021 : ℕ)^1024*5000000000000000^5263 ≤ 5017467254865661^5263*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6362625898637239021 6250000000000000000 5017467254865661 5000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017467254865661/5000000000000000 : ℝ)) (X := (6362625898637239021/6250000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17467254865661/4000000000000000 : ℝ)*(0 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17467254865661/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(112625898637239021/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17467254865661/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5263/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17467254865661/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10017467254865661/10000000000000000 : ℝ) by norm_num, show 1+(112625898637239021/12500000000000000000 : ℝ)+(0 : ℝ)=(12612625898637239021/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(112625898637239021/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17467254865661/4000000000000000 : ℝ)*(2/5 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17467254865661/4000000000000000 : ℝ)*(2/5 : ℝ)=(5017467254865661/5000000000000000 : ℝ) by norm_num, show 1+2*(112625898637239021/12500000000000000000 : ℝ)=(6362625898637239021/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17467254865661/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17467254865661/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17467254865661/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17467254865661/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17467254865661/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17467254865661/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1348450541/10000000000 : ℝ)*X 0 0+(1426480753/2500000000 : ℝ)*X 0 1+(4955928251/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1351771081/2500000000 : ℝ)*X 1 0+(-1755104919/10000000000 : ℝ)*X 1 1+(4955927657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2703541611/5000000000 : ℝ)*X 2 0+(2477964191/5000000000 : ℝ)*X 2 1+(-1755105433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((505366967/1250000000 : ℝ)*X 0 0+(1528294953/5000000000 : ℝ)*X 0 1+(5211166697/10000000000 : ℝ)*X 0 2+(505366967/1250000000 : ℝ)*X 1 0+(1528294953/5000000000 : ℝ)*X 1 1+(5211166697/10000000000 : ℝ)*X 1 2+(505366967/1250000000 : ℝ)*X 2 0+(1528294953/5000000000 : ℝ)*X 2 1+(5211166697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1350183669/10000000000 : ℝ)*X 0 0+(4974439019/10000000000 : ℝ)*X 0 1+(5686790663/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10163637/19531250 : ℝ)*X 1 0+(-256060569/2500000000 : ℝ)*X 1 1+(2843395339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((260189097/500000000 : ℝ)*X 2 0+(1137358257/2000000000 : ℝ)*X 2 1+(-1024241661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4047910673/10000000000 : ℝ)*X 0 0+(1031597921/2000000000 : ℝ)*X 0 1+(3111550851/10000000000 : ℝ)*X 0 2+(4047910673/10000000000 : ℝ)*X 1 0+(1031597921/2000000000 : ℝ)*X 1 1+(3111550851/10000000000 : ℝ)*X 1 2+(4047910673/10000000000 : ℝ)*X 2 0+(1031597921/2000000000 : ℝ)*X 2 1+(3111550851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109024815294455885953593/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32816537/20000000000000 : ℝ)*(base1) + (7411921/100000000000000 : ℝ)*(base16) + (97217153/10000000000000 : ℝ)*(base19) + (353919213/50000000000000 : ℝ)*(base23) + (47268933/20000000000000 : ℝ)*(upper3) + (449369365583329/50000000000000 : ℝ)*(major0) + (449369365583329/50000000000000 : ℝ)*(major1) + (449369365583329/50000000000000 : ℝ)*(major2) + (666673263016219/50000000000000 : ℝ)*(sp0) + (666673305753991/50000000000000 : ℝ)*(sp1) + (1333346883253007/100000000000000 : ℝ)*(sp2) + (464128596040517/100000000000000 : ℝ)*(sp3) + (1229141679/100000000000000 : ℝ)*(sp4) + (193150451/20000000000000 : ℝ)*(sp7) + (464129725875457/100000000000000 : ℝ)*(f.failure) + (166668448886429/12500000000000 : ℝ)*(f.sum) + (270804404365469/100000000000000000000000000000 : ℝ)*base65 + (187395429365469/200000000000000000000000000000 : ℝ)*base67 + (555902702365469/200000000000000000000000000000 : ℝ)*base69 + (48732662834531/200000000000000000000000000000 : ℝ)*base72 + (709332074265469/100000000000000000000000000000 : ℝ)*base73 + (75480890565469/200000000000000000000000000000 : ℝ)*base75 + (59732459965469/200000000000000000000000000000 : ℝ)*base77 + (800346274034531/200000000000000000000000000000 : ℝ)*base80 + (414769363865469/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (23486911/5000000000000000000000 : ℝ)*base90 + (23486911/5000000000000000000000 : ℝ)*base92 + (23486911/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33583648145985832602237/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1482310357/100000000000000 : ℝ)*(base19) + (105906461/6250000000000 : ℝ)*(base23) + (103258071/100000000000000 : ℝ)*(upper2) + (267400019/100000000000000 : ℝ)*(upper3) + (6105563/2500000000000 : ℝ)*(upper5) + (37849079733113/4000000000000 : ℝ)*(major0) + (37849079733113/4000000000000 : ℝ)*(major1) + (37849079733113/4000000000000 : ℝ)*(major2) + (2559010067/50000000000000 : ℝ)*(sp1) + (3439489011/50000000000000 : ℝ)*(sp2) + (701900035135369/50000000000000 : ℝ)*(sp4) + (1403793469940247/100000000000000 : ℝ)*(sp5) + (70189574839467/5000000000000 : ℝ)*(sp6) + (488653776453041/100000000000000 : ℝ)*(sp7) + (488653776453041/100000000000000 : ℝ)*(f.failure) + (701900035135369/50000000000000 : ℝ)*(f.sum) + (13935682635307/8000000000000000000000000000 : ℝ)*base66 + (114803688899307/16000000000000000000000000000 : ℝ)*base68 + (45582833372693/16000000000000000000000000000 : ℝ)*base69 + (35616020899307/16000000000000000000000000000 : ℝ)*base72 + (33630791563307/8000000000000000000000000000 : ℝ)*base74 + (23049873987307/16000000000000000000000000000 : ℝ)*base76 + (6594220899307/16000000000000000000000000000 : ℝ)*base78 + (140016429411307/16000000000000000000000000000 : ℝ)*base80 + (18659743332693/8000000000000000000000000000 : ℝ)*base81 + (30591857/5000000000000000000000 : ℝ)*base89 + (30591857/5000000000000000000000 : ℝ)*base91 + (30591857/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1706_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5933/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (441/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1706_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1706_s1_0 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1422699409/10000000000 : ℝ)*x 0 + (2744365883/5000000000 : ℝ)*x 1 + (2562148363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1422699409/10000000000 : ℝ)^5271 ≤ (8890354945167/100000000000000 : ℝ)^4247 := by
    have hnat : (1422699409 : ℕ)^5271*100000000000000^4247 ≤ 8890354945167^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1422699409 10000000000 8890354945167 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744365883/5000000000 : ℝ)^5271 ≤ (23747929432923/50000000000000 : ℝ)^4247 := by
    have hnat : (2744365883 : ℕ)^5271*50000000000000^4247 ≤ 23747929432923^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744365883 5000000000 23747929432923 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2562148363/5000000000 : ℝ)^5271 ≤ (10903446546803/25000000000000 : ℝ)^4247 := by
    have hnat : (2562148363 : ℕ)^5271*25000000000000^4247 ≤ 10903446546803^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562148363 5000000000 10903446546803 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1422699409/10000000000 : ℝ), (2744365883/5000000000 : ℝ), (2562148363/5000000000 : ℝ)] ![(8890354945167/100000000000000 : ℝ), (23747929432923/50000000000000 : ℝ), (10903446546803/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1422699409/10000000000 : ℝ)|^5271 ≤ (8890354945167/100000000000000 : ℝ)^4247
        have hw : |(-1422699409/10000000000 : ℝ)|=(1422699409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744365883/5000000000 : ℝ)|^5271 ≤ (23747929432923/50000000000000 : ℝ)^4247
        have hw : |(2744365883/5000000000 : ℝ)|=(2744365883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2562148363/5000000000 : ℝ)|^5271 ≤ (10903446546803/25000000000000 : ℝ)^4247
        have hw : |(2562148363/5000000000 : ℝ)|=(2562148363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s1_1 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267461369/500000000 : ℝ)*x 0 + (-403084043/2500000000 : ℝ)*x 1 + (5124295857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267461369/500000000 : ℝ)^5271 ≤ (9200447230489/20000000000000 : ℝ)^4247 := by
    have hnat : (267461369 : ℕ)^5271*20000000000000^4247 ≤ 9200447230489^4247*500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267461369 500000000 9200447230489 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403084043/2500000000 : ℝ)^5271 ≤ (2076797364817/20000000000000 : ℝ)^4247 := by
    have hnat : (403084043 : ℕ)^5271*20000000000000^4247 ≤ 2076797364817^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403084043 2500000000 2076797364817 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5124295857/10000000000 : ℝ)^5271 ≤ (4361377700769/10000000000000 : ℝ)^4247 := by
    have hnat : (5124295857 : ℕ)^5271*10000000000000^4247 ≤ 4361377700769^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124295857 10000000000 4361377700769 10000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267461369/500000000 : ℝ), (-403084043/2500000000 : ℝ), (5124295857/10000000000 : ℝ)] ![(9200447230489/20000000000000 : ℝ), (2076797364817/20000000000000 : ℝ), (4361377700769/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267461369/500000000 : ℝ)|^5271 ≤ (9200447230489/20000000000000 : ℝ)^4247
        have hw : |(267461369/500000000 : ℝ)|=(267461369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-403084043/2500000000 : ℝ)|^5271 ≤ (2076797364817/20000000000000 : ℝ)^4247
        have hw : |(-403084043/2500000000 : ℝ)|=(403084043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5124295857/10000000000 : ℝ)|^5271 ≤ (4361377700769/10000000000000 : ℝ)^4247
        have hw : |(5124295857/10000000000 : ℝ)|=(5124295857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s1_2 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674613007/5000000000 : ℝ)*x 0 + (5124297049/10000000000 : ℝ)*x 1 + (-1612336421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674613007/5000000000 : ℝ)^5271 ≤ (575027769659/1250000000000 : ℝ)^4247 := by
    have hnat : (2674613007 : ℕ)^5271*1250000000000^4247 ≤ 575027769659^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674613007 5000000000 575027769659 1250000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5124297049/10000000000 : ℝ)^5271 ≤ (43613789599163/100000000000000 : ℝ)^4247 := by
    have hnat : (5124297049 : ℕ)^5271*100000000000000^4247 ≤ 43613789599163^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5124297049 10000000000 43613789599163 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1612336421/10000000000 : ℝ)^5271 ≤ (2076797762877/20000000000000 : ℝ)^4247 := by
    have hnat : (1612336421 : ℕ)^5271*20000000000000^4247 ≤ 2076797762877^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612336421 10000000000 2076797762877 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674613007/5000000000 : ℝ), (5124297049/10000000000 : ℝ), (-1612336421/10000000000 : ℝ)] ![(575027769659/1250000000000 : ℝ), (43613789599163/100000000000000 : ℝ), (2076797762877/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674613007/5000000000 : ℝ)|^5271 ≤ (575027769659/1250000000000 : ℝ)^4247
        have hw : |(2674613007/5000000000 : ℝ)|=(2674613007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5124297049/10000000000 : ℝ)|^5271 ≤ (43613789599163/100000000000000 : ℝ)^4247
        have hw : |(5124297049/10000000000 : ℝ)|=(5124297049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1612336421/10000000000 : ℝ)|^5271 ≤ (2076797762877/20000000000000 : ℝ)^4247
        have hw : |(-1612336421/10000000000 : ℝ)|=(1612336421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s1_3 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2053411839/5000000000 : ℝ)*x 0 + (144186567/400000000 : ℝ)*x 1 + (1162902287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053411839/5000000000 : ℝ)^5271 ≤ (33137365058293/100000000000000 : ℝ)^4247 := by
    have hnat : (2053411839 : ℕ)^5271*100000000000000^4247 ≤ 33137365058293^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053411839 5000000000 33137365058293 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144186567/400000000 : ℝ)^5271 ≤ (28185119236361/100000000000000 : ℝ)^4247 := by
    have hnat : (144186567 : ℕ)^5271*100000000000000^4247 ≤ 28185119236361^4247*400000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144186567 400000000 28185119236361 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1162902287/2500000000 : ℝ)^5271 ≤ (9669378924149/25000000000000 : ℝ)^4247 := by
    have hnat : (1162902287 : ℕ)^5271*25000000000000^4247 ≤ 9669378924149^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1162902287 2500000000 9669378924149 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2053411839/5000000000 : ℝ), (144186567/400000000 : ℝ), (1162902287/2500000000 : ℝ)] ![(33137365058293/100000000000000 : ℝ), (28185119236361/100000000000000 : ℝ), (9669378924149/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2053411839/5000000000 : ℝ)|^5271 ≤ (33137365058293/100000000000000 : ℝ)^4247
        have hw : |(2053411839/5000000000 : ℝ)|=(2053411839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(144186567/400000000 : ℝ)|^5271 ≤ (28185119236361/100000000000000 : ℝ)^4247
        have hw : |(144186567/400000000 : ℝ)|=(144186567/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1162902287/2500000000 : ℝ)|^5271 ≤ (9669378924149/25000000000000 : ℝ)^4247
        have hw : |(1162902287/2500000000 : ℝ)|=(1162902287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s1_4 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-711448323/5000000000 : ℝ)*x 0 + (5128670717/10000000000 : ℝ)*x 1 + (5484286321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (711448323/5000000000 : ℝ)^5271 ≤ (4445942333299/50000000000000 : ℝ)^4247 := by
    have hnat : (711448323 : ℕ)^5271*50000000000000^4247 ≤ 4445942333299^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711448323 5000000000 4445942333299 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128670717/10000000000 : ℝ)^5271 ≤ (8731998958047/20000000000000 : ℝ)^4247 := by
    have hnat : (5128670717 : ℕ)^5271*20000000000000^4247 ≤ 8731998958047^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128670717 10000000000 8731998958047 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484286321/10000000000 : ℝ)^5271 ≤ (47448120525201/100000000000000 : ℝ)^4247 := by
    have hnat : (5484286321 : ℕ)^5271*100000000000000^4247 ≤ 47448120525201^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484286321 10000000000 47448120525201 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-711448323/5000000000 : ℝ), (5128670717/10000000000 : ℝ), (5484286321/10000000000 : ℝ)] ![(4445942333299/50000000000000 : ℝ), (8731998958047/20000000000000 : ℝ), (47448120525201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-711448323/5000000000 : ℝ)|^5271 ≤ (4445942333299/50000000000000 : ℝ)^4247
        have hw : |(-711448323/5000000000 : ℝ)|=(711448323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128670717/10000000000 : ℝ)|^5271 ≤ (8731998958047/20000000000000 : ℝ)^4247
        have hw : |(5128670717/10000000000 : ℝ)|=(5128670717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484286321/10000000000 : ℝ)|^5271 ≤ (47448120525201/100000000000000 : ℝ)^4247
        have hw : |(5484286321/10000000000 : ℝ)|=(5484286321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s1_5 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050329579/2000000000 : ℝ)*x 0 + (-125234593/1000000000 : ℝ)*x 1 + (685535761/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050329579/2000000000 : ℝ)^5271 ≤ (11240760569999/25000000000000 : ℝ)^4247 := by
    have hnat : (1050329579 : ℕ)^5271*25000000000000^4247 ≤ 11240760569999^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050329579 2000000000 11240760569999 25000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125234593/1000000000 : ℝ)^5271 ≤ (1517767936213/20000000000000 : ℝ)^4247 := by
    have hnat : (125234593 : ℕ)^5271*20000000000000^4247 ≤ 1517767936213^4247*1000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125234593 1000000000 1517767936213 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685535761/1250000000 : ℝ)^5271 ≤ (23724059011663/50000000000000 : ℝ)^4247 := by
    have hnat : (685535761 : ℕ)^5271*50000000000000^4247 ≤ 23724059011663^4247*1250000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685535761 1250000000 23724059011663 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050329579/2000000000 : ℝ), (-125234593/1000000000 : ℝ), (685535761/1250000000 : ℝ)] ![(11240760569999/25000000000000 : ℝ), (1517767936213/20000000000000 : ℝ), (23724059011663/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050329579/2000000000 : ℝ)|^5271 ≤ (11240760569999/25000000000000 : ℝ)^4247
        have hw : |(1050329579/2000000000 : ℝ)|=(1050329579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125234593/1000000000 : ℝ)|^5271 ≤ (1517767936213/20000000000000 : ℝ)^4247
        have hw : |(-125234593/1000000000 : ℝ)|=(125234593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685535761/1250000000 : ℝ)|^5271 ≤ (23724059011663/50000000000000 : ℝ)^4247
        have hw : |(685535761/1250000000 : ℝ)|=(685535761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s1_6 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251647487/10000000000 : ℝ)*x 0 + (2742142913/5000000000 : ℝ)*x 1 + (-244599/1953125 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251647487/10000000000 : ℝ)^5271 ≤ (22481518972289/50000000000000 : ℝ)^4247 := by
    have hnat : (5251647487 : ℕ)^5271*50000000000000^4247 ≤ 22481518972289^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251647487 10000000000 22481518972289 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742142913/5000000000 : ℝ)^5271 ≤ (47448115210059/100000000000000 : ℝ)^4247 := by
    have hnat : (2742142913 : ℕ)^5271*100000000000000^4247 ≤ 47448115210059^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742142913 5000000000 47448115210059 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (244599/1953125 : ℝ)^5271 ≤ (7588846825789/100000000000000 : ℝ)^4247 := by
    have hnat : (244599 : ℕ)^5271*100000000000000^4247 ≤ 7588846825789^4247*1953125^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      244599 1953125 7588846825789 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251647487/10000000000 : ℝ), (2742142913/5000000000 : ℝ), (-244599/1953125 : ℝ)] ![(22481518972289/50000000000000 : ℝ), (47448115210059/100000000000000 : ℝ), (7588846825789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251647487/10000000000 : ℝ)|^5271 ≤ (22481518972289/50000000000000 : ℝ)^4247
        have hw : |(5251647487/10000000000 : ℝ)|=(5251647487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742142913/5000000000 : ℝ)|^5271 ≤ (47448115210059/100000000000000 : ℝ)^4247
        have hw : |(2742142913/5000000000 : ℝ)|=(2742142913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-244599/1953125 : ℝ)|^5271 ≤ (7588846825789/100000000000000 : ℝ)^4247
        have hw : |(-244599/1953125 : ℝ)|=(244599/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s1_7 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (20536947/50000000 : ℝ)*x 0 + (4639043107/10000000000 : ℝ)*x 1 + (3617433407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20536947/50000000 : ℝ)^5271 ≤ (6628606097847/20000000000000 : ℝ)^4247 := by
    have hnat : (20536947 : ℕ)^5271*20000000000000^4247 ≤ 6628606097847^4247*50000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20536947 50000000 6628606097847 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4639043107/10000000000 : ℝ)^5271 ≤ (7709576094397/20000000000000 : ℝ)^4247 := by
    have hnat : (4639043107 : ℕ)^5271*20000000000000^4247 ≤ 7709576094397^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4639043107 10000000000 7709576094397 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3617433407/10000000000 : ℝ)^5271 ≤ (14154544512783/50000000000000 : ℝ)^4247 := by
    have hnat : (3617433407 : ℕ)^5271*50000000000000^4247 ≤ 14154544512783^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3617433407 10000000000 14154544512783 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20536947/50000000 : ℝ), (4639043107/10000000000 : ℝ), (3617433407/10000000000 : ℝ)] ![(6628606097847/20000000000000 : ℝ), (7709576094397/20000000000000 : ℝ), (14154544512783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20536947/50000000 : ℝ)|^5271 ≤ (6628606097847/20000000000000 : ℝ)^4247
        have hw : |(20536947/50000000 : ℝ)|=(20536947/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4639043107/10000000000 : ℝ)|^5271 ≤ (7709576094397/20000000000000 : ℝ)^4247
        have hw : |(4639043107/10000000000 : ℝ)|=(4639043107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3617433407/10000000000 : ℝ)|^5271 ≤ (14154544512783/50000000000000 : ℝ)^4247
        have hw : |(3617433407/10000000000 : ℝ)|=(3617433407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1706_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5933/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2421/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (873/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5933/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5933/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5933/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5933/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5933/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5933/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5933/100000 : ℝ) ^ (5263/1024 : ℝ) ≤ (24776013302581/50000000000000000000 : ℝ) := by
    have hpowers : (5933/100000 : ℝ)^5263 ≤ (24776013302581/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5933 : ℕ)^5263*50000000000000000000^1024 ≤ 24776013302581^1024*100000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5933 100000 24776013302581 50000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5933/100000 : ℝ)) (X := (24776013302581/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (441/2000 : ℝ) ^ (5263/1024 : ℝ) ≤ (42203746433760379/100000000000000000000 : ℝ) := by
    have hpowers : (441/2000 : ℝ)^5263 ≤ (42203746433760379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^5263*100000000000000000000^1024 ≤ 42203746433760379^1024*2000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 2000 42203746433760379 100000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/2000 : ℝ)) (X := (42203746433760379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000024776013302581/25000000000000000000 : ℝ) ≤ (10000001928225537/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (25000024776013302581/25000000000000000000 : ℝ)^1024 ≤ (10000001928225537/10000000000000000 : ℝ)^5263 := by
      have hnat : (25000024776013302581 : ℕ)^1024*10000000000000000^5263 ≤ 10000001928225537^5263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000024776013302581 25000000000000000000 10000001928225537 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001928225537/10000000000000000 : ℝ)) (X := (25000024776013302581/25000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042253298460365541/100000000000000000000 : ℝ) ≤ (2000164392996633/2000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (100042253298460365541/100000000000000000000 : ℝ)^1024 ≤ (2000164392996633/2000000000000000 : ℝ)^5263 := by
      have hnat : (100042253298460365541 : ℕ)^1024*2000000000000000^5263 ≤ 2000164392996633^5263*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042253298460365541 100000000000000000000 2000164392996633 2000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000164392996633/2000000000000000 : ℝ)) (X := (100042253298460365541/100000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50042203746433760379/50000000000000000000 : ℝ) ≤ (10001642001740793/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (50042203746433760379/50000000000000000000 : ℝ)^1024 ≤ (10001642001740793/10000000000000000 : ℝ)^5263 := by
      have hnat : (50042203746433760379 : ℕ)^1024*10000000000000000^5263 ≤ 10001642001740793^5263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50042203746433760379 50000000000000000000 10001642001740793 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001642001740793/10000000000000000 : ℝ)) (X := (50042203746433760379/50000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24776013302581/50000000000000000000 : ℝ) ≤ ((161160300521044965981/161170000000000000000 : ℝ)+2*(205009189407/402925000000000 : ℝ)*(5933/100000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (161160300521044965981/161170000000000000000 : ℝ)+2*(205009189407/402925000000000 : ℝ)*(5933/100000 : ℝ)=(10000001928225537/10000000000000000 : ℝ) by norm_num, show 1+2*(24776013302581/50000000000000000000 : ℝ)=(25000024776013302581/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(42203746433760379/100000000000000000000 : ℝ)+(24776013302581/50000000000000000000 : ℝ) ≤ ((161160300521044965981/161170000000000000000 : ℝ)+(205009189407/402925000000000 : ℝ)*((441/2000 : ℝ)+(5933/100000 : ℝ)))^(5263/1024 : ℝ) := by
    rw [show (161160300521044965981/161170000000000000000 : ℝ)+(205009189407/402925000000000 : ℝ)*((441/2000 : ℝ)+(5933/100000 : ℝ))=(2000164392996633/2000000000000000 : ℝ) by norm_num, show 1+(42203746433760379/100000000000000000000 : ℝ)+(24776013302581/50000000000000000000 : ℝ)=(100042253298460365541/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(42203746433760379/100000000000000000000 : ℝ) ≤ ((161160300521044965981/161170000000000000000 : ℝ)+2*(205009189407/402925000000000 : ℝ)*(441/2000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (161160300521044965981/161170000000000000000 : ℝ)+2*(205009189407/402925000000000 : ℝ)*(441/2000 : ℝ)=(10001642001740793/10000000000000000 : ℝ) by norm_num, show 1+2*(42203746433760379/100000000000000000000 : ℝ)=(50042203746433760379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (161160300521044965981/161170000000000000000 : ℝ)*(X 1 0+X 2 0)+(205009189407/402925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (5933/100000 : ℝ)) (hi := (441/2000 : ℝ)) (c := (161160300521044965981/161170000000000000000 : ℝ)) (alpha := (205009189407/402925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (161160300521044965981/161170000000000000000 : ℝ)*(X 0 1+X 2 1)+(205009189407/402925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (5933/100000 : ℝ)) (hi := (441/2000 : ℝ)) (c := (161160300521044965981/161170000000000000000 : ℝ)) (alpha := (205009189407/402925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (161160300521044965981/161170000000000000000 : ℝ)*(X 0 2+X 1 2)+(205009189407/402925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (5933/100000 : ℝ)) (hi := (441/2000 : ℝ)) (c := (161160300521044965981/161170000000000000000 : ℝ)) (alpha := (205009189407/402925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1422699409/10000000000 : ℝ)*X 0 0+(2744365883/5000000000 : ℝ)*X 0 1+(2562148363/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267461369/500000000 : ℝ)*X 1 0+(-403084043/2500000000 : ℝ)*X 1 1+(5124295857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674613007/5000000000 : ℝ)*X 2 0+(5124297049/10000000000 : ℝ)*X 2 1+(-1612336421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2053411839/5000000000 : ℝ)*X 0 0+(144186567/400000000 : ℝ)*X 0 1+(1162902287/2500000000 : ℝ)*X 0 2+(2053411839/5000000000 : ℝ)*X 1 0+(144186567/400000000 : ℝ)*X 1 1+(1162902287/2500000000 : ℝ)*X 1 2+(2053411839/5000000000 : ℝ)*X 2 0+(144186567/400000000 : ℝ)*X 2 1+(1162902287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-711448323/5000000000 : ℝ)*X 0 0+(5128670717/10000000000 : ℝ)*X 0 1+(5484286321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050329579/2000000000 : ℝ)*X 1 0+(-125234593/1000000000 : ℝ)*X 1 1+(685535761/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251647487/10000000000 : ℝ)*X 2 0+(2742142913/5000000000 : ℝ)*X 2 1+(-244599/1953125 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((20536947/50000000 : ℝ)*X 0 0+(4639043107/10000000000 : ℝ)*X 0 1+(3617433407/10000000000 : ℝ)*X 0 2+(20536947/50000000 : ℝ)*X 1 0+(4639043107/10000000000 : ℝ)*X 1 1+(3617433407/10000000000 : ℝ)*X 1 2+(20536947/50000000 : ℝ)*X 2 0+(4639043107/10000000000 : ℝ)*X 2 1+(3617433407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1845095822892569341433302611/201462500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (489940303/50000000000000 : ℝ)*(base19) + (385817463/100000000000000 : ℝ)*(base23) + (2444663/10000000000000 : ℝ)*(lower2) + (166847723/100000000000000 : ℝ)*(upper3) + (81496749/100000000000000 : ℝ)*(lower4) + (1849572960883079/100000000000000 : ℝ)*(major0) + (1849572960883079/100000000000000 : ℝ)*(major1) + (46239324022077/2500000000000 : ℝ)*(major2) + (274398081653607/10000000000000 : ℝ)*(sp0) + (137199092475907/5000000000000 : ℝ)*(sp1) + (1371991221790641/50000000000000 : ℝ)*(sp2) + (477580691184313/50000000000000 : ℝ)*(sp3) + (80514507/4000000000000 : ℝ)*(sp4) + (702357597/50000000000000 : ℝ)*(sp7) + (47758139354191/5000000000000 : ℝ)*(f.failure) + (1371991414699373/50000000000000 : ℝ)*(f.sum) + (271403675648423/40292500000000000000000000000 : ℝ)*base65 + (18114151925046535499/16117000000000000000000000000000000 : ℝ)*base67 + (81631467795932463/402925000000000000000000000000000 : ℝ)*base70 + (76133459850978464501/16117000000000000000000000000000000 : ℝ)*base72 + (133825664498523/40292500000000000000000000000 : ℝ)*base73 + (3116652137964557463/402925000000000000000000000000000 : ℝ)*base76 + (23080885514257264501/16117000000000000000000000000000000 : ℝ)*base78 + (46468189722192735499/16117000000000000000000000000000000 : ℝ)*base79 + (9213169575033/5036562500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (864593/250000000000000000000 : ℝ)*base90 + (864593/250000000000000000000 : ℝ)*base92 + (3364593/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53515391125757191469214780657/8058500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1291687769/100000000000000 : ℝ)*(base19) + (1195979/125000000000 : ℝ)*(base23) + (43855489/25000000000000 : ℝ)*(upper3) + (3774539/50000000000000 : ℝ)*(lower4) + (140072357/100000000000000 : ℝ)*(upper5) + (1895435357623267/100000000000000 : ℝ)*(major0) + (1895435357623267/100000000000000 : ℝ)*(major1) + (1895435357623267/100000000000000 : ℝ)*(major2) + (9509900971/100000000000000 : ℝ)*(sp1) + (2469648801/100000000000000 : ℝ)*(sp2) + (1406011645599059/50000000000000 : ℝ)*(sp4) + (1406006244804689/50000000000000 : ℝ)*(sp5) + (1406009932383059/50000000000000 : ℝ)*(sp6) + (12235590033579/1250000000000 : ℝ)*(sp7) + (12235590033579/1250000000000 : ℝ)*(f.failure) + (1406011645599059/50000000000000 : ℝ)*(f.sum) + (49959898406993/10073125000000000000000000000 : ℝ)*base66 + (94821728539114679927/16117000000000000000000000000000000 : ℝ)*base67 + (97733598662290679927/16117000000000000000000000000000000 : ℝ)*base69 + (38904660201166679927/16117000000000000000000000000000000 : ℝ)*base71 + (25389669974201/20146250000000000000000000000 : ℝ)*base74 + (190455239049929679927/16117000000000000000000000000000000 : ℝ)*base75 + (27899821262536679927/16117000000000000000000000000000000 : ℝ)*base77 + (108504721293127679927/16117000000000000000000000000000000 : ℝ)*base79 + (117817307309039/80585000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (583117/62500000000000000000 : ℝ)*base90 + (583117/62500000000000000000 : ℝ)*base92 + (583117/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1706_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5933/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2421/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (873/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1706_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1706_s2_0 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426500963/10000000000 : ℝ)*x 0 + (5473213983/10000000000 : ℝ)*x 1 + (2568636177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426500963/10000000000 : ℝ)^5271 ≤ (445992392849/5000000000000 : ℝ)^4247 := by
    have hnat : (1426500963 : ℕ)^5271*5000000000000^4247 ≤ 445992392849^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426500963 10000000000 445992392849 5000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473213983/10000000000 : ℝ)^5271 ≤ (23664629238009/50000000000000 : ℝ)^4247 := by
    have hnat : (5473213983 : ℕ)^5271*50000000000000^4247 ≤ 23664629238009^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473213983 10000000000 23664629238009 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568636177/5000000000 : ℝ)^5271 ≤ (21875446831127/50000000000000 : ℝ)^4247 := by
    have hnat : (2568636177 : ℕ)^5271*50000000000000^4247 ≤ 21875446831127^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568636177 5000000000 21875446831127 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426500963/10000000000 : ℝ), (5473213983/10000000000 : ℝ), (2568636177/5000000000 : ℝ)] ![(445992392849/5000000000000 : ℝ), (23664629238009/50000000000000 : ℝ), (21875446831127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426500963/10000000000 : ℝ)|^5271 ≤ (445992392849/5000000000000 : ℝ)^4247
        have hw : |(-1426500963/10000000000 : ℝ)|=(1426500963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473213983/10000000000 : ℝ)|^5271 ≤ (23664629238009/50000000000000 : ℝ)^4247
        have hw : |(5473213983/10000000000 : ℝ)|=(5473213983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568636177/5000000000 : ℝ)|^5271 ≤ (21875446831127/50000000000000 : ℝ)^4247
        have hw : |(2568636177/5000000000 : ℝ)|=(2568636177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s2_1 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345030729/10000000000 : ℝ)*x 0 + (-320154949/2000000000 : ℝ)*x 1 + (5137272703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345030729/10000000000 : ℝ)^5271 ≤ (22978724141279/50000000000000 : ℝ)^4247 := by
    have hnat : (5345030729 : ℕ)^5271*50000000000000^4247 ≤ 22978724141279^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345030729 10000000000 22978724141279 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (320154949/2000000000 : ℝ)^5271 ≤ (10291654354307/100000000000000 : ℝ)^4247 := by
    have hnat : (320154949 : ℕ)^5271*100000000000000^4247 ≤ 10291654354307^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320154949 2000000000 10291654354307 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137272703/10000000000 : ℝ)^5271 ≤ (437508973511/1000000000000 : ℝ)^4247 := by
    have hnat : (5137272703 : ℕ)^5271*1000000000000^4247 ≤ 437508973511^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137272703 10000000000 437508973511 1000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345030729/10000000000 : ℝ), (-320154949/2000000000 : ℝ), (5137272703/10000000000 : ℝ)] ![(22978724141279/50000000000000 : ℝ), (10291654354307/100000000000000 : ℝ), (437508973511/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345030729/10000000000 : ℝ)|^5271 ≤ (22978724141279/50000000000000 : ℝ)^4247
        have hw : |(5345030729/10000000000 : ℝ)|=(5345030729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-320154949/2000000000 : ℝ)|^5271 ≤ (10291654354307/100000000000000 : ℝ)^4247
        have hw : |(-320154949/2000000000 : ℝ)|=(320154949/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137272703/10000000000 : ℝ)|^5271 ≤ (437508973511/1000000000000 : ℝ)^4247
        have hw : |(5137272703/10000000000 : ℝ)|=(5137272703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s2_2 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668128847/1250000000 : ℝ)*x 0 + (1027454509/2000000000 : ℝ)*x 1 + (-1600774891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668128847/1250000000 : ℝ)^5271 ≤ (45957448784109/100000000000000 : ℝ)^4247 := by
    have hnat : (668128847 : ℕ)^5271*100000000000000^4247 ≤ 45957448784109^4247*1250000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668128847 1250000000 45957448784109 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1027454509/2000000000 : ℝ)^5271 ≤ (21875447840539/50000000000000 : ℝ)^4247 := by
    have hnat : (1027454509 : ℕ)^5271*50000000000000^4247 ≤ 21875447840539^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027454509 2000000000 21875447840539 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1600774891/10000000000 : ℝ)^5271 ≤ (1286456939911/12500000000000 : ℝ)^4247 := by
    have hnat : (1600774891 : ℕ)^5271*12500000000000^4247 ≤ 1286456939911^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1600774891 10000000000 1286456939911 12500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668128847/1250000000 : ℝ), (1027454509/2000000000 : ℝ), (-1600774891/10000000000 : ℝ)] ![(45957448784109/100000000000000 : ℝ), (21875447840539/50000000000000 : ℝ), (1286456939911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668128847/1250000000 : ℝ)|^5271 ≤ (45957448784109/100000000000000 : ℝ)^4247
        have hw : |(668128847/1250000000 : ℝ)|=(668128847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1027454509/2000000000 : ℝ)|^5271 ≤ (21875447840539/50000000000000 : ℝ)^4247
        have hw : |(1027454509/2000000000 : ℝ)|=(1027454509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1600774891/10000000000 : ℝ)|^5271 ≤ (1286456939911/12500000000000 : ℝ)^4247
        have hw : |(-1600774891/10000000000 : ℝ)|=(1600774891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s2_3 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4109765137/10000000000 : ℝ)*x 0 + (729065793/2000000000 : ℝ)*x 1 + (1152604627/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4109765137/10000000000 : ℝ)^5271 ≤ (16583412197383/50000000000000 : ℝ)^4247 := by
    have hnat : (4109765137 : ℕ)^5271*50000000000000^4247 ≤ 16583412197383^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4109765137 10000000000 16583412197383 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (729065793/2000000000 : ℝ)^5271 ≤ (14290139593677/50000000000000 : ℝ)^4247 := by
    have hnat : (729065793 : ℕ)^5271*50000000000000^4247 ≤ 14290139593677^4247*2000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      729065793 2000000000 14290139593677 50000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152604627/2500000000 : ℝ)^5271 ≤ (38252896393393/100000000000000 : ℝ)^4247 := by
    have hnat : (1152604627 : ℕ)^5271*100000000000000^4247 ≤ 38252896393393^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152604627 2500000000 38252896393393 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4109765137/10000000000 : ℝ), (729065793/2000000000 : ℝ), (1152604627/2500000000 : ℝ)] ![(16583412197383/50000000000000 : ℝ), (14290139593677/50000000000000 : ℝ), (38252896393393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4109765137/10000000000 : ℝ)|^5271 ≤ (16583412197383/50000000000000 : ℝ)^4247
        have hw : |(4109765137/10000000000 : ℝ)|=(4109765137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(729065793/2000000000 : ℝ)|^5271 ≤ (14290139593677/50000000000000 : ℝ)^4247
        have hw : |(729065793/2000000000 : ℝ)|=(729065793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152604627/2500000000 : ℝ)|^5271 ≤ (38252896393393/100000000000000 : ℝ)^4247
        have hw : |(1152604627/2500000000 : ℝ)|=(1152604627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s2_4 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1426654771/10000000000 : ℝ)*x 0 + (2570496129/5000000000 : ℝ)*x 1 + (5469438607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1426654771/10000000000 : ℝ)^5271 ≤ (178420830343/2000000000000 : ℝ)^4247 := by
    have hnat : (1426654771 : ℕ)^5271*2000000000000^4247 ≤ 178420830343^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426654771 10000000000 178420830343 2000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570496129/5000000000 : ℝ)^5271 ≤ (8758043116683/20000000000000 : ℝ)^4247 := by
    have hnat : (2570496129 : ℕ)^5271*20000000000000^4247 ≤ 8758043116683^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570496129 5000000000 8758043116683 20000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469438607/10000000000 : ℝ)^5271 ≤ (47288742890891/100000000000000 : ℝ)^4247 := by
    have hnat : (5469438607 : ℕ)^5271*100000000000000^4247 ≤ 47288742890891^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469438607 10000000000 47288742890891 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1426654771/10000000000 : ℝ), (2570496129/5000000000 : ℝ), (5469438607/10000000000 : ℝ)] ![(178420830343/2000000000000 : ℝ), (8758043116683/20000000000000 : ℝ), (47288742890891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1426654771/10000000000 : ℝ)|^5271 ≤ (178420830343/2000000000000 : ℝ)^4247
        have hw : |(-1426654771/10000000000 : ℝ)|=(1426654771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570496129/5000000000 : ℝ)|^5271 ≤ (8758043116683/20000000000000 : ℝ)^4247
        have hw : |(2570496129/5000000000 : ℝ)|=(2570496129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469438607/10000000000 : ℝ)|^5271 ≤ (47288742890891/100000000000000 : ℝ)^4247
        have hw : |(5469438607/10000000000 : ℝ)|=(5469438607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s2_5 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525511779/1000000000 : ℝ)*x 0 + (-1268608991/10000000000 : ℝ)*x 1 + (1367359641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525511779/1000000000 : ℝ)^5271 ≤ (5624989551041/12500000000000 : ℝ)^4247 := by
    have hnat : (525511779 : ℕ)^5271*12500000000000^4247 ≤ 5624989551041^4247*1000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525511779 1000000000 5624989551041 12500000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268608991/10000000000 : ℝ)^5271 ≤ (7711341143789/100000000000000 : ℝ)^4247 := by
    have hnat : (1268608991 : ℕ)^5271*100000000000000^4247 ≤ 7711341143789^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268608991 10000000000 7711341143789 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367359641/2500000000 : ℝ)^5271 ≤ (47288742429473/100000000000000 : ℝ)^4247 := by
    have hnat : (1367359641 : ℕ)^5271*100000000000000^4247 ≤ 47288742429473^4247*2500000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367359641 2500000000 47288742429473 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525511779/1000000000 : ℝ), (-1268608991/10000000000 : ℝ), (1367359641/2500000000 : ℝ)] ![(5624989551041/12500000000000 : ℝ), (7711341143789/100000000000000 : ℝ), (47288742429473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525511779/1000000000 : ℝ)|^5271 ≤ (5624989551041/12500000000000 : ℝ)^4247
        have hw : |(525511779/1000000000 : ℝ)|=(525511779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1268608991/10000000000 : ℝ)|^5271 ≤ (7711341143789/100000000000000 : ℝ)^4247
        have hw : |(-1268608991/10000000000 : ℝ)|=(1268608991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367359641/2500000000 : ℝ)|^5271 ≤ (47288742429473/100000000000000 : ℝ)^4247
        have hw : |(1367359641/2500000000 : ℝ)|=(1367359641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s2_6 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5255117719/10000000000 : ℝ)*x 0 + (2734719287/5000000000 : ℝ)*x 1 + (-1268609077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255117719/10000000000 : ℝ)^5271 ≤ (70312368209/156250000000 : ℝ)^4247 := by
    have hnat : (5255117719 : ℕ)^5271*156250000000^4247 ≤ 70312368209^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255117719 10000000000 70312368209 156250000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734719287/5000000000 : ℝ)^5271 ≤ (2364437126839/5000000000000 : ℝ)^4247 := by
    have hnat : (2734719287 : ℕ)^5271*5000000000000^4247 ≤ 2364437126839^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734719287 5000000000 2364437126839 5000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1268609077/10000000000 : ℝ)^5271 ≤ (7711341792589/100000000000000 : ℝ)^4247 := by
    have hnat : (1268609077 : ℕ)^5271*100000000000000^4247 ≤ 7711341792589^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268609077 10000000000 7711341792589 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255117719/10000000000 : ℝ), (2734719287/5000000000 : ℝ), (-1268609077/10000000000 : ℝ)] ![(70312368209/156250000000 : ℝ), (2364437126839/5000000000000 : ℝ), (7711341792589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255117719/10000000000 : ℝ)|^5271 ≤ (70312368209/156250000000 : ℝ)^4247
        have hw : |(5255117719/10000000000 : ℝ)|=(5255117719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734719287/5000000000 : ℝ)|^5271 ≤ (2364437126839/5000000000000 : ℝ)^4247
        have hw : |(2734719287/5000000000 : ℝ)|=(2734719287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1268609077/10000000000 : ℝ)|^5271 ≤ (7711341792589/100000000000000 : ℝ)^4247
        have hw : |(-1268609077/10000000000 : ℝ)|=(1268609077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1706_s2_7 (p : ℝ) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4110207651/10000000000 : ℝ)*x 0 + (2299866197/5000000000 : ℝ)*x 1 + (73123503/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4110207651/10000000000 : ℝ)^5271 ≤ (33171256706477/100000000000000 : ℝ)^4247 := by
    have hnat : (4110207651 : ℕ)^5271*100000000000000^4247 ≤ 33171256706477^4247*10000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110207651 10000000000 33171256706477 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2299866197/5000000000 : ℝ)^5271 ≤ (1525715446351/4000000000000 : ℝ)^4247 := by
    have hnat : (2299866197 : ℕ)^5271*4000000000000^4247 ≤ 1525715446351^4247*5000000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299866197 5000000000 1525715446351 4000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (73123503/200000000 : ℝ)^5271 ≤ (28685857116361/100000000000000 : ℝ)^4247 := by
    have hnat : (73123503 : ℕ)^5271*100000000000000^4247 ≤ 28685857116361^4247*200000000^5271 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73123503 200000000 28685857116361 100000000000000 5271 4247 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5271/1024 : ℝ)) 5271 4247 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4110207651/10000000000 : ℝ), (2299866197/5000000000 : ℝ), (73123503/200000000 : ℝ)] ![(33171256706477/100000000000000 : ℝ), (1525715446351/4000000000000 : ℝ), (28685857116361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4110207651/10000000000 : ℝ)|^5271 ≤ (33171256706477/100000000000000 : ℝ)^4247
        have hw : |(4110207651/10000000000 : ℝ)|=(4110207651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2299866197/5000000000 : ℝ)|^5271 ≤ (1525715446351/4000000000000 : ℝ)^4247
        have hw : |(2299866197/5000000000 : ℝ)|=(2299866197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(73123503/200000000 : ℝ)|^5271 ≤ (28685857116361/100000000000000 : ℝ)^4247
        have hw : |(73123503/200000000 : ℝ)|=(73123503/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1706_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2421/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (4983/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8567/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (873/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2421/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (873/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2421/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (873/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2421/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (873/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2421/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (873/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2421/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (873/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2421/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2421/25000 : ℝ) ^ (5263/1024 : ℝ) ≤ (307360491931809/50000000000000000000 : ℝ) := by
    have hpowers : (2421/25000 : ℝ)^5263 ≤ (307360491931809/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2421 : ℕ)^5263*50000000000000000000^1024 ≤ 307360491931809^1024*25000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2421 25000 307360491931809 50000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2421/25000 : ℝ)) (X := (307360491931809/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (873/5000 : ℝ) ^ (5263/1024 : ℝ) ≤ (6358341702059383/50000000000000000000 : ℝ) := by
    have hpowers : (873/5000 : ℝ)^5263 ≤ (6358341702059383/50000000000000000000 : ℝ)^1024 := by
      have hnat : (873 : ℕ)^5263*50000000000000000000^1024 ≤ 6358341702059383^1024*5000^5263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        873 5000 6358341702059383 50000000000000000000 5263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (873/5000 : ℝ)) (X := (6358341702059383/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000307360491931809/25000000000000000000 : ℝ) ≤ (312500747519441/312500000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (25000307360491931809/25000000000000000000 : ℝ)^1024 ≤ (312500747519441/312500000000000 : ℝ)^5263 := by
      have hnat : (25000307360491931809 : ℕ)^1024*312500000000000^5263 ≤ 312500747519441^5263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000307360491931809 25000000000000000000 312500747519441 312500000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500747519441/312500000000000 : ℝ)) (X := (25000307360491931809/25000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6250833212774248899/6250000000000000000 : ℝ) ≤ (10000259369660653/10000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (6250833212774248899/6250000000000000000 : ℝ)^1024 ≤ (10000259369660653/10000000000000000 : ℝ)^5263 := by
      have hnat : (6250833212774248899 : ℕ)^1024*10000000000000000^5263 ≤ 10000259369660653^5263*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250833212774248899 6250000000000000000 10000259369660653 10000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000259369660653/10000000000000000 : ℝ)) (X := (6250833212774248899/6250000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006358341702059383/25000000000000000000 : ℝ) ≤ (5000247409349597/5000000000000000 : ℝ) ^ (5263/1024 : ℝ) := by
    have hpowers : (25006358341702059383/25000000000000000000 : ℝ)^1024 ≤ (5000247409349597/5000000000000000 : ℝ)^5263 := by
      have hnat : (25006358341702059383 : ℕ)^1024*5000000000000000^5263 ≤ 5000247409349597^5263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006358341702059383 25000000000000000000 5000247409349597 5000000000000000 1024 5263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000247409349597/5000000000000000 : ℝ)) (X := (25006358341702059383/25000000000000000000 : ℝ)) (by norm_num) 5263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(307360491931809/50000000000000000000 : ℝ) ≤ ((359979749211940189/360000000000000000 : ℝ)+2*(78483012847/259200000000000 : ℝ)*(2421/25000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (359979749211940189/360000000000000000 : ℝ)+2*(78483012847/259200000000000 : ℝ)*(2421/25000 : ℝ)=(312500747519441/312500000000000 : ℝ) by norm_num, show 1+2*(307360491931809/50000000000000000000 : ℝ)=(25000307360491931809/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6358341702059383/50000000000000000000 : ℝ)+(307360491931809/50000000000000000000 : ℝ) ≤ ((359979749211940189/360000000000000000 : ℝ)+(78483012847/259200000000000 : ℝ)*((873/5000 : ℝ)+(2421/25000 : ℝ)))^(5263/1024 : ℝ) := by
    rw [show (359979749211940189/360000000000000000 : ℝ)+(78483012847/259200000000000 : ℝ)*((873/5000 : ℝ)+(2421/25000 : ℝ))=(10000259369660653/10000000000000000 : ℝ) by norm_num, show 1+(6358341702059383/50000000000000000000 : ℝ)+(307360491931809/50000000000000000000 : ℝ)=(6250833212774248899/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6358341702059383/50000000000000000000 : ℝ) ≤ ((359979749211940189/360000000000000000 : ℝ)+2*(78483012847/259200000000000 : ℝ)*(873/5000 : ℝ))^(5263/1024 : ℝ) := by
    rw [show (359979749211940189/360000000000000000 : ℝ)+2*(78483012847/259200000000000 : ℝ)*(873/5000 : ℝ)=(5000247409349597/5000000000000000 : ℝ) by norm_num, show 1+2*(6358341702059383/50000000000000000000 : ℝ)=(25006358341702059383/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (359979749211940189/360000000000000000 : ℝ)*(X 1 0+X 2 0)+(78483012847/259200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (2421/25000 : ℝ)) (hi := (873/5000 : ℝ)) (c := (359979749211940189/360000000000000000 : ℝ)) (alpha := (78483012847/259200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (359979749211940189/360000000000000000 : ℝ)*(X 0 1+X 2 1)+(78483012847/259200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (2421/25000 : ℝ)) (hi := (873/5000 : ℝ)) (c := (359979749211940189/360000000000000000 : ℝ)) (alpha := (78483012847/259200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (359979749211940189/360000000000000000 : ℝ)*(X 0 2+X 1 2)+(78483012847/259200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5263/1024 : ℝ)) (lo := (2421/25000 : ℝ)) (hi := (873/5000 : ℝ)) (c := (359979749211940189/360000000000000000 : ℝ)) (alpha := (78483012847/259200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1426500963/10000000000 : ℝ)*X 0 0+(5473213983/10000000000 : ℝ)*X 0 1+(2568636177/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345030729/10000000000 : ℝ)*X 1 0+(-320154949/2000000000 : ℝ)*X 1 1+(5137272703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668128847/1250000000 : ℝ)*X 2 0+(1027454509/2000000000 : ℝ)*X 2 1+(-1600774891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4109765137/10000000000 : ℝ)*X 0 0+(729065793/2000000000 : ℝ)*X 0 1+(1152604627/2500000000 : ℝ)*X 0 2+(4109765137/10000000000 : ℝ)*X 1 0+(729065793/2000000000 : ℝ)*X 1 1+(1152604627/2500000000 : ℝ)*X 1 2+(4109765137/10000000000 : ℝ)*X 2 0+(729065793/2000000000 : ℝ)*X 2 1+(1152604627/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1426654771/10000000000 : ℝ)*X 0 0+(2570496129/5000000000 : ℝ)*X 0 1+(5469438607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525511779/1000000000 : ℝ)*X 1 0+(-1268608991/10000000000 : ℝ)*X 1 1+(1367359641/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5255117719/10000000000 : ℝ)*X 2 0+(2734719287/5000000000 : ℝ)*X 2 1+(-1268609077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4110207651/10000000000 : ℝ)*X 0 0+(2299866197/5000000000 : ℝ)*X 0 1+(73123503/200000000 : ℝ)*X 0 2+(4110207651/10000000000 : ℝ)*X 1 0+(2299866197/5000000000 : ℝ)*X 1 1+(73123503/200000000 : ℝ)*X 1 2+(4110207651/10000000000 : ℝ)*X 2 0+(2299866197/5000000000 : ℝ)*X 2 1+(73123503/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1706_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (342439643112557865548422081/27000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (105518049/5000000000000 : ℝ)*(base19) + (2121777671/100000000000000 : ℝ)*(base23) + (3944241/50000000000000 : ℝ)*(lower2) + (364759899/100000000000000 : ℝ)*(upper3) + (264989867/100000000000000 : ℝ)*(upper5) + (2006472303183131/100000000000000 : ℝ)*(major0) + (2006472303183131/100000000000000 : ℝ)*(major1) + (2006472303183131/100000000000000 : ℝ)*(major2) + (1488365930645403/50000000000000 : ℝ)*(sp0) + (744188197949179/25000000000000 : ℝ)*(sp1) + (1488376390190013/50000000000000 : ℝ)*(sp2) + (259045221824387/25000000000000 : ℝ)*(sp3) + (2304086689/10000000000000 : ℝ)*(sp4) + (8394146021/100000000000000 : ℝ)*(sp7) + (1036189281443569/100000000000000 : ℝ)*(f.failure) + (23255897673107/781250000000 : ℝ)*(f.sum) + (83123997747883/12960000000000000000000000000 : ℝ)*base66 + (575057856566771669/324000000000000000000000000000000 : ℝ)*base68 + (1256862745190771669/324000000000000000000000000000000 : ℝ)*base70 + (1185155267042771669/324000000000000000000000000000000 : ℝ)*base72 + (13737872291083/12960000000000000000000000000 : ℝ)*base74 + (654852665553228331/324000000000000000000000000000000 : ℝ)*base75 + (1769778991730771669/324000000000000000000000000000000 : ℝ)*base78 + (2943208930214771669/324000000000000000000000000000000 : ℝ)*base80 + (51114832325323/12960000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (38664113/5000000000000000000000 : ℝ)*base89 + (38664113/5000000000000000000000 : ℝ)*base91 + (38664113/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (942460965050514718508147/250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (246319359/50000000000000 : ℝ)*(base19) + (250420681/50000000000000 : ℝ)*(base23) + (13905509/25000000000000 : ℝ)*(upper3) + (8448327/25000000000000 : ℝ)*(lower4) + (6237359/6250000000000 : ℝ)*(upper5) + (256528521814223/12500000000000 : ℝ)*(major0) + (256528521814223/12500000000000 : ℝ)*(major1) + (256528521814223/12500000000000 : ℝ)*(major2) + (1162664787/25000000000000 : ℝ)*(sp1) + (3775830269/100000000000000 : ℝ)*(sp2) + (1522318769267971/50000000000000 : ℝ)*(sp4) + (761158098809519/25000000000000 : ℝ)*(sp5) + (3044633261864311/100000000000000 : ℝ)*(sp6) + (529909342415079/50000000000000 : ℝ)*(sp7) + (529909342415079/50000000000000 : ℝ)*(f.failure) + (1522318769267971/50000000000000 : ℝ)*(f.sum) + (3622123809761/1620000000000000000000000000 : ℝ)*base65 + (130441528718414177/40500000000000000000000000000000 : ℝ)*base68 + (201875882561414177/40500000000000000000000000000000 : ℝ)*base70 + (127347106049414177/40500000000000000000000000000000 : ℝ)*base72 + (5919089247761/1620000000000000000000000000 : ℝ)*base73 + (338818010678414177/40500000000000000000000000000000 : ℝ)*base76 + (120431910099914177/40500000000000000000000000000000 : ℝ)*base78 + (404799062079914177/40500000000000000000000000000000 : ℝ)*base80 + (2905456063001/1620000000000000000000000000 : ℝ)*base81 + (9782617/2500000000000000000000 : ℝ)*base90 + (9782617/2500000000000000000000 : ℝ)*base92 + (9782617/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1706_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (873/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2421/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8567/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1706_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1706_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8567/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1706_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1706_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1706_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5263/1024 : ℝ) ≤ p) (hpb : p ≤ (5271/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (96819777/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4983/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8567/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1706_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
