-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1645_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:55.285984+00:00
-- url     : https://prove2.me/submissions/fa154867-a494-4509-8999-4a4886a2d3b9

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
theorem support_rectangle_w1645_s3_0 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-404989233/2500000000 : ℝ)*x 0 + (2724552159/5000000000 : ℝ)*x 1 + (2591748017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (404989233/2500000000 : ℝ)^4899 ≤ (5007009201683/50000000000000 : ℝ)^3875 := by
    have hnat : (404989233 : ℕ)^4899*50000000000000^3875 ≤ 5007009201683^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404989233 2500000000 5007009201683 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724552159/5000000000 : ℝ)^4899 ≤ (46413776781191/100000000000000 : ℝ)^3875 := by
    have hnat : (2724552159 : ℕ)^4899*100000000000000^3875 ≤ 46413776781191^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724552159 5000000000 46413776781191 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591748017/5000000000 : ℝ)^4899 ≤ (21786102401307/50000000000000 : ℝ)^3875 := by
    have hnat : (2591748017 : ℕ)^4899*50000000000000^3875 ≤ 21786102401307^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591748017 5000000000 21786102401307 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-404989233/2500000000 : ℝ), (2724552159/5000000000 : ℝ), (2591748017/5000000000 : ℝ)] ![(5007009201683/50000000000000 : ℝ), (46413776781191/100000000000000 : ℝ), (21786102401307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-404989233/2500000000 : ℝ)|^4899 ≤ (5007009201683/50000000000000 : ℝ)^3875
        have hw : |(-404989233/2500000000 : ℝ)|=(404989233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724552159/5000000000 : ℝ)|^4899 ≤ (46413776781191/100000000000000 : ℝ)^3875
        have hw : |(2724552159/5000000000 : ℝ)|=(2724552159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591748017/5000000000 : ℝ)|^4899 ≤ (21786102401307/50000000000000 : ℝ)^3875
        have hw : |(2591748017/5000000000 : ℝ)|=(2591748017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s3_1 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348518379/10000000000 : ℝ)*x 0 + (-878359701/5000000000 : ℝ)*x 1 + (2591748007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348518379/10000000000 : ℝ)^4899 ≤ (45333265230929/100000000000000 : ℝ)^3875 := by
    have hnat : (5348518379 : ℕ)^4899*100000000000000^3875 ≤ 45333265230929^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348518379 10000000000 45333265230929 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878359701/5000000000 : ℝ)^4899 ≤ (11094530167277/100000000000000 : ℝ)^3875 := by
    have hnat : (878359701 : ℕ)^4899*100000000000000^3875 ≤ 11094530167277^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878359701 5000000000 11094530167277 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591748007/5000000000 : ℝ)^4899 ≤ (10893051147517/25000000000000 : ℝ)^3875 := by
    have hnat : (2591748007 : ℕ)^4899*25000000000000^3875 ≤ 10893051147517^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591748007 5000000000 10893051147517 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348518379/10000000000 : ℝ), (-878359701/5000000000 : ℝ), (2591748007/5000000000 : ℝ)] ![(45333265230929/100000000000000 : ℝ), (11094530167277/100000000000000 : ℝ), (10893051147517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348518379/10000000000 : ℝ)|^4899 ≤ (45333265230929/100000000000000 : ℝ)^3875
        have hw : |(5348518379/10000000000 : ℝ)|=(5348518379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878359701/5000000000 : ℝ)|^4899 ≤ (11094530167277/100000000000000 : ℝ)^3875
        have hw : |(-878359701/5000000000 : ℝ)|=(878359701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591748007/5000000000 : ℝ)|^4899 ≤ (10893051147517/25000000000000 : ℝ)^3875
        have hw : |(2591748007/5000000000 : ℝ)|=(2591748007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s3_2 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069703673/2000000000 : ℝ)*x 0 + (5183495999/10000000000 : ℝ)*x 1 + (-21958993/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069703673/2000000000 : ℝ)^4899 ≤ (4533326508091/10000000000000 : ℝ)^3875 := by
    have hnat : (1069703673 : ℕ)^4899*10000000000000^3875 ≤ 4533326508091^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069703673 2000000000 4533326508091 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183495999/10000000000 : ℝ)^4899 ≤ (43572204430659/100000000000000 : ℝ)^3875 := by
    have hnat : (5183495999 : ℕ)^4899*100000000000000^3875 ≤ 43572204430659^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183495999 10000000000 43572204430659 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21958993/125000000 : ℝ)^4899 ≤ (2773632617671/25000000000000 : ℝ)^3875 := by
    have hnat : (21958993 : ℕ)^4899*25000000000000^3875 ≤ 2773632617671^3875*125000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21958993 125000000 2773632617671 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069703673/2000000000 : ℝ), (5183495999/10000000000 : ℝ), (-21958993/125000000 : ℝ)] ![(4533326508091/10000000000000 : ℝ), (43572204430659/100000000000000 : ℝ), (2773632617671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069703673/2000000000 : ℝ)|^4899 ≤ (4533326508091/10000000000000 : ℝ)^3875
        have hw : |(1069703673/2000000000 : ℝ)|=(1069703673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183495999/10000000000 : ℝ)|^4899 ≤ (43572204430659/100000000000000 : ℝ)^3875
        have hw : |(5183495999/10000000000 : ℝ)|=(5183495999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21958993/125000000 : ℝ)|^4899 ≤ (2773632617671/25000000000000 : ℝ)^3875
        have hw : |(-21958993/125000000 : ℝ)|=(21958993/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s3_3 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209228233/500000000 : ℝ)*x 0 + (1926653439/5000000000 : ℝ)*x 1 + (567021957/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209228233/500000000 : ℝ)^4899 ≤ (4155069879073/12500000000000 : ℝ)^3875 := by
    have hnat : (209228233 : ℕ)^4899*12500000000000^3875 ≤ 4155069879073^3875*500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209228233 500000000 4155069879073 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926653439/5000000000 : ℝ)^4899 ≤ (29949307562083/100000000000000 : ℝ)^3875 := by
    have hnat : (1926653439 : ℕ)^4899*100000000000000^3875 ≤ 29949307562083^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926653439 5000000000 29949307562083 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567021957/1250000000 : ℝ)^4899 ≤ (7362026680617/20000000000000 : ℝ)^3875 := by
    have hnat : (567021957 : ℕ)^4899*20000000000000^3875 ≤ 7362026680617^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567021957 1250000000 7362026680617 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209228233/500000000 : ℝ), (1926653439/5000000000 : ℝ), (567021957/1250000000 : ℝ)] ![(4155069879073/12500000000000 : ℝ), (29949307562083/100000000000000 : ℝ), (7362026680617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209228233/500000000 : ℝ)|^4899 ≤ (4155069879073/12500000000000 : ℝ)^3875
        have hw : |(209228233/500000000 : ℝ)|=(209228233/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1926653439/5000000000 : ℝ)|^4899 ≤ (29949307562083/100000000000000 : ℝ)^3875
        have hw : |(1926653439/5000000000 : ℝ)|=(1926653439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567021957/1250000000 : ℝ)|^4899 ≤ (7362026680617/20000000000000 : ℝ)^3875
        have hw : |(567021957/1250000000 : ℝ)|=(567021957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s3_4 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50625691/312500000 : ℝ)*x 0 + (2592751547/5000000000 : ℝ)*x 1 + (2723538041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50625691/312500000 : ℝ)^4899 ≤ (5007263900729/50000000000000 : ℝ)^3875 := by
    have hnat : (50625691 : ℕ)^4899*50000000000000^3875 ≤ 5007263900729^3875*312500000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50625691 312500000 5007263900729 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592751547/5000000000 : ℝ)^4899 ≤ (21796767750383/50000000000000 : ℝ)^3875 := by
    have hnat : (2592751547 : ℕ)^4899*50000000000000^3875 ≤ 21796767750383^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592751547 5000000000 21796767750383 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723538041/5000000000 : ℝ)^4899 ≤ (46391936680041/100000000000000 : ℝ)^3875 := by
    have hnat : (2723538041 : ℕ)^4899*100000000000000^3875 ≤ 46391936680041^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723538041 5000000000 46391936680041 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50625691/312500000 : ℝ), (2592751547/5000000000 : ℝ), (2723538041/5000000000 : ℝ)] ![(5007263900729/50000000000000 : ℝ), (21796767750383/50000000000000 : ℝ), (46391936680041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50625691/312500000 : ℝ)|^4899 ≤ (5007263900729/50000000000000 : ℝ)^3875
        have hw : |(-50625691/312500000 : ℝ)|=(50625691/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592751547/5000000000 : ℝ)|^4899 ≤ (21796767750383/50000000000000 : ℝ)^3875
        have hw : |(2592751547/5000000000 : ℝ)|=(2592751547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723538041/5000000000 : ℝ)|^4899 ≤ (46391936680041/100000000000000 : ℝ)^3875
        have hw : |(2723538041/5000000000 : ℝ)|=(2723538041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s3_5 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055520609/2000000000 : ℝ)*x 0 + (-1493139319/10000000000 : ℝ)*x 1 + (2723538041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055520609/2000000000 : ℝ)^4899 ≤ (44574695688359/100000000000000 : ℝ)^3875 := by
    have hnat : (1055520609 : ℕ)^4899*100000000000000^3875 ≤ 44574695688359^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055520609 2000000000 44574695688359 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1493139319/10000000000 : ℝ)^4899 ≤ (4516683806089/50000000000000 : ℝ)^3875 := by
    have hnat : (1493139319 : ℕ)^4899*50000000000000^3875 ≤ 4516683806089^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493139319 10000000000 4516683806089 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2723538041/5000000000 : ℝ)^4899 ≤ (46391936680041/100000000000000 : ℝ)^3875 := by
    have hnat : (2723538041 : ℕ)^4899*100000000000000^3875 ≤ 46391936680041^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723538041 5000000000 46391936680041 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055520609/2000000000 : ℝ), (-1493139319/10000000000 : ℝ), (2723538041/5000000000 : ℝ)] ![(44574695688359/100000000000000 : ℝ), (4516683806089/50000000000000 : ℝ), (46391936680041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055520609/2000000000 : ℝ)|^4899 ≤ (44574695688359/100000000000000 : ℝ)^3875
        have hw : |(1055520609/2000000000 : ℝ)|=(1055520609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1493139319/10000000000 : ℝ)|^4899 ≤ (4516683806089/50000000000000 : ℝ)^3875
        have hw : |(-1493139319/10000000000 : ℝ)|=(1493139319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2723538041/5000000000 : ℝ)|^4899 ≤ (46391936680041/100000000000000 : ℝ)^3875
        have hw : |(2723538041/5000000000 : ℝ)|=(2723538041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s3_6 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055520609/2000000000 : ℝ)*x 0 + (2723538041/5000000000 : ℝ)*x 1 + (-1493139319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055520609/2000000000 : ℝ)^4899 ≤ (44574695688359/100000000000000 : ℝ)^3875 := by
    have hnat : (1055520609 : ℕ)^4899*100000000000000^3875 ≤ 44574695688359^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055520609 2000000000 44574695688359 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723538041/5000000000 : ℝ)^4899 ≤ (46391936680041/100000000000000 : ℝ)^3875 := by
    have hnat : (2723538041 : ℕ)^4899*100000000000000^3875 ≤ 46391936680041^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723538041 5000000000 46391936680041 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493139319/10000000000 : ℝ)^4899 ≤ (4516683806089/50000000000000 : ℝ)^3875 := by
    have hnat : (1493139319 : ℕ)^4899*50000000000000^3875 ≤ 4516683806089^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493139319 10000000000 4516683806089 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055520609/2000000000 : ℝ), (2723538041/5000000000 : ℝ), (-1493139319/10000000000 : ℝ)] ![(44574695688359/100000000000000 : ℝ), (46391936680041/100000000000000 : ℝ), (4516683806089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055520609/2000000000 : ℝ)|^4899 ≤ (44574695688359/100000000000000 : ℝ)^3875
        have hw : |(1055520609/2000000000 : ℝ)|=(1055520609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723538041/5000000000 : ℝ)|^4899 ≤ (46391936680041/100000000000000 : ℝ)^3875
        have hw : |(2723538041/5000000000 : ℝ)|=(2723538041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1493139319/10000000000 : ℝ)|^4899 ≤ (4516683806089/50000000000000 : ℝ)^3875
        have hw : |(-1493139319/10000000000 : ℝ)|=(1493139319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s3_7 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130772881/312500000 : ℝ)*x 0 + (906203089/2000000000 : ℝ)*x 1 + (1929260733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130772881/312500000 : ℝ)^4899 ≤ (8310560381951/25000000000000 : ℝ)^3875 := by
    have hnat : (130772881 : ℕ)^4899*25000000000000^3875 ≤ 8310560381951^3875*312500000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130772881 312500000 8310560381951 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906203089/2000000000 : ℝ)^4899 ≤ (4594650219313/12500000000000 : ℝ)^3875 := by
    have hnat : (906203089 : ℕ)^4899*12500000000000^3875 ≤ 4594650219313^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906203089 2000000000 4594650219313 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929260733/5000000000 : ℝ)^4899 ≤ (1875034793599/6250000000000 : ℝ)^3875 := by
    have hnat : (1929260733 : ℕ)^4899*6250000000000^3875 ≤ 1875034793599^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929260733 5000000000 1875034793599 6250000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130772881/312500000 : ℝ), (906203089/2000000000 : ℝ), (1929260733/5000000000 : ℝ)] ![(8310560381951/25000000000000 : ℝ), (4594650219313/12500000000000 : ℝ), (1875034793599/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130772881/312500000 : ℝ)|^4899 ≤ (8310560381951/25000000000000 : ℝ)^3875
        have hw : |(130772881/312500000 : ℝ)|=(130772881/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906203089/2000000000 : ℝ)|^4899 ≤ (4594650219313/12500000000000 : ℝ)^3875
        have hw : |(906203089/2000000000 : ℝ)|=(906203089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1929260733/5000000000 : ℝ)|^4899 ≤ (1875034793599/6250000000000 : ℝ)^3875
        have hw : |(1929260733/5000000000 : ℝ)|=(1929260733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1645_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10639/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16283/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1321/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1321/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1321/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1321/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1321/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1321/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1321/12500 : ℝ) ^ (4895/1024 : ℝ) ≤ (2159825821676383/100000000000000000000 : ℝ) := by
    have hpowers : (1321/12500 : ℝ)^4895 ≤ (2159825821676383/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1321 : ℕ)^4895*100000000000000000000^1024 ≤ 2159825821676383^1024*12500^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1321 12500 2159825821676383 100000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1321/12500 : ℝ)) (X := (2159825821676383/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8181/50000 : ℝ) ^ (4895/1024 : ℝ) ≤ (17455125254910533/100000000000000000000 : ℝ) := by
    have hpowers : (8181/50000 : ℝ)^4895 ≤ (17455125254910533/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8181 : ℕ)^4895*100000000000000000000^1024 ≤ 17455125254910533^1024*50000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8181 50000 17455125254910533 100000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8181/50000 : ℝ)) (X := (17455125254910533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002159825821676383/50000000000000000000 : ℝ) ≤ (80000722900549/80000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (50002159825821676383/50000000000000000000 : ℝ)^1024 ≤ (80000722900549/80000000000000 : ℝ)^4895 := by
      have hnat : (50002159825821676383 : ℕ)^1024*80000000000000^4895 ≤ 80000722900549^4895*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002159825821676383 50000000000000000000 80000722900549 80000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80000722900549/80000000000000 : ℝ)) (X := (50002159825821676383/50000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004903737769146729/25000000000000000000 : ℝ) ≤ (10000410299331427/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (25004903737769146729/25000000000000000000 : ℝ)^1024 ≤ (10000410299331427/10000000000000000 : ℝ)^4895 := by
      have hnat : (25004903737769146729 : ℕ)^1024*10000000000000000^4895 ≤ 10000410299331427^4895*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004903737769146729 25000000000000000000 10000410299331427 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000410299331427/10000000000000000 : ℝ)) (X := (25004903737769146729/25000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017455125254910533/50000000000000000000 : ℝ) ≤ (10000730236094229/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (50017455125254910533/50000000000000000000 : ℝ)^1024 ≤ (10000730236094229/10000000000000000 : ℝ)^4895 := by
      have hnat : (50017455125254910533 : ℕ)^1024*10000000000000000^4895 ≤ 10000730236094229^4895*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017455125254910533 50000000000000000000 10000730236094229 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000730236094229/10000000000000000 : ℝ)) (X := (50017455125254910533/50000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2159825821676383/100000000000000000000 : ℝ) ≤ ((28966880688652015089/28970000000000000000 : ℝ)+2*(159968381401/289700000000000 : ℝ)*(1321/12500 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (28966880688652015089/28970000000000000000 : ℝ)+2*(159968381401/289700000000000 : ℝ)*(1321/12500 : ℝ)=(80000722900549/80000000000000 : ℝ) by norm_num, show 1+2*(2159825821676383/100000000000000000000 : ℝ)=(50002159825821676383/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17455125254910533/100000000000000000000 : ℝ)+(2159825821676383/100000000000000000000 : ℝ) ≤ ((28966880688652015089/28970000000000000000 : ℝ)+(159968381401/289700000000000 : ℝ)*((8181/50000 : ℝ)+(1321/12500 : ℝ)))^(4895/1024 : ℝ) := by
    rw [show (28966880688652015089/28970000000000000000 : ℝ)+(159968381401/289700000000000 : ℝ)*((8181/50000 : ℝ)+(1321/12500 : ℝ))=(10000410299331427/10000000000000000 : ℝ) by norm_num, show 1+(17455125254910533/100000000000000000000 : ℝ)+(2159825821676383/100000000000000000000 : ℝ)=(25004903737769146729/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17455125254910533/100000000000000000000 : ℝ) ≤ ((28966880688652015089/28970000000000000000 : ℝ)+2*(159968381401/289700000000000 : ℝ)*(8181/50000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (28966880688652015089/28970000000000000000 : ℝ)+2*(159968381401/289700000000000 : ℝ)*(8181/50000 : ℝ)=(10000730236094229/10000000000000000 : ℝ) by norm_num, show 1+2*(17455125254910533/100000000000000000000 : ℝ)=(50017455125254910533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28966880688652015089/28970000000000000000 : ℝ)*(X 1 0+X 2 0)+(159968381401/289700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (1321/12500 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (28966880688652015089/28970000000000000000 : ℝ)) (alpha := (159968381401/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28966880688652015089/28970000000000000000 : ℝ)*(X 0 1+X 2 1)+(159968381401/289700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (1321/12500 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (28966880688652015089/28970000000000000000 : ℝ)) (alpha := (159968381401/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28966880688652015089/28970000000000000000 : ℝ)*(X 0 2+X 1 2)+(159968381401/289700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (1321/12500 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (28966880688652015089/28970000000000000000 : ℝ)) (alpha := (159968381401/289700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-404989233/2500000000 : ℝ)*X 0 0+(2724552159/5000000000 : ℝ)*X 0 1+(2591748017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348518379/10000000000 : ℝ)*X 1 0+(-878359701/5000000000 : ℝ)*X 1 1+(2591748007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069703673/2000000000 : ℝ)*X 2 0+(5183495999/10000000000 : ℝ)*X 2 1+(-21958993/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209228233/500000000 : ℝ)*X 0 0+(1926653439/5000000000 : ℝ)*X 0 1+(567021957/1250000000 : ℝ)*X 0 2+(209228233/500000000 : ℝ)*X 1 0+(1926653439/5000000000 : ℝ)*X 1 1+(567021957/1250000000 : ℝ)*X 1 2+(209228233/500000000 : ℝ)*X 2 0+(1926653439/5000000000 : ℝ)*X 2 1+(567021957/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-50625691/312500000 : ℝ)*X 0 0+(2592751547/5000000000 : ℝ)*X 0 1+(2723538041/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055520609/2000000000 : ℝ)*X 1 0+(-1493139319/10000000000 : ℝ)*X 1 1+(2723538041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055520609/2000000000 : ℝ)*X 2 0+(2723538041/5000000000 : ℝ)*X 2 1+(-1493139319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((130772881/312500000 : ℝ)*X 0 0+(906203089/2000000000 : ℝ)*X 0 1+(1929260733/5000000000 : ℝ)*X 0 2+(130772881/312500000 : ℝ)*X 1 0+(906203089/2000000000 : ℝ)*X 1 1+(1929260733/5000000000 : ℝ)*X 1 2+(130772881/312500000 : ℝ)*X 2 0+(906203089/2000000000 : ℝ)*X 2 1+(1929260733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5683455641632802337285726849/724250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301027331/25000000000000 : ℝ)*(base19) + (27567423/2500000000000 : ℝ)*(base23) + (48969651/100000000000000 : ℝ)*(lower2) + (206359773/100000000000000 : ℝ)*(upper3) + (54493959/50000000000000 : ℝ)*(upper5) + (1307348588942649/50000000000000 : ℝ)*(major0) + (1307348588942649/50000000000000 : ℝ)*(major1) + (1307348588942649/50000000000000 : ℝ)*(major2) + (37649581050571/1000000000000 : ℝ)*(sp0) + (470621348666123/12500000000000 : ℝ)*(sp1) + (941242722685347/25000000000000 : ℝ)*(sp2) + (183051952579093/12500000000000 : ℝ)*(sp3) + (1736047651/12500000000000 : ℝ)*(sp4) + (1296024127/20000000000000 : ℝ)*(sp7) + (1464422100753379/100000000000000 : ℝ)*(f.failure) + (941242998359577/25000000000000 : ℝ)*(f.sum) + (18687602689271/7242500000000000000000000000 : ℝ)*base66 + (7839394271482969239/1448500000000000000000000000000000 : ℝ)*base68 + (5278016459526469239/1448500000000000000000000000000000 : ℝ)*base70 + (5404421935527469239/1448500000000000000000000000000000 : ℝ)*base72 + (11894757675583/14485000000000000000000000000 : ℝ)*base73 + (10072640281546469239/1448500000000000000000000000000000 : ℝ)*base76 + (11462329486801469239/1448500000000000000000000000000000 : ℝ)*base78 + (14878657061592969239/1448500000000000000000000000000000 : ℝ)*base80 + (3155185729173/3621250000000000000000000000 : ℝ)*base82 + (11025569/2000000000000000000000 : ℝ)*base89 + (11025569/2000000000000000000000 : ℝ)*base91 + (11025569/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1054012895529546920062476051/144850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107874659/10000000000000 : ℝ)*(base19) + (1166596549/100000000000000 : ℝ)*(base23) + (382483/250000000000 : ℝ)*(upper3) + (39541981/100000000000000 : ℝ)*(lower4) + (3017423/2000000000000 : ℝ)*(upper5) + (531002633520753/20000000000000 : ℝ)*(major0) + (531002633520753/20000000000000 : ℝ)*(major1) + (531002633520753/20000000000000 : ℝ)*(major2) + (3207297853/25000000000000 : ℝ)*(sp1) + (689557489/5000000000000 : ℝ)*(sp2) + (1911512041064761/50000000000000 : ℝ)*(sp4) + (23893813588697/625000000000 : ℝ)*(sp5) + (3823009124383193/100000000000000 : ℝ)*(sp6) + (148700201052527/10000000000000 : ℝ)*(sp7) + (148700201052527/10000000000000 : ℝ)*(f.failure) + (1911512041064761/50000000000000 : ℝ)*(f.sum) + (16804430228681/2897000000000000000000000000 : ℝ)*base65 + (4538143881063257983/579400000000000000000000000000000 : ℝ)*base68 + (5407824675099657983/579400000000000000000000000000000 : ℝ)*base70 + (2517734177438742017/579400000000000000000000000000000 : ℝ)*base71 + (4754300024509/2897000000000000000000000000 : ℝ)*base74 + (9064976387257257983/579400000000000000000000000000000 : ℝ)*base76 + (242059752319057983/579400000000000000000000000000000 : ℝ)*base78 + (6504093840916457983/579400000000000000000000000000000 : ℝ)*base80 + (253866941897/724250000000000000000000000 : ℝ)*base82 + (263003/200000000000000000000 : ℝ)*base90 + (263003/200000000000000000000 : ℝ)*base92 + (263003/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1645_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10639/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1645_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1645_s4_0 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-810003869/5000000000 : ℝ)*x 0 + (68110587/125000000 : ℝ)*x 1 + (5183719447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (810003869/5000000000 : ℝ)^4899 ≤ (1251801933071/12500000000000 : ℝ)^3875 := by
    have hnat : (810003869 : ℕ)^4899*12500000000000^3875 ≤ 1251801933071^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810003869 5000000000 1251801933071 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68110587/125000000 : ℝ)^4899 ≤ (46411005424139/100000000000000 : ℝ)^3875 := by
    have hnat : (68110587 : ℕ)^4899*100000000000000^3875 ≤ 46411005424139^3875*125000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68110587 125000000 46411005424139 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183719447/10000000000 : ℝ)^4899 ≤ (10893644772673/25000000000000 : ℝ)^3875 := by
    have hnat : (5183719447 : ℕ)^4899*25000000000000^3875 ≤ 10893644772673^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183719447 10000000000 10893644772673 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-810003869/5000000000 : ℝ), (68110587/125000000 : ℝ), (5183719447/10000000000 : ℝ)] ![(1251801933071/12500000000000 : ℝ), (46411005424139/100000000000000 : ℝ), (10893644772673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-810003869/5000000000 : ℝ)|^4899 ≤ (1251801933071/12500000000000 : ℝ)^3875
        have hw : |(-810003869/5000000000 : ℝ)|=(810003869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(68110587/125000000 : ℝ)|^4899 ≤ (46411005424139/100000000000000 : ℝ)^3875
        have hw : |(68110587/125000000 : ℝ)|=(68110587/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183719447/10000000000 : ℝ)|^4899 ≤ (10893644772673/25000000000000 : ℝ)^3875
        have hw : |(5183719447/10000000000 : ℝ)|=(5183719447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s4_1 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337112187/2500000000 : ℝ)*x 0 + (-351303099/2000000000 : ℝ)*x 1 + (5183719417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337112187/2500000000 : ℝ)^4899 ≤ (11333129772387/25000000000000 : ℝ)^3875 := by
    have hnat : (1337112187 : ℕ)^4899*25000000000000^3875 ≤ 11333129772387^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337112187 2500000000 11333129772387 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (351303099/2000000000 : ℝ)^4899 ≤ (1109290211733/10000000000000 : ℝ)^3875 := by
    have hnat : (351303099 : ℕ)^4899*10000000000000^3875 ≤ 1109290211733^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      351303099 2000000000 1109290211733 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183719417/10000000000 : ℝ)^4899 ≤ (4357457877187/10000000000000 : ℝ)^3875 := by
    have hnat : (5183719417 : ℕ)^4899*10000000000000^3875 ≤ 4357457877187^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183719417 10000000000 4357457877187 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337112187/2500000000 : ℝ), (-351303099/2000000000 : ℝ), (5183719417/10000000000 : ℝ)] ![(11333129772387/25000000000000 : ℝ), (1109290211733/10000000000000 : ℝ), (4357457877187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337112187/2500000000 : ℝ)|^4899 ≤ (11333129772387/25000000000000 : ℝ)^3875
        have hw : |(1337112187/2500000000 : ℝ)|=(1337112187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-351303099/2000000000 : ℝ)|^4899 ≤ (1109290211733/10000000000000 : ℝ)^3875
        have hw : |(-351303099/2000000000 : ℝ)|=(351303099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183719417/10000000000 : ℝ)|^4899 ≤ (4357457877187/10000000000000 : ℝ)^3875
        have hw : |(5183719417/10000000000 : ℝ)|=(5183719417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s4_2 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534844877/1000000000 : ℝ)*x 0 + (2591859707/5000000000 : ℝ)*x 1 + (-175651547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534844877/1000000000 : ℝ)^4899 ≤ (11333129831323/25000000000000 : ℝ)^3875 := by
    have hnat : (534844877 : ℕ)^4899*25000000000000^3875 ≤ 11333129831323^3875*1000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534844877 1000000000 11333129831323 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591859707/5000000000 : ℝ)^4899 ≤ (10893644684997/25000000000000 : ℝ)^3875 := by
    have hnat : (2591859707 : ℕ)^4899*25000000000000^3875 ≤ 10893644684997^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591859707 5000000000 10893644684997 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175651547/1000000000 : ℝ)^4899 ≤ (5546450958863/50000000000000 : ℝ)^3875 := by
    have hnat : (175651547 : ℕ)^4899*50000000000000^3875 ≤ 5546450958863^3875*1000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175651547 1000000000 5546450958863 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534844877/1000000000 : ℝ), (2591859707/5000000000 : ℝ), (-175651547/1000000000 : ℝ)] ![(11333129831323/25000000000000 : ℝ), (10893644684997/25000000000000 : ℝ), (5546450958863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534844877/1000000000 : ℝ)|^4899 ≤ (11333129831323/25000000000000 : ℝ)^3875
        have hw : |(534844877/1000000000 : ℝ)|=(534844877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591859707/5000000000 : ℝ)|^4899 ≤ (10893644684997/25000000000000 : ℝ)^3875
        have hw : |(2591859707/5000000000 : ℝ)|=(2591859707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175651547/1000000000 : ℝ)|^4899 ≤ (5546450958863/50000000000000 : ℝ)^3875
        have hw : |(-175651547/1000000000 : ℝ)|=(175651547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s4_3 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2092299037/5000000000 : ℝ)*x 0 + (3853921631/10000000000 : ℝ)*x 1 + (4535554111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092299037/5000000000 : ℝ)^4899 ≤ (33240894602249/100000000000000 : ℝ)^3875 := by
    have hnat : (2092299037 : ℕ)^4899*100000000000000^3875 ≤ 33240894602249^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092299037 5000000000 33240894602249 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3853921631/10000000000 : ℝ)^4899 ≤ (29955348421541/100000000000000 : ℝ)^3875 := by
    have hnat : (3853921631 : ℕ)^4899*100000000000000^3875 ≤ 29955348421541^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3853921631 10000000000 29955348421541 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4535554111/10000000000 : ℝ)^4899 ≤ (9200939241883/25000000000000 : ℝ)^3875 := by
    have hnat : (4535554111 : ℕ)^4899*25000000000000^3875 ≤ 9200939241883^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535554111 10000000000 9200939241883 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092299037/5000000000 : ℝ), (3853921631/10000000000 : ℝ), (4535554111/10000000000 : ℝ)] ![(33240894602249/100000000000000 : ℝ), (29955348421541/100000000000000 : ℝ), (9200939241883/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092299037/5000000000 : ℝ)|^4899 ≤ (33240894602249/100000000000000 : ℝ)^3875
        have hw : |(2092299037/5000000000 : ℝ)|=(2092299037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3853921631/10000000000 : ℝ)|^4899 ≤ (29955348421541/100000000000000 : ℝ)^3875
        have hw : |(3853921631/10000000000 : ℝ)|=(3853921631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4535554111/10000000000 : ℝ)|^4899 ≤ (9200939241883/25000000000000 : ℝ)^3875
        have hw : |(4535554111/10000000000 : ℝ)|=(4535554111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s4_4 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1620072571/10000000000 : ℝ)*x 0 + (129642983/250000000 : ℝ)*x 1 + (5446826023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1620072571/10000000000 : ℝ)^4899 ≤ (10014922154953/100000000000000 : ℝ)^3875 := by
    have hnat : (1620072571 : ℕ)^4899*100000000000000^3875 ≤ 10014922154953^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620072571 10000000000 10014922154953 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129642983/250000000 : ℝ)^4899 ≤ (43595833644747/100000000000000 : ℝ)^3875 := by
    have hnat : (129642983 : ℕ)^4899*100000000000000^3875 ≤ 43595833644747^3875*250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129642983 250000000 43595833644747 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446826023/10000000000 : ℝ)^4899 ≤ (371113953493/800000000000 : ℝ)^3875 := by
    have hnat : (5446826023 : ℕ)^4899*800000000000^3875 ≤ 371113953493^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446826023 10000000000 371113953493 800000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1620072571/10000000000 : ℝ), (129642983/250000000 : ℝ), (5446826023/10000000000 : ℝ)] ![(10014922154953/100000000000000 : ℝ), (43595833644747/100000000000000 : ℝ), (371113953493/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1620072571/10000000000 : ℝ)|^4899 ≤ (10014922154953/100000000000000 : ℝ)^3875
        have hw : |(-1620072571/10000000000 : ℝ)|=(1620072571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129642983/250000000 : ℝ)|^4899 ≤ (43595833644747/100000000000000 : ℝ)^3875
        have hw : |(129642983/250000000 : ℝ)|=(129642983/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446826023/10000000000 : ℝ)|^4899 ≤ (371113953493/800000000000 : ℝ)^3875
        have hw : |(5446826023/10000000000 : ℝ)|=(5446826023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s4_5 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659707761/1250000000 : ℝ)*x 0 + (-1493408909/10000000000 : ℝ)*x 1 + (5446826023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659707761/1250000000 : ℝ)^4899 ≤ (44575326146789/100000000000000 : ℝ)^3875 := by
    have hnat : (659707761 : ℕ)^4899*100000000000000^3875 ≤ 44575326146789^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659707761 1250000000 44575326146789 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1493408909/10000000000 : ℝ)^4899 ≤ (903542966233/10000000000000 : ℝ)^3875 := by
    have hnat : (1493408909 : ℕ)^4899*10000000000000^3875 ≤ 903542966233^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493408909 10000000000 903542966233 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446826023/10000000000 : ℝ)^4899 ≤ (371113953493/800000000000 : ℝ)^3875 := by
    have hnat : (5446826023 : ℕ)^4899*800000000000^3875 ≤ 371113953493^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446826023 10000000000 371113953493 800000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659707761/1250000000 : ℝ), (-1493408909/10000000000 : ℝ), (5446826023/10000000000 : ℝ)] ![(44575326146789/100000000000000 : ℝ), (903542966233/10000000000000 : ℝ), (371113953493/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659707761/1250000000 : ℝ)|^4899 ≤ (44575326146789/100000000000000 : ℝ)^3875
        have hw : |(659707761/1250000000 : ℝ)|=(659707761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1493408909/10000000000 : ℝ)|^4899 ≤ (903542966233/10000000000000 : ℝ)^3875
        have hw : |(-1493408909/10000000000 : ℝ)|=(1493408909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446826023/10000000000 : ℝ)|^4899 ≤ (371113953493/800000000000 : ℝ)^3875
        have hw : |(5446826023/10000000000 : ℝ)|=(5446826023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s4_6 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659707761/1250000000 : ℝ)*x 0 + (5446826023/10000000000 : ℝ)*x 1 + (-1493408909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659707761/1250000000 : ℝ)^4899 ≤ (44575326146789/100000000000000 : ℝ)^3875 := by
    have hnat : (659707761 : ℕ)^4899*100000000000000^3875 ≤ 44575326146789^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659707761 1250000000 44575326146789 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446826023/10000000000 : ℝ)^4899 ≤ (371113953493/800000000000 : ℝ)^3875 := by
    have hnat : (5446826023 : ℕ)^4899*800000000000^3875 ≤ 371113953493^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446826023 10000000000 371113953493 800000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493408909/10000000000 : ℝ)^4899 ≤ (903542966233/10000000000000 : ℝ)^3875 := by
    have hnat : (1493408909 : ℕ)^4899*10000000000000^3875 ≤ 903542966233^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493408909 10000000000 903542966233 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659707761/1250000000 : ℝ), (5446826023/10000000000 : ℝ), (-1493408909/10000000000 : ℝ)] ![(44575326146789/100000000000000 : ℝ), (371113953493/800000000000 : ℝ), (903542966233/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659707761/1250000000 : ℝ)|^4899 ≤ (44575326146789/100000000000000 : ℝ)^3875
        have hw : |(659707761/1250000000 : ℝ)|=(659707761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446826023/10000000000 : ℝ)|^4899 ≤ (371113953493/800000000000 : ℝ)^3875
        have hw : |(5446826023/10000000000 : ℝ)|=(5446826023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1493408909/10000000000 : ℝ)|^4899 ≤ (903542966233/10000000000000 : ℝ)^3875
        have hw : |(-1493408909/10000000000 : ℝ)|=(1493408909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s4_7 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184764683/10000000000 : ℝ)*x 0 + (4530412509/10000000000 : ℝ)*x 1 + (1929558667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184764683/10000000000 : ℝ)^4899 ≤ (1662128391571/5000000000000 : ℝ)^3875 := by
    have hnat : (4184764683 : ℕ)^4899*5000000000000^3875 ≤ 1662128391571^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184764683 10000000000 1662128391571 5000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530412509/10000000000 : ℝ)^4899 ≤ (7350203617167/20000000000000 : ℝ)^3875 := by
    have hnat : (4530412509 : ℕ)^4899*20000000000000^3875 ≤ 7350203617167^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530412509 10000000000 7350203617167 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929558667/5000000000 : ℝ)^4899 ≤ (30006414072861/100000000000000 : ℝ)^3875 := by
    have hnat : (1929558667 : ℕ)^4899*100000000000000^3875 ≤ 30006414072861^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929558667 5000000000 30006414072861 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184764683/10000000000 : ℝ), (4530412509/10000000000 : ℝ), (1929558667/5000000000 : ℝ)] ![(1662128391571/5000000000000 : ℝ), (7350203617167/20000000000000 : ℝ), (30006414072861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184764683/10000000000 : ℝ)|^4899 ≤ (1662128391571/5000000000000 : ℝ)^3875
        have hw : |(4184764683/10000000000 : ℝ)|=(4184764683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530412509/10000000000 : ℝ)|^4899 ≤ (7350203617167/20000000000000 : ℝ)^3875
        have hw : |(4530412509/10000000000 : ℝ)|=(4530412509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1929558667/5000000000 : ℝ)|^4899 ≤ (30006414072861/100000000000000 : ℝ)^3875
        have hw : |(1929558667/5000000000 : ℝ)|=(1929558667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1645_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2661/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8139/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10639/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16283/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10639/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10639/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16283/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10639/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10639/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16283/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10639/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10639/100000 : ℝ) ^ (4895/1024 : ℝ) ≤ (1115038310206517/50000000000000000000 : ℝ) := by
    have hpowers : (10639/100000 : ℝ)^4895 ≤ (1115038310206517/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10639 : ℕ)^4895*50000000000000000000^1024 ≤ 1115038310206517^1024*100000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10639 100000 1115038310206517 50000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10639/100000 : ℝ)) (X := (1115038310206517/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16283/100000 : ℝ) ^ (4895/1024 : ℝ) ≤ (17055914095957863/100000000000000000000 : ℝ) := by
    have hpowers : (16283/100000 : ℝ)^4895 ≤ (17055914095957863/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16283 : ℕ)^4895*100000000000000000000^1024 ≤ 17055914095957863^1024*100000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16283 100000 17055914095957863 100000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16283/100000 : ℝ)) (X := (17055914095957863/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001115038310206517/25000000000000000000 : ℝ) ≤ (10000093301662421/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (25001115038310206517/25000000000000000000 : ℝ)^1024 ≤ (10000093301662421/10000000000000000 : ℝ)^4895 := by
      have hnat : (25001115038310206517 : ℕ)^1024*10000000000000000^4895 ≤ 10000093301662421^4895*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001115038310206517 25000000000000000000 10000093301662421 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000093301662421/10000000000000000 : ℝ)) (X := (25001115038310206517/25000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019285990716370897/100000000000000000000 : ℝ) ≤ (4000161367507/4000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (100019285990716370897/100000000000000000000 : ℝ)^1024 ≤ (4000161367507/4000000000000 : ℝ)^4895 := by
      have hnat : (100019285990716370897 : ℕ)^1024*4000000000000^4895 ≤ 4000161367507^4895*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019285990716370897 100000000000000000000 4000161367507 4000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4000161367507/4000000000000 : ℝ)) (X := (100019285990716370897/100000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017055914095957863/50000000000000000000 : ℝ) ≤ (10000713535872579/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (50017055914095957863/50000000000000000000 : ℝ)^1024 ≤ (10000713535872579/10000000000000000 : ℝ)^4895 := by
      have hnat : (50017055914095957863 : ℕ)^1024*10000000000000000^4895 ≤ 10000713535872579^4895*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017055914095957863 50000000000000000000 10000713535872579 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000713535872579/10000000000000000 : ℝ)) (X := (50017055914095957863/50000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1115038310206517/50000000000000000000 : ℝ) ≤ ((28216963961410416581/28220000000000000000 : ℝ)+2*(310117105079/564400000000000 : ℝ)*(10639/100000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (28216963961410416581/28220000000000000000 : ℝ)+2*(310117105079/564400000000000 : ℝ)*(10639/100000 : ℝ)=(10000093301662421/10000000000000000 : ℝ) by norm_num, show 1+2*(1115038310206517/50000000000000000000 : ℝ)=(25001115038310206517/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17055914095957863/100000000000000000000 : ℝ)+(1115038310206517/50000000000000000000 : ℝ) ≤ ((28216963961410416581/28220000000000000000 : ℝ)+(310117105079/564400000000000 : ℝ)*((16283/100000 : ℝ)+(10639/100000 : ℝ)))^(4895/1024 : ℝ) := by
    rw [show (28216963961410416581/28220000000000000000 : ℝ)+(310117105079/564400000000000 : ℝ)*((16283/100000 : ℝ)+(10639/100000 : ℝ))=(4000161367507/4000000000000 : ℝ) by norm_num, show 1+(17055914095957863/100000000000000000000 : ℝ)+(1115038310206517/50000000000000000000 : ℝ)=(100019285990716370897/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17055914095957863/100000000000000000000 : ℝ) ≤ ((28216963961410416581/28220000000000000000 : ℝ)+2*(310117105079/564400000000000 : ℝ)*(16283/100000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (28216963961410416581/28220000000000000000 : ℝ)+2*(310117105079/564400000000000 : ℝ)*(16283/100000 : ℝ)=(10000713535872579/10000000000000000 : ℝ) by norm_num, show 1+2*(17055914095957863/100000000000000000000 : ℝ)=(50017055914095957863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28216963961410416581/28220000000000000000 : ℝ)*(X 1 0+X 2 0)+(310117105079/564400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (10639/100000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (28216963961410416581/28220000000000000000 : ℝ)) (alpha := (310117105079/564400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28216963961410416581/28220000000000000000 : ℝ)*(X 0 1+X 2 1)+(310117105079/564400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (10639/100000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (28216963961410416581/28220000000000000000 : ℝ)) (alpha := (310117105079/564400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28216963961410416581/28220000000000000000 : ℝ)*(X 0 2+X 1 2)+(310117105079/564400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (10639/100000 : ℝ)) (hi := (16283/100000 : ℝ)) (c := (28216963961410416581/28220000000000000000 : ℝ)) (alpha := (310117105079/564400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-810003869/5000000000 : ℝ)*X 0 0+(68110587/125000000 : ℝ)*X 0 1+(5183719447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337112187/2500000000 : ℝ)*X 1 0+(-351303099/2000000000 : ℝ)*X 1 1+(5183719417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534844877/1000000000 : ℝ)*X 2 0+(2591859707/5000000000 : ℝ)*X 2 1+(-175651547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2092299037/5000000000 : ℝ)*X 0 0+(3853921631/10000000000 : ℝ)*X 0 1+(4535554111/10000000000 : ℝ)*X 0 2+(2092299037/5000000000 : ℝ)*X 1 0+(3853921631/10000000000 : ℝ)*X 1 1+(4535554111/10000000000 : ℝ)*X 1 2+(2092299037/5000000000 : ℝ)*X 2 0+(3853921631/10000000000 : ℝ)*X 2 1+(4535554111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1620072571/10000000000 : ℝ)*X 0 0+(129642983/250000000 : ℝ)*X 0 1+(5446826023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659707761/1250000000 : ℝ)*X 1 0+(-1493408909/10000000000 : ℝ)*X 1 1+(5446826023/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659707761/1250000000 : ℝ)*X 2 0+(5446826023/10000000000 : ℝ)*X 2 1+(-1493408909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4184764683/10000000000 : ℝ)*X 0 0+(4530412509/10000000000 : ℝ)*X 0 1+(1929558667/5000000000 : ℝ)*X 0 2+(4184764683/10000000000 : ℝ)*X 1 0+(4530412509/10000000000 : ℝ)*X 1 1+(1929558667/5000000000 : ℝ)*X 1 2+(4184764683/10000000000 : ℝ)*X 2 0+(4530412509/10000000000 : ℝ)*X 2 1+(1929558667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (160721547575233103337911793/28220000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (928145253/100000000000000 : ℝ)*(base19) + (54080983/6250000000000 : ℝ)*(base23) + (4191269/10000000000000 : ℝ)*(lower2) + (3261059/2500000000000 : ℝ)*(upper3) + (96336173/100000000000000 : ℝ)*(upper5) + (52388685415649/2000000000000 : ℝ)*(major0) + (52388685415649/2000000000000 : ℝ)*(major1) + (52388685415649/2000000000000 : ℝ)*(major2) + (3771781529414757/100000000000000 : ℝ)*(sp0) + (1885896101764109/50000000000000 : ℝ)*(sp1) + (235737016648609/6250000000000 : ℝ)*(sp2) + (29341409117987/2000000000000 : ℝ)*(sp3) + (2320451743/20000000000000 : ℝ)*(sp4) + (1191037131/25000000000000 : ℝ)*(sp7) + (11736601760383/800000000000 : ℝ)*(f.failure) + (29467133841199/781250000000 : ℝ)*(f.sum) + (9026142350613/2822000000000000000000000000 : ℝ)*base65 + (16808552723813931/56440000000000000000000000000000 : ℝ)*base68 + (38547750933573931/56440000000000000000000000000000 : ℝ)*base70 + (280539278977386069/56440000000000000000000000000000 : ℝ)*base71 + (1069358719123/2822000000000000000000000000 : ℝ)*base73 + (146361593278346069/56440000000000000000000000000000 : ℝ)*base75 + (364781407602346069/56440000000000000000000000000000 : ℝ)*base77 + (109737857321946069/56440000000000000000000000000000 : ℝ)*base79 + (7240072235463/2822000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (141013/16000000000000000000 : ℝ)*base89 + (141013/16000000000000000000 : ℝ)*base91 + (141013/16000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8184048306419930392568039619/705500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (857836317/50000000000000 : ℝ)*(base19) + (371061953/20000000000000 : ℝ)*(base23) + (107607887/20000000000000 : ℝ)*(lower1) + (48627233/20000000000000 : ℝ)*(upper3) + (62928637/100000000000000 : ℝ)*(lower4) + (60096381/25000000000000 : ℝ)*(upper5) + (1329870016051089/50000000000000 : ℝ)*(major0) + (1329870016051089/50000000000000 : ℝ)*(major1) + (1329870016051089/50000000000000 : ℝ)*(major2) + (1521066541/100000000000000 : ℝ)*(sp2) + (957457569089827/25000000000000 : ℝ)*(sp4) + (153193142427467/4000000000000 : ℝ)*(sp5) + (3829826899983003/100000000000000 : ℝ)*(sp6) + (1489649401166637/100000000000000 : ℝ)*(sp7) + (1489649401166637/100000000000000 : ℝ)*(f.failure) + (957457569089827/25000000000000 : ℝ)*(f.sum) + (21848827116701/14110000000000000000000000000 : ℝ)*base65 + (22573289870197256709/1411000000000000000000000000000000 : ℝ)*base67 + (7601500386058256709/1411000000000000000000000000000000 : ℝ)*base69 + (48592037198539256709/1411000000000000000000000000000000 : ℝ)*base71 + (64580475956651/14110000000000000000000000000 : ℝ)*base73 + (13772266982807256709/1411000000000000000000000000000000 : ℝ)*base75 + (4593081799165256709/1411000000000000000000000000000000 : ℝ)*base77 + (15788942975684256709/1411000000000000000000000000000000 : ℝ)*base79 + (20345470776679/14110000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6551793/2000000000000000000000 : ℝ)*base90 + (6551793/2000000000000000000000 : ℝ)*base92 + (6551793/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1645_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16283/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10639/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8139/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1645_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1645_s5_0 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348444299/10000000000 : ℝ)*x 0 + (647966779/1250000000 : ℝ)*x 1 + (-1756501747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348444299/10000000000 : ℝ)^4899 ≤ (1416639731741/3125000000000 : ℝ)^3875 := by
    have hnat : (5348444299 : ℕ)^4899*3125000000000^3875 ≤ 1416639731741^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348444299 10000000000 1416639731741 3125000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647966779/1250000000 : ℝ)^4899 ≤ (10893684054253/25000000000000 : ℝ)^3875 := by
    have hnat : (647966779 : ℕ)^4899*25000000000000^3875 ≤ 10893684054253^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647966779 1250000000 10893684054253 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1756501747/10000000000 : ℝ)^4899 ≤ (1386599043911/12500000000000 : ℝ)^3875 := by
    have hnat : (1756501747 : ℕ)^4899*12500000000000^3875 ≤ 1386599043911^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1756501747 10000000000 1386599043911 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348444299/10000000000 : ℝ), (647966779/1250000000 : ℝ), (-1756501747/10000000000 : ℝ)] ![(1416639731741/3125000000000 : ℝ), (10893684054253/25000000000000 : ℝ), (1386599043911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348444299/10000000000 : ℝ)|^4899 ≤ (1416639731741/3125000000000 : ℝ)^3875
        have hw : |(5348444299/10000000000 : ℝ)|=(5348444299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647966779/1250000000 : ℝ)|^4899 ≤ (10893684054253/25000000000000 : ℝ)^3875
        have hw : |(647966779/1250000000 : ℝ)|=(647966779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1756501747/10000000000 : ℝ)|^4899 ≤ (1386599043911/12500000000000 : ℝ)^3875
        have hw : |(-1756501747/10000000000 : ℝ)|=(1756501747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s5_1 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1620075337/10000000000 : ℝ)*x 0 + (1296433403/2500000000 : ℝ)*x 1 + (1361702477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1620075337/10000000000 : ℝ)^4899 ≤ (2503735943059/25000000000000 : ℝ)^3875 := by
    have hnat : (1620075337 : ℕ)^4899*25000000000000^3875 ≤ 2503735943059^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620075337 10000000000 2503735943059 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296433403/2500000000 : ℝ)^4899 ≤ (1362374548351/3125000000000 : ℝ)^3875 := by
    have hnat : (1296433403 : ℕ)^4899*3125000000000^3875 ≤ 1362374548351^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296433403 2500000000 1362374548351 3125000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1361702477/2500000000 : ℝ)^4899 ≤ (4638907067057/10000000000000 : ℝ)^3875 := by
    have hnat : (1361702477 : ℕ)^4899*10000000000000^3875 ≤ 4638907067057^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1361702477 2500000000 4638907067057 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1620075337/10000000000 : ℝ), (1296433403/2500000000 : ℝ), (1361702477/2500000000 : ℝ)] ![(2503735943059/25000000000000 : ℝ), (1362374548351/3125000000000 : ℝ), (4638907067057/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1620075337/10000000000 : ℝ)|^4899 ≤ (2503735943059/25000000000000 : ℝ)^3875
        have hw : |(-1620075337/10000000000 : ℝ)|=(1620075337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296433403/2500000000 : ℝ)|^4899 ≤ (1362374548351/3125000000000 : ℝ)^3875
        have hw : |(1296433403/2500000000 : ℝ)|=(1296433403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1361702477/2500000000 : ℝ)|^4899 ≤ (4638907067057/10000000000000 : ℝ)^3875
        have hw : |(1361702477/2500000000 : ℝ)|=(1361702477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s5_2 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277666067/10000000000 : ℝ)*x 0 + (-1493425907/10000000000 : ℝ)*x 1 + (5446810001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277666067/10000000000 : ℝ)^4899 ≤ (22287684317217/50000000000000 : ℝ)^3875 := by
    have hnat : (5277666067 : ℕ)^4899*50000000000000^3875 ≤ 22287684317217^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277666067 10000000000 22287684317217 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1493425907/10000000000 : ℝ)^4899 ≤ (903555968057/10000000000000 : ℝ)^3875 := by
    have hnat : (1493425907 : ℕ)^4899*10000000000000^3875 ≤ 903555968057^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493425907 10000000000 903555968057 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446810001/10000000000 : ℝ)^4899 ≤ (23194535835967/50000000000000 : ℝ)^3875 := by
    have hnat : (5446810001 : ℕ)^4899*50000000000000^3875 ≤ 23194535835967^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446810001 10000000000 23194535835967 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277666067/10000000000 : ℝ), (-1493425907/10000000000 : ℝ), (5446810001/10000000000 : ℝ)] ![(22287684317217/50000000000000 : ℝ), (903555968057/10000000000000 : ℝ), (23194535835967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277666067/10000000000 : ℝ)|^4899 ≤ (22287684317217/50000000000000 : ℝ)^3875
        have hw : |(5277666067/10000000000 : ℝ)|=(5277666067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1493425907/10000000000 : ℝ)|^4899 ≤ (903555968057/10000000000000 : ℝ)^3875
        have hw : |(-1493425907/10000000000 : ℝ)|=(1493425907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446810001/10000000000 : ℝ)|^4899 ≤ (23194535835967/50000000000000 : ℝ)^3875
        have hw : |(5446810001/10000000000 : ℝ)|=(5446810001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s5_3 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659708273/1250000000 : ℝ)*x 0 + (5446809849/10000000000 : ℝ)*x 1 + (-373356489/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659708273/1250000000 : ℝ)^4899 ≤ (44575369883757/100000000000000 : ℝ)^3875 := by
    have hnat : (659708273 : ℕ)^4899*100000000000000^3875 ≤ 44575369883757^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659708273 1250000000 44575369883757 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446809849/10000000000 : ℝ)^4899 ≤ (1449658438603/3125000000000 : ℝ)^3875 := by
    have hnat : (5446809849 : ℕ)^4899*3125000000000^3875 ≤ 1449658438603^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446809849 10000000000 1449658438603 3125000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373356489/2500000000 : ℝ)^4899 ≤ (9035560055373/100000000000000 : ℝ)^3875 := by
    have hnat : (373356489 : ℕ)^4899*100000000000000^3875 ≤ 9035560055373^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373356489 2500000000 9035560055373 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659708273/1250000000 : ℝ), (5446809849/10000000000 : ℝ), (-373356489/2500000000 : ℝ)] ![(44575369883757/100000000000000 : ℝ), (1449658438603/3125000000000 : ℝ), (9035560055373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659708273/1250000000 : ℝ)|^4899 ≤ (44575369883757/100000000000000 : ℝ)^3875
        have hw : |(659708273/1250000000 : ℝ)|=(659708273/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446809849/10000000000 : ℝ)|^4899 ≤ (1449658438603/3125000000000 : ℝ)^3875
        have hw : |(5446809849/10000000000 : ℝ)|=(5446809849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373356489/2500000000 : ℝ)|^4899 ≤ (9035560055373/100000000000000 : ℝ)^3875
        have hw : |(-373356489/2500000000 : ℝ)|=(373356489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s5_4 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184766749/10000000000 : ℝ)*x 0 + (70787083/156250000 : ℝ)*x 1 + (964789029/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184766749/10000000000 : ℝ)^4899 ≤ (33242588580059/100000000000000 : ℝ)^3875 := by
    have hnat : (4184766749 : ℕ)^4899*100000000000000^3875 ≤ 33242588580059^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184766749 10000000000 33242588580059 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70787083/156250000 : ℝ)^4899 ≤ (36750616091723/100000000000000 : ℝ)^3875 := by
    have hnat : (70787083 : ℕ)^4899*100000000000000^3875 ≤ 36750616091723^3875*156250000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70787083 156250000 36750616091723 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964789029/2500000000 : ℝ)^4899 ≤ (30006795307739/100000000000000 : ℝ)^3875 := by
    have hnat : (964789029 : ℕ)^4899*100000000000000^3875 ≤ 30006795307739^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964789029 2500000000 30006795307739 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184766749/10000000000 : ℝ), (70787083/156250000 : ℝ), (964789029/2500000000 : ℝ)] ![(33242588580059/100000000000000 : ℝ), (36750616091723/100000000000000 : ℝ), (30006795307739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184766749/10000000000 : ℝ)|^4899 ≤ (33242588580059/100000000000000 : ℝ)^3875
        have hw : |(4184766749/10000000000 : ℝ)|=(4184766749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70787083/156250000 : ℝ)|^4899 ≤ (36750616091723/100000000000000 : ℝ)^3875
        have hw : |(70787083/156250000 : ℝ)|=(70787083/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(964789029/2500000000 : ℝ)|^4899 ≤ (30006795307739/100000000000000 : ℝ)^3875
        have hw : |(964789029/2500000000 : ℝ)|=(964789029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1645_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8139/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2661/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16277/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8139/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8139/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8139/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8139/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8139/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8139/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2661/25000 : ℝ) ^ (4895/1024 : ℝ) ≤ (2235091118876023/100000000000000000000 : ℝ) := by
    have hpowers : (2661/25000 : ℝ)^4895 ≤ (2235091118876023/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2661 : ℕ)^4895*100000000000000000000^1024 ≤ 2235091118876023^1024*25000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2661 25000 2235091118876023 100000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2661/25000 : ℝ)) (X := (2235091118876023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8139/50000 : ℝ) ^ (4895/1024 : ℝ) ≤ (17030892716210949/100000000000000000000 : ℝ) := by
    have hpowers : (8139/50000 : ℝ)^4895 ≤ (17030892716210949/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8139 : ℕ)^4895*100000000000000000000^1024 ≤ 17030892716210949^1024*50000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8139 50000 17030892716210949 100000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8139/50000 : ℝ)) (X := (17030892716210949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002235091118876023/50000000000000000000 : ℝ) ≤ (10000093511454663/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (50002235091118876023/50000000000000000000 : ℝ)^1024 ≤ (10000093511454663/10000000000000000 : ℝ)^4895 := by
      have hnat : (50002235091118876023 : ℕ)^1024*10000000000000000^4895 ≤ 10000093511454663^4895*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002235091118876023 50000000000000000000 10000093511454663 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000093511454663/10000000000000000 : ℝ)) (X := (50002235091118876023/50000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004816495958771743/25000000000000000000 : ℝ) ≤ (2500100750075307/2500000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (25004816495958771743/25000000000000000000 : ℝ)^1024 ≤ (2500100750075307/2500000000000000 : ℝ)^4895 := by
      have hnat : (25004816495958771743 : ℕ)^1024*2500000000000000^4895 ≤ 2500100750075307^4895*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004816495958771743 25000000000000000000 2500100750075307 2500000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500100750075307/2500000000000000 : ℝ)) (X := (25004816495958771743/25000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017030892716210949/50000000000000000000 : ℝ) ≤ (10000712489147793/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (50017030892716210949/50000000000000000000 : ℝ)^1024 ≤ (10000712489147793/10000000000000000 : ℝ)^4895 := by
      have hnat : (50017030892716210949 : ℕ)^1024*10000000000000000^4895 ≤ 10000712489147793^4895*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017030892716210949 50000000000000000000 10000712489147793 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000712489147793/10000000000000000 : ℝ)) (X := (50017030892716210949/50000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2235091118876023/100000000000000000000 : ℝ) ≤ ((3129663246942771979/3130000000000000000 : ℝ)+2*(20632589771/37560000000000 : ℝ)*(2661/25000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (3129663246942771979/3130000000000000000 : ℝ)+2*(20632589771/37560000000000 : ℝ)*(2661/25000 : ℝ)=(10000093511454663/10000000000000000 : ℝ) by norm_num, show 1+2*(2235091118876023/100000000000000000000 : ℝ)=(50002235091118876023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17030892716210949/100000000000000000000 : ℝ)+(2235091118876023/100000000000000000000 : ℝ) ≤ ((3129663246942771979/3130000000000000000 : ℝ)+(20632589771/37560000000000 : ℝ)*((8139/50000 : ℝ)+(2661/25000 : ℝ)))^(4895/1024 : ℝ) := by
    rw [show (3129663246942771979/3130000000000000000 : ℝ)+(20632589771/37560000000000 : ℝ)*((8139/50000 : ℝ)+(2661/25000 : ℝ))=(2500100750075307/2500000000000000 : ℝ) by norm_num, show 1+(17030892716210949/100000000000000000000 : ℝ)+(2235091118876023/100000000000000000000 : ℝ)=(25004816495958771743/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17030892716210949/100000000000000000000 : ℝ) ≤ ((3129663246942771979/3130000000000000000 : ℝ)+2*(20632589771/37560000000000 : ℝ)*(8139/50000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (3129663246942771979/3130000000000000000 : ℝ)+2*(20632589771/37560000000000 : ℝ)*(8139/50000 : ℝ)=(10000712489147793/10000000000000000 : ℝ) by norm_num, show 1+2*(17030892716210949/100000000000000000000 : ℝ)=(50017030892716210949/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3129663246942771979/3130000000000000000 : ℝ)*(X 1 0+X 2 0)+(20632589771/37560000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (8139/50000 : ℝ)) (c := (3129663246942771979/3130000000000000000 : ℝ)) (alpha := (20632589771/37560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3129663246942771979/3130000000000000000 : ℝ)*(X 0 1+X 2 1)+(20632589771/37560000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (8139/50000 : ℝ)) (c := (3129663246942771979/3130000000000000000 : ℝ)) (alpha := (20632589771/37560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3129663246942771979/3130000000000000000 : ℝ)*(X 0 2+X 1 2)+(20632589771/37560000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2661/25000 : ℝ)) (hi := (8139/50000 : ℝ)) (c := (3129663246942771979/3130000000000000000 : ℝ)) (alpha := (20632589771/37560000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348444299/10000000000 : ℝ)*X 2 0+(647966779/1250000000 : ℝ)*X 2 1+(-1756501747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s5_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1620075337/10000000000 : ℝ)*X 0 0+(1296433403/2500000000 : ℝ)*X 0 1+(1361702477/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s5_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5277666067/10000000000 : ℝ)*X 1 0+(-1493425907/10000000000 : ℝ)*X 1 1+(5446810001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s5_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((659708273/1250000000 : ℝ)*X 2 0+(5446809849/10000000000 : ℝ)*X 2 1+(-373356489/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s5_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4184766749/10000000000 : ℝ)*X 0 0+(70787083/156250000 : ℝ)*X 0 1+(964789029/2500000000 : ℝ)*X 0 2+(4184766749/10000000000 : ℝ)*X 1 0+(70787083/156250000 : ℝ)*X 1 1+(964789029/2500000000 : ℝ)*X 1 2+(4184766749/10000000000 : ℝ)*X 2 0+(70787083/156250000 : ℝ)*X 2 1+(964789029/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s5_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (326284447479217884739/78250000000000000000000000 : ℝ) := by norm_num
    linear_combination (594821439/100000000000000 : ℝ)*(base19) + (178073057/25000000000000 : ℝ)*(base23) + (209356771/100000000000000 : ℝ)*(lower1) + (97098419/100000000000000 : ℝ)*(upper3) + (3798849/25000000000000 : ℝ)*(lower4) + (70402963/100000000000000 : ℝ)*(upper5) + (665014672409059/25000000000000 : ℝ)*(major0) + (665014672409059/25000000000000 : ℝ)*(major1) + (665014672409059/25000000000000 : ℝ)*(major2) + (140395401/50000000000000 : ℝ)*(sp0) + (3830289367533941/100000000000000 : ℝ)*(sp1) + (1915144386356251/50000000000000 : ℝ)*(sp2) + (3830288374450911/100000000000000 : ℝ)*(sp3) + (372456968186553/25000000000000 : ℝ)*(sp4) + (372456968186553/25000000000000 : ℝ)*(f.failure) + (3830289367533941/100000000000000 : ℝ)*(f.sum) + (4612393108091/939000000000000000000000000 : ℝ)*base66 + (1830253717075876717/234750000000000000000000000000000 : ℝ)*base68 + (631921426930123283/234750000000000000000000000000000 : ℝ)*base69 + (4590339843939376717/234750000000000000000000000000000 : ℝ)*base72 + (494437504451/117375000000000000000000000 : ℝ)*base73 + (8388639604191376717/234750000000000000000000000000000 : ℝ)*base76 + (252749426327623283/234750000000000000000000000000000 : ℝ)*base77 + (1699111212241873283/234750000000000000000000000000000 : ℝ)*base79 + (40120903013/23475000000000000000000000 : ℝ)*base82 + (3060883/500000000000000000000 : ℝ)*base89 + (3060883/500000000000000000000 : ℝ)*base91 + (3060883/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1645_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8139/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1645_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1645_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1645_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1645_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1645_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1645_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
