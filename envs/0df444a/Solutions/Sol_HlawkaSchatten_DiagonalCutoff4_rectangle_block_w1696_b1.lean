-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1696_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:43:37.766472+00:00
-- url     : https://prove2.me/submissions/809f75b0-9f67-4c99-a232-c4a4fd546f69

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
theorem support_rectangle_w1696_s3_0 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1464306673/10000000000 : ℝ)*x 0 + (1369792421/2500000000 : ℝ)*x 1 + (1027261839/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1464306673/10000000000 : ℝ)^5191 ≤ (4566297252779/50000000000000 : ℝ)^4167 := by
    have hnat : (1464306673 : ℕ)^5191*50000000000000^4167 ≤ 4566297252779^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464306673 10000000000 4566297252779 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369792421/2500000000 : ℝ)^5191 ≤ (4726138276271/10000000000000 : ℝ)^4167 := by
    have hnat : (1369792421 : ℕ)^5191*10000000000000^4167 ≤ 4726138276271^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369792421 2500000000 4726138276271 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027261839/2000000000 : ℝ)^5191 ≤ (43606022725283/100000000000000 : ℝ)^4167 := by
    have hnat : (1027261839 : ℕ)^5191*100000000000000^4167 ≤ 43606022725283^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027261839 2000000000 43606022725283 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1464306673/10000000000 : ℝ), (1369792421/2500000000 : ℝ), (1027261839/2000000000 : ℝ)] ![(4566297252779/50000000000000 : ℝ), (4726138276271/10000000000000 : ℝ), (43606022725283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1464306673/10000000000 : ℝ)|^5191 ≤ (4566297252779/50000000000000 : ℝ)^4167
        have hw : |(-1464306673/10000000000 : ℝ)|=(1464306673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369792421/2500000000 : ℝ)|^5191 ≤ (4726138276271/10000000000000 : ℝ)^4167
        have hw : |(1369792421/2500000000 : ℝ)|=(1369792421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027261839/2000000000 : ℝ)|^5191 ≤ (43606022725283/100000000000000 : ℝ)^4167
        have hw : |(1027261839/2000000000 : ℝ)|=(1027261839/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s3_1 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337053621/2500000000 : ℝ)*x 0 + (-1642304037/10000000000 : ℝ)*x 1 + (2568154709/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337053621/2500000000 : ℝ)^5191 ≤ (9171677032453/20000000000000 : ℝ)^4167 := by
    have hnat : (1337053621 : ℕ)^5191*20000000000000^4167 ≤ 9171677032453^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337053621 2500000000 9171677032453 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1642304037/10000000000 : ℝ)^5191 ≤ (10535589748303/100000000000000 : ℝ)^4167 := by
    have hnat : (1642304037 : ℕ)^5191*100000000000000^4167 ≤ 10535589748303^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642304037 10000000000 10535589748303 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568154709/5000000000 : ℝ)^5191 ≤ (21803012541869/50000000000000 : ℝ)^4167 := by
    have hnat : (2568154709 : ℕ)^5191*50000000000000^4167 ≤ 21803012541869^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568154709 5000000000 21803012541869 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337053621/2500000000 : ℝ), (-1642304037/10000000000 : ℝ), (2568154709/5000000000 : ℝ)] ![(9171677032453/20000000000000 : ℝ), (10535589748303/100000000000000 : ℝ), (21803012541869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337053621/2500000000 : ℝ)|^5191 ≤ (9171677032453/20000000000000 : ℝ)^4167
        have hw : |(1337053621/2500000000 : ℝ)|=(1337053621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1642304037/10000000000 : ℝ)|^5191 ≤ (10535589748303/100000000000000 : ℝ)^4167
        have hw : |(-1642304037/10000000000 : ℝ)|=(1642304037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568154709/5000000000 : ℝ)|^5191 ≤ (21803012541869/50000000000000 : ℝ)^4167
        have hw : |(2568154709/5000000000 : ℝ)|=(2568154709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s3_2 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348214301/10000000000 : ℝ)*x 0 + (5136309567/10000000000 : ℝ)*x 1 + (-410576021/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348214301/10000000000 : ℝ)^5191 ≤ (45858383207527/100000000000000 : ℝ)^4167 := by
    have hnat : (5348214301 : ℕ)^5191*100000000000000^4167 ≤ 45858383207527^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348214301 10000000000 45858383207527 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5136309567/10000000000 : ℝ)^5191 ≤ (43606026659567/100000000000000 : ℝ)^4167 := by
    have hnat : (5136309567 : ℕ)^5191*100000000000000^4167 ≤ 43606026659567^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5136309567 10000000000 43606026659567 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410576021/2500000000 : ℝ)^5191 ≤ (10535590123907/100000000000000 : ℝ)^4167 := by
    have hnat : (410576021 : ℕ)^5191*100000000000000^4167 ≤ 10535590123907^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410576021 2500000000 10535590123907 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348214301/10000000000 : ℝ), (5136309567/10000000000 : ℝ), (-410576021/2500000000 : ℝ)] ![(45858383207527/100000000000000 : ℝ), (43606026659567/100000000000000 : ℝ), (10535590123907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348214301/10000000000 : ℝ)|^5191 ≤ (45858383207527/100000000000000 : ℝ)^4167
        have hw : |(5348214301/10000000000 : ℝ)|=(5348214301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5136309567/10000000000 : ℝ)|^5191 ≤ (43606026659567/100000000000000 : ℝ)^4167
        have hw : |(5136309567/10000000000 : ℝ)|=(5136309567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410576021/2500000000 : ℝ)|^5191 ≤ (10535590123907/100000000000000 : ℝ)^4167
        have hw : |(-410576021/2500000000 : ℝ)|=(410576021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s3_3 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4123097149/10000000000 : ℝ)*x 0 + (457544883/1250000000 : ℝ)*x 1 + (4622703741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123097149/10000000000 : ℝ)^5191 ≤ (16582059937161/50000000000000 : ℝ)^4167 := by
    have hnat : (4123097149 : ℕ)^5191*50000000000000^4167 ≤ 16582059937161^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123097149 10000000000 16582059937161 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457544883/1250000000 : ℝ)^5191 ≤ (28593271795431/100000000000000 : ℝ)^4167 := by
    have hnat : (457544883 : ℕ)^5191*100000000000000^4167 ≤ 28593271795431^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457544883 1250000000 28593271795431 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4622703741/10000000000 : ℝ)^5191 ≤ (1912130415071/5000000000000 : ℝ)^4167 := by
    have hnat : (4622703741 : ℕ)^5191*5000000000000^4167 ≤ 1912130415071^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4622703741 10000000000 1912130415071 5000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123097149/10000000000 : ℝ), (457544883/1250000000 : ℝ), (4622703741/10000000000 : ℝ)] ![(16582059937161/50000000000000 : ℝ), (28593271795431/100000000000000 : ℝ), (1912130415071/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123097149/10000000000 : ℝ)|^5191 ≤ (16582059937161/50000000000000 : ℝ)^4167
        have hw : |(4123097149/10000000000 : ℝ)|=(4123097149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457544883/1250000000 : ℝ)|^5191 ≤ (28593271795431/100000000000000 : ℝ)^4167
        have hw : |(457544883/1250000000 : ℝ)|=(457544883/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4622703741/10000000000 : ℝ)|^5191 ≤ (1912130415071/5000000000000 : ℝ)^4167
        have hw : |(4622703741/10000000000 : ℝ)|=(4622703741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s3_4 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-732232399/5000000000 : ℝ)*x 0 + (1285015121/2500000000 : ℝ)*x 1 + (5475362501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (732232399/5000000000 : ℝ)^5191 ≤ (9133823064403/100000000000000 : ℝ)^4167 := by
    have hnat : (732232399 : ℕ)^5191*100000000000000^4167 ≤ 9133823064403^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732232399 5000000000 9133823064403 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285015121/2500000000 : ℝ)^5191 ≤ (8729140009111/20000000000000 : ℝ)^4167 := by
    have hnat : (1285015121 : ℕ)^5191*20000000000000^4167 ≤ 8729140009111^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285015121 2500000000 8729140009111 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475362501/10000000000 : ℝ)^5191 ≤ (23610238435311/50000000000000 : ℝ)^4167 := by
    have hnat : (5475362501 : ℕ)^5191*50000000000000^4167 ≤ 23610238435311^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475362501 10000000000 23610238435311 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-732232399/5000000000 : ℝ), (1285015121/2500000000 : ℝ), (5475362501/10000000000 : ℝ)] ![(9133823064403/100000000000000 : ℝ), (8729140009111/20000000000000 : ℝ), (23610238435311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-732232399/5000000000 : ℝ)|^5191 ≤ (9133823064403/100000000000000 : ℝ)^4167
        have hw : |(-732232399/5000000000 : ℝ)|=(732232399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285015121/2500000000 : ℝ)|^5191 ≤ (8729140009111/20000000000000 : ℝ)^4167
        have hw : |(1285015121/2500000000 : ℝ)|=(1285015121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475362501/10000000000 : ℝ)|^5191 ≤ (23610238435311/50000000000000 : ℝ)^4167
        have hw : |(5475362501/10000000000 : ℝ)|=(5475362501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s3_5 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328531473/625000000 : ℝ)*x 0 + (-651625663/5000000000 : ℝ)*x 1 + (5475362501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328531473/625000000 : ℝ)^5191 ≤ (11220209057069/25000000000000 : ℝ)^4167 := by
    have hnat : (328531473 : ℕ)^5191*25000000000000^4167 ≤ 11220209057069^4167*625000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328531473 625000000 11220209057069 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651625663/5000000000 : ℝ)^5191 ≤ (1974671719501/25000000000000 : ℝ)^4167 := by
    have hnat : (651625663 : ℕ)^5191*25000000000000^4167 ≤ 1974671719501^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651625663 5000000000 1974671719501 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475362501/10000000000 : ℝ)^5191 ≤ (23610238435311/50000000000000 : ℝ)^4167 := by
    have hnat : (5475362501 : ℕ)^5191*50000000000000^4167 ≤ 23610238435311^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475362501 10000000000 23610238435311 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328531473/625000000 : ℝ), (-651625663/5000000000 : ℝ), (5475362501/10000000000 : ℝ)] ![(11220209057069/25000000000000 : ℝ), (1974671719501/25000000000000 : ℝ), (23610238435311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328531473/625000000 : ℝ)|^5191 ≤ (11220209057069/25000000000000 : ℝ)^4167
        have hw : |(328531473/625000000 : ℝ)|=(328531473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-651625663/5000000000 : ℝ)|^5191 ≤ (1974671719501/25000000000000 : ℝ)^4167
        have hw : |(-651625663/5000000000 : ℝ)|=(651625663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475362501/10000000000 : ℝ)|^5191 ≤ (23610238435311/50000000000000 : ℝ)^4167
        have hw : |(5475362501/10000000000 : ℝ)|=(5475362501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s3_6 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328531473/625000000 : ℝ)*x 0 + (5475362501/10000000000 : ℝ)*x 1 + (-651625663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328531473/625000000 : ℝ)^5191 ≤ (11220209057069/25000000000000 : ℝ)^4167 := by
    have hnat : (328531473 : ℕ)^5191*25000000000000^4167 ≤ 11220209057069^4167*625000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328531473 625000000 11220209057069 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475362501/10000000000 : ℝ)^5191 ≤ (23610238435311/50000000000000 : ℝ)^4167 := by
    have hnat : (5475362501 : ℕ)^5191*50000000000000^4167 ≤ 23610238435311^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475362501 10000000000 23610238435311 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651625663/5000000000 : ℝ)^5191 ≤ (1974671719501/25000000000000 : ℝ)^4167 := by
    have hnat : (651625663 : ℕ)^5191*25000000000000^4167 ≤ 1974671719501^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651625663 5000000000 1974671719501 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328531473/625000000 : ℝ), (5475362501/10000000000 : ℝ), (-651625663/5000000000 : ℝ)] ![(11220209057069/25000000000000 : ℝ), (23610238435311/50000000000000 : ℝ), (1974671719501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328531473/625000000 : ℝ)|^5191 ≤ (11220209057069/25000000000000 : ℝ)^4167
        have hw : |(328531473/625000000 : ℝ)|=(328531473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475362501/10000000000 : ℝ)|^5191 ≤ (23610238435311/50000000000000 : ℝ)^4167
        have hw : |(5475362501/10000000000 : ℝ)|=(5475362501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-651625663/5000000000 : ℝ)|^5191 ≤ (1974671719501/25000000000000 : ℝ)^4167
        have hw : |(-651625663/5000000000 : ℝ)|=(651625663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s3_7 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1030885281/2500000000 : ℝ)*x 0 + (4612175887/10000000000 : ℝ)*x 1 + (458880543/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030885281/2500000000 : ℝ)^5191 ≤ (1658428430549/5000000000000 : ℝ)^4167 := by
    have hnat : (1030885281 : ℕ)^5191*5000000000000^4167 ≤ 1658428430549^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030885281 2500000000 1658428430549 5000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4612175887/10000000000 : ℝ)^5191 ≤ (38134141405527/100000000000000 : ℝ)^4167 := by
    have hnat : (4612175887 : ℕ)^5191*100000000000000^4167 ≤ 38134141405527^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612175887 10000000000 38134141405527 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458880543/1250000000 : ℝ)^5191 ≤ (14348644985171/50000000000000 : ℝ)^4167 := by
    have hnat : (458880543 : ℕ)^5191*50000000000000^4167 ≤ 14348644985171^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458880543 1250000000 14348644985171 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030885281/2500000000 : ℝ), (4612175887/10000000000 : ℝ), (458880543/1250000000 : ℝ)] ![(1658428430549/5000000000000 : ℝ), (38134141405527/100000000000000 : ℝ), (14348644985171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030885281/2500000000 : ℝ)|^5191 ≤ (1658428430549/5000000000000 : ℝ)^4167
        have hw : |(1030885281/2500000000 : ℝ)|=(1030885281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4612175887/10000000000 : ℝ)|^5191 ≤ (38134141405527/100000000000000 : ℝ)^4167
        have hw : |(4612175887/10000000000 : ℝ)|=(4612175887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(458880543/1250000000 : ℝ)|^5191 ≤ (14348644985171/50000000000000 : ℝ)^4167
        have hw : |(458880543/1250000000 : ℝ)|=(458880543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1696_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9889/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17193/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9873/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17211/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9873/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9873/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17211/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9873/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17211/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9873/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17211/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9873/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9873/100000 : ℝ) ^ (5183/1024 : ℝ) ≤ (81354342482593/10000000000000000000 : ℝ) := by
    have hpowers : (9873/100000 : ℝ)^5183 ≤ (81354342482593/10000000000000000000 : ℝ)^1024 := by
      have hnat : (9873 : ℕ)^5183*10000000000000000000^1024 ≤ 81354342482593^1024*100000^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9873 100000 81354342482593 10000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9873/100000 : ℝ)) (X := (81354342482593/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17211/100000 : ℝ) ^ (5183/1024 : ℝ) ≤ (13552352450382997/100000000000000000000 : ℝ) := by
    have hpowers : (17211/100000 : ℝ)^5183 ≤ (13552352450382997/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17211 : ℕ)^5183*100000000000000000000^1024 ≤ 13552352450382997^1024*100000^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17211 100000 13552352450382997 100000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17211/100000 : ℝ)) (X := (13552352450382997/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000081354342482593/5000000000000000000 : ℝ) ≤ (10000032145978341/10000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (5000081354342482593/5000000000000000000 : ℝ)^1024 ≤ (10000032145978341/10000000000000000 : ℝ)^5183 := by
      have hnat : (5000081354342482593 : ℕ)^1024*10000000000000000^5183 ≤ 10000032145978341^5183*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000081354342482593 5000000000000000000 10000032145978341 10000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000032145978341/10000000000000000 : ℝ)) (X := (5000081354342482593/5000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014365895875208927/100000000000000000000 : ℝ) ≤ (2000056761835047/2000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (100014365895875208927/100000000000000000000 : ℝ)^1024 ≤ (2000056761835047/2000000000000000 : ℝ)^5183 := by
      have hnat : (100014365895875208927 : ℕ)^1024*2000000000000000^5183 ≤ 2000056761835047^5183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014365895875208927 100000000000000000000 2000056761835047 2000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056761835047/2000000000000000 : ℝ)) (X := (100014365895875208927/100000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013552352450382997/50000000000000000000 : ℝ) ≤ (10000535472372129/10000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (50013552352450382997/50000000000000000000 : ℝ)^1024 ≤ (10000535472372129/10000000000000000 : ℝ)^5183 := by
      have hnat : (50013552352450382997 : ℕ)^1024*10000000000000000^5183 ≤ 10000535472372129^5183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013552352450382997 50000000000000000000 10000535472372129 10000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000535472372129/10000000000000000 : ℝ)) (X := (50013552352450382997/50000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(81354342482593/10000000000000000000 : ℝ) ≤ ((12229211090950532889/12230000000000000000 : ℝ)+2*(41943866149/122300000000000 : ℝ)*(9873/100000 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (12229211090950532889/12230000000000000000 : ℝ)+2*(41943866149/122300000000000 : ℝ)*(9873/100000 : ℝ)=(10000032145978341/10000000000000000 : ℝ) by norm_num, show 1+2*(81354342482593/10000000000000000000 : ℝ)=(5000081354342482593/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13552352450382997/100000000000000000000 : ℝ)+(81354342482593/10000000000000000000 : ℝ) ≤ ((12229211090950532889/12230000000000000000 : ℝ)+(41943866149/122300000000000 : ℝ)*((17211/100000 : ℝ)+(9873/100000 : ℝ)))^(5183/1024 : ℝ) := by
    rw [show (12229211090950532889/12230000000000000000 : ℝ)+(41943866149/122300000000000 : ℝ)*((17211/100000 : ℝ)+(9873/100000 : ℝ))=(2000056761835047/2000000000000000 : ℝ) by norm_num, show 1+(13552352450382997/100000000000000000000 : ℝ)+(81354342482593/10000000000000000000 : ℝ)=(100014365895875208927/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13552352450382997/100000000000000000000 : ℝ) ≤ ((12229211090950532889/12230000000000000000 : ℝ)+2*(41943866149/122300000000000 : ℝ)*(17211/100000 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (12229211090950532889/12230000000000000000 : ℝ)+2*(41943866149/122300000000000 : ℝ)*(17211/100000 : ℝ)=(10000535472372129/10000000000000000 : ℝ) by norm_num, show 1+2*(13552352450382997/100000000000000000000 : ℝ)=(50013552352450382997/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12229211090950532889/12230000000000000000 : ℝ)*(X 1 0+X 2 0)+(41943866149/122300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9873/100000 : ℝ)) (hi := (17211/100000 : ℝ)) (c := (12229211090950532889/12230000000000000000 : ℝ)) (alpha := (41943866149/122300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12229211090950532889/12230000000000000000 : ℝ)*(X 0 1+X 2 1)+(41943866149/122300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9873/100000 : ℝ)) (hi := (17211/100000 : ℝ)) (c := (12229211090950532889/12230000000000000000 : ℝ)) (alpha := (41943866149/122300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12229211090950532889/12230000000000000000 : ℝ)*(X 0 2+X 1 2)+(41943866149/122300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9873/100000 : ℝ)) (hi := (17211/100000 : ℝ)) (c := (12229211090950532889/12230000000000000000 : ℝ)) (alpha := (41943866149/122300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1464306673/10000000000 : ℝ)*X 0 0+(1369792421/2500000000 : ℝ)*X 0 1+(1027261839/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337053621/2500000000 : ℝ)*X 1 0+(-1642304037/10000000000 : ℝ)*X 1 1+(2568154709/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348214301/10000000000 : ℝ)*X 2 0+(5136309567/10000000000 : ℝ)*X 2 1+(-410576021/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4123097149/10000000000 : ℝ)*X 0 0+(457544883/1250000000 : ℝ)*X 0 1+(4622703741/10000000000 : ℝ)*X 0 2+(4123097149/10000000000 : ℝ)*X 1 0+(457544883/1250000000 : ℝ)*X 1 1+(4622703741/10000000000 : ℝ)*X 1 2+(4123097149/10000000000 : ℝ)*X 2 0+(457544883/1250000000 : ℝ)*X 2 1+(4622703741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-732232399/5000000000 : ℝ)*X 0 0+(1285015121/2500000000 : ℝ)*X 0 1+(5475362501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328531473/625000000 : ℝ)*X 1 0+(-651625663/5000000000 : ℝ)*X 1 1+(5475362501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328531473/625000000 : ℝ)*X 2 0+(5475362501/10000000000 : ℝ)*X 2 1+(-651625663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1030885281/2500000000 : ℝ)*X 0 0+(4612175887/10000000000 : ℝ)*X 0 1+(458880543/1250000000 : ℝ)*X 0 2+(1030885281/2500000000 : ℝ)*X 1 0+(4612175887/10000000000 : ℝ)*X 1 1+(458880543/1250000000 : ℝ)*X 1 2+(1030885281/2500000000 : ℝ)*X 2 0+(4612175887/10000000000 : ℝ)*X 2 1+(458880543/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1212317235943134916457917701/305750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (253177421/25000000000000 : ℝ)*(base19) + (905134247/100000000000000 : ℝ)*(base23) + (166349/4000000000000 : ℝ)*(lower2) + (71373757/50000000000000 : ℝ)*(upper3) + (94639707/100000000000000 : ℝ)*(upper5) + (1977899599669793/100000000000000 : ℝ)*(major0) + (1977899599669793/100000000000000 : ℝ)*(major1) + (988949799834897/50000000000000 : ℝ)*(major2) + (729162827942597/25000000000000 : ℝ)*(sp0) + (2916662534444709/100000000000000 : ℝ)*(sp1) + (1458331321010073/50000000000000 : ℝ)*(sp2) + (519565999100291/50000000000000 : ℝ)*(sp3) + (3058846001/25000000000000 : ℝ)*(sp4) + (1760907961/50000000000000 : ℝ)*(sp7) + (129891940002063/12500000000000 : ℝ)*(f.failure) + (364582943394299/12500000000000 : ℝ)*(f.sum) + (14141934032563/12230000000000000000000000000 : ℝ)*base65 + (5711276856146921977/1223000000000000000000000000000000 : ℝ)*base67 + (4753254184745277433/611500000000000000000000000000000 : ℝ)*base69 + (10534711250929078023/1223000000000000000000000000000000 : ℝ)*base72 + (51638733691793/12230000000000000000000000000 : ℝ)*base73 + (9775492862418277433/611500000000000000000000000000000 : ℝ)*base75 + (6620832869713978023/1223000000000000000000000000000000 : ℝ)*base78 + (470292531290021977/1223000000000000000000000000000000 : ℝ)*base79 + (12406004732067/6115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (716873/1250000000000000000000 : ℝ)*base89 + (716873/1250000000000000000000 : ℝ)*base91 + (11783127/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1620764785681905446992812357/152875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37326787/2500000000000 : ℝ)*(base19) + (402267/25000000000 : ℝ)*(base23) + (224490053/50000000000000 : ℝ)*(lower1) + (226580613/100000000000000 : ℝ)*(upper3) + (3242089/6250000000000 : ℝ)*(lower4) + (220774977/100000000000000 : ℝ)*(upper5) + (1011229480146071/50000000000000 : ℝ)*(major0) + (1011229480146071/50000000000000 : ℝ)*(major1) + (1011229480146071/50000000000000 : ℝ)*(major2) + (248067699/25000000000000 : ℝ)*(sp2) + (372796468941571/12500000000000 : ℝ)*(sp4) + (2982370258461089/100000000000000 : ℝ)*(sp5) + (745592287548443/25000000000000 : ℝ)*(sp6) + (106254581565519/10000000000000 : ℝ)*(sp7) + (106254581565519/10000000000000 : ℝ)*(f.failure) + (372796468941571/12500000000000 : ℝ)*(f.sum) + (200977944441/3057500000000000000000000000 : ℝ)*base66 + (197704421215470881/611500000000000000000000000000000 : ℝ)*base68 + (1424209224904470881/611500000000000000000000000000000 : ℝ)*base70 + (2359083378920470881/611500000000000000000000000000000 : ℝ)*base72 + (9328463105409/3057500000000000000000000000 : ℝ)*base73 + (15226247934245970881/611500000000000000000000000000000 : ℝ)*base76 + (378255681869529119/611500000000000000000000000000000 : ℝ)*base77 + (5961829507623470881/611500000000000000000000000000000 : ℝ)*base80 + (12738502908801/3057500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10027049/1000000000000000000000 : ℝ)*base89 + (10027049/1000000000000000000000 : ℝ)*base91 + (10027049/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1696_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17193/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1696_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1696_s4_0 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534820687/1000000000 : ℝ)*x 0 + (1284084511/2500000000 : ℝ)*x 1 + (-1642276329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534820687/1000000000 : ℝ)^5191 ≤ (1146457595809/2500000000000 : ℝ)^4167 := by
    have hnat : (534820687 : ℕ)^5191*2500000000000^4167 ≤ 1146457595809^4167*1000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534820687 1000000000 1146457595809 2500000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284084511/2500000000 : ℝ)^5191 ≤ (43606327833503/100000000000000 : ℝ)^4167 := by
    have hnat : (1284084511 : ℕ)^5191*100000000000000^4167 ≤ 43606327833503^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284084511 2500000000 43606327833503 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1642276329/10000000000 : ℝ)^5191 ≤ (10535368317977/100000000000000 : ℝ)^4167 := by
    have hnat : (1642276329 : ℕ)^5191*100000000000000^4167 ≤ 10535368317977^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642276329 10000000000 10535368317977 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534820687/1000000000 : ℝ), (1284084511/2500000000 : ℝ), (-1642276329/10000000000 : ℝ)] ![(1146457595809/2500000000000 : ℝ), (43606327833503/100000000000000 : ℝ), (10535368317977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534820687/1000000000 : ℝ)|^5191 ≤ (1146457595809/2500000000000 : ℝ)^4167
        have hw : |(534820687/1000000000 : ℝ)|=(534820687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284084511/2500000000 : ℝ)|^5191 ≤ (43606327833503/100000000000000 : ℝ)^4167
        have hw : |(1284084511/2500000000 : ℝ)|=(1284084511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1642276329/10000000000 : ℝ)|^5191 ≤ (10535368317977/100000000000000 : ℝ)^4167
        have hw : |(-1642276329/10000000000 : ℝ)|=(1642276329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s4_1 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-366118543/2500000000 : ℝ)*x 0 + (5140090037/10000000000 : ℝ)*x 1 + (171103957/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366118543/2500000000 : ℝ)^5191 ≤ (4566947948557/50000000000000 : ℝ)^4167 := by
    have hnat : (366118543 : ℕ)^5191*50000000000000^4167 ≤ 4566947948557^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366118543 2500000000 4566947948557 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140090037/10000000000 : ℝ)^5191 ≤ (21823006327697/50000000000000 : ℝ)^4167 := by
    have hnat : (5140090037 : ℕ)^5191*50000000000000^4167 ≤ 21823006327697^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140090037 10000000000 21823006327697 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (171103957/312500000 : ℝ)^5191 ≤ (9444018285413/20000000000000 : ℝ)^4167 := by
    have hnat : (171103957 : ℕ)^5191*20000000000000^4167 ≤ 9444018285413^4167*312500000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171103957 312500000 9444018285413 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366118543/2500000000 : ℝ), (5140090037/10000000000 : ℝ), (171103957/312500000 : ℝ)] ![(4566947948557/50000000000000 : ℝ), (21823006327697/50000000000000 : ℝ), (9444018285413/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366118543/2500000000 : ℝ)|^5191 ≤ (4566947948557/50000000000000 : ℝ)^4167
        have hw : |(-366118543/2500000000 : ℝ)|=(366118543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140090037/10000000000 : ℝ)|^5191 ≤ (21823006327697/50000000000000 : ℝ)^4167
        have hw : |(5140090037/10000000000 : ℝ)|=(5140090037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(171103957/312500000 : ℝ)|^5191 ≤ (9444018285413/20000000000000 : ℝ)^4167
        have hw : |(171103957/312500000 : ℝ)|=(171103957/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s4_2 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256511733/10000000000 : ℝ)*x 0 + (-1303290883/10000000000 : ℝ)*x 1 + (5475326619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256511733/10000000000 : ℝ)^5191 ≤ (44880923073867/100000000000000 : ℝ)^4167 := by
    have hnat : (5256511733 : ℕ)^5191*100000000000000^4167 ≤ 44880923073867^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256511733 10000000000 44880923073867 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303290883/10000000000 : ℝ)^5191 ≤ (246843298109/3125000000000 : ℝ)^4167 := by
    have hnat : (1303290883 : ℕ)^5191*3125000000000^4167 ≤ 246843298109^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303290883 10000000000 246843298109 3125000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5475326619/10000000000 : ℝ)^5191 ≤ (11805022843337/25000000000000 : ℝ)^4167 := by
    have hnat : (5475326619 : ℕ)^5191*25000000000000^4167 ≤ 11805022843337^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475326619 10000000000 11805022843337 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256511733/10000000000 : ℝ), (-1303290883/10000000000 : ℝ), (5475326619/10000000000 : ℝ)] ![(44880923073867/100000000000000 : ℝ), (246843298109/3125000000000 : ℝ), (11805022843337/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256511733/10000000000 : ℝ)|^5191 ≤ (44880923073867/100000000000000 : ℝ)^4167
        have hw : |(5256511733/10000000000 : ℝ)|=(5256511733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1303290883/10000000000 : ℝ)|^5191 ≤ (246843298109/3125000000000 : ℝ)^4167
        have hw : |(-1303290883/10000000000 : ℝ)|=(1303290883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5475326619/10000000000 : ℝ)|^5191 ≤ (11805022843337/25000000000000 : ℝ)^4167
        have hw : |(5475326619/10000000000 : ℝ)|=(5475326619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s4_3 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256511763/10000000000 : ℝ)*x 0 + (5475326629/10000000000 : ℝ)*x 1 + (-1303290827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256511763/10000000000 : ℝ)^5191 ≤ (44880923392957/100000000000000 : ℝ)^4167 := by
    have hnat : (5256511763 : ℕ)^5191*100000000000000^4167 ≤ 44880923392957^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256511763 10000000000 44880923392957 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475326629/10000000000 : ℝ)^5191 ≤ (47220091480783/100000000000000 : ℝ)^4167 := by
    have hnat : (5475326629 : ℕ)^5191*100000000000000^4167 ≤ 47220091480783^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475326629 10000000000 47220091480783 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303290827/10000000000 : ℝ)^5191 ≤ (7898985116677/100000000000000 : ℝ)^4167 := by
    have hnat : (1303290827 : ℕ)^5191*100000000000000^4167 ≤ 7898985116677^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303290827 10000000000 7898985116677 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256511763/10000000000 : ℝ), (5475326629/10000000000 : ℝ), (-1303290827/10000000000 : ℝ)] ![(44880923392957/100000000000000 : ℝ), (47220091480783/100000000000000 : ℝ), (7898985116677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256511763/10000000000 : ℝ)|^5191 ≤ (44880923392957/100000000000000 : ℝ)^4167
        have hw : |(5256511763/10000000000 : ℝ)|=(5256511763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475326629/10000000000 : ℝ)|^5191 ≤ (47220091480783/100000000000000 : ℝ)^4167
        have hw : |(5475326629/10000000000 : ℝ)|=(5475326629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1303290827/10000000000 : ℝ)|^5191 ≤ (7898985116677/100000000000000 : ℝ)^4167
        have hw : |(-1303290827/10000000000 : ℝ)|=(1303290827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_s4_4 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4123547609/10000000000 : ℝ)*x 0 + (4612083351/10000000000 : ℝ)*x 1 + (734227109/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123547609/10000000000 : ℝ)^5191 ≤ (16584316796559/50000000000000 : ℝ)^4167 := by
    have hnat : (4123547609 : ℕ)^5191*50000000000000^4167 ≤ 16584316796559^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123547609 10000000000 16584316796559 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4612083351/10000000000 : ℝ)^5191 ≤ (19066594145277/50000000000000 : ℝ)^4167 := by
    have hnat : (4612083351 : ℕ)^5191*50000000000000^4167 ≤ 19066594145277^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612083351 10000000000 19066594145277 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (734227109/2000000000 : ℝ)^5191 ≤ (3587272263353/12500000000000 : ℝ)^4167 := by
    have hnat : (734227109 : ℕ)^5191*12500000000000^4167 ≤ 3587272263353^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734227109 2000000000 3587272263353 12500000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123547609/10000000000 : ℝ), (4612083351/10000000000 : ℝ), (734227109/2000000000 : ℝ)] ![(16584316796559/50000000000000 : ℝ), (19066594145277/50000000000000 : ℝ), (3587272263353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123547609/10000000000 : ℝ)|^5191 ≤ (16584316796559/50000000000000 : ℝ)^4167
        have hw : |(4123547609/10000000000 : ℝ)|=(4123547609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4612083351/10000000000 : ℝ)|^5191 ≤ (19066594145277/50000000000000 : ℝ)^4167
        have hw : |(4612083351/10000000000 : ℝ)|=(4612083351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(734227109/2000000000 : ℝ)|^5191 ≤ (3587272263353/12500000000000 : ℝ)^4167
        have hw : |(734227109/2000000000 : ℝ)|=(734227109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1696_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17193/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9889/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2149/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17193/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17193/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17193/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17193/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17193/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17193/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9889/100000 : ℝ) ^ (5183/1024 : ℝ) ≤ (820238602674587/100000000000000000000 : ℝ) := by
    have hpowers : (9889/100000 : ℝ)^5183 ≤ (820238602674587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9889 : ℕ)^5183*100000000000000000000^1024 ≤ 820238602674587^1024*100000^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9889 100000 820238602674587 100000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9889/100000 : ℝ)) (X := (820238602674587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17193/100000 : ℝ) ^ (5183/1024 : ℝ) ≤ (6740382246911621/50000000000000000000 : ℝ) := by
    have hpowers : (17193/100000 : ℝ)^5183 ≤ (6740382246911621/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17193 : ℕ)^5183*50000000000000000000^1024 ≤ 6740382246911621^1024*100000^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17193 100000 6740382246911621 50000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17193/100000 : ℝ)) (X := (6740382246911621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000820238602674587/50000000000000000000 : ℝ) ≤ (10000032410526759/10000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (50000820238602674587/50000000000000000000 : ℝ)^1024 ≤ (10000032410526759/10000000000000000 : ℝ)^5183 := by
      have hnat : (50000820238602674587 : ℕ)^1024*10000000000000000^5183 ≤ 10000032410526759^5183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000820238602674587 50000000000000000000 10000032410526759 10000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000032410526759/10000000000000000 : ℝ)) (X := (50000820238602674587/50000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100014301003096497829/100000000000000000000 : ℝ) ≤ (2000056505448539/2000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (100014301003096497829/100000000000000000000 : ℝ)^1024 ≤ (2000056505448539/2000000000000000 : ℝ)^5183 := by
      have hnat : (100014301003096497829 : ℕ)^1024*2000000000000000^5183 ≤ 2000056505448539^5183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100014301003096497829 100000000000000000000 2000056505448539 2000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056505448539/2000000000000000 : ℝ)) (X := (100014301003096497829/100000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25006740382246911621/25000000000000000000 : ℝ) ≤ (10000532643958631/10000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (25006740382246911621/25000000000000000000 : ℝ)^1024 ≤ (10000532643958631/10000000000000000 : ℝ)^5183 := by
      have hnat : (25006740382246911621 : ℕ)^1024*10000000000000000^5183 ≤ 10000532643958631^5183*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006740382246911621 25000000000000000000 10000532643958631 10000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000532643958631/10000000000000000 : ℝ)) (X := (25006740382246911621/25000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(820238602674587/100000000000000000000 : ℝ) ≤ ((829946476341814381/830000000000000000 : ℝ)+2*(7816147373/22825000000000 : ℝ)*(9889/100000 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (829946476341814381/830000000000000000 : ℝ)+2*(7816147373/22825000000000 : ℝ)*(9889/100000 : ℝ)=(10000032410526759/10000000000000000 : ℝ) by norm_num, show 1+2*(820238602674587/100000000000000000000 : ℝ)=(50000820238602674587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6740382246911621/50000000000000000000 : ℝ)+(820238602674587/100000000000000000000 : ℝ) ≤ ((829946476341814381/830000000000000000 : ℝ)+(7816147373/22825000000000 : ℝ)*((17193/100000 : ℝ)+(9889/100000 : ℝ)))^(5183/1024 : ℝ) := by
    rw [show (829946476341814381/830000000000000000 : ℝ)+(7816147373/22825000000000 : ℝ)*((17193/100000 : ℝ)+(9889/100000 : ℝ))=(2000056505448539/2000000000000000 : ℝ) by norm_num, show 1+(6740382246911621/50000000000000000000 : ℝ)+(820238602674587/100000000000000000000 : ℝ)=(100014301003096497829/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6740382246911621/50000000000000000000 : ℝ) ≤ ((829946476341814381/830000000000000000 : ℝ)+2*(7816147373/22825000000000 : ℝ)*(17193/100000 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (829946476341814381/830000000000000000 : ℝ)+2*(7816147373/22825000000000 : ℝ)*(17193/100000 : ℝ)=(10000532643958631/10000000000000000 : ℝ) by norm_num, show 1+2*(6740382246911621/50000000000000000000 : ℝ)=(25006740382246911621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (829946476341814381/830000000000000000 : ℝ)*(X 1 0+X 2 0)+(7816147373/22825000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (17193/100000 : ℝ)) (c := (829946476341814381/830000000000000000 : ℝ)) (alpha := (7816147373/22825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (829946476341814381/830000000000000000 : ℝ)*(X 0 1+X 2 1)+(7816147373/22825000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (17193/100000 : ℝ)) (c := (829946476341814381/830000000000000000 : ℝ)) (alpha := (7816147373/22825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (829946476341814381/830000000000000000 : ℝ)*(X 0 2+X 1 2)+(7816147373/22825000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (17193/100000 : ℝ)) (c := (829946476341814381/830000000000000000 : ℝ)) (alpha := (7816147373/22825000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((534820687/1000000000 : ℝ)*X 2 0+(1284084511/2500000000 : ℝ)*X 2 1+(-1642276329/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s4_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-366118543/2500000000 : ℝ)*X 0 0+(5140090037/10000000000 : ℝ)*X 0 1+(171103957/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s4_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5256511733/10000000000 : ℝ)*X 1 0+(-1303290883/10000000000 : ℝ)*X 1 1+(5475326619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s4_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5256511763/10000000000 : ℝ)*X 2 0+(5475326629/10000000000 : ℝ)*X 2 1+(-1303290827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s4_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4123547609/10000000000 : ℝ)*X 0 0+(4612083351/10000000000 : ℝ)*X 0 1+(734227109/2000000000 : ℝ)*X 0 2+(4123547609/10000000000 : ℝ)*X 1 0+(4612083351/10000000000 : ℝ)*X 1 1+(734227109/2000000000 : ℝ)*X 1 2+(4123547609/10000000000 : ℝ)*X 2 0+(4612083351/10000000000 : ℝ)*X 2 1+(734227109/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_s4_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332765045499378634123765947/41500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1132019541/100000000000000 : ℝ)*(base19) + (1244125791/100000000000000 : ℝ)*(base23) + (342735339/100000000000000 : ℝ)*(lower1) + (3359501/2000000000000 : ℝ)*(upper3) + (984983/2500000000000 : ℝ)*(lower4) + (2143401/1250000000000 : ℝ)*(upper5) + (2022856059796371/100000000000000 : ℝ)*(major0) + (2022856059796371/100000000000000 : ℝ)*(major1) + (2022856059796371/100000000000000 : ℝ)*(major2) + (288472119/25000000000000 : ℝ)*(sp0) + (1491478705601727/50000000000000 : ℝ)*(sp1) + (1491478139591957/50000000000000 : ℝ)*(sp2) + (745738753297297/25000000000000 : ℝ)*(sp3) + (265688610277029/25000000000000 : ℝ)*(sp4) + (265688610277029/25000000000000 : ℝ)*(f.failure) + (1491478705601727/50000000000000 : ℝ)*(f.sum) + (13021954067/4458007812500000000000000 : ℝ)*base66 + (10384249939004724861/913000000000000000000000000000000 : ℝ)*base67 + (3635739223178724861/913000000000000000000000000000000 : ℝ)*base69 + (1457627653991275139/913000000000000000000000000000000 : ℝ)*base72 + (9821502774011/2282500000000000000000000000 : ℝ)*base73 + (7643323516931275139/913000000000000000000000000000000 : ℝ)*base76 + (4186916691382724861/913000000000000000000000000000000 : ℝ)*base77 + (2169185135630724861/913000000000000000000000000000000 : ℝ)*base79 + (336360753299/142656250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (23847741/2500000000000000000000 : ℝ)*base90 + (23847741/2500000000000000000000 : ℝ)*base92 + (23847741/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1696_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17193/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2149/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1696_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1696_box_0 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1134445817/10000000000 : ℝ)*x 0 + (21190457/39062500 : ℝ)*x 1 + (5424756871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134445817/10000000000 : ℝ)^5191 ≤ (6645168484463/100000000000000 : ℝ)^4167 := by
    have hnat : (1134445817 : ℕ)^5191*100000000000000^4167 ≤ 6645168484463^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134445817 10000000000 6645168484463 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21190457/39062500 : ℝ)^5191 ≤ (9335483279589/20000000000000 : ℝ)^4167 := by
    have hnat : (21190457 : ℕ)^5191*20000000000000^4167 ≤ 9335483279589^4167*39062500^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21190457 39062500 9335483279589 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424756871/10000000000 : ℝ)^5191 ≤ (23338707550473/50000000000000 : ℝ)^4167 := by
    have hnat : (5424756871 : ℕ)^5191*50000000000000^4167 ≤ 23338707550473^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424756871 10000000000 23338707550473 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1134445817/10000000000 : ℝ), (21190457/39062500 : ℝ), (5424756871/10000000000 : ℝ)] ![(6645168484463/100000000000000 : ℝ), (9335483279589/20000000000000 : ℝ), (23338707550473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1134445817/10000000000 : ℝ)|^5191 ≤ (6645168484463/100000000000000 : ℝ)^4167
        have hw : |(-1134445817/10000000000 : ℝ)|=(1134445817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21190457/39062500 : ℝ)|^5191 ≤ (9335483279589/20000000000000 : ℝ)^4167
        have hw : |(21190457/39062500 : ℝ)|=(21190457/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424756871/10000000000 : ℝ)|^5191 ≤ (23338707550473/50000000000000 : ℝ)^4167
        have hw : |(5424756871/10000000000 : ℝ)|=(5424756871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_1 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306480589/2500000000 : ℝ)*x 0 + (-708517421/5000000000 : ℝ)*x 1 + (1084951369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306480589/2500000000 : ℝ)^5191 ≤ (22277898722289/50000000000000 : ℝ)^4167 := by
    have hnat : (1306480589 : ℕ)^5191*50000000000000^4167 ≤ 22277898722289^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306480589 2500000000 22277898722289 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708517421/5000000000 : ℝ)^5191 ≤ (4383393861309/50000000000000 : ℝ)^4167 := by
    have hnat : (708517421 : ℕ)^5191*50000000000000^4167 ≤ 4383393861309^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708517421 5000000000 4383393861309 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084951369/2000000000 : ℝ)^5191 ≤ (11669353705563/25000000000000 : ℝ)^4167 := by
    have hnat : (1084951369 : ℕ)^5191*25000000000000^4167 ≤ 11669353705563^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084951369 2000000000 11669353705563 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306480589/2500000000 : ℝ), (-708517421/5000000000 : ℝ), (1084951369/2000000000 : ℝ)] ![(22277898722289/50000000000000 : ℝ), (4383393861309/50000000000000 : ℝ), (11669353705563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306480589/2500000000 : ℝ)|^5191 ≤ (22277898722289/50000000000000 : ℝ)^4167
        have hw : |(1306480589/2500000000 : ℝ)|=(1306480589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-708517421/5000000000 : ℝ)|^5191 ≤ (4383393861309/50000000000000 : ℝ)^4167
        have hw : |(-708517421/5000000000 : ℝ)|=(708517421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084951369/2000000000 : ℝ)|^5191 ≤ (11669353705563/25000000000000 : ℝ)^4167
        have hw : |(1084951369/2000000000 : ℝ)|=(1084951369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_2 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612961127/5000000000 : ℝ)*x 0 + (1356189219/2500000000 : ℝ)*x 1 + (-1417034939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612961127/5000000000 : ℝ)^5191 ≤ (44555796361227/100000000000000 : ℝ)^4167 := by
    have hnat : (2612961127 : ℕ)^5191*100000000000000^4167 ≤ 44555796361227^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612961127 5000000000 44555796361227 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356189219/2500000000 : ℝ)^5191 ≤ (46677415154541/100000000000000 : ℝ)^4167 := by
    have hnat : (1356189219 : ℕ)^5191*100000000000000^4167 ≤ 46677415154541^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356189219 2500000000 46677415154541 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1417034939/10000000000 : ℝ)^5191 ≤ (8766788470201/100000000000000 : ℝ)^4167 := by
    have hnat : (1417034939 : ℕ)^5191*100000000000000^4167 ≤ 8766788470201^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417034939 10000000000 8766788470201 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612961127/5000000000 : ℝ), (1356189219/2500000000 : ℝ), (-1417034939/10000000000 : ℝ)] ![(44555796361227/100000000000000 : ℝ), (46677415154541/100000000000000 : ℝ), (8766788470201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612961127/5000000000 : ℝ)|^5191 ≤ (44555796361227/100000000000000 : ℝ)^4167
        have hw : |(2612961127/5000000000 : ℝ)|=(2612961127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356189219/2500000000 : ℝ)|^5191 ≤ (46677415154541/100000000000000 : ℝ)^4167
        have hw : |(1356189219/2500000000 : ℝ)|=(1356189219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1417034939/10000000000 : ℝ)|^5191 ≤ (8766788470201/100000000000000 : ℝ)^4167
        have hw : |(-1417034939/10000000000 : ℝ)|=(1417034939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_3 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4506606429/10000000000 : ℝ)*x 0 + (247104187/625000000 : ℝ)*x 1 + (3953666733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506606429/10000000000 : ℝ)^5191 ≤ (7236299969/19531250000 : ℝ)^4167 := by
    have hnat : (4506606429 : ℕ)^5191*19531250000^4167 ≤ 7236299969^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506606429 10000000000 7236299969 19531250000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (247104187/625000000 : ℝ)^5191 ≤ (15737536678067/50000000000000 : ℝ)^4167 := by
    have hnat : (247104187 : ℕ)^5191*50000000000000^4167 ≤ 15737536678067^4167*625000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      247104187 625000000 15737536678067 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3953666733/10000000000 : ℝ)^5191 ≤ (31475070787549/100000000000000 : ℝ)^4167 := by
    have hnat : (3953666733 : ℕ)^5191*100000000000000^4167 ≤ 31475070787549^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3953666733 10000000000 31475070787549 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506606429/10000000000 : ℝ), (247104187/625000000 : ℝ), (3953666733/10000000000 : ℝ)] ![(7236299969/19531250000 : ℝ), (15737536678067/50000000000000 : ℝ), (31475070787549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506606429/10000000000 : ℝ)|^5191 ≤ (7236299969/19531250000 : ℝ)^4167
        have hw : |(4506606429/10000000000 : ℝ)|=(4506606429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(247104187/625000000 : ℝ)|^5191 ≤ (15737536678067/50000000000000 : ℝ)^4167
        have hw : |(247104187/625000000 : ℝ)|=(247104187/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3953666733/10000000000 : ℝ)|^5191 ≤ (31475070787549/100000000000000 : ℝ)^4167
        have hw : |(3953666733/10000000000 : ℝ)|=(3953666733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_4 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-453761159/2500000000 : ℝ)*x 0 + (5176668501/10000000000 : ℝ)*x 1 + (5176668403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (453761159/2500000000 : ℝ)^5191 ≤ (1193345019037/10000000000000 : ℝ)^4167 := by
    have hnat : (453761159 : ℕ)^5191*10000000000000^4167 ≤ 1193345019037^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453761159 2500000000 1193345019037 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176668501/10000000000 : ℝ)^5191 ≤ (5504159427059/12500000000000 : ℝ)^4167 := by
    have hnat : (5176668501 : ℕ)^5191*12500000000000^4167 ≤ 5504159427059^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176668501 10000000000 5504159427059 12500000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176668403/10000000000 : ℝ)^5191 ≤ (1761330975121/4000000000000 : ℝ)^4167 := by
    have hnat : (5176668403 : ℕ)^5191*4000000000000^4167 ≤ 1761330975121^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176668403 10000000000 1761330975121 4000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-453761159/2500000000 : ℝ), (5176668501/10000000000 : ℝ), (5176668403/10000000000 : ℝ)] ![(1193345019037/10000000000000 : ℝ), (5504159427059/12500000000000 : ℝ), (1761330975121/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-453761159/2500000000 : ℝ)|^5191 ≤ (1193345019037/10000000000000 : ℝ)^4167
        have hw : |(-453761159/2500000000 : ℝ)|=(453761159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176668501/10000000000 : ℝ)|^5191 ≤ (5504159427059/12500000000000 : ℝ)^4167
        have hw : |(5176668501/10000000000 : ℝ)|=(5176668501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176668403/10000000000 : ℝ)|^5191 ≤ (1761330975121/4000000000000 : ℝ)^4167
        have hw : |(5176668403/10000000000 : ℝ)|=(5176668403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_5 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394744209/10000000000 : ℝ)*x 0 + (-1525544341/10000000000 : ℝ)*x 1 + (5176668469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394744209/10000000000 : ℝ)^5191 ≤ (46355928537531/100000000000000 : ℝ)^4167 := by
    have hnat : (5394744209 : ℕ)^5191*100000000000000^4167 ≤ 46355928537531^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394744209 10000000000 46355928537531 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1525544341/10000000000 : ℝ)^5191 ≤ (4805398188281/50000000000000 : ℝ)^4167 := by
    have hnat : (1525544341 : ℕ)^5191*50000000000000^4167 ≤ 4805398188281^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525544341 10000000000 4805398188281 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176668469/10000000000 : ℝ)^5191 ≤ (44033275077387/100000000000000 : ℝ)^4167 := by
    have hnat : (5176668469 : ℕ)^5191*100000000000000^4167 ≤ 44033275077387^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176668469 10000000000 44033275077387 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394744209/10000000000 : ℝ), (-1525544341/10000000000 : ℝ), (5176668469/10000000000 : ℝ)] ![(46355928537531/100000000000000 : ℝ), (4805398188281/50000000000000 : ℝ), (44033275077387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394744209/10000000000 : ℝ)|^5191 ≤ (46355928537531/100000000000000 : ℝ)^4167
        have hw : |(5394744209/10000000000 : ℝ)|=(5394744209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1525544341/10000000000 : ℝ)|^5191 ≤ (4805398188281/50000000000000 : ℝ)^4167
        have hw : |(-1525544341/10000000000 : ℝ)|=(1525544341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176668469/10000000000 : ℝ)|^5191 ≤ (44033275077387/100000000000000 : ℝ)^4167
        have hw : |(5176668469/10000000000 : ℝ)|=(5176668469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_6 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394744277/10000000000 : ℝ)*x 0 + (5176668389/10000000000 : ℝ)*x 1 + (-381386089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394744277/10000000000 : ℝ)^5191 ≤ (4635592926543/10000000000000 : ℝ)^4167 := by
    have hnat : (5394744277 : ℕ)^5191*10000000000000^4167 ≤ 4635592926543^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394744277 10000000000 4635592926543 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176668389/10000000000 : ℝ)^5191 ≤ (1761330969187/4000000000000 : ℝ)^4167 := by
    have hnat : (5176668389 : ℕ)^5191*4000000000000^4167 ≤ 1761330969187^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176668389 10000000000 1761330969187 4000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (381386089/2500000000 : ℝ)^5191 ≤ (9610796494283/100000000000000 : ℝ)^4167 := by
    have hnat : (381386089 : ℕ)^5191*100000000000000^4167 ≤ 9610796494283^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381386089 2500000000 9610796494283 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394744277/10000000000 : ℝ), (5176668389/10000000000 : ℝ), (-381386089/2500000000 : ℝ)] ![(4635592926543/10000000000000 : ℝ), (1761330969187/4000000000000 : ℝ), (9610796494283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394744277/10000000000 : ℝ)|^5191 ≤ (4635592926543/10000000000000 : ℝ)^4167
        have hw : |(5394744277/10000000000 : ℝ)|=(5394744277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176668389/10000000000 : ℝ)|^5191 ≤ (1761330969187/4000000000000 : ℝ)^4167
        have hw : |(5176668389/10000000000 : ℝ)|=(5176668389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-381386089/2500000000 : ℝ)|^5191 ≤ (9610796494283/100000000000000 : ℝ)^4167
        have hw : |(-381386089/2500000000 : ℝ)|=(381386089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_7 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3724695163/10000000000 : ℝ)*x 0 + (4343772063/10000000000 : ℝ)*x 1 + (1085943007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3724695163/10000000000 : ℝ)^5191 ≤ (29220687248591/100000000000000 : ℝ)^4167 := by
    have hnat : (3724695163 : ℕ)^5191*100000000000000^4167 ≤ 29220687248591^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3724695163 10000000000 29220687248591 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4343772063/10000000000 : ℝ)^5191 ≤ (35389656543461/100000000000000 : ℝ)^4167 := by
    have hnat : (4343772063 : ℕ)^5191*100000000000000^4167 ≤ 35389656543461^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343772063 10000000000 35389656543461 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085943007/2500000000 : ℝ)^5191 ≤ (17694828094117/50000000000000 : ℝ)^4167 := by
    have hnat : (1085943007 : ℕ)^5191*50000000000000^4167 ≤ 17694828094117^4167*2500000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085943007 2500000000 17694828094117 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3724695163/10000000000 : ℝ), (4343772063/10000000000 : ℝ), (1085943007/2500000000 : ℝ)] ![(29220687248591/100000000000000 : ℝ), (35389656543461/100000000000000 : ℝ), (17694828094117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3724695163/10000000000 : ℝ)|^5191 ≤ (29220687248591/100000000000000 : ℝ)^4167
        have hw : |(3724695163/10000000000 : ℝ)|=(3724695163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4343772063/10000000000 : ℝ)|^5191 ≤ (35389656543461/100000000000000 : ℝ)^4167
        have hw : |(4343772063/10000000000 : ℝ)|=(4343772063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085943007/2500000000 : ℝ)|^5191 ≤ (17694828094117/50000000000000 : ℝ)^4167
        have hw : |(1085943007/2500000000 : ℝ)|=(1085943007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_8 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-52152949/312500000 : ℝ)*x 0 + (4994296267/10000000000 : ℝ)*x 1 + (5468081179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52152949/312500000 : ℝ)^5191 ≤ (10748509618887/100000000000000 : ℝ)^4167 := by
    have hnat : (52152949 : ℕ)^5191*100000000000000^4167 ≤ 10748509618887^4167*312500000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52152949 312500000 10748509618887 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4994296267/10000000000 : ℝ)^5191 ≤ (42109227443551/100000000000000 : ℝ)^4167 := by
    have hnat : (4994296267 : ℕ)^5191*100000000000000^4167 ≤ 42109227443551^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4994296267 10000000000 42109227443551 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468081179/10000000000 : ℝ)^5191 ≤ (4714226291241/10000000000000 : ℝ)^4167 := by
    have hnat : (5468081179 : ℕ)^5191*10000000000000^4167 ≤ 4714226291241^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468081179 10000000000 4714226291241 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52152949/312500000 : ℝ), (4994296267/10000000000 : ℝ), (5468081179/10000000000 : ℝ)] ![(10748509618887/100000000000000 : ℝ), (42109227443551/100000000000000 : ℝ), (4714226291241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52152949/312500000 : ℝ)|^5191 ≤ (10748509618887/100000000000000 : ℝ)^4167
        have hw : |(-52152949/312500000 : ℝ)|=(52152949/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4994296267/10000000000 : ℝ)|^5191 ≤ (42109227443551/100000000000000 : ℝ)^4167
        have hw : |(4994296267/10000000000 : ℝ)|=(4994296267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468081179/10000000000 : ℝ)|^5191 ≤ (4714226291241/10000000000000 : ℝ)^4167
        have hw : |(5468081179/10000000000 : ℝ)|=(5468081179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_9 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598227209/5000000000 : ℝ)*x 0 + (-1397267631/10000000000 : ℝ)*x 1 + (874893/1600000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598227209/5000000000 : ℝ)^5191 ≤ (8848606637629/20000000000000 : ℝ)^4167 := by
    have hnat : (2598227209 : ℕ)^5191*20000000000000^4167 ≤ 8848606637629^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598227209 5000000000 8848606637629 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1397267631/10000000000 : ℝ)^5191 ≤ (1722940624737/20000000000000 : ℝ)^4167 := by
    have hnat : (1397267631 : ℕ)^5191*20000000000000^4167 ≤ 1722940624737^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397267631 10000000000 1722940624737 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (874893/1600000 : ℝ)^5191 ≤ (11785565918737/25000000000000 : ℝ)^4167 := by
    have hnat : (874893 : ℕ)^5191*25000000000000^4167 ≤ 11785565918737^4167*1600000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874893 1600000 11785565918737 25000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598227209/5000000000 : ℝ), (-1397267631/10000000000 : ℝ), (874893/1600000 : ℝ)] ![(8848606637629/20000000000000 : ℝ), (1722940624737/20000000000000 : ℝ), (11785565918737/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598227209/5000000000 : ℝ)|^5191 ≤ (8848606637629/20000000000000 : ℝ)^4167
        have hw : |(2598227209/5000000000 : ℝ)|=(2598227209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1397267631/10000000000 : ℝ)|^5191 ≤ (1722940624737/20000000000000 : ℝ)^4167
        have hw : |(-1397267631/10000000000 : ℝ)|=(1397267631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(874893/1600000 : ℝ)|^5191 ≤ (11785565918737/25000000000000 : ℝ)^4167
        have hw : |(874893/1600000 : ℝ)|=(874893/1600000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_10 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598227041/5000000000 : ℝ)*x 0 + (2734040713/5000000000 : ℝ)*x 1 + (-1397267849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598227041/5000000000 : ℝ)^5191 ≤ (44243029624417/100000000000000 : ℝ)^4167 := by
    have hnat : (2598227041 : ℕ)^5191*100000000000000^4167 ≤ 44243029624417^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598227041 5000000000 44243029624417 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734040713/5000000000 : ℝ)^5191 ≤ (23571132782591/50000000000000 : ℝ)^4167 := by
    have hnat : (2734040713 : ℕ)^5191*50000000000000^4167 ≤ 23571132782591^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734040713 5000000000 23571132782591 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1397267849/10000000000 : ℝ)^5191 ≤ (861470479803/10000000000000 : ℝ)^4167 := by
    have hnat : (1397267849 : ℕ)^5191*10000000000000^4167 ≤ 861470479803^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1397267849 10000000000 861470479803 10000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598227041/5000000000 : ℝ), (2734040713/5000000000 : ℝ), (-1397267849/10000000000 : ℝ)] ![(44243029624417/100000000000000 : ℝ), (23571132782591/50000000000000 : ℝ), (861470479803/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598227041/5000000000 : ℝ)|^5191 ≤ (44243029624417/100000000000000 : ℝ)^4167
        have hw : |(2598227041/5000000000 : ℝ)|=(2598227041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734040713/5000000000 : ℝ)|^5191 ≤ (23571132782591/50000000000000 : ℝ)^4167
        have hw : |(2734040713/5000000000 : ℝ)|=(2734040713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1397267849/10000000000 : ℝ)|^5191 ≤ (861470479803/10000000000000 : ℝ)^4167
        have hw : |(-1397267849/10000000000 : ℝ)|=(1397267849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_11 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4638138507/10000000000 : ℝ)*x 0 + (3885362949/10000000000 : ℝ)*x 1 + (777072801/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4638138507/10000000000 : ℝ)^5191 ≤ (38401740112789/100000000000000 : ℝ)^4167 := by
    have hnat : (4638138507 : ℕ)^5191*100000000000000^4167 ≤ 38401740112789^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4638138507 10000000000 38401740112789 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3885362949/10000000000 : ℝ)^5191 ≤ (30799124722901/100000000000000 : ℝ)^4167 := by
    have hnat : (3885362949 : ℕ)^5191*100000000000000^4167 ≤ 30799124722901^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3885362949 10000000000 30799124722901 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (777072801/2000000000 : ℝ)^5191 ≤ (6159827030167/20000000000000 : ℝ)^4167 := by
    have hnat : (777072801 : ℕ)^5191*20000000000000^4167 ≤ 6159827030167^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777072801 2000000000 6159827030167 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4638138507/10000000000 : ℝ), (3885362949/10000000000 : ℝ), (777072801/2000000000 : ℝ)] ![(38401740112789/100000000000000 : ℝ), (30799124722901/100000000000000 : ℝ), (6159827030167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4638138507/10000000000 : ℝ)|^5191 ≤ (38401740112789/100000000000000 : ℝ)^4167
        have hw : |(4638138507/10000000000 : ℝ)|=(4638138507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3885362949/10000000000 : ℝ)|^5191 ≤ (30799124722901/100000000000000 : ℝ)^4167
        have hw : |(3885362949/10000000000 : ℝ)|=(3885362949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(777072801/2000000000 : ℝ)|^5191 ≤ (6159827030167/20000000000000 : ℝ)^4167
        have hw : |(777072801/2000000000 : ℝ)|=(777072801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_12 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1275577811/10000000000 : ℝ)*x 0 + (5598209859/10000000000 : ℝ)*x 1 + (1030282253/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1275577811/10000000000 : ℝ)^5191 ≤ (3845148198659/50000000000000 : ℝ)^4167 := by
    have hnat : (1275577811 : ℕ)^5191*50000000000000^4167 ≤ 3845148198659^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275577811 10000000000 3845148198659 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5598209859/10000000000 : ℝ)^5191 ≤ (48543903199879/100000000000000 : ℝ)^4167 := by
    have hnat : (5598209859 : ℕ)^5191*100000000000000^4167 ≤ 48543903199879^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5598209859 10000000000 48543903199879 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030282253/2000000000 : ℝ)^5191 ≤ (8753160078647/20000000000000 : ℝ)^4167 := by
    have hnat : (1030282253 : ℕ)^5191*20000000000000^4167 ≤ 8753160078647^4167*2000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030282253 2000000000 8753160078647 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1275577811/10000000000 : ℝ), (5598209859/10000000000 : ℝ), (1030282253/2000000000 : ℝ)] ![(3845148198659/50000000000000 : ℝ), (48543903199879/100000000000000 : ℝ), (8753160078647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1275577811/10000000000 : ℝ)|^5191 ≤ (3845148198659/50000000000000 : ℝ)^4167
        have hw : |(-1275577811/10000000000 : ℝ)|=(1275577811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5598209859/10000000000 : ℝ)|^5191 ≤ (48543903199879/100000000000000 : ℝ)^4167
        have hw : |(5598209859/10000000000 : ℝ)|=(5598209859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030282253/2000000000 : ℝ)|^5191 ≤ (8753160078647/20000000000000 : ℝ)^4167
        have hw : |(1030282253/2000000000 : ℝ)|=(1030282253/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_13 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2705979651/5000000000 : ℝ)*x 0 + (-24001971/156250000 : ℝ)*x 1 + (5151412037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705979651/5000000000 : ℝ)^5191 ≤ (46540277815633/100000000000000 : ℝ)^4167 := by
    have hnat : (2705979651 : ℕ)^5191*100000000000000^4167 ≤ 46540277815633^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705979651 5000000000 46540277815633 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24001971/156250000 : ℝ)^5191 ≤ (1938782722037/20000000000000 : ℝ)^4167 := by
    have hnat : (24001971 : ℕ)^5191*20000000000000^4167 ≤ 1938782722037^4167*156250000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24001971 156250000 1938782722037 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151412037/10000000000 : ℝ)^5191 ≤ (21882904281913/50000000000000 : ℝ)^4167 := by
    have hnat : (5151412037 : ℕ)^5191*50000000000000^4167 ≤ 21882904281913^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151412037 10000000000 21882904281913 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705979651/5000000000 : ℝ), (-24001971/156250000 : ℝ), (5151412037/10000000000 : ℝ)] ![(46540277815633/100000000000000 : ℝ), (1938782722037/20000000000000 : ℝ), (21882904281913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705979651/5000000000 : ℝ)|^5191 ≤ (46540277815633/100000000000000 : ℝ)^4167
        have hw : |(2705979651/5000000000 : ℝ)|=(2705979651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24001971/156250000 : ℝ)|^5191 ≤ (1938782722037/20000000000000 : ℝ)^4167
        have hw : |(-24001971/156250000 : ℝ)|=(24001971/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151412037/10000000000 : ℝ)|^5191 ≤ (21882904281913/50000000000000 : ℝ)^4167
        have hw : |(5151412037/10000000000 : ℝ)|=(5151412037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_14 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2705980243/5000000000 : ℝ)*x 0 + (2575705227/5000000000 : ℝ)*x 1 + (-768063331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705980243/5000000000 : ℝ)^5191 ≤ (46540290499559/100000000000000 : ℝ)^4167 := by
    have hnat : (2705980243 : ℕ)^5191*100000000000000^4167 ≤ 46540290499559^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705980243 5000000000 46540290499559 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2575705227/5000000000 : ℝ)^5191 ≤ (43765791809881/100000000000000 : ℝ)^4167 := by
    have hnat : (2575705227 : ℕ)^5191*100000000000000^4167 ≤ 43765791809881^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2575705227 5000000000 43765791809881 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (768063331/5000000000 : ℝ)^5191 ≤ (9693917682389/100000000000000 : ℝ)^4167 := by
    have hnat : (768063331 : ℕ)^5191*100000000000000^4167 ≤ 9693917682389^4167*5000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768063331 5000000000 9693917682389 100000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705980243/5000000000 : ℝ), (2575705227/5000000000 : ℝ), (-768063331/5000000000 : ℝ)] ![(46540290499559/100000000000000 : ℝ), (43765791809881/100000000000000 : ℝ), (9693917682389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705980243/5000000000 : ℝ)|^5191 ≤ (46540290499559/100000000000000 : ℝ)^4167
        have hw : |(2705980243/5000000000 : ℝ)|=(2705980243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2575705227/5000000000 : ℝ)|^5191 ≤ (43765791809881/100000000000000 : ℝ)^4167
        have hw : |(2575705227/5000000000 : ℝ)|=(2575705227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-768063331/5000000000 : ℝ)|^5191 ≤ (9693917682389/100000000000000 : ℝ)^4167
        have hw : |(-768063331/5000000000 : ℝ)|=(768063331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1696_box_15 (p : ℝ) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3642109109/10000000000 : ℝ)*x 0 + (4383382191/10000000000 : ℝ)*x 1 + (547922409/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3642109109/10000000000 : ℝ)^5191 ≤ (5683157247533/20000000000000 : ℝ)^4167 := by
    have hnat : (3642109109 : ℕ)^5191*20000000000000^4167 ≤ 5683157247533^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3642109109 10000000000 5683157247533 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4383382191/10000000000 : ℝ)^5191 ≤ (7158424344139/20000000000000 : ℝ)^4167 := by
    have hnat : (4383382191 : ℕ)^5191*20000000000000^4167 ≤ 7158424344139^4167*10000000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4383382191 10000000000 7158424344139 20000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547922409/1250000000 : ℝ)^5191 ≤ (17896046014339/50000000000000 : ℝ)^4167 := by
    have hnat : (547922409 : ℕ)^5191*50000000000000^4167 ≤ 17896046014339^4167*1250000000^5191 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547922409 1250000000 17896046014339 50000000000000 5191 4167 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5191/1024 : ℝ)) 5191 4167 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3642109109/10000000000 : ℝ), (4383382191/10000000000 : ℝ), (547922409/1250000000 : ℝ)] ![(5683157247533/20000000000000 : ℝ), (7158424344139/20000000000000 : ℝ), (17896046014339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3642109109/10000000000 : ℝ)|^5191 ≤ (5683157247533/20000000000000 : ℝ)^4167
        have hw : |(3642109109/10000000000 : ℝ)|=(3642109109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4383382191/10000000000 : ℝ)|^5191 ≤ (7158424344139/20000000000000 : ℝ)^4167
        have hw : |(4383382191/10000000000 : ℝ)|=(4383382191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(547922409/1250000000 : ℝ)|^5191 ≤ (17896046014339/50000000000000 : ℝ)^4167
        have hw : |(547922409/1250000000 : ℝ)|=(547922409/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1696_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2149/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(33311/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58073/100000 : ℝ) ∧ (40507/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90221/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2149/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2149/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9889/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2149/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2149/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9889/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2149/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2149/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9889/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9889/100000 : ℝ) ^ (5183/1024 : ℝ) ≤ (820238602674587/100000000000000000000 : ℝ) := by
    have hpowers : (9889/100000 : ℝ)^5183 ≤ (820238602674587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9889 : ℕ)^5183*100000000000000000000^1024 ≤ 820238602674587^1024*100000^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9889 100000 820238602674587 100000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9889/100000 : ℝ)) (X := (820238602674587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2149/12500 : ℝ) ^ (5183/1024 : ℝ) ≤ (13476796300575267/100000000000000000000 : ℝ) := by
    have hpowers : (2149/12500 : ℝ)^5183 ≤ (13476796300575267/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2149 : ℕ)^5183*100000000000000000000^1024 ≤ 13476796300575267^1024*12500^5183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2149 12500 13476796300575267 100000000000000000000 5183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2149/12500 : ℝ)) (X := (13476796300575267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000820238602674587/50000000000000000000 : ℝ) ≤ (10000032410526759/10000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (50000820238602674587/50000000000000000000 : ℝ)^1024 ≤ (10000032410526759/10000000000000000 : ℝ)^5183 := by
      have hnat : (50000820238602674587 : ℕ)^1024*10000000000000000^5183 ≤ 10000032410526759^5183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000820238602674587 50000000000000000000 10000032410526759 10000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000032410526759/10000000000000000 : ℝ)) (X := (50000820238602674587/50000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007148517451624927/50000000000000000000 : ℝ) ≤ (5000141224426251/5000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (50007148517451624927/50000000000000000000 : ℝ)^1024 ≤ (5000141224426251/5000000000000000 : ℝ)^5183 := by
      have hnat : (50007148517451624927 : ℕ)^1024*5000000000000000^5183 ≤ 5000141224426251^5183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007148517451624927 50000000000000000000 5000141224426251 5000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141224426251/5000000000000000 : ℝ)) (X := (50007148517451624927/50000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50013476796300575267/50000000000000000000 : ℝ) ≤ (2000106497435649/2000000000000000 : ℝ) ^ (5183/1024 : ℝ) := by
    have hpowers : (50013476796300575267/50000000000000000000 : ℝ)^1024 ≤ (2000106497435649/2000000000000000 : ℝ)^5183 := by
      have hnat : (50013476796300575267 : ℕ)^1024*2000000000000000^5183 ≤ 2000106497435649^5183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013476796300575267 50000000000000000000 2000106497435649 2000000000000000 1024 5183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000106497435649/2000000000000000 : ℝ)) (X := (50013476796300575267/50000000000000000000 : ℝ)) (by norm_num) 5183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(820238602674587/100000000000000000000 : ℝ) ≤ ((73025291436070375923/73030000000000000000 : ℝ)+2*(250038325743/730300000000000 : ℝ)*(9889/100000 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (73025291436070375923/73030000000000000000 : ℝ)+2*(250038325743/730300000000000 : ℝ)*(9889/100000 : ℝ)=(10000032410526759/10000000000000000 : ℝ) by norm_num, show 1+2*(820238602674587/100000000000000000000 : ℝ)=(50000820238602674587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13476796300575267/100000000000000000000 : ℝ)+(820238602674587/100000000000000000000 : ℝ) ≤ ((73025291436070375923/73030000000000000000 : ℝ)+(250038325743/730300000000000 : ℝ)*((2149/12500 : ℝ)+(9889/100000 : ℝ)))^(5183/1024 : ℝ) := by
    rw [show (73025291436070375923/73030000000000000000 : ℝ)+(250038325743/730300000000000 : ℝ)*((2149/12500 : ℝ)+(9889/100000 : ℝ))=(5000141224426251/5000000000000000 : ℝ) by norm_num, show 1+(13476796300575267/100000000000000000000 : ℝ)+(820238602674587/100000000000000000000 : ℝ)=(50007148517451624927/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13476796300575267/100000000000000000000 : ℝ) ≤ ((73025291436070375923/73030000000000000000 : ℝ)+2*(250038325743/730300000000000 : ℝ)*(2149/12500 : ℝ))^(5183/1024 : ℝ) := by
    rw [show (73025291436070375923/73030000000000000000 : ℝ)+2*(250038325743/730300000000000 : ℝ)*(2149/12500 : ℝ)=(2000106497435649/2000000000000000 : ℝ) by norm_num, show 1+2*(13476796300575267/100000000000000000000 : ℝ)=(50013476796300575267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (73025291436070375923/73030000000000000000 : ℝ)*(X 1 0+X 2 0)+(250038325743/730300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (2149/12500 : ℝ)) (c := (73025291436070375923/73030000000000000000 : ℝ)) (alpha := (250038325743/730300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (73025291436070375923/73030000000000000000 : ℝ)*(X 0 1+X 2 1)+(250038325743/730300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (2149/12500 : ℝ)) (c := (73025291436070375923/73030000000000000000 : ℝ)) (alpha := (250038325743/730300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (73025291436070375923/73030000000000000000 : ℝ)*(X 0 2+X 1 2)+(250038325743/730300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5183/1024 : ℝ)) (lo := (9889/100000 : ℝ)) (hi := (2149/12500 : ℝ)) (c := (73025291436070375923/73030000000000000000 : ℝ)) (alpha := (250038325743/730300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1134445817/10000000000 : ℝ)*X 0 0+(21190457/39062500 : ℝ)*X 0 1+(5424756871/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1306480589/2500000000 : ℝ)*X 1 0+(-708517421/5000000000 : ℝ)*X 1 1+(1084951369/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612961127/5000000000 : ℝ)*X 2 0+(1356189219/2500000000 : ℝ)*X 2 1+(-1417034939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4506606429/10000000000 : ℝ)*X 0 0+(247104187/625000000 : ℝ)*X 0 1+(3953666733/10000000000 : ℝ)*X 0 2+(4506606429/10000000000 : ℝ)*X 1 0+(247104187/625000000 : ℝ)*X 1 1+(3953666733/10000000000 : ℝ)*X 1 2+(4506606429/10000000000 : ℝ)*X 2 0+(247104187/625000000 : ℝ)*X 2 1+(3953666733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-453761159/2500000000 : ℝ)*X 0 0+(5176668501/10000000000 : ℝ)*X 0 1+(5176668403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5394744209/10000000000 : ℝ)*X 1 0+(-1525544341/10000000000 : ℝ)*X 1 1+(5176668469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5394744277/10000000000 : ℝ)*X 2 0+(5176668389/10000000000 : ℝ)*X 2 1+(-381386089/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3724695163/10000000000 : ℝ)*X 0 0+(4343772063/10000000000 : ℝ)*X 0 1+(1085943007/2500000000 : ℝ)*X 0 2+(3724695163/10000000000 : ℝ)*X 1 0+(4343772063/10000000000 : ℝ)*X 1 1+(1085943007/2500000000 : ℝ)*X 1 2+(3724695163/10000000000 : ℝ)*X 2 0+(4343772063/10000000000 : ℝ)*X 2 1+(1085943007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-52152949/312500000 : ℝ)*X 0 0+(4994296267/10000000000 : ℝ)*X 0 1+(5468081179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598227209/5000000000 : ℝ)*X 1 0+(-1397267631/10000000000 : ℝ)*X 1 1+(874893/1600000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2598227041/5000000000 : ℝ)*X 2 0+(2734040713/5000000000 : ℝ)*X 2 1+(-1397267849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4638138507/10000000000 : ℝ)*X 0 0+(3885362949/10000000000 : ℝ)*X 0 1+(777072801/2000000000 : ℝ)*X 0 2+(4638138507/10000000000 : ℝ)*X 1 0+(3885362949/10000000000 : ℝ)*X 1 1+(777072801/2000000000 : ℝ)*X 1 2+(4638138507/10000000000 : ℝ)*X 2 0+(3885362949/10000000000 : ℝ)*X 2 1+(777072801/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1275577811/10000000000 : ℝ)*X 0 0+(5598209859/10000000000 : ℝ)*X 0 1+(1030282253/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2705979651/5000000000 : ℝ)*X 1 0+(-24001971/156250000 : ℝ)*X 1 1+(5151412037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2705980243/5000000000 : ℝ)*X 2 0+(2575705227/5000000000 : ℝ)*X 2 1+(-768063331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3642109109/10000000000 : ℝ)*X 0 0+(4383382191/10000000000 : ℝ)*X 0 1+(547922409/1250000000 : ℝ)*X 0 2+(3642109109/10000000000 : ℝ)*X 1 0+(4383382191/10000000000 : ℝ)*X 1 1+(547922409/1250000000 : ℝ)*X 1 2+(3642109109/10000000000 : ℝ)*X 2 0+(4383382191/10000000000 : ℝ)*X 2 1+(547922409/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1696_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-33311/50000 : ℝ) ≤ (-304076724984211077813780487032891/456437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9537/1562500000000 : ℝ)*(lower2) + (2132569/50000000000000 : ℝ)*(upper4) + (92911/100000000000000 : ℝ)*(upper5) + (330243182132861/25000000000000 : ℝ)*(major0) + (330243182132861/25000000000000 : ℝ)*(major1) + (264194545706289/20000000000000 : ℝ)*(major2) + (18575287/50000000000000 : ℝ)*(sp1) + (270956523/50000000000000 : ℝ)*(sp2) + (31481017/50000000000000 : ℝ)*(sp3) + (985073891383681/50000000000000 : ℝ)*(sp4) + (1970148223449/100000000000 : ℝ)*(sp5) + (1970147718686529/100000000000000 : ℝ)*(sp6) + (27760146346897/4000000000000 : ℝ)*(sp7) + (477832213/100000000000000 : ℝ)*(sp8) + (694003721634459/100000000000000 : ℝ)*(f.failure) + (78805930423983/4000000000000 : ℝ)*(f.sum) + (24484078740823/73030000000000000000000000000 : ℝ)*base66 + (10951020321084619297/1825750000000000000000000000000000 : ℝ)*base68 + (1696092140967880253/1460600000000000000000000000000000 : ℝ)*base70 + (12009612936361369297/1825750000000000000000000000000000 : ℝ)*base72 + (90239264669323/73030000000000000000000000000 : ℝ)*base74 + (7152985067401919747/1460600000000000000000000000000000 : ℝ)*base75 + (10450094985384694297/1825750000000000000000000000000000 : ℝ)*base78 + (12130357361661194297/1825750000000000000000000000000000 : ℝ)*base80 + (386306835583/9128750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (69673789/10000000000000000000000 : ℝ)*base89 + (69673789/10000000000000000000000 : ℝ)*base91 + (30326211/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58073/100000 : ℝ) ≤ (1325382103723163843139062739/2282187500000000000000000000 : ℝ) := by norm_num
    linear_combination (1435327/20000000000000 : ℝ)*(lower0) + (3280773/25000000000000 : ℝ)*(upper2) + (10481401/100000000000000 : ℝ)*(upper3) + (27245763/100000000000000 : ℝ)*(lower5) + (710868180283663/50000000000000 : ℝ)*(major0) + (710868180283663/50000000000000 : ℝ)*(major1) + (710868180283663/50000000000000 : ℝ)*(major2) + (103858606268127/5000000000000 : ℝ)*(sp0) + (2077168459519113/100000000000000 : ℝ)*(sp1) + (103858559804071/5000000000000 : ℝ)*(sp2) + (93367750999691/12500000000000 : ℝ)*(sp3) + (57354989/25000000000000 : ℝ)*(sp7) + (916460857/25000000000000 : ℝ)*(sp9) + (929281121/100000000000000 : ℝ)*(sp10) + (186735559354371/25000000000000 : ℝ)*(f.failure) + (103858606268127/5000000000000 : ℝ)*(f.sum) + (33787643927909/18257500000000000000000000000 : ℝ)*base65 + (16699931841220345949/3651500000000000000000000000000000 : ℝ)*base67 + (1632475544348345949/3651500000000000000000000000000000 : ℝ)*base69 + (10873168291161654051/3651500000000000000000000000000000 : ℝ)*base72 + (27033351713977/2282187500000000000000000000 : ℝ)*base74 + (18474842021619154051/3651500000000000000000000000000000 : ℝ)*base76 + (10462358266133345949/3651500000000000000000000000000000 : ℝ)*base77 + (2556336611858654051/3651500000000000000000000000000000 : ℝ)*base80 + (22055509176527/36515000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (23797141/2500000000000000000000 : ℝ)*base89 + (23797141/2500000000000000000000 : ℝ)*base91 + (23797141/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40507/50000 : ℝ) ≤ (591662387620600815703671450639507/730300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8773111/25000000000000 : ℝ)*(upper0) + (21474753/25000000000000 : ℝ)*(upper2) + (9368919/100000000000000 : ℝ)*(lower3) + (289926732869803/20000000000000 : ℝ)*(major0) + (289926732869803/20000000000000 : ℝ)*(major1) + (181204208043627/12500000000000 : ℝ)*(major2) + (22678531753/100000000000000 : ℝ)*(sp1) + (17594653157/100000000000000 : ℝ)*(sp2) + (238914949/5000000000000 : ℝ)*(sp3) + (2535879263/100000000000000 : ℝ)*(sp4) + (105533030464551/5000000000000 : ℝ)*(sp8) + (211064046663853/10000000000000 : ℝ)*(sp9) + (1055322775258563/50000000000000 : ℝ)*(sp10) + (15231879119573/2000000000000 : ℝ)*(sp11) + (761598734277629/100000000000000 : ℝ)*(f.failure) + (1055331572585141/50000000000000 : ℝ)*(f.sum) + (272827199034227/73030000000000000000000000000 : ℝ)*base66 + (3783451514245086831/1460600000000000000000000000000000 : ℝ)*base68 + (3411094540833419779/912875000000000000000000000000000 : ℝ)*base70 + (5956078626824086831/1460600000000000000000000000000000 : ℝ)*base72 + (505432535873413/73030000000000000000000000000 : ℝ)*base73 + (1640370278735580221/912875000000000000000000000000000 : ℝ)*base75 + (7575288653420146831/1460600000000000000000000000000000 : ℝ)*base78 + (16904536720677053169/1460600000000000000000000000000000 : ℝ)*base79 + (1055718648877/146060000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (40325141/10000000000000000000000 : ℝ)*base90 + (40325141/10000000000000000000000 : ℝ)*base92 + (140325141/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-90221/100000 : ℝ) ≤ (-16471579904173073322554182099113/18257500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27227019/100000000000000 : ℝ)*(lower0) + (71291933/50000000000000 : ℝ)*(lower2) + (121546271/50000000000000 : ℝ)*(upper3) + (7486889504559/500000000000 : ℝ)*(major0) + (7486889504559/500000000000 : ℝ)*(major1) + (7486889504559/500000000000 : ℝ)*(major2) + (81719191/20000000000000 : ℝ)*(sp0) + (32259680569/100000000000000 : ℝ)*(sp5) + (103360727559/100000000000000 : ℝ)*(sp6) + (20966430731/100000000000000 : ℝ)*(sp7) + (2238145833520183/100000000000000 : ℝ)*(sp12) + (2238113982435569/100000000000000 : ℝ)*(sp13) + (1119021440694289/50000000000000 : ℝ)*(sp14) + (393330656037853/50000000000000 : ℝ)*(sp15) + (393341139253219/50000000000000 : ℝ)*(f.failure) + (1119073121058069/50000000000000 : ℝ)*(f.sum) + (4847136248597/7303000000000000000000000000 : ℝ)*base66 + (239430511370192957/36515000000000000000000000000000 : ℝ)*base67 + (90821569234032957/36515000000000000000000000000000 : ℝ)*base69 + (242188255259042957/36515000000000000000000000000000 : ℝ)*base71 + (63221406496739/3651500000000000000000000000 : ℝ)*base73 + (141296085253822957/36515000000000000000000000000000 : ℝ)*base75 + (302387943486162957/36515000000000000000000000000000 : ℝ)*base77 + (1112614071602957/36515000000000000000000000000000 : ℝ)*base79 + (13147378609/73030000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (5986251/5000000000000000000000 : ℝ)*base90 + (5986251/5000000000000000000000 : ℝ)*base92 + (5986251/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1696_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2149/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9889/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33311/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58073/100000 : ℝ) else (40507/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90221/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1696_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1696_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33311/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58073/100000 : ℝ) else (40507/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90221/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1696_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1696_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1696_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5183/1024 : ℝ) ≤ p) (hpb : p ≤ (5191/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (190340871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17211/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9873/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(33311/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58073/100000 : ℝ) else (40507/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90221/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1696_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
