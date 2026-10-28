-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:50:07.483759+00:00
-- url     : https://prove2.me/submissions/e872a73c-d762-4097-a8e1-d081369e2da8

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
theorem support_rectangle_w1182_s0_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-375843029/2000000000 : ℝ)*x 0 + (75564141/125000000 : ℝ)*x 1 + (239275511/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375843029/2000000000 : ℝ)^8375 ≤ (10938768319629/100000000000000 : ℝ)^6327 := by
    have hnat : (375843029 : ℕ)^8375*100000000000000^6327 ≤ 10938768319629^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375843029 2000000000 10938768319629 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75564141/125000000 : ℝ)^8375 ≤ (6420347143961/12500000000000 : ℝ)^6327 := by
    have hnat : (75564141 : ℕ)^8375*12500000000000^6327 ≤ 6420347143961^6327*125000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75564141 125000000 6420347143961 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (239275511/500000000 : ℝ)^8375 ≤ (7539690903957/20000000000000 : ℝ)^6327 := by
    have hnat : (239275511 : ℕ)^8375*20000000000000^6327 ≤ 7539690903957^6327*500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239275511 500000000 7539690903957 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375843029/2000000000 : ℝ), (75564141/125000000 : ℝ), (239275511/500000000 : ℝ)] ![(10938768319629/100000000000000 : ℝ), (6420347143961/12500000000000 : ℝ), (7539690903957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375843029/2000000000 : ℝ)|^8375 ≤ (10938768319629/100000000000000 : ℝ)^6327
        have hw : |(-375843029/2000000000 : ℝ)|=(375843029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75564141/125000000 : ℝ)|^8375 ≤ (6420347143961/12500000000000 : ℝ)^6327
        have hw : |(75564141/125000000 : ℝ)|=(75564141/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(239275511/500000000 : ℝ)|^8375 ≤ (7539690903957/20000000000000 : ℝ)^6327
        have hw : |(239275511/500000000 : ℝ)|=(239275511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s0_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757270021/5000000000 : ℝ)*x 0 + (-1300483831/5000000000 : ℝ)*x 1 + (4785510219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757270021/5000000000 : ℝ)^8375 ≤ (11370456486813/25000000000000 : ℝ)^6327 := by
    have hnat : (2757270021 : ℕ)^8375*25000000000000^6327 ≤ 11370456486813^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757270021 5000000000 11370456486813 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1300483831/5000000000 : ℝ)^8375 ≤ (8409859762727/50000000000000 : ℝ)^6327 := by
    have hnat : (1300483831 : ℕ)^8375*50000000000000^6327 ≤ 8409859762727^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300483831 5000000000 8409859762727 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4785510219/10000000000 : ℝ)^8375 ≤ (37698454509357/100000000000000 : ℝ)^6327 := by
    have hnat : (4785510219 : ℕ)^8375*100000000000000^6327 ≤ 37698454509357^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4785510219 10000000000 37698454509357 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757270021/5000000000 : ℝ), (-1300483831/5000000000 : ℝ), (4785510219/10000000000 : ℝ)] ![(11370456486813/25000000000000 : ℝ), (8409859762727/50000000000000 : ℝ), (37698454509357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757270021/5000000000 : ℝ)|^8375 ≤ (11370456486813/25000000000000 : ℝ)^6327
        have hw : |(2757270021/5000000000 : ℝ)|=(2757270021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1300483831/5000000000 : ℝ)|^8375 ≤ (8409859762727/50000000000000 : ℝ)^6327
        have hw : |(-1300483831/5000000000 : ℝ)|=(1300483831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4785510219/10000000000 : ℝ)|^8375 ≤ (37698454509357/100000000000000 : ℝ)^6327
        have hw : |(4785510219/10000000000 : ℝ)|=(4785510219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s0_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2757270013/5000000000 : ℝ)*x 0 + (191420409/400000000 : ℝ)*x 1 + (-650241919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2757270013/5000000000 : ℝ)^8375 ≤ (1819273030903/4000000000000 : ℝ)^6327 := by
    have hnat : (2757270013 : ℕ)^8375*4000000000000^6327 ≤ 1819273030903^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757270013 5000000000 1819273030903 4000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (191420409/400000000 : ℝ)^8375 ≤ (37698454571923/100000000000000 : ℝ)^6327 := by
    have hnat : (191420409 : ℕ)^8375*100000000000000^6327 ≤ 37698454571923^6327*400000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191420409 400000000 37698454571923 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650241919/2500000000 : ℝ)^8375 ≤ (16819719645293/100000000000000 : ℝ)^6327 := by
    have hnat : (650241919 : ℕ)^8375*100000000000000^6327 ≤ 16819719645293^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650241919 2500000000 16819719645293 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2757270013/5000000000 : ℝ), (191420409/400000000 : ℝ), (-650241919/2500000000 : ℝ)] ![(1819273030903/4000000000000 : ℝ), (37698454571923/100000000000000 : ℝ), (16819719645293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2757270013/5000000000 : ℝ)|^8375 ≤ (1819273030903/4000000000000 : ℝ)^6327
        have hw : |(2757270013/5000000000 : ℝ)|=(2757270013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(191420409/400000000 : ℝ)|^8375 ≤ (37698454571923/100000000000000 : ℝ)^6327
        have hw : |(191420409/400000000 : ℝ)|=(191420409/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-650241919/2500000000 : ℝ)|^8375 ≤ (16819719645293/100000000000000 : ℝ)^6327
        have hw : |(-650241919/2500000000 : ℝ)|=(650241919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s0_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4197774963/10000000000 : ℝ)*x 0 + (1559648703/5000000000 : ℝ)*x 1 + (2822478689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4197774963/10000000000 : ℝ)^8375 ≤ (31695194845001/100000000000000 : ℝ)^6327 := by
    have hnat : (4197774963 : ℕ)^8375*100000000000000^6327 ≤ 31695194845001^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4197774963 10000000000 31695194845001 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1559648703/5000000000 : ℝ)^8375 ≤ (21393751914941/100000000000000 : ℝ)^6327 := by
    have hnat : (1559648703 : ℕ)^8375*100000000000000^6327 ≤ 21393751914941^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1559648703 5000000000 21393751914941 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2822478689/5000000000 : ℝ)^8375 ≤ (46911053234453/100000000000000 : ℝ)^6327 := by
    have hnat : (2822478689 : ℕ)^8375*100000000000000^6327 ≤ 46911053234453^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2822478689 5000000000 46911053234453 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4197774963/10000000000 : ℝ), (1559648703/5000000000 : ℝ), (2822478689/5000000000 : ℝ)] ![(31695194845001/100000000000000 : ℝ), (21393751914941/100000000000000 : ℝ), (46911053234453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4197774963/10000000000 : ℝ)|^8375 ≤ (31695194845001/100000000000000 : ℝ)^6327
        have hw : |(4197774963/10000000000 : ℝ)|=(4197774963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1559648703/5000000000 : ℝ)|^8375 ≤ (21393751914941/100000000000000 : ℝ)^6327
        have hw : |(1559648703/5000000000 : ℝ)|=(1559648703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2822478689/5000000000 : ℝ)|^8375 ≤ (46911053234453/100000000000000 : ℝ)^6327
        have hw : |(2822478689/5000000000 : ℝ)|=(2822478689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s0_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-471061019/2500000000 : ℝ)*x 0 + (4817983667/10000000000 : ℝ)*x 1 + (3005756631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471061019/2500000000 : ℝ)^8375 ≤ (2744383390933/25000000000000 : ℝ)^6327 := by
    have hnat : (471061019 : ℕ)^8375*25000000000000^6327 ≤ 2744383390933^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471061019 2500000000 2744383390933 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4817983667/10000000000 : ℝ)^8375 ≤ (38037444332279/100000000000000 : ℝ)^6327 := by
    have hnat : (4817983667 : ℕ)^8375*100000000000000^6327 ≤ 38037444332279^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4817983667 10000000000 38037444332279 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005756631/5000000000 : ℝ)^8375 ≤ (25492511045339/50000000000000 : ℝ)^6327 := by
    have hnat : (3005756631 : ℕ)^8375*50000000000000^6327 ≤ 25492511045339^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005756631 5000000000 25492511045339 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471061019/2500000000 : ℝ), (4817983667/10000000000 : ℝ), (3005756631/5000000000 : ℝ)] ![(2744383390933/25000000000000 : ℝ), (38037444332279/100000000000000 : ℝ), (25492511045339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471061019/2500000000 : ℝ)|^8375 ≤ (2744383390933/25000000000000 : ℝ)^6327
        have hw : |(-471061019/2500000000 : ℝ)|=(471061019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4817983667/10000000000 : ℝ)|^8375 ≤ (38037444332279/100000000000000 : ℝ)^6327
        have hw : |(4817983667/10000000000 : ℝ)|=(4817983667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005756631/5000000000 : ℝ)|^8375 ≤ (25492511045339/50000000000000 : ℝ)^6327
        have hw : |(3005756631/5000000000 : ℝ)|=(3005756631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s0_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5172082931/10000000000 : ℝ)*x 0 + (-1374964841/10000000000 : ℝ)*x 1 + (3005756483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5172082931/10000000000 : ℝ)^8375 ≤ (5222654146333/12500000000000 : ℝ)^6327 := by
    have hnat : (5172082931 : ℕ)^8375*12500000000000^6327 ≤ 5222654146333^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172082931 10000000000 5222654146333 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1374964841/10000000000 : ℝ)^8375 ≤ (3616874021281/50000000000000 : ℝ)^6327 := by
    have hnat : (1374964841 : ℕ)^8375*50000000000000^6327 ≤ 3616874021281^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1374964841 10000000000 3616874021281 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005756483/5000000000 : ℝ)^8375 ≤ (50985018767623/100000000000000 : ℝ)^6327 := by
    have hnat : (3005756483 : ℕ)^8375*100000000000000^6327 ≤ 50985018767623^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005756483 5000000000 50985018767623 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5172082931/10000000000 : ℝ), (-1374964841/10000000000 : ℝ), (3005756483/5000000000 : ℝ)] ![(5222654146333/12500000000000 : ℝ), (3616874021281/50000000000000 : ℝ), (50985018767623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5172082931/10000000000 : ℝ)|^8375 ≤ (5222654146333/12500000000000 : ℝ)^6327
        have hw : |(5172082931/10000000000 : ℝ)|=(5172082931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1374964841/10000000000 : ℝ)|^8375 ≤ (3616874021281/50000000000000 : ℝ)^6327
        have hw : |(-1374964841/10000000000 : ℝ)|=(1374964841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3005756483/5000000000 : ℝ)|^8375 ≤ (50985018767623/100000000000000 : ℝ)^6327
        have hw : |(3005756483/5000000000 : ℝ)|=(3005756483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s0_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (41376663/80000000 : ℝ)*x 0 + (3005756561/5000000000 : ℝ)*x 1 + (-343741169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41376663/80000000 : ℝ)^8375 ≤ (10445308142963/25000000000000 : ℝ)^6327 := by
    have hnat : (41376663 : ℕ)^8375*25000000000000^6327 ≤ 10445308142963^6327*80000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41376663 80000000 10445308142963 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3005756561/5000000000 : ℝ)^8375 ≤ (50985020518963/100000000000000 : ℝ)^6327 := by
    have hnat : (3005756561 : ℕ)^8375*100000000000000^6327 ≤ 50985020518963^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005756561 5000000000 50985020518963 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343741169/2500000000 : ℝ)^8375 ≤ (3616873446751/50000000000000 : ℝ)^6327 := by
    have hnat : (343741169 : ℕ)^8375*50000000000000^6327 ≤ 3616873446751^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343741169 2500000000 3616873446751 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41376663/80000000 : ℝ), (3005756561/5000000000 : ℝ), (-343741169/2500000000 : ℝ)] ![(10445308142963/25000000000000 : ℝ), (50985020518963/100000000000000 : ℝ), (3616873446751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41376663/80000000 : ℝ)|^8375 ≤ (10445308142963/25000000000000 : ℝ)^6327
        have hw : |(41376663/80000000 : ℝ)|=(41376663/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3005756561/5000000000 : ℝ)|^8375 ≤ (50985020518963/100000000000000 : ℝ)^6327
        have hw : |(3005756561/5000000000 : ℝ)|=(3005756561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343741169/2500000000 : ℝ)|^8375 ≤ (3616873446751/50000000000000 : ℝ)^6327
        have hw : |(-343741169/2500000000 : ℝ)|=(343741169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s0_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2103929263/5000000000 : ℝ)*x 0 + (1115968927/2000000000 : ℝ)*x 1 + (3186705061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103929263/5000000000 : ℝ)^8375 ≤ (31796014217129/100000000000000 : ℝ)^6327 := by
    have hnat : (2103929263 : ℕ)^8375*100000000000000^6327 ≤ 31796014217129^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103929263 5000000000 31796014217129 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115968927/2000000000 : ℝ)^8375 ≤ (2887258697209/6250000000000 : ℝ)^6327 := by
    have hnat : (1115968927 : ℕ)^8375*6250000000000^6327 ≤ 2887258697209^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115968927 2000000000 2887258697209 6250000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3186705061/10000000000 : ℝ)^8375 ≤ (11003923306239/50000000000000 : ℝ)^6327 := by
    have hnat : (3186705061 : ℕ)^8375*50000000000000^6327 ≤ 11003923306239^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3186705061 10000000000 11003923306239 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2103929263/5000000000 : ℝ), (1115968927/2000000000 : ℝ), (3186705061/10000000000 : ℝ)] ![(31796014217129/100000000000000 : ℝ), (2887258697209/6250000000000 : ℝ), (11003923306239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2103929263/5000000000 : ℝ)|^8375 ≤ (31796014217129/100000000000000 : ℝ)^6327
        have hw : |(2103929263/5000000000 : ℝ)|=(2103929263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115968927/2000000000 : ℝ)|^8375 ≤ (2887258697209/6250000000000 : ℝ)^6327
        have hw : |(1115968927/2000000000 : ℝ)|=(1115968927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3186705061/10000000000 : ℝ)|^8375 ≤ (11003923306239/50000000000000 : ℝ)^6327
        have hw : |(3186705061/10000000000 : ℝ)|=(3186705061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (577/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13831/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4187/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4187 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4187*1^1024 ≤ 0^1024*1^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4187/1024 : ℝ) ≤ (73743912865745481/3125000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4187 ≤ (73743912865745481/3125000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4187*3125000000000000000^1024 ≤ 73743912865745481^1024*5^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 73743912865745481 3125000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (73743912865745481/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4187 := by
      have hnat : (1 : ℕ)^1024*1^4187 ≤ 1^4187*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3198743912865745481/3125000000000000000 : ℝ) ≤ (2011441101249359/2000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (3198743912865745481/3125000000000000000 : ℝ)^1024 ≤ (2011441101249359/2000000000000000 : ℝ)^4187 := by
      have hnat : (3198743912865745481 : ℕ)^1024*2000000000000000^4187 ≤ 2011441101249359^4187*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3198743912865745481 3125000000000000000 2011441101249359 2000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011441101249359/2000000000000000 : ℝ)) (X := (3198743912865745481/3125000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1636243912865745481/1562500000000000000 : ℝ) ≤ (1011441101249359/1000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (1636243912865745481/1562500000000000000 : ℝ)^1024 ≤ (1011441101249359/1000000000000000 : ℝ)^4187 := by
      have hnat : (1636243912865745481 : ℕ)^1024*1000000000000000^4187 ≤ 1011441101249359^4187*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1636243912865745481 1562500000000000000 1011441101249359 1000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011441101249359/1000000000000000 : ℝ)) (X := (1636243912865745481/1562500000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11441101249359/800000000000000 : ℝ)*(0 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11441101249359/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73743912865745481/3125000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11441101249359/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11441101249359/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011441101249359/2000000000000000 : ℝ) by norm_num, show 1+(73743912865745481/3125000000000000000 : ℝ)+(0 : ℝ)=(3198743912865745481/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73743912865745481/3125000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11441101249359/800000000000000 : ℝ)*(2/5 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11441101249359/800000000000000 : ℝ)*(2/5 : ℝ)=(1011441101249359/1000000000000000 : ℝ) by norm_num, show 1+2*(73743912865745481/3125000000000000000 : ℝ)=(1636243912865745481/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11441101249359/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11441101249359/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11441101249359/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11441101249359/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11441101249359/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11441101249359/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-375843029/2000000000 : ℝ)*X 0 0+(75564141/125000000 : ℝ)*X 0 1+(239275511/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2757270021/5000000000 : ℝ)*X 1 0+(-1300483831/5000000000 : ℝ)*X 1 1+(4785510219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2757270013/5000000000 : ℝ)*X 2 0+(191420409/400000000 : ℝ)*X 2 1+(-650241919/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4197774963/10000000000 : ℝ)*X 0 0+(1559648703/5000000000 : ℝ)*X 0 1+(2822478689/5000000000 : ℝ)*X 0 2+(4197774963/10000000000 : ℝ)*X 1 0+(1559648703/5000000000 : ℝ)*X 1 1+(2822478689/5000000000 : ℝ)*X 1 2+(4197774963/10000000000 : ℝ)*X 2 0+(1559648703/5000000000 : ℝ)*X 2 1+(2822478689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-471061019/2500000000 : ℝ)*X 0 0+(4817983667/10000000000 : ℝ)*X 0 1+(3005756631/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5172082931/10000000000 : ℝ)*X 1 0+(-1374964841/10000000000 : ℝ)*X 1 1+(3005756483/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41376663/80000000 : ℝ)*X 2 0+(3005756561/5000000000 : ℝ)*X 2 1+(-343741169/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2103929263/5000000000 : ℝ)*X 0 0+(1115968927/2000000000 : ℝ)*X 0 1+(3186705061/10000000000 : ℝ)*X 0 2+(2103929263/5000000000 : ℝ)*X 1 0+(1115968927/2000000000 : ℝ)*X 1 1+(3186705061/10000000000 : ℝ)*X 1 2+(2103929263/5000000000 : ℝ)*X 2 0+(1115968927/2000000000 : ℝ)*X 2 1+(3186705061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11751384827166840760401/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49616197/100000000000000 : ℝ)*(base1) + (115487317/10000000000000 : ℝ)*(base19) + (536993407/50000000000000 : ℝ)*(base23) + (78582933/100000000000000 : ℝ)*(base24) + (266002021/100000000000000 : ℝ)*(upper3) + (148729436114787/25000000000000 : ℝ)*(major0) + (148729436114787/25000000000000 : ℝ)*(major1) + (148729436114787/25000000000000 : ℝ)*(major2) + (793893449211671/100000000000000 : ℝ)*(sp0) + (793894792694301/100000000000000 : ℝ)*(sp1) + (198473698749431/25000000000000 : ℝ)*(sp2) + (395937304684169/100000000000000 : ℝ)*(sp3) + (2547971997/100000000000000 : ℝ)*(sp4) + (2030365321/100000000000000 : ℝ)*(sp7) + (395939384665687/100000000000000 : ℝ)*(f.failure) + (49618496722967/6250000000000 : ℝ)*(f.sum) + (24119228911533/10000000000000000000000000000 : ℝ)*base65 + (24987572388467/20000000000000000000000000000 : ℝ)*base68 + (118123828231533/20000000000000000000000000000 : ℝ)*base69 + (28221869471533/20000000000000000000000000000 : ℝ)*base71 + (21818892301533/10000000000000000000000000000 : ℝ)*base73 + (112230626531533/20000000000000000000000000000 : ℝ)*base75 + (4722134168467/20000000000000000000000000000 : ℝ)*base78 + (18388707191533/20000000000000000000000000000 : ℝ)*base79 + (36636943781533/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12239689/10000000000000000000000 : ℝ)*base90 + (12239689/10000000000000000000000 : ℝ)*base92 + (12239689/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (76068119177830676902719/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2487459/10000000000000 : ℝ)*(base1) + (252824131/50000000000000 : ℝ)*(base19) + (99854531/20000000000000 : ℝ)*(base23) + (44123599/100000000000000 : ℝ)*(upper3) + (66608907/100000000000000 : ℝ)*(upper5) + (627856150746551/100000000000000 : ℝ)*(major0) + (627856150746551/100000000000000 : ℝ)*(major1) + (627856150746551/100000000000000 : ℝ)*(major2) + (960844241/100000000000000 : ℝ)*(sp1) + (1001562997/100000000000000 : ℝ)*(sp2) + (837851171590651/100000000000000 : ℝ)*(sp4) + (418924840111779/50000000000000 : ℝ)*(sp5) + (837849645880409/100000000000000 : ℝ)*(sp6) + (8357221330247/2000000000000 : ℝ)*(sp7) + (20893054569347/5000000000000 : ℝ)*(f.failure) + (837851146716061/100000000000000 : ℝ)*(f.sum) + (41764155250809/40000000000000000000000000000 : ℝ)*base65 + (158355502850809/80000000000000000000000000000 : ℝ)*base67 + (21570692749191/80000000000000000000000000000 : ℝ)*base70 + (197504042610809/80000000000000000000000000000 : ℝ)*base71 + (98131323010809/40000000000000000000000000000 : ℝ)*base73 + (81309752349191/80000000000000000000000000000 : ℝ)*base76 + (238429868450809/80000000000000000000000000000 : ℝ)*base77 + (173122417629191/80000000000000000000000000000 : ℝ)*base80 + (41531224450809/40000000000000000000000000000 : ℝ)*base81 + (143709/500000000000000000000 : ℝ)*base90 + (143709/500000000000000000000 : ℝ)*base92 + (143709/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1182_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (577/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13831/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1182_s1_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-416197903/2000000000 : ℝ)*x 0 + (5690939031/10000000000 : ℝ)*x 1 + (5010538427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416197903/2000000000 : ℝ)^8375 ≤ (6259926544441/50000000000000 : ℝ)^6327 := by
    have hnat : (416197903 : ℕ)^8375*50000000000000^6327 ≤ 6259926544441^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416197903 2000000000 6259926544441 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690939031/10000000000 : ℝ)^8375 ≤ (4741752728619/10000000000000 : ℝ)^6327 := by
    have hnat : (5690939031 : ℕ)^8375*10000000000000^6327 ≤ 4741752728619^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690939031 10000000000 4741752728619 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5010538427/10000000000 : ℝ)^8375 ≤ (2003130980657/5000000000000 : ℝ)^6327 := by
    have hnat : (5010538427 : ℕ)^8375*5000000000000^6327 ≤ 2003130980657^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5010538427 10000000000 2003130980657 5000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416197903/2000000000 : ℝ), (5690939031/10000000000 : ℝ), (5010538427/10000000000 : ℝ)] ![(6259926544441/50000000000000 : ℝ), (4741752728619/10000000000000 : ℝ), (2003130980657/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416197903/2000000000 : ℝ)|^8375 ≤ (6259926544441/50000000000000 : ℝ)^6327
        have hw : |(-416197903/2000000000 : ℝ)|=(416197903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690939031/10000000000 : ℝ)|^8375 ≤ (4741752728619/10000000000000 : ℝ)^6327
        have hw : |(5690939031/10000000000 : ℝ)|=(5690939031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5010538427/10000000000 : ℝ)|^8375 ≤ (2003130980657/5000000000000 : ℝ)^6327
        have hw : |(5010538427/10000000000 : ℝ)|=(5010538427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s1_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5416926919/10000000000 : ℝ)*x 0 + (-152964267/625000000 : ℝ)*x 1 + (1252634659/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5416926919/10000000000 : ℝ)^8375 ≤ (44419218640093/100000000000000 : ℝ)^6327 := by
    have hnat : (5416926919 : ℕ)^8375*100000000000000^6327 ≤ 44419218640093^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416926919 10000000000 44419218640093 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (152964267/625000000 : ℝ)^8375 ≤ (775907975871/5000000000000 : ℝ)^6327 := by
    have hnat : (152964267 : ℕ)^8375*5000000000000^6327 ≤ 775907975871^6327*625000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      152964267 625000000 775907975871 5000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1252634659/2500000000 : ℝ)^8375 ≤ (10015655456289/25000000000000 : ℝ)^6327 := by
    have hnat : (1252634659 : ℕ)^8375*25000000000000^6327 ≤ 10015655456289^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252634659 2500000000 10015655456289 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5416926919/10000000000 : ℝ), (-152964267/625000000 : ℝ), (1252634659/2500000000 : ℝ)] ![(44419218640093/100000000000000 : ℝ), (775907975871/5000000000000 : ℝ), (10015655456289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5416926919/10000000000 : ℝ)|^8375 ≤ (44419218640093/100000000000000 : ℝ)^6327
        have hw : |(5416926919/10000000000 : ℝ)|=(5416926919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-152964267/625000000 : ℝ)|^8375 ≤ (775907975871/5000000000000 : ℝ)^6327
        have hw : |(-152964267/625000000 : ℝ)|=(152964267/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1252634659/2500000000 : ℝ)|^8375 ≤ (10015655456289/25000000000000 : ℝ)^6327
        have hw : |(1252634659/2500000000 : ℝ)|=(1252634659/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s1_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1354231529/2500000000 : ℝ)*x 0 + (250526959/500000000 : ℝ)*x 1 + (-19579429/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354231529/2500000000 : ℝ)^8375 ≤ (11104802481007/25000000000000 : ℝ)^6327 := by
    have hnat : (1354231529 : ℕ)^8375*25000000000000^6327 ≤ 11104802481007^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354231529 2500000000 11104802481007 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250526959/500000000 : ℝ)^8375 ≤ (40062627582747/100000000000000 : ℝ)^6327 := by
    have hnat : (250526959 : ℕ)^8375*100000000000000^6327 ≤ 40062627582747^6327*500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250526959 500000000 40062627582747 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19579429/80000000 : ℝ)^8375 ≤ (15518162480149/100000000000000 : ℝ)^6327 := by
    have hnat : (19579429 : ℕ)^8375*100000000000000^6327 ≤ 15518162480149^6327*80000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19579429 80000000 15518162480149 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354231529/2500000000 : ℝ), (250526959/500000000 : ℝ), (-19579429/80000000 : ℝ)] ![(11104802481007/25000000000000 : ℝ), (40062627582747/100000000000000 : ℝ), (15518162480149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354231529/2500000000 : ℝ)|^8375 ≤ (11104802481007/25000000000000 : ℝ)^6327
        have hw : |(1354231529/2500000000 : ℝ)|=(1354231529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(250526959/500000000 : ℝ)|^8375 ≤ (40062627582747/100000000000000 : ℝ)^6327
        have hw : |(250526959/500000000 : ℝ)|=(250526959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19579429/80000000 : ℝ)|^8375 ≤ (15518162480149/100000000000000 : ℝ)^6327
        have hw : |(-19579429/80000000 : ℝ)|=(19579429/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s1_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (269627053/625000000 : ℝ)*x 0 + (36845109/100000000 : ℝ)*x 1 + (2524389449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269627053/625000000 : ℝ)^8375 ≤ (6572462166947/20000000000000 : ℝ)^6327 := by
    have hnat : (269627053 : ℕ)^8375*20000000000000^6327 ≤ 6572462166947^6327*625000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269627053 625000000 6572462166947 20000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36845109/100000000 : ℝ)^8375 ≤ (6667460173983/25000000000000 : ℝ)^6327 := by
    have hnat : (36845109 : ℕ)^8375*25000000000000^6327 ≤ 6667460173983^6327*100000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36845109 100000000 6667460173983 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2524389449/5000000000 : ℝ)^8375 ≤ (20233924230817/50000000000000 : ℝ)^6327 := by
    have hnat : (2524389449 : ℕ)^8375*50000000000000^6327 ≤ 20233924230817^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2524389449 5000000000 20233924230817 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269627053/625000000 : ℝ), (36845109/100000000 : ℝ), (2524389449/5000000000 : ℝ)] ![(6572462166947/20000000000000 : ℝ), (6667460173983/25000000000000 : ℝ), (20233924230817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269627053/625000000 : ℝ)|^8375 ≤ (6572462166947/20000000000000 : ℝ)^6327
        have hw : |(269627053/625000000 : ℝ)|=(269627053/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36845109/100000000 : ℝ)|^8375 ≤ (6667460173983/25000000000000 : ℝ)^6327
        have hw : |(36845109/100000000 : ℝ)|=(36845109/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2524389449/5000000000 : ℝ)|^8375 ≤ (20233924230817/50000000000000 : ℝ)^6327
        have hw : |(2524389449/5000000000 : ℝ)|=(2524389449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s1_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2081742217/10000000000 : ℝ)*x 0 + (1003937501/2000000000 : ℝ)*x 1 + (284080539/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2081742217/10000000000 : ℝ)^8375 ≤ (6262923876213/50000000000000 : ℝ)^6327 := by
    have hnat : (2081742217 : ℕ)^8375*50000000000000^6327 ≤ 6262923876213^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081742217 10000000000 6262923876213 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003937501/2000000000 : ℝ)^8375 ≤ (20079740148521/50000000000000 : ℝ)^6327 := by
    have hnat : (1003937501 : ℕ)^8375*50000000000000^6327 ≤ 20079740148521^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003937501 2000000000 20079740148521 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284080539/500000000 : ℝ)^8375 ≤ (47314671932183/100000000000000 : ℝ)^6327 := by
    have hnat : (284080539 : ℕ)^8375*100000000000000^6327 ≤ 47314671932183^6327*500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284080539 500000000 47314671932183 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2081742217/10000000000 : ℝ), (1003937501/2000000000 : ℝ), (284080539/500000000 : ℝ)] ![(6262923876213/50000000000000 : ℝ), (20079740148521/50000000000000 : ℝ), (47314671932183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2081742217/10000000000 : ℝ)|^8375 ≤ (6262923876213/50000000000000 : ℝ)^6327
        have hw : |(-2081742217/10000000000 : ℝ)|=(2081742217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003937501/2000000000 : ℝ)|^8375 ≤ (20079740148521/50000000000000 : ℝ)^6327
        have hw : |(1003937501/2000000000 : ℝ)|=(1003937501/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(284080539/500000000 : ℝ)|^8375 ≤ (47314671932183/100000000000000 : ℝ)^6327
        have hw : |(284080539/500000000 : ℝ)|=(284080539/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s1_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1310534683/2500000000 : ℝ)*x 0 + (-222044331/1250000000 : ℝ)*x 1 + (2840806251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310534683/2500000000 : ℝ)^8375 ≤ (42531982570257/100000000000000 : ℝ)^6327 := by
    have hnat : (1310534683 : ℕ)^8375*100000000000000^6327 ≤ 42531982570257^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310534683 2500000000 42531982570257 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222044331/1250000000 : ℝ)^8375 ≤ (1015332649733/10000000000000 : ℝ)^6327 := by
    have hnat : (222044331 : ℕ)^8375*10000000000000^6327 ≤ 1015332649733^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222044331 1250000000 1015332649733 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2840806251/5000000000 : ℝ)^8375 ≤ (23657345457147/50000000000000 : ℝ)^6327 := by
    have hnat : (2840806251 : ℕ)^8375*50000000000000^6327 ≤ 23657345457147^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840806251 5000000000 23657345457147 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310534683/2500000000 : ℝ), (-222044331/1250000000 : ℝ), (2840806251/5000000000 : ℝ)] ![(42531982570257/100000000000000 : ℝ), (1015332649733/10000000000000 : ℝ), (23657345457147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310534683/2500000000 : ℝ)|^8375 ≤ (42531982570257/100000000000000 : ℝ)^6327
        have hw : |(1310534683/2500000000 : ℝ)|=(1310534683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222044331/1250000000 : ℝ)|^8375 ≤ (1015332649733/10000000000000 : ℝ)^6327
        have hw : |(-222044331/1250000000 : ℝ)|=(222044331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2840806251/5000000000 : ℝ)|^8375 ≤ (23657345457147/50000000000000 : ℝ)^6327
        have hw : |(2840806251/5000000000 : ℝ)|=(2840806251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s1_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1048427677/2000000000 : ℝ)*x 0 + (2840806711/5000000000 : ℝ)*x 1 + (-8881769/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048427677/2000000000 : ℝ)^8375 ≤ (10632994710891/25000000000000 : ℝ)^6327 := by
    have hnat : (1048427677 : ℕ)^8375*25000000000000^6327 ≤ 10632994710891^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048427677 2000000000 10632994710891 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2840806711/5000000000 : ℝ)^8375 ≤ (11828675263931/25000000000000 : ℝ)^6327 := by
    have hnat : (2840806711 : ℕ)^8375*25000000000000^6327 ≤ 11828675263931^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2840806711 5000000000 11828675263931 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8881769/50000000 : ℝ)^8375 ≤ (10153320081373/100000000000000 : ℝ)^6327 := by
    have hnat : (8881769 : ℕ)^8375*100000000000000^6327 ≤ 10153320081373^6327*50000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8881769 50000000 10153320081373 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048427677/2000000000 : ℝ), (2840806711/5000000000 : ℝ), (-8881769/50000000 : ℝ)] ![(10632994710891/25000000000000 : ℝ), (11828675263931/25000000000000 : ℝ), (10153320081373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048427677/2000000000 : ℝ)|^8375 ≤ (10632994710891/25000000000000 : ℝ)^6327
        have hw : |(1048427677/2000000000 : ℝ)|=(1048427677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2840806711/5000000000 : ℝ)|^8375 ≤ (11828675263931/25000000000000 : ℝ)^6327
        have hw : |(2840806711/5000000000 : ℝ)|=(2840806711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8881769/50000000 : ℝ)|^8375 ≤ (10153320081373/100000000000000 : ℝ)^6327
        have hw : |(-8881769/50000000 : ℝ)|=(8881769/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s1_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4315539217/10000000000 : ℝ)*x 0 + (5030434793/10000000000 : ℝ)*x 1 + (3703211497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315539217/10000000000 : ℝ)^8375 ≤ (8219375206667/25000000000000 : ℝ)^6327 := by
    have hnat : (4315539217 : ℕ)^8375*25000000000000^6327 ≤ 8219375206667^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315539217 10000000000 8219375206667 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5030434793/10000000000 : ℝ)^8375 ≤ (4027333413171/10000000000000 : ℝ)^6327 := by
    have hnat : (5030434793 : ℕ)^8375*10000000000000^6327 ≤ 4027333413171^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5030434793 10000000000 4027333413171 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3703211497/10000000000 : ℝ)^8375 ≤ (1342458251431/5000000000000 : ℝ)^6327 := by
    have hnat : (3703211497 : ℕ)^8375*5000000000000^6327 ≤ 1342458251431^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3703211497 10000000000 1342458251431 5000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315539217/10000000000 : ℝ), (5030434793/10000000000 : ℝ), (3703211497/10000000000 : ℝ)] ![(8219375206667/25000000000000 : ℝ), (4027333413171/10000000000000 : ℝ), (1342458251431/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315539217/10000000000 : ℝ)|^8375 ≤ (8219375206667/25000000000000 : ℝ)^6327
        have hw : |(4315539217/10000000000 : ℝ)|=(4315539217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5030434793/10000000000 : ℝ)|^8375 ≤ (4027333413171/10000000000000 : ℝ)^6327
        have hw : |(5030434793/10000000000 : ℝ)|=(5030434793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3703211497/10000000000 : ℝ)|^8375 ≤ (1342458251431/5000000000000 : ℝ)^6327
        have hw : |(3703211497/10000000000 : ℝ)|=(3703211497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13831/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (577/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5871/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10129/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13831/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (577/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13831/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (577/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13831/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (577/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13831/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (577/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13831/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (577/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13831/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (577/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (577/100000 : ℝ) ^ (4187/1024 : ℝ) ≤ (35052197349/50000000000000000000 : ℝ) := by
    have hpowers : (577/100000 : ℝ)^4187 ≤ (35052197349/50000000000000000000 : ℝ)^1024 := by
      have hnat : (577 : ℕ)^4187*50000000000000000000^1024 ≤ 35052197349^1024*100000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        577 100000 35052197349 50000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (577/100000 : ℝ)) (X := (35052197349/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13831/50000 : ℝ) ^ (4187/1024 : ℝ) ≤ (522319297078055663/100000000000000000000 : ℝ) := by
    have hpowers : (13831/50000 : ℝ)^4187 ≤ (522319297078055663/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13831 : ℕ)^4187*100000000000000000000^1024 ≤ 522319297078055663^1024*50000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13831 50000 522319297078055663 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13831/50000 : ℝ)) (X := (522319297078055663/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000035052197349/25000000000000000000 : ℝ) ≤ (5000000001714519/5000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (25000000035052197349/25000000000000000000 : ℝ)^1024 ≤ (5000000001714519/5000000000000000 : ℝ)^4187 := by
      have hnat : (25000000035052197349 : ℕ)^1024*5000000000000000^4187 ≤ 5000000001714519^4187*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000035052197349 25000000000000000000 5000000001714519 5000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000001714519/5000000000000000 : ℝ)) (X := (25000000035052197349/25000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100522319367182450361/100000000000000000000 : ℝ) ≤ (5006374528738747/5000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (100522319367182450361/100000000000000000000 : ℝ)^1024 ≤ (5006374528738747/5000000000000000 : ℝ)^4187 := by
      have hnat : (100522319367182450361 : ℕ)^1024*5000000000000000^4187 ≤ 5006374528738747^4187*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100522319367182450361 100000000000000000000 5006374528738747 5000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006374528738747/5000000000000000 : ℝ)) (X := (100522319367182450361/100000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50522319297078055663/50000000000000000000 : ℝ) ≤ (200509962230519/200000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50522319297078055663/50000000000000000000 : ℝ)^1024 ≤ (200509962230519/200000000000000 : ℝ)^4187 := by
      have hnat : (50522319297078055663 : ℕ)^1024*200000000000000^4187 ≤ 200509962230519^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50522319297078055663 50000000000000000000 200509962230519 200000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200509962230519/200000000000000 : ℝ)) (X := (50522319297078055663/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(35052197349/50000000000000000000 : ℝ) ≤ ((135417643842251788003/135425000000000000000 : ℝ)+2*(1593631756057/338562500000000 : ℝ)*(577/100000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (135417643842251788003/135425000000000000000 : ℝ)+2*(1593631756057/338562500000000 : ℝ)*(577/100000 : ℝ)=(5000000001714519/5000000000000000 : ℝ) by norm_num, show 1+2*(35052197349/50000000000000000000 : ℝ)=(25000000035052197349/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(522319297078055663/100000000000000000000 : ℝ)+(35052197349/50000000000000000000 : ℝ) ≤ ((135417643842251788003/135425000000000000000 : ℝ)+(1593631756057/338562500000000 : ℝ)*((13831/50000 : ℝ)+(577/100000 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (135417643842251788003/135425000000000000000 : ℝ)+(1593631756057/338562500000000 : ℝ)*((13831/50000 : ℝ)+(577/100000 : ℝ))=(5006374528738747/5000000000000000 : ℝ) by norm_num, show 1+(522319297078055663/100000000000000000000 : ℝ)+(35052197349/50000000000000000000 : ℝ)=(100522319367182450361/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(522319297078055663/100000000000000000000 : ℝ) ≤ ((135417643842251788003/135425000000000000000 : ℝ)+2*(1593631756057/338562500000000 : ℝ)*(13831/50000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (135417643842251788003/135425000000000000000 : ℝ)+2*(1593631756057/338562500000000 : ℝ)*(13831/50000 : ℝ)=(200509962230519/200000000000000 : ℝ) by norm_num, show 1+2*(522319297078055663/100000000000000000000 : ℝ)=(50522319297078055663/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (135417643842251788003/135425000000000000000 : ℝ)*(X 1 0+X 2 0)+(1593631756057/338562500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (577/100000 : ℝ)) (hi := (13831/50000 : ℝ)) (c := (135417643842251788003/135425000000000000000 : ℝ)) (alpha := (1593631756057/338562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (135417643842251788003/135425000000000000000 : ℝ)*(X 0 1+X 2 1)+(1593631756057/338562500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (577/100000 : ℝ)) (hi := (13831/50000 : ℝ)) (c := (135417643842251788003/135425000000000000000 : ℝ)) (alpha := (1593631756057/338562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (135417643842251788003/135425000000000000000 : ℝ)*(X 0 2+X 1 2)+(1593631756057/338562500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (577/100000 : ℝ)) (hi := (13831/50000 : ℝ)) (c := (135417643842251788003/135425000000000000000 : ℝ)) (alpha := (1593631756057/338562500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416197903/2000000000 : ℝ)*X 0 0+(5690939031/10000000000 : ℝ)*X 0 1+(5010538427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5416926919/10000000000 : ℝ)*X 1 0+(-152964267/625000000 : ℝ)*X 1 1+(1252634659/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1354231529/2500000000 : ℝ)*X 2 0+(250526959/500000000 : ℝ)*X 2 1+(-19579429/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269627053/625000000 : ℝ)*X 0 0+(36845109/100000000 : ℝ)*X 0 1+(2524389449/5000000000 : ℝ)*X 0 2+(269627053/625000000 : ℝ)*X 1 0+(36845109/100000000 : ℝ)*X 1 1+(2524389449/5000000000 : ℝ)*X 1 2+(269627053/625000000 : ℝ)*X 2 0+(36845109/100000000 : ℝ)*X 2 1+(2524389449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2081742217/10000000000 : ℝ)*X 0 0+(1003937501/2000000000 : ℝ)*X 0 1+(284080539/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1310534683/2500000000 : ℝ)*X 1 0+(-222044331/1250000000 : ℝ)*X 1 1+(2840806251/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1048427677/2000000000 : ℝ)*X 2 0+(2840806711/5000000000 : ℝ)*X 2 1+(-8881769/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4315539217/10000000000 : ℝ)*X 0 0+(5030434793/10000000000 : ℝ)*X 0 1+(3703211497/10000000000 : ℝ)*X 0 2+(4315539217/10000000000 : ℝ)*X 1 0+(5030434793/10000000000 : ℝ)*X 1 1+(3703211497/10000000000 : ℝ)*X 1 2+(4315539217/10000000000 : ℝ)*X 2 0+(5030434793/10000000000 : ℝ)*X 2 1+(3703211497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1005004421774247818290405077/423203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5880853/100000000000000 : ℝ)*(base16) + (344004943/50000000000000 : ℝ)*(base19) + (99272851/20000000000000 : ℝ)*(base23) + (1377587/12500000000000 : ℝ)*(upper2) + (76110243/50000000000000 : ℝ)*(upper3) + (68835284066461/6250000000000 : ℝ)*(major0) + (68835284066461/6250000000000 : ℝ)*(major1) + (68835284066461/6250000000000 : ℝ)*(major2) + (734863804929177/50000000000000 : ℝ)*(sp0) + (367432544217487/25000000000000 : ℝ)*(sp1) + (91858148399777/6250000000000 : ℝ)*(sp2) + (732995731117311/100000000000000 : ℝ)*(sp3) + (1630451167/50000000000000 : ℝ)*(sp4) + (2409090191/100000000000000 : ℝ)*(sp7) + (366499070103751/50000000000000 : ℝ)*(f.failure) + (91858179422543/6250000000000 : ℝ)*(f.sum) + (202910434962981/135425000000000000000000000000 : ℝ)*base65 + (2698227317689173633/846406250000000000000000000000000 : ℝ)*base67 + (2489906020168951367/846406250000000000000000000000000 : ℝ)*base70 + (6022127820273548633/846406250000000000000000000000000 : ℝ)*base71 + (366155723588019/135425000000000000000000000000 : ℝ)*base74 + (7772108506198236133/846406250000000000000000000000000 : ℝ)*base75 + (7922574014914173633/846406250000000000000000000000000 : ℝ)*base77 + (8434276669818548633/846406250000000000000000000000000 : ℝ)*base79 + (765460087089669/135425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (9121497/5000000000000000000000 : ℝ)*base90 + (9121497/5000000000000000000000 : ℝ)*base92 + (9121497/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1114267845318722372036398749/423203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (388950281/25000000000000 : ℝ)*(base19) + (409965399/20000000000000 : ℝ)*(base23) + (113178469/50000000000000 : ℝ)*(upper2) + (9252473/2500000000000 : ℝ)*(upper3) + (16628941/10000000000000 : ℝ)*(upper5) + (35378111732831/3125000000000 : ℝ)*(major0) + (35378111732831/3125000000000 : ℝ)*(major1) + (35378111732831/3125000000000 : ℝ)*(major2) + (8373246533/100000000000000 : ℝ)*(sp1) + (1654832527/12500000000000 : ℝ)*(sp2) + (755372821481913/50000000000000 : ℝ)*(sp4) + (151073571391617/10000000000000 : ℝ)*(sp5) + (302146070895323/20000000000000 : ℝ)*(sp6) + (753453420172733/100000000000000 : ℝ)*(sp7) + (753453420172733/100000000000000 : ℝ)*(f.failure) + (755372821481913/50000000000000 : ℝ)*(f.sum) + (621852046997877/135425000000000000000000000000 : ℝ)*base65 + (1255860092894922691/211601562500000000000000000000000 : ℝ)*base68 + (341047226914141033/105800781250000000000000000000000 : ℝ)*base70 + (2542230985039298507/423203125000000000000000000000000 : ℝ)*base72 + (430424433374427/135425000000000000000000000000 : ℝ)*base73 + (790685951797266033/105800781250000000000000000000000 : ℝ)*base76 + (336390312241486007/423203125000000000000000000000000 : ℝ)*base78 + (833756297260547691/211601562500000000000000000000000 : ℝ)*base80 + (265614758698027/135425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (14249949/10000000000000000000000 : ℝ)*base89 + (14249949/10000000000000000000000 : ℝ)*base91 + (14249949/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1182_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13831/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (577/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10129/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1182_s2_0 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-213209709/1000000000 : ℝ)*x 0 + (5503353983/10000000000 : ℝ)*x 1 + (2582793549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213209709/1000000000 : ℝ)^8375 ≤ (6464234368689/50000000000000 : ℝ)^6327 := by
    have hnat : (213209709 : ℕ)^8375*50000000000000^6327 ≤ 6464234368689^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213209709 1000000000 6464234368689 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503353983/10000000000 : ℝ)^8375 ≤ (45359744402219/100000000000000 : ℝ)^6327 := by
    have hnat : (5503353983 : ℕ)^8375*100000000000000^6327 ≤ 45359744402219^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503353983 10000000000 45359744402219 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582793549/5000000000 : ℝ)^8375 ≤ (20855893420797/50000000000000 : ℝ)^6327 := by
    have hnat : (2582793549 : ℕ)^8375*50000000000000^6327 ≤ 20855893420797^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582793549 5000000000 20855893420797 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213209709/1000000000 : ℝ), (5503353983/10000000000 : ℝ), (2582793549/5000000000 : ℝ)] ![(6464234368689/50000000000000 : ℝ), (45359744402219/100000000000000 : ℝ), (20855893420797/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213209709/1000000000 : ℝ)|^8375 ≤ (6464234368689/50000000000000 : ℝ)^6327
        have hw : |(-213209709/1000000000 : ℝ)|=(213209709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503353983/10000000000 : ℝ)|^8375 ≤ (45359744402219/100000000000000 : ℝ)^6327
        have hw : |(5503353983/10000000000 : ℝ)|=(5503353983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2582793549/5000000000 : ℝ)|^8375 ≤ (20855893420797/50000000000000 : ℝ)^6327
        have hw : |(2582793549/5000000000 : ℝ)|=(2582793549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s2_1 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1343040479/2500000000 : ℝ)*x 0 + (-288429143/1250000000 : ℝ)*x 1 + (5165590639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343040479/2500000000 : ℝ)^8375 ≤ (21966986746597/50000000000000 : ℝ)^6327 := by
    have hnat : (1343040479 : ℕ)^8375*50000000000000^6327 ≤ 21966986746597^6327*2500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343040479 2500000000 21966986746597 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288429143/1250000000 : ℝ)^8375 ≤ (14354201806539/100000000000000 : ℝ)^6327 := by
    have hnat : (288429143 : ℕ)^8375*100000000000000^6327 ≤ 14354201806539^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288429143 1250000000 14354201806539 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5165590639/10000000000 : ℝ)^8375 ≤ (41711824690389/100000000000000 : ℝ)^6327 := by
    have hnat : (5165590639 : ℕ)^8375*100000000000000^6327 ≤ 41711824690389^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5165590639 10000000000 41711824690389 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343040479/2500000000 : ℝ), (-288429143/1250000000 : ℝ), (5165590639/10000000000 : ℝ)] ![(21966986746597/50000000000000 : ℝ), (14354201806539/100000000000000 : ℝ), (41711824690389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343040479/2500000000 : ℝ)|^8375 ≤ (21966986746597/50000000000000 : ℝ)^6327
        have hw : |(1343040479/2500000000 : ℝ)|=(1343040479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-288429143/1250000000 : ℝ)|^8375 ≤ (14354201806539/100000000000000 : ℝ)^6327
        have hw : |(-288429143/1250000000 : ℝ)|=(288429143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5165590639/10000000000 : ℝ)|^8375 ≤ (41711824690389/100000000000000 : ℝ)^6327
        have hw : |(5165590639/10000000000 : ℝ)|=(5165590639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s2_2 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2686081561/5000000000 : ℝ)*x 0 + (1033117779/2000000000 : ℝ)*x 1 + (-1153716911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686081561/5000000000 : ℝ)^8375 ≤ (43933986548459/100000000000000 : ℝ)^6327 := by
    have hnat : (2686081561 : ℕ)^8375*100000000000000^6327 ≤ 43933986548459^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686081561 5000000000 43933986548459 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1033117779/2000000000 : ℝ)^8375 ≤ (20855903024621/50000000000000 : ℝ)^6327 := by
    have hnat : (1033117779 : ℕ)^8375*50000000000000^6327 ≤ 20855903024621^6327*2000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033117779 2000000000 20855903024621 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153716911/5000000000 : ℝ)^8375 ≤ (7177103694763/50000000000000 : ℝ)^6327 := by
    have hnat : (1153716911 : ℕ)^8375*50000000000000^6327 ≤ 7177103694763^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153716911 5000000000 7177103694763 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686081561/5000000000 : ℝ), (1033117779/2000000000 : ℝ), (-1153716911/5000000000 : ℝ)] ![(43933986548459/100000000000000 : ℝ), (20855903024621/50000000000000 : ℝ), (7177103694763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686081561/5000000000 : ℝ)|^8375 ≤ (43933986548459/100000000000000 : ℝ)^6327
        have hw : |(2686081561/5000000000 : ℝ)|=(2686081561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1033117779/2000000000 : ℝ)|^8375 ≤ (20855903024621/50000000000000 : ℝ)^6327
        have hw : |(1033117779/2000000000 : ℝ)|=(1033117779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1153716911/5000000000 : ℝ)|^8375 ≤ (7177103694763/50000000000000 : ℝ)^6327
        have hw : |(-1153716911/5000000000 : ℝ)|=(1153716911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s2_3 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349195129/10000000000 : ℝ)*x 0 + (201175727/500000000 : ℝ)*x 1 + (4700764773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349195129/10000000000 : ℝ)^8375 ≤ (33217328651947/100000000000000 : ℝ)^6327 := by
    have hnat : (4349195129 : ℕ)^8375*100000000000000^6327 ≤ 33217328651947^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349195129 10000000000 33217328651947 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201175727/500000000 : ℝ)^8375 ≤ (29965361279781/100000000000000 : ℝ)^6327 := by
    have hnat : (201175727 : ℕ)^8375*100000000000000^6327 ≤ 29965361279781^6327*500000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201175727 500000000 29965361279781 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4700764773/10000000000 : ℝ)^8375 ≤ (4602163756731/12500000000000 : ℝ)^6327 := by
    have hnat : (4700764773 : ℕ)^8375*12500000000000^6327 ≤ 4602163756731^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4700764773 10000000000 4602163756731 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349195129/10000000000 : ℝ), (201175727/500000000 : ℝ), (4700764773/10000000000 : ℝ)] ![(33217328651947/100000000000000 : ℝ), (29965361279781/100000000000000 : ℝ), (4602163756731/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349195129/10000000000 : ℝ)|^8375 ≤ (33217328651947/100000000000000 : ℝ)^6327
        have hw : |(4349195129/10000000000 : ℝ)|=(4349195129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201175727/500000000 : ℝ)|^8375 ≤ (29965361279781/100000000000000 : ℝ)^6327
        have hw : |(201175727/500000000 : ℝ)|=(201175727/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4700764773/10000000000 : ℝ)|^8375 ≤ (4602163756731/12500000000000 : ℝ)^6327
        have hw : |(4700764773/10000000000 : ℝ)|=(4700764773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s2_4 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2132188303/10000000000 : ℝ)*x 0 + (5167852617/10000000000 : ℝ)*x 1 + (5501067023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2132188303/10000000000 : ℝ)^8375 ≤ (323230021627/2500000000000 : ℝ)^6327 := by
    have hnat : (2132188303 : ℕ)^8375*2500000000000^6327 ≤ 323230021627^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132188303 10000000000 323230021627 2500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5167852617/10000000000 : ℝ)^8375 ≤ (1304250127503/3125000000000 : ℝ)^6327 := by
    have hnat : (5167852617 : ℕ)^8375*3125000000000^6327 ≤ 1304250127503^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5167852617 10000000000 1304250127503 3125000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501067023/10000000000 : ℝ)^8375 ≤ (45334795037731/100000000000000 : ℝ)^6327 := by
    have hnat : (5501067023 : ℕ)^8375*100000000000000^6327 ≤ 45334795037731^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501067023 10000000000 45334795037731 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2132188303/10000000000 : ℝ), (5167852617/10000000000 : ℝ), (5501067023/10000000000 : ℝ)] ![(323230021627/2500000000000 : ℝ), (1304250127503/3125000000000 : ℝ), (45334795037731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2132188303/10000000000 : ℝ)|^8375 ≤ (323230021627/2500000000000 : ℝ)^6327
        have hw : |(-2132188303/10000000000 : ℝ)|=(2132188303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5167852617/10000000000 : ℝ)|^8375 ≤ (1304250127503/3125000000000 : ℝ)^6327
        have hw : |(5167852617/10000000000 : ℝ)|=(5167852617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501067023/10000000000 : ℝ)|^8375 ≤ (45334795037731/100000000000000 : ℝ)^6327
        have hw : |(5501067023/10000000000 : ℝ)|=(5501067023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s2_5 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2643117921/5000000000 : ℝ)*x 0 + (-985977661/5000000000 : ℝ)*x 1 + (550106703/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643117921/5000000000 : ℝ)^8375 ≤ (4300621798317/10000000000000 : ℝ)^6327 := by
    have hnat : (2643117921 : ℕ)^8375*10000000000000^6327 ≤ 4300621798317^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643117921 5000000000 4300621798317 10000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985977661/5000000000 : ℝ)^8375 ≤ (11658986890131/100000000000000 : ℝ)^6327 := by
    have hnat : (985977661 : ℕ)^8375*100000000000000^6327 ≤ 11658986890131^6327*5000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985977661 5000000000 11658986890131 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550106703/1000000000 : ℝ)^8375 ≤ (11333698778523/25000000000000 : ℝ)^6327 := by
    have hnat : (550106703 : ℕ)^8375*25000000000000^6327 ≤ 11333698778523^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550106703 1000000000 11333698778523 25000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643117921/5000000000 : ℝ), (-985977661/5000000000 : ℝ), (550106703/1000000000 : ℝ)] ![(4300621798317/10000000000000 : ℝ), (11658986890131/100000000000000 : ℝ), (11333698778523/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643117921/5000000000 : ℝ)|^8375 ≤ (4300621798317/10000000000000 : ℝ)^6327
        have hw : |(2643117921/5000000000 : ℝ)|=(2643117921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-985977661/5000000000 : ℝ)|^8375 ≤ (11658986890131/100000000000000 : ℝ)^6327
        have hw : |(-985977661/5000000000 : ℝ)|=(985977661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550106703/1000000000 : ℝ)|^8375 ≤ (11333698778523/25000000000000 : ℝ)^6327
        have hw : |(550106703/1000000000 : ℝ)|=(550106703/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s2_6 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5286235993/10000000000 : ℝ)*x 0 + (5501067033/10000000000 : ℝ)*x 1 + (-197195511/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286235993/10000000000 : ℝ)^8375 ≤ (1720248784371/4000000000000 : ℝ)^6327 := by
    have hnat : (5286235993 : ℕ)^8375*4000000000000^6327 ≤ 1720248784371^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286235993 10000000000 1720248784371 4000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501067033/10000000000 : ℝ)^8375 ≤ (22667397573409/50000000000000 : ℝ)^6327 := by
    have hnat : (5501067033 : ℕ)^8375*50000000000000^6327 ≤ 22667397573409^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501067033 10000000000 22667397573409 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197195511/1000000000 : ℝ)^8375 ≤ (5829492615489/50000000000000 : ℝ)^6327 := by
    have hnat : (197195511 : ℕ)^8375*50000000000000^6327 ≤ 5829492615489^6327*1000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197195511 1000000000 5829492615489 50000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286235993/10000000000 : ℝ), (5501067033/10000000000 : ℝ), (-197195511/1000000000 : ℝ)] ![(1720248784371/4000000000000 : ℝ), (22667397573409/50000000000000 : ℝ), (5829492615489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286235993/10000000000 : ℝ)|^8375 ≤ (1720248784371/4000000000000 : ℝ)^6327
        have hw : |(5286235993/10000000000 : ℝ)|=(5286235993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501067033/10000000000 : ℝ)|^8375 ≤ (22667397573409/50000000000000 : ℝ)^6327
        have hw : |(5501067033/10000000000 : ℝ)|=(5501067033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197195511/1000000000 : ℝ)|^8375 ≤ (5829492615489/50000000000000 : ℝ)^6327
        have hw : |(-197195511/1000000000 : ℝ)|=(197195511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1182_s2_7 (p : ℝ) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (173975199/400000000 : ℝ)*x 0 + (587028101/1250000000 : ℝ)*x 1 + (4028097821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173975199/400000000 : ℝ)^8375 ≤ (33219197421871/100000000000000 : ℝ)^6327 := by
    have hnat : (173975199 : ℕ)^8375*100000000000000^6327 ≤ 33219197421871^6327*400000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173975199 400000000 33219197421871 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (587028101/1250000000 : ℝ)^8375 ≤ (4596281213469/12500000000000 : ℝ)^6327 := by
    have hnat : (587028101 : ℕ)^8375*12500000000000^6327 ≤ 4596281213469^6327*1250000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587028101 1250000000 4596281213469 12500000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4028097821/10000000000 : ℝ)^8375 ≤ (30010552851783/100000000000000 : ℝ)^6327 := by
    have hnat : (4028097821 : ℕ)^8375*100000000000000^6327 ≤ 30010552851783^6327*10000000000^8375 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028097821 10000000000 30010552851783 100000000000000 8375 6327 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8375/2048 : ℝ)) 8375 6327 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173975199/400000000 : ℝ), (587028101/1250000000 : ℝ), (4028097821/10000000000 : ℝ)] ![(33219197421871/100000000000000 : ℝ), (4596281213469/12500000000000 : ℝ), (30010552851783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173975199/400000000 : ℝ)|^8375 ≤ (33219197421871/100000000000000 : ℝ)^6327
        have hw : |(173975199/400000000 : ℝ)|=(173975199/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(587028101/1250000000 : ℝ)|^8375 ≤ (4596281213469/12500000000000 : ℝ)^6327
        have hw : |(587028101/1250000000 : ℝ)|=(587028101/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4028097821/10000000000 : ℝ)|^8375 ≤ (30010552851783/100000000000000 : ℝ)^6327
        have hw : |(4028097821/10000000000 : ℝ)|=(4028097821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1182_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (289/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8193/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5871/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10129/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5871/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5871/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10129/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5871/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5871/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10129/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5871/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5871/100000 : ℝ) ^ (4187/1024 : ℝ) ≤ (923479431870193/100000000000000000000 : ℝ) := by
    have hpowers : (5871/100000 : ℝ)^4187 ≤ (923479431870193/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5871 : ℕ)^4187*100000000000000000000^1024 ≤ 923479431870193^1024*100000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5871 100000 923479431870193 100000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5871/100000 : ℝ)) (X := (923479431870193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10129/50000 : ℝ) ^ (4187/1024 : ℝ) ≤ (73069386103867277/50000000000000000000 : ℝ) := by
    have hpowers : (10129/50000 : ℝ)^4187 ≤ (73069386103867277/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10129 : ℕ)^4187*50000000000000000000^1024 ≤ 73069386103867277^1024*50000^4187 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10129 50000 73069386103867277 50000000000000000000 4187 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10129/50000 : ℝ)) (X := (73069386103867277/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000923479431870193/50000000000000000000 : ℝ) ≤ (10000045170114223/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (50000923479431870193/50000000000000000000 : ℝ)^1024 ≤ (10000045170114223/10000000000000000 : ℝ)^4187 := by
      have hnat : (50000923479431870193 : ℕ)^1024*10000000000000000^4187 ≤ 10000045170114223^4187*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000923479431870193 50000000000000000000 10000045170114223 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000045170114223/10000000000000000 : ℝ)) (X := (50000923479431870193/50000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100147062251639604747/100000000000000000000 : ℝ) ≤ (10003594654097817/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (100147062251639604747/100000000000000000000 : ℝ)^1024 ≤ (10003594654097817/10000000000000000 : ℝ)^4187 := by
      have hnat : (100147062251639604747 : ℕ)^1024*10000000000000000^4187 ≤ 10003594654097817^4187*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100147062251639604747 100000000000000000000 10003594654097817 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003594654097817/10000000000000000 : ℝ)) (X := (100147062251639604747/100000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25073069386103867277/25000000000000000000 : ℝ) ≤ (10007144138081411/10000000000000000 : ℝ) ^ (4187/1024 : ℝ) := by
    have hpowers : (25073069386103867277/25000000000000000000 : ℝ)^1024 ≤ (10007144138081411/10000000000000000 : ℝ)^4187 := by
      have hnat : (25073069386103867277 : ℕ)^1024*10000000000000000^4187 ≤ 10007144138081411^4187*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25073069386103867277 25000000000000000000 10007144138081411 10000000000000000 1024 4187 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007144138081411/10000000000000000 : ℝ)) (X := (25073069386103867277/25000000000000000000 : ℝ)) (by norm_num) 4187 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(923479431870193/100000000000000000000 : ℝ) ≤ ((143828971821497965553/143870000000000000000 : ℝ)+2*(1774741991797/719350000000000 : ℝ)*(5871/100000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (143828971821497965553/143870000000000000000 : ℝ)+2*(1774741991797/719350000000000 : ℝ)*(5871/100000 : ℝ)=(10000045170114223/10000000000000000 : ℝ) by norm_num, show 1+2*(923479431870193/100000000000000000000 : ℝ)=(50000923479431870193/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(73069386103867277/50000000000000000000 : ℝ)+(923479431870193/100000000000000000000 : ℝ) ≤ ((143828971821497965553/143870000000000000000 : ℝ)+(1774741991797/719350000000000 : ℝ)*((10129/50000 : ℝ)+(5871/100000 : ℝ)))^(4187/1024 : ℝ) := by
    rw [show (143828971821497965553/143870000000000000000 : ℝ)+(1774741991797/719350000000000 : ℝ)*((10129/50000 : ℝ)+(5871/100000 : ℝ))=(10003594654097817/10000000000000000 : ℝ) by norm_num, show 1+(73069386103867277/50000000000000000000 : ℝ)+(923479431870193/100000000000000000000 : ℝ)=(100147062251639604747/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(73069386103867277/50000000000000000000 : ℝ) ≤ ((143828971821497965553/143870000000000000000 : ℝ)+2*(1774741991797/719350000000000 : ℝ)*(10129/50000 : ℝ))^(4187/1024 : ℝ) := by
    rw [show (143828971821497965553/143870000000000000000 : ℝ)+2*(1774741991797/719350000000000 : ℝ)*(10129/50000 : ℝ)=(10007144138081411/10000000000000000 : ℝ) by norm_num, show 1+2*(73069386103867277/50000000000000000000 : ℝ)=(25073069386103867277/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (143828971821497965553/143870000000000000000 : ℝ)*(X 1 0+X 2 0)+(1774741991797/719350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (5871/100000 : ℝ)) (hi := (10129/50000 : ℝ)) (c := (143828971821497965553/143870000000000000000 : ℝ)) (alpha := (1774741991797/719350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (143828971821497965553/143870000000000000000 : ℝ)*(X 0 1+X 2 1)+(1774741991797/719350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (5871/100000 : ℝ)) (hi := (10129/50000 : ℝ)) (c := (143828971821497965553/143870000000000000000 : ℝ)) (alpha := (1774741991797/719350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (143828971821497965553/143870000000000000000 : ℝ)*(X 0 2+X 1 2)+(1774741991797/719350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4187/1024 : ℝ)) (lo := (5871/100000 : ℝ)) (hi := (10129/50000 : ℝ)) (c := (143828971821497965553/143870000000000000000 : ℝ)) (alpha := (1774741991797/719350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213209709/1000000000 : ℝ)*X 0 0+(5503353983/10000000000 : ℝ)*X 0 1+(2582793549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343040479/2500000000 : ℝ)*X 1 0+(-288429143/1250000000 : ℝ)*X 1 1+(5165590639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686081561/5000000000 : ℝ)*X 2 0+(1033117779/2000000000 : ℝ)*X 2 1+(-1153716911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349195129/10000000000 : ℝ)*X 0 0+(201175727/500000000 : ℝ)*X 0 1+(4700764773/10000000000 : ℝ)*X 0 2+(4349195129/10000000000 : ℝ)*X 1 0+(201175727/500000000 : ℝ)*X 1 1+(4700764773/10000000000 : ℝ)*X 1 2+(4349195129/10000000000 : ℝ)*X 2 0+(201175727/500000000 : ℝ)*X 2 1+(4700764773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2132188303/10000000000 : ℝ)*X 0 0+(5167852617/10000000000 : ℝ)*X 0 1+(5501067023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643117921/5000000000 : ℝ)*X 1 0+(-985977661/5000000000 : ℝ)*X 1 1+(550106703/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5286235993/10000000000 : ℝ)*X 2 0+(5501067033/10000000000 : ℝ)*X 2 1+(-197195511/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173975199/400000000 : ℝ)*X 0 0+(587028101/1250000000 : ℝ)*X 0 1+(4028097821/10000000000 : ℝ)*X 0 2+(173975199/400000000 : ℝ)*X 1 0+(587028101/1250000000 : ℝ)*X 1 1+(4028097821/10000000000 : ℝ)*X 1 2+(173975199/400000000 : ℝ)*X 2 0+(587028101/1250000000 : ℝ)*X 2 1+(4028097821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1182_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (171005651753995377736107/71935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2241111/1250000000000 : ℝ)*(base23) + (5240329/10000000000000 : ℝ)*(upper2) + (289365041/100000000000000 : ℝ)*(upper3) + (136490711/50000000000000 : ℝ)*(upper4) + (1109309835655981/50000000000000 : ℝ)*(major0) + (1109309835655981/50000000000000 : ℝ)*(major1) + (1109309835655981/50000000000000 : ℝ)*(major2) + (92520143719823/3125000000000 : ℝ)*(sp0) + (1480333611777103/50000000000000 : ℝ)*(sp1) + (1480331185185989/50000000000000 : ℝ)*(sp2) + (738281699184837/50000000000000 : ℝ)*(sp3) + (22624519869/100000000000000 : ℝ)*(sp4) + (1168473337/25000000000000 : ℝ)*(sp6) + (4320729609/50000000000000 : ℝ)*(sp7) + (1476572039828891/100000000000000 : ℝ)*(f.failure) + (1480333611777103/50000000000000 : ℝ)*(f.sum) + (290098124684887/71935000000000000000000000000 : ℝ)*base66 + (32223859609440322493/7193500000000000000000000000000000 : ℝ)*base67 + (27271945351085322493/7193500000000000000000000000000000 : ℝ)*base69 + (18270997211115822493/7193500000000000000000000000000000 : ℝ)*base71 + (75024874714993/17983750000000000000000000000 : ℝ)*base74 + (8392713471041177507/7193500000000000000000000000000000 : ℝ)*base76 + (22299272280988177507/7193500000000000000000000000000000 : ℝ)*base78 + (73213236111495177507/7193500000000000000000000000000000 : ℝ)*base80 + (100095541215153/17983750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (20531077/10000000000000000000000 : ℝ)*base90 + (20531077/10000000000000000000000 : ℝ)*base92 + (20531077/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33679690167616434655817159511/7193500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (240359193/20000000000000 : ℝ)*(base19) + (138021331/10000000000000 : ℝ)*(base23) + (839139/4000000000000 : ℝ)*(upper2) + (38654093/25000000000000 : ℝ)*(upper3) + (100606141/100000000000000 : ℝ)*(upper5) + (2248896110520371/100000000000000 : ℝ)*(major0) + (2248896110520371/100000000000000 : ℝ)*(major1) + (2248896110520371/100000000000000 : ℝ)*(major2) + (11570540739/100000000000000 : ℝ)*(sp1) + (7415709141/50000000000000 : ℝ)*(sp2) + (1500534977140439/50000000000000 : ℝ)*(sp4) + (1500528590972087/50000000000000 : ℝ)*(sp5) + (1500526871324643/50000000000000 : ℝ)*(sp6) + (374180527673619/25000000000000 : ℝ)*(sp7) + (374180527673619/25000000000000 : ℝ)*(f.failure) + (1500534977140439/50000000000000 : ℝ)*(f.sum) + (1087789736987/561992187500000000000000000 : ℝ)*base66 + (83426095824742180163/14387000000000000000000000000000000 : ℝ)*base67 + (86198403738870180163/14387000000000000000000000000000000 : ℝ)*base69 + (1288120316116180163/14387000000000000000000000000000000 : ℝ)*base71 + (128441347670517/35967500000000000000000000000 : ℝ)*base73 + (69083929307718819837/14387000000000000000000000000000000 : ℝ)*base76 + (103122658918726180163/14387000000000000000000000000000000 : ℝ)*base77 + (91655192925731819837/14387000000000000000000000000000000 : ℝ)*base80 + (18598769080523/35967500000000000000000000000 : ℝ)*base82 + (12461107/2500000000000000000000 : ℝ)*base89 + (12461107/2500000000000000000000 : ℝ)*base91 + (12461107/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1182_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10129/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5871/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (289/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1182_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1182_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (289/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1182_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1182_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1182_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4187/1024 : ℝ) ≤ p) (hpb : p ≤ (8375/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150254753/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (289/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8193/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1182_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
