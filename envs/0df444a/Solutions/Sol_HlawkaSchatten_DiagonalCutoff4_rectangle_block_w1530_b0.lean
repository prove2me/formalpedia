-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1530_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:52.726994+00:00
-- url     : https://prove2.me/submissions/c20da1ad-649a-42eb-92fa-98a0b17e7872

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
theorem support_rectangle_w1530_s0_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-416727127/2500000000 : ℝ)*x 0 + (294955179/500000000 : ℝ)*x 1 + (4862941463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416727127/2500000000 : ℝ)^4557 ≤ (9917260205111/100000000000000 : ℝ)^3533 := by
    have hnat : (416727127 : ℕ)^4557*100000000000000^3533 ≤ 9917260205111^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416727127 2500000000 9917260205111 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294955179/500000000 : ℝ)^4557 ≤ (50623357859283/100000000000000 : ℝ)^3533 := by
    have hnat : (294955179 : ℕ)^4557*100000000000000^3533 ≤ 50623357859283^3533*500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294955179 500000000 50623357859283 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4862941463/10000000000 : ℝ)^4557 ≤ (39459381929999/100000000000000 : ℝ)^3533 := by
    have hnat : (4862941463 : ℕ)^4557*100000000000000^3533 ≤ 39459381929999^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4862941463 10000000000 39459381929999 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416727127/2500000000 : ℝ), (294955179/500000000 : ℝ), (4862941463/10000000000 : ℝ)] ![(9917260205111/100000000000000 : ℝ), (50623357859283/100000000000000 : ℝ), (39459381929999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416727127/2500000000 : ℝ)|^4557 ≤ (9917260205111/100000000000000 : ℝ)^3533
        have hw : |(-416727127/2500000000 : ℝ)|=(416727127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(294955179/500000000 : ℝ)|^4557 ≤ (50623357859283/100000000000000 : ℝ)^3533
        have hw : |(294955179/500000000 : ℝ)|=(294955179/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4862941463/10000000000 : ℝ)|^4557 ≤ (39459381929999/100000000000000 : ℝ)^3533
        have hw : |(4862941463/10000000000 : ℝ)|=(4862941463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s0_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2737036971/5000000000 : ℝ)*x 0 + (-561591351/2500000000 : ℝ)*x 1 + (2431470749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2737036971/5000000000 : ℝ)^4557 ≤ (45968779229759/100000000000000 : ℝ)^3533 := by
    have hnat : (2737036971 : ℕ)^4557*100000000000000^3533 ≤ 45968779229759^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737036971 5000000000 45968779229759 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561591351/2500000000 : ℝ)^4557 ≤ (14571838459759/100000000000000 : ℝ)^3533 := by
    have hnat : (561591351 : ℕ)^4557*100000000000000^3533 ≤ 14571838459759^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561591351 2500000000 14571838459759 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2431470749/5000000000 : ℝ)^4557 ≤ (19729691148157/50000000000000 : ℝ)^3533 := by
    have hnat : (2431470749 : ℕ)^4557*50000000000000^3533 ≤ 19729691148157^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2431470749 5000000000 19729691148157 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2737036971/5000000000 : ℝ), (-561591351/2500000000 : ℝ), (2431470749/5000000000 : ℝ)] ![(45968779229759/100000000000000 : ℝ), (14571838459759/100000000000000 : ℝ), (19729691148157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2737036971/5000000000 : ℝ)|^4557 ≤ (45968779229759/100000000000000 : ℝ)^3533
        have hw : |(2737036971/5000000000 : ℝ)|=(2737036971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-561591351/2500000000 : ℝ)|^4557 ≤ (14571838459759/100000000000000 : ℝ)^3533
        have hw : |(-561591351/2500000000 : ℝ)|=(561591351/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2431470749/5000000000 : ℝ)|^4557 ≤ (19729691148157/50000000000000 : ℝ)^3533
        have hw : |(2431470749/5000000000 : ℝ)|=(2431470749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s0_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2737036957/5000000000 : ℝ)*x 0 + (972588297/2000000000 : ℝ)*x 1 + (-1123182729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2737036957/5000000000 : ℝ)^4557 ≤ (22984389463239/50000000000000 : ℝ)^3533 := by
    have hnat : (2737036957 : ℕ)^4557*50000000000000^3533 ≤ 22984389463239^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737036957 5000000000 22984389463239 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972588297/2000000000 : ℝ)^4557 ≤ (19729691080127/50000000000000 : ℝ)^3533 := by
    have hnat : (972588297 : ℕ)^4557*50000000000000^3533 ≤ 19729691080127^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972588297 2000000000 19729691080127 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123182729/5000000000 : ℝ)^4557 ≤ (1821479863947/12500000000000 : ℝ)^3533 := by
    have hnat : (1123182729 : ℕ)^4557*12500000000000^3533 ≤ 1821479863947^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123182729 5000000000 1821479863947 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2737036957/5000000000 : ℝ), (972588297/2000000000 : ℝ), (-1123182729/5000000000 : ℝ)] ![(22984389463239/50000000000000 : ℝ), (19729691080127/50000000000000 : ℝ), (1821479863947/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2737036957/5000000000 : ℝ)|^4557 ≤ (22984389463239/50000000000000 : ℝ)^3533
        have hw : |(2737036957/5000000000 : ℝ)|=(2737036957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(972588297/2000000000 : ℝ)|^4557 ≤ (19729691080127/50000000000000 : ℝ)^3533
        have hw : |(972588297/2000000000 : ℝ)|=(972588297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1123182729/5000000000 : ℝ)|^4557 ≤ (1821479863947/12500000000000 : ℝ)^3533
        have hw : |(-1123182729/5000000000 : ℝ)|=(1123182729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s0_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (129385149/312500000 : ℝ)*x 0 + (3091557869/10000000000 : ℝ)*x 1 + (5470975757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129385149/312500000 : ℝ)^4557 ≤ (3206536392081/10000000000000 : ℝ)^3533 := by
    have hnat : (129385149 : ℕ)^4557*10000000000000^3533 ≤ 3206536392081^3533*312500000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129385149 312500000 3206536392081 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091557869/10000000000 : ℝ)^4557 ≤ (21999412001813/100000000000000 : ℝ)^3533 := by
    have hnat : (3091557869 : ℕ)^4557*100000000000000^3533 ≤ 21999412001813^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091557869 10000000000 21999412001813 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470975757/10000000000 : ℝ)^4557 ≤ (45935224061421/100000000000000 : ℝ)^3533 := by
    have hnat : (5470975757 : ℕ)^4557*100000000000000^3533 ≤ 45935224061421^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470975757 10000000000 45935224061421 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(129385149/312500000 : ℝ), (3091557869/10000000000 : ℝ), (5470975757/10000000000 : ℝ)] ![(3206536392081/10000000000000 : ℝ), (21999412001813/100000000000000 : ℝ), (45935224061421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(129385149/312500000 : ℝ)|^4557 ≤ (3206536392081/10000000000000 : ℝ)^3533
        have hw : |(129385149/312500000 : ℝ)|=(129385149/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091557869/10000000000 : ℝ)|^4557 ≤ (21999412001813/100000000000000 : ℝ)^3533
        have hw : |(3091557869/10000000000 : ℝ)|=(3091557869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470975757/10000000000 : ℝ)|^4557 ≤ (45935224061421/100000000000000 : ℝ)^3533
        have hw : |(5470975757/10000000000 : ℝ)|=(5470975757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s0_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1670278203/10000000000 : ℝ)*x 0 + (4889278203/10000000000 : ℝ)*x 1 + (1467956523/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1670278203/10000000000 : ℝ)^4557 ≤ (1242890803981/12500000000000 : ℝ)^3533 := by
    have hnat : (1670278203 : ℕ)^4557*12500000000000^3533 ≤ 1242890803981^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1670278203 10000000000 1242890803981 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4889278203/10000000000 : ℝ)^4557 ≤ (39735242057651/100000000000000 : ℝ)^3533 := by
    have hnat : (4889278203 : ℕ)^4557*100000000000000^3533 ≤ 39735242057651^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4889278203 10000000000 39735242057651 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1467956523/2500000000 : ℝ)^4557 ≤ (50321631501537/100000000000000 : ℝ)^3533 := by
    have hnat : (1467956523 : ℕ)^4557*100000000000000^3533 ≤ 50321631501537^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1467956523 2500000000 50321631501537 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1670278203/10000000000 : ℝ), (4889278203/10000000000 : ℝ), (1467956523/2500000000 : ℝ)] ![(1242890803981/12500000000000 : ℝ), (39735242057651/100000000000000 : ℝ), (50321631501537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1670278203/10000000000 : ℝ)|^4557 ≤ (1242890803981/12500000000000 : ℝ)^3533
        have hw : |(-1670278203/10000000000 : ℝ)|=(1670278203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4889278203/10000000000 : ℝ)|^4557 ≤ (39735242057651/100000000000000 : ℝ)^3533
        have hw : |(4889278203/10000000000 : ℝ)|=(4889278203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1467956523/2500000000 : ℝ)|^4557 ≤ (50321631501537/100000000000000 : ℝ)^3533
        have hw : |(1467956523/2500000000 : ℝ)|=(1467956523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s0_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5190911257/10000000000 : ℝ)*x 0 + (-1237480993/10000000000 : ℝ)*x 1 + (1174365231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5190911257/10000000000 : ℝ)^4557 ≤ (42924988849121/100000000000000 : ℝ)^3533 := by
    have hnat : (5190911257 : ℕ)^4557*100000000000000^3533 ≤ 42924988849121^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190911257 10000000000 42924988849121 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1237480993/10000000000 : ℝ)^4557 ≤ (6753378938717/100000000000000 : ℝ)^3533 := by
    have hnat : (1237480993 : ℕ)^4557*100000000000000^3533 ≤ 6753378938717^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237480993 10000000000 6753378938717 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1174365231/2000000000 : ℝ)^4557 ≤ (10064326439587/20000000000000 : ℝ)^3533 := by
    have hnat : (1174365231 : ℕ)^4557*20000000000000^3533 ≤ 10064326439587^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174365231 2000000000 10064326439587 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5190911257/10000000000 : ℝ), (-1237480993/10000000000 : ℝ), (1174365231/2000000000 : ℝ)] ![(42924988849121/100000000000000 : ℝ), (6753378938717/100000000000000 : ℝ), (10064326439587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5190911257/10000000000 : ℝ)|^4557 ≤ (42924988849121/100000000000000 : ℝ)^3533
        have hw : |(5190911257/10000000000 : ℝ)|=(5190911257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1237480993/10000000000 : ℝ)|^4557 ≤ (6753378938717/100000000000000 : ℝ)^3533
        have hw : |(-1237480993/10000000000 : ℝ)|=(1237480993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1174365231/2000000000 : ℝ)|^4557 ≤ (10064326439587/20000000000000 : ℝ)^3533
        have hw : |(1174365231/2000000000 : ℝ)|=(1174365231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s0_6 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038182243/2000000000 : ℝ)*x 0 + (2935913203/5000000000 : ℝ)*x 1 + (-1237480663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038182243/2000000000 : ℝ)^4557 ≤ (10731247100287/25000000000000 : ℝ)^3533 := by
    have hnat : (1038182243 : ℕ)^4557*25000000000000^3533 ≤ 10731247100287^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038182243 2000000000 10731247100287 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2935913203/5000000000 : ℝ)^4557 ≤ (50321634972473/100000000000000 : ℝ)^3533 := by
    have hnat : (2935913203 : ℕ)^4557*100000000000000^3533 ≤ 50321634972473^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2935913203 5000000000 50321634972473 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237480663/10000000000 : ℝ)^4557 ≤ (675337661581/10000000000000 : ℝ)^3533 := by
    have hnat : (1237480663 : ℕ)^4557*10000000000000^3533 ≤ 675337661581^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237480663 10000000000 675337661581 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038182243/2000000000 : ℝ), (2935913203/5000000000 : ℝ), (-1237480663/10000000000 : ℝ)] ![(10731247100287/25000000000000 : ℝ), (50321634972473/100000000000000 : ℝ), (675337661581/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038182243/2000000000 : ℝ)|^4557 ≤ (10731247100287/25000000000000 : ℝ)^3533
        have hw : |(1038182243/2000000000 : ℝ)|=(1038182243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2935913203/5000000000 : ℝ)|^4557 ≤ (50321634972473/100000000000000 : ℝ)^3533
        have hw : |(2935913203/5000000000 : ℝ)|=(2935913203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1237480663/10000000000 : ℝ)|^4557 ≤ (675337661581/10000000000000 : ℝ)^3533
        have hw : |(-1237480663/10000000000 : ℝ)|=(1237480663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s0_7 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4148061929/10000000000 : ℝ)*x 0 + (5410496643/10000000000 : ℝ)*x 1 + (788549213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4148061929/10000000000 : ℝ)^4557 ≤ (16071337019357/50000000000000 : ℝ)^3533 := by
    have hnat : (4148061929 : ℕ)^4557*50000000000000^3533 ≤ 16071337019357^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4148061929 10000000000 16071337019357 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410496643/10000000000 : ℝ)^4557 ≤ (22640652706177/50000000000000 : ℝ)^3533 := by
    have hnat : (5410496643 : ℕ)^4557*50000000000000^3533 ≤ 22640652706177^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410496643 10000000000 22640652706177 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788549213/2500000000 : ℝ)^4557 ≤ (2822002567089/12500000000000 : ℝ)^3533 := by
    have hnat : (788549213 : ℕ)^4557*12500000000000^3533 ≤ 2822002567089^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788549213 2500000000 2822002567089 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4148061929/10000000000 : ℝ), (5410496643/10000000000 : ℝ), (788549213/2500000000 : ℝ)] ![(16071337019357/50000000000000 : ℝ), (22640652706177/50000000000000 : ℝ), (2822002567089/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4148061929/10000000000 : ℝ)|^4557 ≤ (16071337019357/50000000000000 : ℝ)^3533
        have hw : |(4148061929/10000000000 : ℝ)|=(4148061929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410496643/10000000000 : ℝ)|^4557 ≤ (22640652706177/50000000000000 : ℝ)^3533
        have hw : |(5410496643/10000000000 : ℝ)|=(5410496643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788549213/2500000000 : ℝ)|^4557 ≤ (2822002567089/12500000000000 : ℝ)^3533
        have hw : |(788549213/2500000000 : ℝ)|=(788549213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (191/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (25253/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4555/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4555 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4555*1^1024 ≤ 0^1024*1^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4555/1024 : ℝ) ≤ (424430391341941489/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4555 ≤ (424430391341941489/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4555*25000000000000000000^1024 ≤ 424430391341941489^1024*5^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 424430391341941489 25000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (424430391341941489/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4555 := by
      have hnat : (1 : ℕ)^1024*1^4555 ≤ 1^4555*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25424430391341941489/25000000000000000000 : ℝ) ≤ (501895873580391/500000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (25424430391341941489/25000000000000000000 : ℝ)^1024 ≤ (501895873580391/500000000000000 : ℝ)^4555 := by
      have hnat : (25424430391341941489 : ℕ)^1024*500000000000000^4555 ≤ 501895873580391^4555*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25424430391341941489 25000000000000000000 501895873580391 500000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (501895873580391/500000000000000 : ℝ)) (X := (25424430391341941489/25000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12924430391341941489/12500000000000000000 : ℝ) ≤ (251895873580391/250000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (12924430391341941489/12500000000000000000 : ℝ)^1024 ≤ (251895873580391/250000000000000 : ℝ)^4555 := by
      have hnat : (12924430391341941489 : ℕ)^1024*250000000000000^4555 ≤ 251895873580391^4555*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12924430391341941489 12500000000000000000 251895873580391 250000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251895873580391/250000000000000 : ℝ)) (X := (12924430391341941489/12500000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1895873580391/200000000000000 : ℝ)*(0 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1895873580391/200000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(424430391341941489/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1895873580391/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1895873580391/200000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(501895873580391/500000000000000 : ℝ) by norm_num, show 1+(424430391341941489/25000000000000000000 : ℝ)+(0 : ℝ)=(25424430391341941489/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(424430391341941489/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1895873580391/200000000000000 : ℝ)*(2/5 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1895873580391/200000000000000 : ℝ)*(2/5 : ℝ)=(251895873580391/250000000000000 : ℝ) by norm_num, show 1+2*(424430391341941489/25000000000000000000 : ℝ)=(12924430391341941489/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1895873580391/200000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1895873580391/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1895873580391/200000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1895873580391/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1895873580391/200000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1895873580391/200000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-416727127/2500000000 : ℝ)*X 0 0+(294955179/500000000 : ℝ)*X 0 1+(4862941463/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2737036971/5000000000 : ℝ)*X 1 0+(-561591351/2500000000 : ℝ)*X 1 1+(2431470749/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2737036957/5000000000 : ℝ)*X 2 0+(972588297/2000000000 : ℝ)*X 2 1+(-1123182729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((129385149/312500000 : ℝ)*X 0 0+(3091557869/10000000000 : ℝ)*X 0 1+(5470975757/10000000000 : ℝ)*X 0 2+(129385149/312500000 : ℝ)*X 1 0+(3091557869/10000000000 : ℝ)*X 1 1+(5470975757/10000000000 : ℝ)*X 1 2+(129385149/312500000 : ℝ)*X 2 0+(3091557869/10000000000 : ℝ)*X 2 1+(5470975757/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1670278203/10000000000 : ℝ)*X 0 0+(4889278203/10000000000 : ℝ)*X 0 1+(1467956523/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5190911257/10000000000 : ℝ)*X 1 0+(-1237480993/10000000000 : ℝ)*X 1 1+(1174365231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1038182243/2000000000 : ℝ)*X 2 0+(2935913203/5000000000 : ℝ)*X 2 1+(-1237480663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4148061929/10000000000 : ℝ)*X 0 0+(5410496643/10000000000 : ℝ)*X 0 1+(788549213/2500000000 : ℝ)*X 0 2+(4148061929/10000000000 : ℝ)*X 1 0+(5410496643/10000000000 : ℝ)*X 1 1+(788549213/2500000000 : ℝ)*X 1 2+(4148061929/10000000000 : ℝ)*X 2 0+(5410496643/10000000000 : ℝ)*X 2 1+(788549213/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3757410067163439037839/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38868603/50000000000000 : ℝ)*(base1) + (50250649/3125000000000 : ℝ)*(base19) + (801542107/50000000000000 : ℝ)*(base23) + (214901167/100000000000000 : ℝ)*(upper3) + (49512333/25000000000000 : ℝ)*(upper5) + (138538719013657/20000000000000 : ℝ)*(major0) + (138538719013657/20000000000000 : ℝ)*(major1) + (138538719013657/20000000000000 : ℝ)*(major2) + (60319093103637/6250000000000 : ℝ)*(sp0) + (96510952034423/10000000000000 : ℝ)*(sp1) + (193021905056157/20000000000000 : ℝ)*(sp2) + (42027320888459/10000000000000 : ℝ)*(sp3) + (1429111003/25000000000000 : ℝ)*(sp4) + (315581971/12500000000000 : ℝ)*(sp7) + (105068952819391/25000000000000 : ℝ)*(f.failure) + (482555564182499/50000000000000 : ℝ)*(f.sum) + (458210840113/2000000000000000000000000000 : ℝ)*base66 + (27136923079887/4000000000000000000000000000 : ℝ)*base67 + (6991404535887/4000000000000000000000000000 : ℝ)*base69 + (8546071391887/4000000000000000000000000000 : ℝ)*base71 + (4646803171887/2000000000000000000000000000 : ℝ)*base73 + (12516682375887/4000000000000000000000000000 : ℝ)*base75 + (7022520071887/4000000000000000000000000000 : ℝ)*base77 + (4317451363887/4000000000000000000000000000 : ℝ)*base79 + (1534611527887/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2635899/2500000000000000000000 : ℝ)*base90 + (2635899/2500000000000000000000 : ℝ)*base92 + (2635899/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10884018522380559931737/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (114421409/12500000000000 : ℝ)*(base19) + (991766959/100000000000000 : ℝ)*(base23) + (75221637/100000000000000 : ℝ)*(base39) + (13054493/10000000000000 : ℝ)*(upper3) + (81243097/50000000000000 : ℝ)*(upper5) + (29219305087813/4000000000000 : ℝ)*(major0) + (29219305087813/4000000000000 : ℝ)*(major1) + (91310318996711/12500000000000 : ℝ)*(major2) + (2515135309/100000000000000 : ℝ)*(sp1) + (2712798479/100000000000000 : ℝ)*(sp2) + (1017761601889961/100000000000000 : ℝ)*(sp4) + (50887908569169/5000000000000 : ℝ)*(sp5) + (12721974656827/1250000000000 : ℝ)*(sp6) + (1108008580397/250000000000 : ℝ)*(sp7) + (1108008580397/250000000000 : ℝ)*(f.failure) + (508880838555799/50000000000000 : ℝ)*(f.sum) + (6503670715917/20000000000000000000000000000 : ℝ)*base66 + (25085298113499/2500000000000000000000000000 : ℝ)*base68 + (3834438134717/800000000000000000000000000 : ℝ)*base70 + (12843606750999/2500000000000000000000000000 : ℝ)*base72 + (101720812855917/20000000000000000000000000000 : ℝ)*base74 + (4574273630717/800000000000000000000000000 : ℝ)*base76 + (2560459249917/800000000000000000000000000 : ℝ)*base78 + (2972078665117/800000000000000000000000000 : ℝ)*base80 + (1768492180317/400000000000000000000000000 : ℝ)*base82 + (197967/25000000000000000000 : ℝ)*base89 + (197967/25000000000000000000 : ℝ)*base91 + (197967/25000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1530_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (191/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (25253/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1530_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1530_s1_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-11348987/62500000 : ℝ)*x 0 + (5558828747/10000000000 : ℝ)*x 1 + (1276854321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (11348987/62500000 : ℝ)^4557 ≤ (1384327942823/12500000000000 : ℝ)^3533 := by
    have hnat : (11348987 : ℕ)^4557*12500000000000^3533 ≤ 1384327942823^3533*62500000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11348987 62500000 1384327942823 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5558828747/10000000000 : ℝ)^4557 ≤ (46888851327009/100000000000000 : ℝ)^3533 := by
    have hnat : (5558828747 : ℕ)^4557*100000000000000^3533 ≤ 46888851327009^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558828747 10000000000 46888851327009 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1276854321/2500000000 : ℝ)^4557 ≤ (10509131279959/25000000000000 : ℝ)^3533 := by
    have hnat : (1276854321 : ℕ)^4557*25000000000000^3533 ≤ 10509131279959^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1276854321 2500000000 10509131279959 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-11348987/62500000 : ℝ), (5558828747/10000000000 : ℝ), (1276854321/2500000000 : ℝ)] ![(1384327942823/12500000000000 : ℝ), (46888851327009/100000000000000 : ℝ), (10509131279959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-11348987/62500000 : ℝ)|^4557 ≤ (1384327942823/12500000000000 : ℝ)^3533
        have hw : |(-11348987/62500000 : ℝ)|=(11348987/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5558828747/10000000000 : ℝ)|^4557 ≤ (46888851327009/100000000000000 : ℝ)^3533
        have hw : |(5558828747/10000000000 : ℝ)|=(5558828747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1276854321/2500000000 : ℝ)|^4557 ≤ (10509131279959/25000000000000 : ℝ)^3533
        have hw : |(1276854321/2500000000 : ℝ)|=(1276854321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s1_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691690187/5000000000 : ℝ)*x 0 + (-410603173/2000000000 : ℝ)*x 1 + (319213477/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691690187/5000000000 : ℝ)^4557 ≤ (4498880181529/10000000000000 : ℝ)^3533 := by
    have hnat : (2691690187 : ℕ)^4557*10000000000000^3533 ≤ 4498880181529^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691690187 5000000000 4498880181529 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410603173/2000000000 : ℝ)^4557 ≤ (6487345294487/50000000000000 : ℝ)^3533 := by
    have hnat : (410603173 : ℕ)^4557*50000000000000^3533 ≤ 6487345294487^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410603173 2000000000 6487345294487 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319213477/625000000 : ℝ)^4557 ≤ (42036507582207/100000000000000 : ℝ)^3533 := by
    have hnat : (319213477 : ℕ)^4557*100000000000000^3533 ≤ 42036507582207^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319213477 625000000 42036507582207 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691690187/5000000000 : ℝ), (-410603173/2000000000 : ℝ), (319213477/625000000 : ℝ)] ![(4498880181529/10000000000000 : ℝ), (6487345294487/50000000000000 : ℝ), (42036507582207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691690187/5000000000 : ℝ)|^4557 ≤ (4498880181529/10000000000000 : ℝ)^3533
        have hw : |(2691690187/5000000000 : ℝ)|=(2691690187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410603173/2000000000 : ℝ)|^4557 ≤ (6487345294487/50000000000000 : ℝ)^3533
        have hw : |(-410603173/2000000000 : ℝ)|=(410603173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319213477/625000000 : ℝ)|^4557 ≤ (42036507582207/100000000000000 : ℝ)^3533
        have hw : |(319213477/625000000 : ℝ)|=(319213477/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s1_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076675827/2000000000 : ℝ)*x 0 + (319213577/625000000 : ℝ)*x 1 + (-102650771/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076675827/2000000000 : ℝ)^4557 ≤ (11247197114979/25000000000000 : ℝ)^3533 := by
    have hnat : (1076675827 : ℕ)^4557*25000000000000^3533 ≤ 11247197114979^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076675827 2000000000 11247197114979 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319213577/625000000 : ℝ)^4557 ≤ (10509131141951/25000000000000 : ℝ)^3533 := by
    have hnat : (319213577 : ℕ)^4557*25000000000000^3533 ≤ 10509131141951^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319213577 625000000 10509131141951 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102650771/500000000 : ℝ)^4557 ≤ (101364741887/781250000000 : ℝ)^3533 := by
    have hnat : (102650771 : ℕ)^4557*781250000000^3533 ≤ 101364741887^3533*500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102650771 500000000 101364741887 781250000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076675827/2000000000 : ℝ), (319213577/625000000 : ℝ), (-102650771/500000000 : ℝ)] ![(11247197114979/25000000000000 : ℝ), (10509131141951/25000000000000 : ℝ), (101364741887/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076675827/2000000000 : ℝ)|^4557 ≤ (11247197114979/25000000000000 : ℝ)^3533
        have hw : |(1076675827/2000000000 : ℝ)|=(1076675827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319213577/625000000 : ℝ)|^4557 ≤ (10509131141951/25000000000000 : ℝ)^3533
        have hw : |(319213577/625000000 : ℝ)|=(319213577/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102650771/500000000 : ℝ)|^4557 ≤ (101364741887/781250000000 : ℝ)^3533
        have hw : |(-102650771/500000000 : ℝ)|=(102650771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s1_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530380593/1250000000 : ℝ)*x 0 + (3751079909/10000000000 : ℝ)*x 1 + (1196923331/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530380593/1250000000 : ℝ)^4557 ≤ (33095137354689/100000000000000 : ℝ)^3533 := by
    have hnat : (530380593 : ℕ)^4557*100000000000000^3533 ≤ 33095137354689^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530380593 1250000000 33095137354689 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3751079909/10000000000 : ℝ)^4557 ≤ (882227057419/3125000000000 : ℝ)^3533 := by
    have hnat : (3751079909 : ℕ)^4557*3125000000000^3533 ≤ 882227057419^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3751079909 10000000000 882227057419 3125000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1196923331/2500000000 : ℝ)^4557 ≤ (38673596785077/100000000000000 : ℝ)^3533 := by
    have hnat : (1196923331 : ℕ)^4557*100000000000000^3533 ≤ 38673596785077^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1196923331 2500000000 38673596785077 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530380593/1250000000 : ℝ), (3751079909/10000000000 : ℝ), (1196923331/2500000000 : ℝ)] ![(33095137354689/100000000000000 : ℝ), (882227057419/3125000000000 : ℝ), (38673596785077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530380593/1250000000 : ℝ)|^4557 ≤ (33095137354689/100000000000000 : ℝ)^3533
        have hw : |(530380593/1250000000 : ℝ)|=(530380593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3751079909/10000000000 : ℝ)|^4557 ≤ (882227057419/3125000000000 : ℝ)^3533
        have hw : |(3751079909/10000000000 : ℝ)|=(3751079909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1196923331/2500000000 : ℝ)|^4557 ≤ (38673596785077/100000000000000 : ℝ)^3533
        have hw : |(1196923331/2500000000 : ℝ)|=(1196923331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s1_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-113506727/625000000 : ℝ)*x 0 + (1022467827/2000000000 : ℝ)*x 1 + (5553829903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113506727/625000000 : ℝ)^4557 ≤ (11076745305719/100000000000000 : ℝ)^3533 := by
    have hnat : (113506727 : ℕ)^4557*100000000000000^3533 ≤ 11076745305719^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113506727 625000000 11076745305719 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1022467827/2000000000 : ℝ)^4557 ≤ (42088782779111/100000000000000 : ℝ)^3533 := by
    have hnat : (1022467827 : ℕ)^4557*100000000000000^3533 ≤ 42088782779111^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022467827 2000000000 42088782779111 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5553829903/10000000000 : ℝ)^4557 ≤ (182947155843/390625000000 : ℝ)^3533 := by
    have hnat : (5553829903 : ℕ)^4557*390625000000^3533 ≤ 182947155843^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553829903 10000000000 182947155843 390625000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-113506727/625000000 : ℝ), (1022467827/2000000000 : ℝ), (5553829903/10000000000 : ℝ)] ![(11076745305719/100000000000000 : ℝ), (42088782779111/100000000000000 : ℝ), (182947155843/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-113506727/625000000 : ℝ)|^4557 ≤ (11076745305719/100000000000000 : ℝ)^3533
        have hw : |(-113506727/625000000 : ℝ)|=(113506727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1022467827/2000000000 : ℝ)|^4557 ≤ (42088782779111/100000000000000 : ℝ)^3533
        have hw : |(1022467827/2000000000 : ℝ)|=(1022467827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5553829903/10000000000 : ℝ)|^4557 ≤ (182947155843/390625000000 : ℝ)^3533
        have hw : |(5553829903/10000000000 : ℝ)|=(5553829903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s1_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264229821/10000000000 : ℝ)*x 0 + (-803301233/5000000000 : ℝ)*x 1 + (5553830029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264229821/10000000000 : ℝ)^4557 ≤ (43708600760131/100000000000000 : ℝ)^3533 := by
    have hnat : (5264229821 : ℕ)^4557*100000000000000^3533 ≤ 43708600760131^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264229821 10000000000 43708600760131 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (803301233/5000000000 : ℝ)^4557 ≤ (147764468251/1562500000000 : ℝ)^3533 := by
    have hnat : (803301233 : ℕ)^4557*1562500000000^3533 ≤ 147764468251^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803301233 5000000000 147764468251 1562500000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5553830029/10000000000 : ℝ)^4557 ≤ (46834473266307/100000000000000 : ℝ)^3533 := by
    have hnat : (5553830029 : ℕ)^4557*100000000000000^3533 ≤ 46834473266307^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553830029 10000000000 46834473266307 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264229821/10000000000 : ℝ), (-803301233/5000000000 : ℝ), (5553830029/10000000000 : ℝ)] ![(43708600760131/100000000000000 : ℝ), (147764468251/1562500000000 : ℝ), (46834473266307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264229821/10000000000 : ℝ)|^4557 ≤ (43708600760131/100000000000000 : ℝ)^3533
        have hw : |(5264229821/10000000000 : ℝ)|=(5264229821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-803301233/5000000000 : ℝ)|^4557 ≤ (147764468251/1562500000000 : ℝ)^3533
        have hw : |(-803301233/5000000000 : ℝ)|=(803301233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5553830029/10000000000 : ℝ)|^4557 ≤ (46834473266307/100000000000000 : ℝ)^3533
        have hw : |(5553830029/10000000000 : ℝ)|=(5553830029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s1_6 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5264229679/10000000000 : ℝ)*x 0 + (2776915069/5000000000 : ℝ)*x 1 + (-160660251/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5264229679/10000000000 : ℝ)^4557 ≤ (10927149809847/25000000000000 : ℝ)^3533 := by
    have hnat : (5264229679 : ℕ)^4557*25000000000000^3533 ≤ 10927149809847^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264229679 10000000000 10927149809847 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2776915069/5000000000 : ℝ)^4557 ≤ (46834474451899/100000000000000 : ℝ)^3533 := by
    have hnat : (2776915069 : ℕ)^4557*100000000000000^3533 ≤ 46834474451899^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2776915069 5000000000 46834474451899 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160660251/1000000000 : ℝ)^4557 ≤ (9456926302127/100000000000000 : ℝ)^3533 := by
    have hnat : (160660251 : ℕ)^4557*100000000000000^3533 ≤ 9456926302127^3533*1000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160660251 1000000000 9456926302127 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5264229679/10000000000 : ℝ), (2776915069/5000000000 : ℝ), (-160660251/1000000000 : ℝ)] ![(10927149809847/25000000000000 : ℝ), (46834474451899/100000000000000 : ℝ), (9456926302127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5264229679/10000000000 : ℝ)|^4557 ≤ (10927149809847/25000000000000 : ℝ)^3533
        have hw : |(5264229679/10000000000 : ℝ)|=(5264229679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2776915069/5000000000 : ℝ)|^4557 ≤ (46834474451899/100000000000000 : ℝ)^3533
        have hw : |(2776915069/5000000000 : ℝ)|=(2776915069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-160660251/1000000000 : ℝ)|^4557 ≤ (9456926302127/100000000000000 : ℝ)^3533
        have hw : |(-160660251/1000000000 : ℝ)|=(160660251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s1_7 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121831673/5000000000 : ℝ)*x 0 + (238819521/500000000 : ℝ)*x 1 + (940640193/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121831673/5000000000 : ℝ)^4557 ≤ (16550680483009/50000000000000 : ℝ)^3533 := by
    have hnat : (2121831673 : ℕ)^4557*50000000000000^3533 ≤ 16550680483009^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121831673 5000000000 16550680483009 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (238819521/500000000 : ℝ)^4557 ≤ (3855587279381/10000000000000 : ℝ)^3533 := by
    have hnat : (238819521 : ℕ)^4557*10000000000000^3533 ≤ 3855587279381^3533*500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238819521 500000000 3855587279381 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940640193/2500000000 : ℝ)^4557 ≤ (885711444807/3125000000000 : ℝ)^3533 := by
    have hnat : (940640193 : ℕ)^4557*3125000000000^3533 ≤ 885711444807^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940640193 2500000000 885711444807 3125000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121831673/5000000000 : ℝ), (238819521/500000000 : ℝ), (940640193/2500000000 : ℝ)] ![(16550680483009/50000000000000 : ℝ), (3855587279381/10000000000000 : ℝ), (885711444807/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121831673/5000000000 : ℝ)|^4557 ≤ (16550680483009/50000000000000 : ℝ)^3533
        have hw : |(2121831673/5000000000 : ℝ)|=(2121831673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(238819521/500000000 : ℝ)|^4557 ≤ (3855587279381/10000000000000 : ℝ)^3533
        have hw : |(238819521/500000000 : ℝ)|=(238819521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(940640193/2500000000 : ℝ)|^4557 ≤ (885711444807/3125000000000 : ℝ)^3533
        have hw : |(940640193/2500000000 : ℝ)|=(940640193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25253/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (191/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (8591/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18143/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (25253/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (191/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (25253/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (191/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (25253/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (191/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (25253/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (191/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (25253/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (191/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (25253/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (191/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (191/6250 : ℝ) ^ (4555/1024 : ℝ) ≤ (18263971611871/100000000000000000000 : ℝ) := by
    have hpowers : (191/6250 : ℝ)^4555 ≤ (18263971611871/100000000000000000000 : ℝ)^1024 := by
      have hnat : (191 : ℕ)^4555*100000000000000000000^1024 ≤ 18263971611871^1024*6250^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        191 6250 18263971611871 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (191/6250 : ℝ)) (X := (18263971611871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (25253/100000 : ℝ) ^ (4555/1024 : ℝ) ≤ (219453937301502337/100000000000000000000 : ℝ) := by
    have hpowers : (25253/100000 : ℝ)^4555 ≤ (219453937301502337/100000000000000000000 : ℝ)^1024 := by
      have hnat : (25253 : ℕ)^4555*100000000000000000000^1024 ≤ 219453937301502337^1024*100000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25253 100000 219453937301502337 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25253/100000 : ℝ)) (X := (219453937301502337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000018263971611871/50000000000000000000 : ℝ) ≤ (10000000821176917/10000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50000018263971611871/50000000000000000000 : ℝ)^1024 ≤ (10000000821176917/10000000000000000 : ℝ)^4555 := by
      have hnat : (50000018263971611871 : ℕ)^1024*10000000000000000^4555 ≤ 10000000821176917^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000018263971611871 50000000000000000000 10000000821176917 10000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000821176917/10000000000000000 : ℝ)) (X := (50000018263971611871/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3131858506289784819/3125000000000000000 : ℝ) ≤ (2501232429219651/2500000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (3131858506289784819/3125000000000000000 : ℝ)^1024 ≤ (2501232429219651/2500000000000000 : ℝ)^4555 := by
      have hnat : (3131858506289784819 : ℕ)^1024*2500000000000000^4555 ≤ 2501232429219651^4555*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3131858506289784819 3125000000000000000 2501232429219651 2500000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501232429219651/2500000000000000 : ℝ)) (X := (3131858506289784819/3125000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50219453937301502337/50000000000000000000 : ℝ) ≤ (10009858612580291/10000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50219453937301502337/50000000000000000000 : ℝ)^1024 ≤ (10009858612580291/10000000000000000 : ℝ)^4555 := by
      have hnat : (50219453937301502337 : ℕ)^1024*10000000000000000^4555 ≤ 10009858612580291^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50219453937301502337 50000000000000000000 10009858612580291 10000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009858612580291/10000000000000000 : ℝ)) (X := (50219453937301502337/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(18263971611871/100000000000000000000 : ℝ) ≤ ((44387978563427063141/44394000000000000000 : ℝ)+2*(4928895701687/2219700000000000 : ℝ)*(191/6250 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (44387978563427063141/44394000000000000000 : ℝ)+2*(4928895701687/2219700000000000 : ℝ)*(191/6250 : ℝ)=(10000000821176917/10000000000000000 : ℝ) by norm_num, show 1+2*(18263971611871/100000000000000000000 : ℝ)=(50000018263971611871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(219453937301502337/100000000000000000000 : ℝ)+(18263971611871/100000000000000000000 : ℝ) ≤ ((44387978563427063141/44394000000000000000 : ℝ)+(4928895701687/2219700000000000 : ℝ)*((25253/100000 : ℝ)+(191/6250 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (44387978563427063141/44394000000000000000 : ℝ)+(4928895701687/2219700000000000 : ℝ)*((25253/100000 : ℝ)+(191/6250 : ℝ))=(2501232429219651/2500000000000000 : ℝ) by norm_num, show 1+(219453937301502337/100000000000000000000 : ℝ)+(18263971611871/100000000000000000000 : ℝ)=(3131858506289784819/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(219453937301502337/100000000000000000000 : ℝ) ≤ ((44387978563427063141/44394000000000000000 : ℝ)+2*(4928895701687/2219700000000000 : ℝ)*(25253/100000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (44387978563427063141/44394000000000000000 : ℝ)+2*(4928895701687/2219700000000000 : ℝ)*(25253/100000 : ℝ)=(10009858612580291/10000000000000000 : ℝ) by norm_num, show 1+2*(219453937301502337/100000000000000000000 : ℝ)=(50219453937301502337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44387978563427063141/44394000000000000000 : ℝ)*(X 1 0+X 2 0)+(4928895701687/2219700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (191/6250 : ℝ)) (hi := (25253/100000 : ℝ)) (c := (44387978563427063141/44394000000000000000 : ℝ)) (alpha := (4928895701687/2219700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44387978563427063141/44394000000000000000 : ℝ)*(X 0 1+X 2 1)+(4928895701687/2219700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (191/6250 : ℝ)) (hi := (25253/100000 : ℝ)) (c := (44387978563427063141/44394000000000000000 : ℝ)) (alpha := (4928895701687/2219700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44387978563427063141/44394000000000000000 : ℝ)*(X 0 2+X 1 2)+(4928895701687/2219700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (191/6250 : ℝ)) (hi := (25253/100000 : ℝ)) (c := (44387978563427063141/44394000000000000000 : ℝ)) (alpha := (4928895701687/2219700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-11348987/62500000 : ℝ)*X 0 0+(5558828747/10000000000 : ℝ)*X 0 1+(1276854321/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2691690187/5000000000 : ℝ)*X 1 0+(-410603173/2000000000 : ℝ)*X 1 1+(319213477/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1076675827/2000000000 : ℝ)*X 2 0+(319213577/625000000 : ℝ)*X 2 1+(-102650771/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530380593/1250000000 : ℝ)*X 0 0+(3751079909/10000000000 : ℝ)*X 0 1+(1196923331/2500000000 : ℝ)*X 0 2+(530380593/1250000000 : ℝ)*X 1 0+(3751079909/10000000000 : ℝ)*X 1 1+(1196923331/2500000000 : ℝ)*X 1 2+(530380593/1250000000 : ℝ)*X 2 0+(3751079909/10000000000 : ℝ)*X 2 1+(1196923331/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-113506727/625000000 : ℝ)*X 0 0+(1022467827/2000000000 : ℝ)*X 0 1+(5553829903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5264229821/10000000000 : ℝ)*X 1 0+(-803301233/5000000000 : ℝ)*X 1 1+(5553830029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5264229679/10000000000 : ℝ)*X 2 0+(2776915069/5000000000 : ℝ)*X 2 1+(-160660251/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121831673/5000000000 : ℝ)*X 0 0+(238819521/500000000 : ℝ)*X 0 1+(940640193/2500000000 : ℝ)*X 0 2+(2121831673/5000000000 : ℝ)*X 1 0+(238819521/500000000 : ℝ)*X 1 1+(940640193/2500000000 : ℝ)*X 1 2+(2121831673/5000000000 : ℝ)*X 2 0+(238819521/500000000 : ℝ)*X 2 1+(940640193/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (278337589882662429637026687/46243750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (206836681/100000000000000 : ℝ)*(base1) + (972592677/50000000000000 : ℝ)*(base19) + (358832659/25000000000000 : ℝ)*(base23) + (1086587/1000000000000 : ℝ)*(upper3) + (30121747/12500000000000 : ℝ)*(upper5) + (198748688874543/12500000000000 : ℝ)*(major0) + (198748688874543/12500000000000 : ℝ)*(major1) + (198748688874543/12500000000000 : ℝ)*(major2) + (443056272226769/20000000000000 : ℝ)*(sp0) + (34613867648813/1562500000000 : ℝ)*(sp1) + (1772230431503/80000000000 : ℝ)*(sp2) + (482342541188211/50000000000000 : ℝ)*(sp3) + (4160206111/50000000000000 : ℝ)*(sp4) + (4057439413/100000000000000 : ℝ)*(sp7) + (192937869330503/20000000000000 : ℝ)*(f.failure) + (1107644737354693/50000000000000 : ℝ)*(f.sum) + (3829041611293/18497500000000000000000000000 : ℝ)*base65 + (448238101082521521/184975000000000000000000000000000 : ℝ)*base67 + (2376863668303479/184975000000000000000000000000000 : ℝ)*base70 + (815607590512296521/184975000000000000000000000000000 : ℝ)*base71 + (45643635984167/18497500000000000000000000000 : ℝ)*base74 + (1304320427821146521/184975000000000000000000000000000 : ℝ)*base75 + (504436489174346521/184975000000000000000000000000000 : ℝ)*base77 + (1491299212052896521/184975000000000000000000000000000 : ℝ)*base79 + (21769561678601/9248750000000000000000000000 : ℝ)*base82 + (9508067/2000000000000000000000 : ℝ)*base90 + (9508067/2000000000000000000000 : ℝ)*base92 + (9508067/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1494502104832286427919643999/147980000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1802961273/100000000000000 : ℝ)*(base19) + (1923140231/100000000000000 : ℝ)*(base23) + (259351389/100000000000000 : ℝ)*(upper3) + (38604243/50000000000000 : ℝ)*(lower4) + (190542173/100000000000000 : ℝ)*(upper5) + (325141068051539/20000000000000 : ℝ)*(major0) + (325141068051539/20000000000000 : ℝ)*(major1) + (325141068051539/20000000000000 : ℝ)*(major2) + (6393336407/50000000000000 : ℝ)*(sp1) + (14315977549/100000000000000 : ℝ)*(sp2) + (2265051244205601/100000000000000 : ℝ)*(sp4) + (1132518327285757/50000000000000 : ℝ)*(sp5) + (1132517502543911/50000000000000 : ℝ)*(sp6) + (986359099664719/100000000000000 : ℝ)*(sp7) + (986359099664719/100000000000000 : ℝ)*(f.failure) + (2265051244205601/100000000000000 : ℝ)*(f.sum) + (18207721262719/22197000000000000000000000000 : ℝ)*base65 + (1201001254915038667/295960000000000000000000000000000 : ℝ)*base68 + (622111559015201333/295960000000000000000000000000000 : ℝ)*base69 + (1121641301704521333/295960000000000000000000000000000 : ℝ)*base71 + (106432904301869/22197000000000000000000000000 : ℝ)*base74 + (490797380254758667/295960000000000000000000000000000 : ℝ)*base76 + (1058411252390558667/295960000000000000000000000000000 : ℝ)*base78 + (1162410636592278667/295960000000000000000000000000000 : ℝ)*base80 + (413815410503/22197000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (15770891/10000000000000000000000 : ℝ)*base90 + (15770891/10000000000000000000000 : ℝ)*base92 + (15770891/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1530_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (25253/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (191/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8591/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18143/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1530_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1530_s2_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-919179973/5000000000 : ℝ)*x 0 + (1090475913/2000000000 : ℝ)*x 1 + (2599625199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (919179973/5000000000 : ℝ)^4557 ≤ (1406514115897/12500000000000 : ℝ)^3533 := by
    have hnat : (919179973 : ℕ)^4557*12500000000000^3533 ≤ 1406514115897^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919179973 5000000000 1406514115897 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090475913/2000000000 : ℝ)^4557 ≤ (9146786431549/20000000000000 : ℝ)^3533 := by
    have hnat : (1090475913 : ℕ)^4557*20000000000000^3533 ≤ 9146786431549^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090475913 2000000000 9146786431549 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2599625199/5000000000 : ℝ)^4557 ≤ (1344186090883/3125000000000 : ℝ)^3533 := by
    have hnat : (2599625199 : ℕ)^4557*3125000000000^3533 ≤ 1344186090883^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599625199 5000000000 1344186090883 3125000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-919179973/5000000000 : ℝ), (1090475913/2000000000 : ℝ), (2599625199/5000000000 : ℝ)] ![(1406514115897/12500000000000 : ℝ), (9146786431549/20000000000000 : ℝ), (1344186090883/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-919179973/5000000000 : ℝ)|^4557 ≤ (1406514115897/12500000000000 : ℝ)^3533
        have hw : |(-919179973/5000000000 : ℝ)|=(919179973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090475913/2000000000 : ℝ)|^4557 ≤ (9146786431549/20000000000000 : ℝ)^3533
        have hw : |(1090475913/2000000000 : ℝ)|=(1090475913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2599625199/5000000000 : ℝ)|^4557 ≤ (1344186090883/3125000000000 : ℝ)^3533
        have hw : |(2599625199/5000000000 : ℝ)|=(2599625199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s2_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267809219/500000000 : ℝ)*x 0 + (-984266623/5000000000 : ℝ)*x 1 + (5199250793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267809219/500000000 : ℝ)^4557 ≤ (2234793341633/5000000000000 : ℝ)^3533 := by
    have hnat : (267809219 : ℕ)^4557*5000000000000^3533 ≤ 2234793341633^3533*500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267809219 500000000 2234793341633 5000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (984266623/5000000000 : ℝ)^4557 ≤ (245803480641/2000000000000 : ℝ)^3533 := by
    have hnat : (984266623 : ℕ)^4557*2000000000000^3533 ≤ 245803480641^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      984266623 5000000000 245803480641 2000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5199250793/10000000000 : ℝ)^4557 ≤ (4301395912329/10000000000000 : ℝ)^3533 := by
    have hnat : (5199250793 : ℕ)^4557*10000000000000^3533 ≤ 4301395912329^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199250793 10000000000 4301395912329 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267809219/500000000 : ℝ), (-984266623/5000000000 : ℝ), (5199250793/10000000000 : ℝ)] ![(2234793341633/5000000000000 : ℝ), (245803480641/2000000000000 : ℝ), (4301395912329/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267809219/500000000 : ℝ)|^4557 ≤ (2234793341633/5000000000000 : ℝ)^3533
        have hw : |(267809219/500000000 : ℝ)|=(267809219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-984266623/5000000000 : ℝ)|^4557 ≤ (245803480641/2000000000000 : ℝ)^3533
        have hw : |(-984266623/5000000000 : ℝ)|=(984266623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5199250793/10000000000 : ℝ)|^4557 ≤ (4301395912329/10000000000000 : ℝ)^3533
        have hw : |(5199250793/10000000000 : ℝ)|=(5199250793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s2_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535618509/1000000000 : ℝ)*x 0 + (649906297/1250000000 : ℝ)*x 1 + (-1968532849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535618509/1000000000 : ℝ)^4557 ≤ (8939174894927/20000000000000 : ℝ)^3533 := by
    have hnat : (535618509 : ℕ)^4557*20000000000000^3533 ≤ 8939174894927^3533*1000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535618509 1000000000 8939174894927 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (649906297/1250000000 : ℝ)^4557 ≤ (8602790934699/20000000000000 : ℝ)^3533 := by
    have hnat : (649906297 : ℕ)^4557*20000000000000^3533 ≤ 8602790934699^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649906297 1250000000 8602790934699 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1968532849/10000000000 : ℝ)^4557 ≤ (614508541753/5000000000000 : ℝ)^3533 := by
    have hnat : (1968532849 : ℕ)^4557*5000000000000^3533 ≤ 614508541753^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968532849 10000000000 614508541753 5000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535618509/1000000000 : ℝ), (649906297/1250000000 : ℝ), (-1968532849/10000000000 : ℝ)] ![(8939174894927/20000000000000 : ℝ), (8602790934699/20000000000000 : ℝ), (614508541753/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535618509/1000000000 : ℝ)|^4557 ≤ (8939174894927/20000000000000 : ℝ)^3533
        have hw : |(535618509/1000000000 : ℝ)|=(535618509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(649906297/1250000000 : ℝ)|^4557 ≤ (8602790934699/20000000000000 : ℝ)^3533
        have hw : |(649906297/1250000000 : ℝ)|=(649906297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1968532849/10000000000 : ℝ)|^4557 ≤ (614508541753/5000000000000 : ℝ)^3533
        have hw : |(-1968532849/10000000000 : ℝ)|=(1968532849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s2_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129631241/5000000000 : ℝ)*x 0 + (994227497/2500000000 : ℝ)*x 1 + (4558191139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129631241/5000000000 : ℝ)^4557 ≤ (16629193552123/50000000000000 : ℝ)^3533 := by
    have hnat : (2129631241 : ℕ)^4557*50000000000000^3533 ≤ 16629193552123^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129631241 5000000000 16629193552123 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (994227497/2500000000 : ℝ)^4557 ≤ (15221191301577/50000000000000 : ℝ)^3533 := by
    have hnat : (994227497 : ℕ)^4557*50000000000000^3533 ≤ 15221191301577^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994227497 2500000000 15221191301577 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4558191139/10000000000 : ℝ)^4557 ≤ (36299230282057/100000000000000 : ℝ)^3533 := by
    have hnat : (4558191139 : ℕ)^4557*100000000000000^3533 ≤ 36299230282057^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558191139 10000000000 36299230282057 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129631241/5000000000 : ℝ), (994227497/2500000000 : ℝ), (4558191139/10000000000 : ℝ)] ![(16629193552123/50000000000000 : ℝ), (15221191301577/50000000000000 : ℝ), (36299230282057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129631241/5000000000 : ℝ)|^4557 ≤ (16629193552123/50000000000000 : ℝ)^3533
        have hw : |(2129631241/5000000000 : ℝ)|=(2129631241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(994227497/2500000000 : ℝ)|^4557 ≤ (15221191301577/50000000000000 : ℝ)^3533
        have hw : |(994227497/2500000000 : ℝ)|=(994227497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4558191139/10000000000 : ℝ)|^4557 ≤ (36299230282057/100000000000000 : ℝ)^3533
        have hw : |(4558191139/10000000000 : ℝ)|=(4558191139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s2_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-459601837/2500000000 : ℝ)*x 0 + (1040161297/2000000000 : ℝ)*x 1 + (85168907/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (459601837/2500000000 : ℝ)^4557 ≤ (11252487155981/100000000000000 : ℝ)^3533 := by
    have hnat : (459601837 : ℕ)^4557*100000000000000^3533 ≤ 11252487155981^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459601837 2500000000 11252487155981 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040161297/2000000000 : ℝ)^4557 ≤ (10757640147807/25000000000000 : ℝ)^3533 := by
    have hnat : (1040161297 : ℕ)^4557*25000000000000^3533 ≤ 10757640147807^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040161297 2000000000 10757640147807 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85168907/156250000 : ℝ)^4557 ≤ (9143390446623/20000000000000 : ℝ)^3533 := by
    have hnat : (85168907 : ℕ)^4557*20000000000000^3533 ≤ 9143390446623^3533*156250000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85168907 156250000 9143390446623 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-459601837/2500000000 : ℝ), (1040161297/2000000000 : ℝ), (85168907/156250000 : ℝ)] ![(11252487155981/100000000000000 : ℝ), (10757640147807/25000000000000 : ℝ), (9143390446623/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-459601837/2500000000 : ℝ)|^4557 ≤ (11252487155981/100000000000000 : ℝ)^3533
        have hw : |(-459601837/2500000000 : ℝ)|=(459601837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040161297/2000000000 : ℝ)|^4557 ≤ (10757640147807/25000000000000 : ℝ)^3533
        have hw : |(1040161297/2000000000 : ℝ)|=(1040161297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(85168907/156250000 : ℝ)|^4557 ≤ (9143390446623/20000000000000 : ℝ)^3533
        have hw : |(85168907/156250000 : ℝ)|=(85168907/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s2_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644774071/5000000000 : ℝ)*x 0 + (-1716973439/10000000000 : ℝ)*x 1 + (5450810001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644774071/5000000000 : ℝ)^4557 ≤ (43979935002549/100000000000000 : ℝ)^3533 := by
    have hnat : (2644774071 : ℕ)^4557*100000000000000^3533 ≤ 43979935002549^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644774071 5000000000 43979935002549 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1716973439/10000000000 : ℝ)^4557 ≤ (5151556633623/50000000000000 : ℝ)^3533 := by
    have hnat : (1716973439 : ℕ)^4557*50000000000000^3533 ≤ 5151556633623^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1716973439 10000000000 5151556633623 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450810001/10000000000 : ℝ)^4557 ≤ (5714618965583/12500000000000 : ℝ)^3533 := by
    have hnat : (5450810001 : ℕ)^4557*12500000000000^3533 ≤ 5714618965583^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450810001 10000000000 5714618965583 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644774071/5000000000 : ℝ), (-1716973439/10000000000 : ℝ), (5450810001/10000000000 : ℝ)] ![(43979935002549/100000000000000 : ℝ), (5151556633623/50000000000000 : ℝ), (5714618965583/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644774071/5000000000 : ℝ)|^4557 ≤ (43979935002549/100000000000000 : ℝ)^3533
        have hw : |(2644774071/5000000000 : ℝ)|=(2644774071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1716973439/10000000000 : ℝ)|^4557 ≤ (5151556633623/50000000000000 : ℝ)^3533
        have hw : |(-1716973439/10000000000 : ℝ)|=(1716973439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450810001/10000000000 : ℝ)|^4557 ≤ (5714618965583/12500000000000 : ℝ)^3533
        have hw : |(5450810001/10000000000 : ℝ)|=(5450810001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s2_6 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644773919/5000000000 : ℝ)*x 0 + (5450810141/10000000000 : ℝ)*x 1 + (-53655427/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644773919/5000000000 : ℝ)^4557 ≤ (5497491467793/12500000000000 : ℝ)^3533 := by
    have hnat : (2644773919 : ℕ)^4557*12500000000000^3533 ≤ 5497491467793^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644773919 5000000000 5497491467793 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450810141/10000000000 : ℝ)^4557 ≤ (57146191549/125000000000 : ℝ)^3533 := by
    have hnat : (5450810141 : ℕ)^4557*125000000000^3533 ≤ 57146191549^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450810141 10000000000 57146191549 125000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53655427/312500000 : ℝ)^4557 ≤ (10303115008743/100000000000000 : ℝ)^3533 := by
    have hnat : (53655427 : ℕ)^4557*100000000000000^3533 ≤ 10303115008743^3533*312500000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53655427 312500000 10303115008743 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644773919/5000000000 : ℝ), (5450810141/10000000000 : ℝ), (-53655427/312500000 : ℝ)] ![(5497491467793/12500000000000 : ℝ), (57146191549/125000000000 : ℝ), (10303115008743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644773919/5000000000 : ℝ)|^4557 ≤ (5497491467793/12500000000000 : ℝ)^3533
        have hw : |(2644773919/5000000000 : ℝ)|=(2644773919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450810141/10000000000 : ℝ)|^4557 ≤ (57146191549/125000000000 : ℝ)^3533
        have hw : |(5450810141/10000000000 : ℝ)|=(5450810141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-53655427/312500000 : ℝ)|^4557 ≤ (10303115008743/100000000000000 : ℝ)^3533
        have hw : |(-53655427/312500000 : ℝ)|=(53655427/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s2_7 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2129686143/5000000000 : ℝ)*x 0 + (4554617039/10000000000 : ℝ)*x 1 + (3980515333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129686143/5000000000 : ℝ)^4557 ≤ (33259493019769/100000000000000 : ℝ)^3533 := by
    have hnat : (2129686143 : ℕ)^4557*100000000000000^3533 ≤ 33259493019769^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129686143 5000000000 33259493019769 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4554617039/10000000000 : ℝ)^4557 ≤ (1450500901799/4000000000000 : ℝ)^3533 := by
    have hnat : (4554617039 : ℕ)^4557*4000000000000^3533 ≤ 1450500901799^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554617039 10000000000 1450500901799 4000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3980515333/10000000000 : ℝ)^4557 ≤ (30477984418247/100000000000000 : ℝ)^3533 := by
    have hnat : (3980515333 : ℕ)^4557*100000000000000^3533 ≤ 30477984418247^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3980515333 10000000000 30477984418247 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2129686143/5000000000 : ℝ), (4554617039/10000000000 : ℝ), (3980515333/10000000000 : ℝ)] ![(33259493019769/100000000000000 : ℝ), (1450500901799/4000000000000 : ℝ), (30477984418247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2129686143/5000000000 : ℝ)|^4557 ≤ (33259493019769/100000000000000 : ℝ)^3533
        have hw : |(2129686143/5000000000 : ℝ)|=(2129686143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4554617039/10000000000 : ℝ)|^4557 ≤ (1450500901799/4000000000000 : ℝ)^3533
        have hw : |(4554617039/10000000000 : ℝ)|=(4554617039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3980515333/10000000000 : ℝ)|^4557 ≤ (30477984418247/100000000000000 : ℝ)^3533
        have hw : |(3980515333/10000000000 : ℝ)|=(3980515333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8591/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10571/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3983/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8591/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18143/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8591/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8591/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18143/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8591/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8591/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18143/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8591/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8591/100000 : ℝ) ^ (4555/1024 : ℝ) ≤ (1812876840881021/100000000000000000000 : ℝ) := by
    have hpowers : (8591/100000 : ℝ)^4555 ≤ (1812876840881021/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8591 : ℕ)^4555*100000000000000000000^1024 ≤ 1812876840881021^1024*100000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8591 100000 1812876840881021 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8591/100000 : ℝ)) (X := (1812876840881021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18143/100000 : ℝ) ^ (4555/1024 : ℝ) ≤ (6301857245136871/12500000000000000000 : ℝ) := by
    have hpowers : (18143/100000 : ℝ)^4555 ≤ (6301857245136871/12500000000000000000 : ℝ)^1024 := by
      have hnat : (18143 : ℕ)^4555*12500000000000000000^1024 ≤ 6301857245136871^1024*100000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18143 100000 6301857245136871 12500000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18143/100000 : ℝ)) (X := (6301857245136871/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001812876840881021/50000000000000000000 : ℝ) ≤ (1000008150866289/1000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50001812876840881021/50000000000000000000 : ℝ)^1024 ≤ (1000008150866289/1000000000000000 : ℝ)^4555 := by
      have hnat : (50001812876840881021 : ℕ)^1024*1000000000000000^4555 ≤ 1000008150866289^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001812876840881021 50000000000000000000 1000008150866289 1000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000008150866289/1000000000000000 : ℝ)) (X := (50001812876840881021/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052227734801975989/100000000000000000000 : ℝ) ≤ (100011738831491/100000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (100052227734801975989/100000000000000000000 : ℝ)^1024 ≤ (100011738831491/100000000000000 : ℝ)^4555 := by
      have hnat : (100052227734801975989 : ℕ)^1024*100000000000000^4555 ≤ 100011738831491^4555*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052227734801975989 100000000000000000000 100011738831491 100000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100011738831491/100000000000000 : ℝ)) (X := (100052227734801975989/100000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6256301857245136871/6250000000000000000 : ℝ) ≤ (1000226625763531/1000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (6256301857245136871/6250000000000000000 : ℝ)^1024 ≤ (1000226625763531/1000000000000000 : ℝ)^4555 := by
      have hnat : (6256301857245136871 : ℕ)^1024*1000000000000000^4555 ≤ 1000226625763531^4555*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6256301857245136871 6250000000000000000 1000226625763531 1000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000226625763531/1000000000000000 : ℝ)) (X := (6256301857245136871/6250000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1812876840881021/100000000000000000000 : ℝ) ≤ ((4775100469616293253/4776000000000000000 : ℝ)+2*(109237448621/95520000000000 : ℝ)*(8591/100000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (4775100469616293253/4776000000000000000 : ℝ)+2*(109237448621/95520000000000 : ℝ)*(8591/100000 : ℝ)=(1000008150866289/1000000000000000 : ℝ) by norm_num, show 1+2*(1812876840881021/100000000000000000000 : ℝ)=(50001812876840881021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6301857245136871/12500000000000000000 : ℝ)+(1812876840881021/100000000000000000000 : ℝ) ≤ ((4775100469616293253/4776000000000000000 : ℝ)+(109237448621/95520000000000 : ℝ)*((18143/100000 : ℝ)+(8591/100000 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (4775100469616293253/4776000000000000000 : ℝ)+(109237448621/95520000000000 : ℝ)*((18143/100000 : ℝ)+(8591/100000 : ℝ))=(100011738831491/100000000000000 : ℝ) by norm_num, show 1+(6301857245136871/12500000000000000000 : ℝ)+(1812876840881021/100000000000000000000 : ℝ)=(100052227734801975989/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6301857245136871/12500000000000000000 : ℝ) ≤ ((4775100469616293253/4776000000000000000 : ℝ)+2*(109237448621/95520000000000 : ℝ)*(18143/100000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (4775100469616293253/4776000000000000000 : ℝ)+2*(109237448621/95520000000000 : ℝ)*(18143/100000 : ℝ)=(1000226625763531/1000000000000000 : ℝ) by norm_num, show 1+2*(6301857245136871/12500000000000000000 : ℝ)=(6256301857245136871/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4775100469616293253/4776000000000000000 : ℝ)*(X 1 0+X 2 0)+(109237448621/95520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (8591/100000 : ℝ)) (hi := (18143/100000 : ℝ)) (c := (4775100469616293253/4776000000000000000 : ℝ)) (alpha := (109237448621/95520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4775100469616293253/4776000000000000000 : ℝ)*(X 0 1+X 2 1)+(109237448621/95520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (8591/100000 : ℝ)) (hi := (18143/100000 : ℝ)) (c := (4775100469616293253/4776000000000000000 : ℝ)) (alpha := (109237448621/95520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4775100469616293253/4776000000000000000 : ℝ)*(X 0 2+X 1 2)+(109237448621/95520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (8591/100000 : ℝ)) (hi := (18143/100000 : ℝ)) (c := (4775100469616293253/4776000000000000000 : ℝ)) (alpha := (109237448621/95520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-919179973/5000000000 : ℝ)*X 0 0+(1090475913/2000000000 : ℝ)*X 0 1+(2599625199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267809219/500000000 : ℝ)*X 1 0+(-984266623/5000000000 : ℝ)*X 1 1+(5199250793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535618509/1000000000 : ℝ)*X 2 0+(649906297/1250000000 : ℝ)*X 2 1+(-1968532849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2129631241/5000000000 : ℝ)*X 0 0+(994227497/2500000000 : ℝ)*X 0 1+(4558191139/10000000000 : ℝ)*X 0 2+(2129631241/5000000000 : ℝ)*X 1 0+(994227497/2500000000 : ℝ)*X 1 1+(4558191139/10000000000 : ℝ)*X 1 2+(2129631241/5000000000 : ℝ)*X 2 0+(994227497/2500000000 : ℝ)*X 2 1+(4558191139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-459601837/2500000000 : ℝ)*X 0 0+(1040161297/2000000000 : ℝ)*X 0 1+(85168907/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644774071/5000000000 : ℝ)*X 1 0+(-1716973439/10000000000 : ℝ)*X 1 1+(5450810001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644773919/5000000000 : ℝ)*X 2 0+(5450810141/10000000000 : ℝ)*X 2 1+(-53655427/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2129686143/5000000000 : ℝ)*X 0 0+(4554617039/10000000000 : ℝ)*X 0 1+(3980515333/10000000000 : ℝ)*X 0 2+(2129686143/5000000000 : ℝ)*X 1 0+(4554617039/10000000000 : ℝ)*X 1 1+(3980515333/10000000000 : ℝ)*X 1 2+(2129686143/5000000000 : ℝ)*X 2 0+(4554617039/10000000000 : ℝ)*X 2 1+(3980515333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (623429001798343665780332757/79600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (413704609/25000000000000 : ℝ)*(base19) + (376003073/20000000000000 : ℝ)*(base23) + (126253013/100000000000000 : ℝ)*(upper3) + (79936659/50000000000000 : ℝ)*(upper4) + (169132571/50000000000000 : ℝ)*(upper5) + (2835486391641169/100000000000000 : ℝ)*(major0) + (2835486391641169/100000000000000 : ℝ)*(major1) + (2835486391641169/100000000000000 : ℝ)*(major2) + (3950573996608071/100000000000000 : ℝ)*(sp0) + (79012102133877/2000000000000 : ℝ)*(sp1) + (98765122037423/2500000000000 : ℝ)*(sp2) + (860175921143547/50000000000000 : ℝ)*(sp3) + (16382452107/50000000000000 : ℝ)*(sp4) + (1391841553/10000000000000 : ℝ)*(sp7) + (1720365760702623/100000000000000 : ℝ)*(f.failure) + (790121352302457/20000000000000 : ℝ)*(f.sum) + (11881418836051/4776000000000000000000000000 : ℝ)*base66 + (1578238024579339081/159200000000000000000000000000000 : ℝ)*base68 + (267402816091860919/159200000000000000000000000000000 : ℝ)*base69 + (374234603586539081/159200000000000000000000000000000 : ℝ)*base72 + (11418400881043/4776000000000000000000000000 : ℝ)*base74 + (368635972292139081/159200000000000000000000000000000 : ℝ)*base76 + (1484313883746539081/159200000000000000000000000000000 : ℝ)*base78 + (882461449032660919/159200000000000000000000000000000 : ℝ)*base79 + (27844416651427/4776000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (52558747/10000000000000000000000 : ℝ)*base90 + (52558747/10000000000000000000000 : ℝ)*base92 + (52558747/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (333011179740684716439520679/39800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (428426969/25000000000000 : ℝ)*(base19) + (142763343/10000000000000 : ℝ)*(base23) + (14687977/10000000000000 : ℝ)*(upper3) + (40587/625000000000 : ℝ)*(lower4) + (219736767/100000000000000 : ℝ)*(upper5) + (1435448503803643/50000000000000 : ℝ)*(major0) + (1435448503803643/50000000000000 : ℝ)*(major1) + (1435448503803643/50000000000000 : ℝ)*(major2) + (24404543759/100000000000000 : ℝ)*(sp1) + (4742338401/25000000000000 : ℝ)*(sp2) + (399994340370077/10000000000000 : ℝ)*(sp4) + (799983457089827/20000000000000 : ℝ)*(sp5) + (499990375839217/12500000000000 : ℝ)*(sp6) + (1741850332609963/100000000000000 : ℝ)*(sp7) + (1741850332609963/100000000000000 : ℝ)*(f.failure) + (399994340370077/10000000000000 : ℝ)*(f.sum) + (6992920356599/2388000000000000000000000000 : ℝ)*base65 + (176447408246243107/79600000000000000000000000000000 : ℝ)*base68 + (153351200153443107/79600000000000000000000000000000 : ℝ)*base70 + (286396818725843107/79600000000000000000000000000000 : ℝ)*base72 + (884363589961/2388000000000000000000000000 : ℝ)*base74 + (553702720111356893/79600000000000000000000000000000 : ℝ)*base75 + (586427171550643107/79600000000000000000000000000000 : ℝ)*base78 + (322544420725756893/79600000000000000000000000000000 : ℝ)*base79 + (3477668010851/2388000000000000000000000000 : ℝ)*base81 + (28413993/10000000000000000000000 : ℝ)*base89 + (28413993/10000000000000000000000 : ℝ)*base91 + (28413993/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1530_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18143/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8591/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3983/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1530_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1530_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3983/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1530_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1530_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1530_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10571/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3983/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1530_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
