-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1067_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:07:46.548882+00:00
-- url     : https://prove2.me/submissions/9a069817-7fbf-4a3d-81fe-3a00b5ec9ab3

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
theorem support_rectangle_w1067_s9_0 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336242863/2500000000 : ℝ)*x 0 + (329030979/625000000 : ℝ)*x 1 + (-1134570843/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336242863/2500000000 : ℝ)^2065 ≤ (43476363066671/100000000000000 : ℝ)^1553 := by
    have hnat : (1336242863 : ℕ)^2065*100000000000000^1553 ≤ 43476363066671^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336242863 2500000000 43476363066671 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329030979/625000000 : ℝ)^2065 ≤ (42608125103139/100000000000000 : ℝ)^1553 := by
    have hnat : (329030979 : ℕ)^2065*100000000000000^1553 ≤ 42608125103139^1553*625000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329030979 625000000 42608125103139 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134570843/5000000000 : ℝ)^2065 ≤ (13915511815531/100000000000000 : ℝ)^1553 := by
    have hnat : (1134570843 : ℕ)^2065*100000000000000^1553 ≤ 13915511815531^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134570843 5000000000 13915511815531 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336242863/2500000000 : ℝ), (329030979/625000000 : ℝ), (-1134570843/5000000000 : ℝ)] ![(43476363066671/100000000000000 : ℝ), (42608125103139/100000000000000 : ℝ), (13915511815531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336242863/2500000000 : ℝ)|^2065 ≤ (43476363066671/100000000000000 : ℝ)^1553
        have hw : |(1336242863/2500000000 : ℝ)|=(1336242863/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(329030979/625000000 : ℝ)|^2065 ≤ (42608125103139/100000000000000 : ℝ)^1553
        have hw : |(329030979/625000000 : ℝ)|=(329030979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134570843/5000000000 : ℝ)|^2065 ≤ (13915511815531/100000000000000 : ℝ)^1553
        have hw : |(-1134570843/5000000000 : ℝ)|=(1134570843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s9_1 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101640421/5000000000 : ℝ)*x 0 + (5264820671/10000000000 : ℝ)*x 1 + (674248663/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101640421/5000000000 : ℝ)^2065 ≤ (2676209947009/20000000000000 : ℝ)^1553 := by
    have hnat : (1101640421 : ℕ)^2065*20000000000000^1553 ≤ 2676209947009^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101640421 5000000000 2676209947009 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264820671/10000000000 : ℝ)^2065 ≤ (21305811396857/50000000000000 : ℝ)^1553 := by
    have hnat : (5264820671 : ℕ)^2065*50000000000000^1553 ≤ 21305811396857^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264820671 10000000000 21305811396857 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674248663/1250000000 : ℝ)^2065 ≤ (5500915932823/12500000000000 : ℝ)^1553 := by
    have hnat : (674248663 : ℕ)^2065*12500000000000^1553 ≤ 5500915932823^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674248663 1250000000 5500915932823 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101640421/5000000000 : ℝ), (5264820671/10000000000 : ℝ), (674248663/1250000000 : ℝ)] ![(2676209947009/20000000000000 : ℝ), (21305811396857/50000000000000 : ℝ), (5500915932823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101640421/5000000000 : ℝ)|^2065 ≤ (2676209947009/20000000000000 : ℝ)^1553
        have hw : |(-1101640421/5000000000 : ℝ)|=(1101640421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264820671/10000000000 : ℝ)|^2065 ≤ (21305811396857/50000000000000 : ℝ)^1553
        have hw : |(5264820671/10000000000 : ℝ)|=(5264820671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674248663/1250000000 : ℝ)|^2065 ≤ (5500915932823/12500000000000 : ℝ)^1553
        have hw : |(674248663/1250000000 : ℝ)|=(674248663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s9_2 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312269713/10000000000 : ℝ)*x 0 + (-2139648083/10000000000 : ℝ)*x 1 + (2696994631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312269713/10000000000 : ℝ)^2065 ≤ (43123026618537/100000000000000 : ℝ)^1553 := by
    have hnat : (5312269713 : ℕ)^2065*100000000000000^1553 ≤ 43123026618537^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312269713 10000000000 43123026618537 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2139648083/10000000000 : ℝ)^2065 ≤ (3217411591067/25000000000000 : ℝ)^1553 := by
    have hnat : (2139648083 : ℕ)^2065*25000000000000^1553 ≤ 3217411591067^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139648083 10000000000 3217411591067 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696994631/5000000000 : ℝ)^2065 ≤ (44007327006953/100000000000000 : ℝ)^1553 := by
    have hnat : (2696994631 : ℕ)^2065*100000000000000^1553 ≤ 44007327006953^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696994631 5000000000 44007327006953 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312269713/10000000000 : ℝ), (-2139648083/10000000000 : ℝ), (2696994631/5000000000 : ℝ)] ![(43123026618537/100000000000000 : ℝ), (3217411591067/25000000000000 : ℝ), (44007327006953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312269713/10000000000 : ℝ)|^2065 ≤ (43123026618537/100000000000000 : ℝ)^1553
        have hw : |(5312269713/10000000000 : ℝ)|=(5312269713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2139648083/10000000000 : ℝ)|^2065 ≤ (3217411591067/25000000000000 : ℝ)^1553
        have hw : |(-2139648083/10000000000 : ℝ)|=(2139648083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696994631/5000000000 : ℝ)|^2065 ≤ (44007327006953/100000000000000 : ℝ)^1553
        have hw : |(2696994631/5000000000 : ℝ)|=(2696994631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s9_3 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312269729/10000000000 : ℝ)*x 0 + (2696994627/5000000000 : ℝ)*x 1 + (-2139648071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312269729/10000000000 : ℝ)^2065 ≤ (43123026791239/100000000000000 : ℝ)^1553 := by
    have hnat : (5312269729 : ℕ)^2065*100000000000000^1553 ≤ 43123026791239^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312269729 10000000000 43123026791239 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696994627/5000000000 : ℝ)^2065 ≤ (44007326920167/100000000000000 : ℝ)^1553 := by
    have hnat : (2696994627 : ℕ)^2065*100000000000000^1553 ≤ 44007326920167^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696994627 5000000000 44007326920167 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139648071/10000000000 : ℝ)^2065 ≤ (6434823134147/50000000000000 : ℝ)^1553 := by
    have hnat : (2139648071 : ℕ)^2065*50000000000000^1553 ≤ 6434823134147^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139648071 10000000000 6434823134147 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312269729/10000000000 : ℝ), (2696994627/5000000000 : ℝ), (-2139648071/10000000000 : ℝ)] ![(43123026791239/100000000000000 : ℝ), (44007326920167/100000000000000 : ℝ), (6434823134147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312269729/10000000000 : ℝ)|^2065 ≤ (43123026791239/100000000000000 : ℝ)^1553
        have hw : |(5312269729/10000000000 : ℝ)|=(5312269729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696994627/5000000000 : ℝ)|^2065 ≤ (44007326920167/100000000000000 : ℝ)^1553
        have hw : |(2696994627/5000000000 : ℝ)|=(2696994627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139648071/10000000000 : ℝ)|^2065 ≤ (6434823134147/50000000000000 : ℝ)^1553
        have hw : |(-2139648071/10000000000 : ℝ)|=(2139648071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_s9_4 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (875071917/2000000000 : ℝ)*x 0 + (281489127/625000000 : ℝ)*x 1 + (4250623409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875071917/2000000000 : ℝ)^2065 ≤ (33316667567931/100000000000000 : ℝ)^1553 := by
    have hnat : (875071917 : ℕ)^2065*100000000000000^1553 ≤ 33316667567931^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875071917 2000000000 33316667567931 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281489127/625000000 : ℝ)^2065 ≤ (34623649158217/100000000000000 : ℝ)^1553 := by
    have hnat : (281489127 : ℕ)^2065*100000000000000^1553 ≤ 34623649158217^1553*625000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281489127 625000000 34623649158217 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250623409/10000000000 : ℝ)^2065 ≤ (16029841633217/50000000000000 : ℝ)^1553 := by
    have hnat : (4250623409 : ℕ)^2065*50000000000000^1553 ≤ 16029841633217^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250623409 10000000000 16029841633217 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875071917/2000000000 : ℝ), (281489127/625000000 : ℝ), (4250623409/10000000000 : ℝ)] ![(33316667567931/100000000000000 : ℝ), (34623649158217/100000000000000 : ℝ), (16029841633217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875071917/2000000000 : ℝ)|^2065 ≤ (33316667567931/100000000000000 : ℝ)^1553
        have hw : |(875071917/2000000000 : ℝ)|=(875071917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281489127/625000000 : ℝ)|^2065 ≤ (34623649158217/100000000000000 : ℝ)^1553
        have hw : |(281489127/625000000 : ℝ)|=(281489127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250623409/10000000000 : ℝ)|^2065 ≤ (16029841633217/50000000000000 : ℝ)^1553
        have hw : |(4250623409/10000000000 : ℝ)|=(4250623409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1067_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11253/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11253/100000 : ℝ) ^ (8259/2048 : ℝ) ≤ (3732292528793319/25000000000000000000 : ℝ) := by
    have hpowers : (11253/100000 : ℝ)^8259 ≤ (3732292528793319/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11253 : ℕ)^8259*25000000000000000000^2048 ≤ 3732292528793319^2048*100000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11253 100000 3732292528793319 25000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11253/100000 : ℝ)) (X := (3732292528793319/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3501/25000 : ℝ) ^ (8259/2048 : ℝ) ≤ (18032177911842857/50000000000000000000 : ℝ) := by
    have hpowers : (3501/25000 : ℝ)^8259 ≤ (18032177911842857/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3501 : ℕ)^8259*50000000000000000000^2048 ≤ 18032177911842857^2048*25000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3501 25000 18032177911842857 50000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3501/25000 : ℝ)) (X := (18032177911842857/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503732292528793319/12500000000000000000 : ℝ) ≤ (10000740319852241/10000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (12503732292528793319/12500000000000000000 : ℝ)^2048 ≤ (10000740319852241/10000000000000000 : ℝ)^8259 := by
      have hnat : (12503732292528793319 : ℕ)^2048*10000000000000000^8259 ≤ 10000740319852241^8259*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503732292528793319 12500000000000000000 10000740319852241 10000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000740319852241/10000000000000000 : ℝ)) (X := (12503732292528793319/12500000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005099352593885899/10000000000000000000 : ℝ) ≤ (1250158031726711/1250000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (10005099352593885899/10000000000000000000 : ℝ)^2048 ≤ (1250158031726711/1250000000000000 : ℝ)^8259 := by
      have hnat : (10005099352593885899 : ℕ)^2048*1250000000000000^8259 ≤ 1250158031726711^8259*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005099352593885899 10000000000000000000 1250158031726711 1250000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250158031726711/1250000000000000 : ℝ)) (X := (10005099352593885899/10000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018032177911842857/25000000000000000000 : ℝ) ≤ (2000357637555027/2000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (25018032177911842857/25000000000000000000 : ℝ)^2048 ≤ (2000357637555027/2000000000000000 : ℝ)^8259 := by
      have hnat : (25018032177911842857 : ℕ)^2048*2000000000000000^8259 ≤ 2000357637555027^8259*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018032177911842857 25000000000000000000 2000357637555027 2000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000357637555027/2000000000000000 : ℝ)) (X := (25018032177911842857/25000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3732292528793319/25000000000000000000 : ℝ) ≤ ((9166748320725729603/9170000000000000000 : ℝ)+2*(523933961447/275100000000000 : ℝ)*(11253/100000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (9166748320725729603/9170000000000000000 : ℝ)+2*(523933961447/275100000000000 : ℝ)*(11253/100000 : ℝ)=(10000740319852241/10000000000000000 : ℝ) by norm_num, show 1+2*(3732292528793319/25000000000000000000 : ℝ)=(12503732292528793319/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18032177911842857/50000000000000000000 : ℝ)+(3732292528793319/25000000000000000000 : ℝ) ≤ ((9166748320725729603/9170000000000000000 : ℝ)+(523933961447/275100000000000 : ℝ)*((3501/25000 : ℝ)+(11253/100000 : ℝ)))^(8259/2048 : ℝ) := by
    rw [show (9166748320725729603/9170000000000000000 : ℝ)+(523933961447/275100000000000 : ℝ)*((3501/25000 : ℝ)+(11253/100000 : ℝ))=(1250158031726711/1250000000000000 : ℝ) by norm_num, show 1+(18032177911842857/50000000000000000000 : ℝ)+(3732292528793319/25000000000000000000 : ℝ)=(10005099352593885899/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18032177911842857/50000000000000000000 : ℝ) ≤ ((9166748320725729603/9170000000000000000 : ℝ)+2*(523933961447/275100000000000 : ℝ)*(3501/25000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (9166748320725729603/9170000000000000000 : ℝ)+2*(523933961447/275100000000000 : ℝ)*(3501/25000 : ℝ)=(2000357637555027/2000000000000000 : ℝ) by norm_num, show 1+2*(18032177911842857/50000000000000000000 : ℝ)=(25018032177911842857/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9166748320725729603/9170000000000000000 : ℝ)*(X 1 0+X 2 0)+(523933961447/275100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (9166748320725729603/9170000000000000000 : ℝ)) (alpha := (523933961447/275100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9166748320725729603/9170000000000000000 : ℝ)*(X 0 1+X 2 1)+(523933961447/275100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (9166748320725729603/9170000000000000000 : ℝ)) (alpha := (523933961447/275100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9166748320725729603/9170000000000000000 : ℝ)*(X 0 2+X 1 2)+(523933961447/275100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (9166748320725729603/9170000000000000000 : ℝ)) (alpha := (523933961447/275100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1336242863/2500000000 : ℝ)*X 2 0+(329030979/625000000 : ℝ)*X 2 1+(-1134570843/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1101640421/5000000000 : ℝ)*X 0 0+(5264820671/10000000000 : ℝ)*X 0 1+(674248663/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312269713/10000000000 : ℝ)*X 1 0+(-2139648083/10000000000 : ℝ)*X 1 1+(2696994631/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312269729/10000000000 : ℝ)*X 2 0+(2696994627/5000000000 : ℝ)*X 2 1+(-2139648071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((875071917/2000000000 : ℝ)*X 0 0+(281489127/625000000 : ℝ)*X 0 1+(4250623409/10000000000 : ℝ)*X 0 2+(875071917/2000000000 : ℝ)*X 1 0+(281489127/625000000 : ℝ)*X 1 1+(4250623409/10000000000 : ℝ)*X 1 2+(875071917/2000000000 : ℝ)*X 2 0+(281489127/625000000 : ℝ)*X 2 1+(4250623409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24560422331262098478117/4585000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184158939/20000000000000 : ℝ)*(base19) + (537563429/50000000000000 : ℝ)*(base23) + (64283297/20000000000000 : ℝ)*(lower1) + (70187003/100000000000000 : ℝ)*(upper3) + (3189819/5000000000000 : ℝ)*(lower4) + (3326659/2500000000000 : ℝ)*(upper5) + (45668696471127/781250000000 : ℝ)*(major0) + (45668696471127/781250000000 : ℝ)*(major1) + (45668696471127/781250000000 : ℝ)*(major2) + (443566257/25000000000000 : ℝ)*(sp0) + (7741794367858373/100000000000000 : ℝ)*(sp1) + (3870896723531839/50000000000000 : ℝ)*(sp2) + (3870895759233243/50000000000000 : ℝ)*(sp3) + (1974695875096899/50000000000000 : ℝ)*(sp4) + (1974695875096899/50000000000000 : ℝ)*(f.failure) + (7741794367858373/100000000000000 : ℝ)*(f.sum) + (1671210837949/1146250000000000000000000000 : ℝ)*base66 + (227719677680914213/14328125000000000000000000000000 : ℝ)*base68 + (16009972951900353/3582031250000000000000000000000 : ℝ)*base69 + (443637113135183669/7164062500000000000000000000000 : ℝ)*base72 + (7879408697563/2292500000000000000000000000 : ℝ)*base74 + (8496326873167011/1791015625000000000000000000000 : ℝ)*base76 + (17735686415503831/7164062500000000000000000000000 : ℝ)*base77 + (211638253679066331/7164062500000000000000000000000 : ℝ)*base79 + (1212813877091/1146250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (9384423/1250000000000000000000 : ℝ)*base90 + (9384423/1250000000000000000000 : ℝ)*base92 + (9384423/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1067_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1067_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1067_box_0 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2073849799/10000000000 : ℝ)*x 0 + (2688676993/5000000000 : ℝ)*x 1 + (5377354407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2073849799/10000000000 : ℝ)^2065 ≤ (1543261030753/12500000000000 : ℝ)^1553 := by
    have hnat : (2073849799 : ℕ)^2065*12500000000000^1553 ≤ 1543261030753^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073849799 10000000000 1543261030753 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688676993/5000000000 : ℝ)^2065 ≤ (1369592299737/3125000000000 : ℝ)^1553 := by
    have hnat : (2688676993 : ℕ)^2065*3125000000000^1553 ≤ 1369592299737^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688676993 5000000000 1369592299737 3125000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377354407/10000000000 : ℝ)^2065 ≤ (43826958154089/100000000000000 : ℝ)^1553 := by
    have hnat : (5377354407 : ℕ)^2065*100000000000000^1553 ≤ 43826958154089^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377354407 10000000000 43826958154089 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2073849799/10000000000 : ℝ), (2688676993/5000000000 : ℝ), (5377354407/10000000000 : ℝ)] ![(1543261030753/12500000000000 : ℝ), (1369592299737/3125000000000 : ℝ), (43826958154089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2073849799/10000000000 : ℝ)|^2065 ≤ (1543261030753/12500000000000 : ℝ)^1553
        have hw : |(-2073849799/10000000000 : ℝ)|=(2073849799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688676993/5000000000 : ℝ)|^2065 ≤ (1369592299737/3125000000000 : ℝ)^1553
        have hw : |(2688676993/5000000000 : ℝ)|=(2688676993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377354407/10000000000 : ℝ)|^2065 ≤ (43826958154089/100000000000000 : ℝ)^1553
        have hw : |(5377354407/10000000000 : ℝ)|=(5377354407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_1 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5295213221/10000000000 : ℝ)*x 0 + (-437009953/2000000000 : ℝ)*x 1 + (5377354173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295213221/10000000000 : ℝ)^2065 ≤ (5367377293297/12500000000000 : ℝ)^1553 := by
    have hnat : (5295213221 : ℕ)^2065*12500000000000^1553 ≤ 5367377293297^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295213221 10000000000 5367377293297 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437009953/2000000000 : ℝ)^2065 ≤ (13234026026111/100000000000000 : ℝ)^1553 := by
    have hnat : (437009953 : ℕ)^2065*100000000000000^1553 ≤ 13234026026111^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437009953 2000000000 13234026026111 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377354173/10000000000 : ℝ)^2065 ≤ (547836945227/1250000000000 : ℝ)^1553 := by
    have hnat : (5377354173 : ℕ)^2065*1250000000000^1553 ≤ 547836945227^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377354173 10000000000 547836945227 1250000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295213221/10000000000 : ℝ), (-437009953/2000000000 : ℝ), (5377354173/10000000000 : ℝ)] ![(5367377293297/12500000000000 : ℝ), (13234026026111/100000000000000 : ℝ), (547836945227/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295213221/10000000000 : ℝ)|^2065 ≤ (5367377293297/12500000000000 : ℝ)^1553
        have hw : |(5295213221/10000000000 : ℝ)|=(5295213221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437009953/2000000000 : ℝ)|^2065 ≤ (13234026026111/100000000000000 : ℝ)^1553
        have hw : |(-437009953/2000000000 : ℝ)|=(437009953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377354173/10000000000 : ℝ)|^2065 ≤ (547836945227/1250000000000 : ℝ)^1553
        have hw : |(5377354173/10000000000 : ℝ)|=(5377354173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_2 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2647606647/5000000000 : ℝ)*x 0 + (268867709/500000000 : ℝ)*x 1 + (-273131207/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647606647/5000000000 : ℝ)^2065 ≤ (8587803826699/20000000000000 : ℝ)^1553 := by
    have hnat : (2647606647 : ℕ)^2065*20000000000000^1553 ≤ 8587803826699^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647606647 5000000000 8587803826699 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (268867709/500000000 : ℝ)^2065 ≤ (43826955694021/100000000000000 : ℝ)^1553 := by
    have hnat : (268867709 : ℕ)^2065*100000000000000^1553 ≤ 43826955694021^1553*500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268867709 500000000 43826955694021 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273131207/1250000000 : ℝ)^2065 ≤ (13234025148291/100000000000000 : ℝ)^1553 := by
    have hnat : (273131207 : ℕ)^2065*100000000000000^1553 ≤ 13234025148291^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273131207 1250000000 13234025148291 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647606647/5000000000 : ℝ), (268867709/500000000 : ℝ), (-273131207/1250000000 : ℝ)] ![(8587803826699/20000000000000 : ℝ), (43826955694021/100000000000000 : ℝ), (13234025148291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647606647/5000000000 : ℝ)|^2065 ≤ (8587803826699/20000000000000 : ℝ)^1553
        have hw : |(2647606647/5000000000 : ℝ)|=(2647606647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(268867709/500000000 : ℝ)|^2065 ≤ (43826955694021/100000000000000 : ℝ)^1553
        have hw : |(268867709/500000000 : ℝ)|=(268867709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273131207/1250000000 : ℝ)|^2065 ≤ (13234025148291/100000000000000 : ℝ)^1553
        have hw : |(-273131207/1250000000 : ℝ)|=(273131207/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_3 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1120931763/2500000000 : ℝ)*x 0 + (864664521/2000000000 : ℝ)*x 1 + (540415311/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120931763/2500000000 : ℝ)^2065 ≤ (34418346802907/100000000000000 : ℝ)^1553 := by
    have hnat : (1120931763 : ℕ)^2065*100000000000000^1553 ≤ 34418346802907^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120931763 2500000000 34418346802907 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (864664521/2000000000 : ℝ)^2065 ≤ (32790827179037/100000000000000 : ℝ)^1553 := by
    have hnat : (864664521 : ℕ)^2065*100000000000000^1553 ≤ 32790827179037^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864664521 2000000000 32790827179037 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540415311/1250000000 : ℝ)^2065 ≤ (32790825999071/100000000000000 : ℝ)^1553 := by
    have hnat : (540415311 : ℕ)^2065*100000000000000^1553 ≤ 32790825999071^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540415311 1250000000 32790825999071 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120931763/2500000000 : ℝ), (864664521/2000000000 : ℝ), (540415311/1250000000 : ℝ)] ![(34418346802907/100000000000000 : ℝ), (32790827179037/100000000000000 : ℝ), (32790825999071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120931763/2500000000 : ℝ)|^2065 ≤ (34418346802907/100000000000000 : ℝ)^1553
        have hw : |(1120931763/2500000000 : ℝ)|=(1120931763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(864664521/2000000000 : ℝ)|^2065 ≤ (32790827179037/100000000000000 : ℝ)^1553
        have hw : |(864664521/2000000000 : ℝ)|=(864664521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540415311/1250000000 : ℝ)|^2065 ≤ (32790825999071/100000000000000 : ℝ)^1553
        have hw : |(540415311/1250000000 : ℝ)|=(540415311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_4 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2334095373/10000000000 : ℝ)*x 0 + (5280104067/10000000000 : ℝ)*x 1 + (5280103209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2334095373/10000000000 : ℝ)^2065 ≤ (7223823219641/50000000000000 : ℝ)^1553 := by
    have hnat : (2334095373 : ℕ)^2065*50000000000000^1553 ≤ 7223823219641^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2334095373 10000000000 7223823219641 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280104067/10000000000 : ℝ)^2065 ≤ (10694045349369/25000000000000 : ℝ)^1553 := by
    have hnat : (5280104067 : ℕ)^2065*25000000000000^1553 ≤ 10694045349369^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280104067 10000000000 10694045349369 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280103209/10000000000 : ℝ)^2065 ≤ (855523443097/2000000000000 : ℝ)^1553 := by
    have hnat : (5280103209 : ℕ)^2065*2000000000000^1553 ≤ 855523443097^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280103209 10000000000 855523443097 2000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2334095373/10000000000 : ℝ), (5280104067/10000000000 : ℝ), (5280103209/10000000000 : ℝ)] ![(7223823219641/50000000000000 : ℝ), (10694045349369/25000000000000 : ℝ), (855523443097/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2334095373/10000000000 : ℝ)|^2065 ≤ (7223823219641/50000000000000 : ℝ)^1553
        have hw : |(-2334095373/10000000000 : ℝ)|=(2334095373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280104067/10000000000 : ℝ)|^2065 ≤ (10694045349369/25000000000000 : ℝ)^1553
        have hw : |(5280104067/10000000000 : ℝ)|=(5280104067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280103209/10000000000 : ℝ)|^2065 ≤ (855523443097/2000000000000 : ℝ)^1553
        have hw : |(5280103209/10000000000 : ℝ)|=(5280103209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_5 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5364038097/10000000000 : ℝ)*x 0 + (-1111536629/5000000000 : ℝ)*x 1 + (13200259/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364038097/10000000000 : ℝ)^2065 ≤ (21841352096419/50000000000000 : ℝ)^1553 := by
    have hnat : (5364038097 : ℕ)^2065*50000000000000^1553 ≤ 21841352096419^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364038097 10000000000 21841352096419 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111536629/5000000000 : ℝ)^2065 ≤ (13541119417159/100000000000000 : ℝ)^1553 := by
    have hnat : (1111536629 : ℕ)^2065*100000000000000^1553 ≤ 13541119417159^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111536629 5000000000 13541119417159 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13200259/25000000 : ℝ)^2065 ≤ (1336755511463/3125000000000 : ℝ)^1553 := by
    have hnat : (13200259 : ℕ)^2065*3125000000000^1553 ≤ 1336755511463^1553*25000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13200259 25000000 1336755511463 3125000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364038097/10000000000 : ℝ), (-1111536629/5000000000 : ℝ), (13200259/25000000 : ℝ)] ![(21841352096419/50000000000000 : ℝ), (13541119417159/100000000000000 : ℝ), (1336755511463/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364038097/10000000000 : ℝ)|^2065 ≤ (21841352096419/50000000000000 : ℝ)^1553
        have hw : |(5364038097/10000000000 : ℝ)|=(5364038097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1111536629/5000000000 : ℝ)|^2065 ≤ (13541119417159/100000000000000 : ℝ)^1553
        have hw : |(-1111536629/5000000000 : ℝ)|=(1111536629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13200259/25000000 : ℝ)|^2065 ≤ (1336755511463/3125000000000 : ℝ)^1553
        have hw : |(13200259/25000000 : ℝ)|=(13200259/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_6 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214561493/400000000 : ℝ)*x 0 + (660013063/1250000000 : ℝ)*x 1 + (-2223073089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214561493/400000000 : ℝ)^2065 ≤ (10920673958319/25000000000000 : ℝ)^1553 := by
    have hnat : (214561493 : ℕ)^2065*25000000000000^1553 ≤ 10920673958319^1553*400000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214561493 400000000 10920673958319 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660013063/1250000000 : ℝ)^2065 ≤ (5347023263121/12500000000000 : ℝ)^1553 := by
    have hnat : (660013063 : ℕ)^2065*12500000000000^1553 ≤ 5347023263121^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660013063 1250000000 5347023263121 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2223073089/10000000000 : ℝ)^2065 ≤ (13541118048371/100000000000000 : ℝ)^1553 := by
    have hnat : (2223073089 : ℕ)^2065*100000000000000^1553 ≤ 13541118048371^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223073089 10000000000 13541118048371 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214561493/400000000 : ℝ), (660013063/1250000000 : ℝ), (-2223073089/10000000000 : ℝ)] ![(10920673958319/25000000000000 : ℝ), (5347023263121/12500000000000 : ℝ), (13541118048371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214561493/400000000 : ℝ)|^2065 ≤ (10920673958319/25000000000000 : ℝ)^1553
        have hw : |(214561493/400000000 : ℝ)|=(214561493/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660013063/1250000000 : ℝ)|^2065 ≤ (5347023263121/12500000000000 : ℝ)^1553
        have hw : |(660013063/1250000000 : ℝ)|=(660013063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2223073089/10000000000 : ℝ)|^2065 ≤ (13541118048371/100000000000000 : ℝ)^1553
        have hw : |(-2223073089/10000000000 : ℝ)|=(2223073089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_7 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4266643309/10000000000 : ℝ)*x 0 + (886368599/2000000000 : ℝ)*x 1 + (4431842943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4266643309/10000000000 : ℝ)^2065 ≤ (16110222836637/50000000000000 : ℝ)^1553 := by
    have hnat : (4266643309 : ℕ)^2065*50000000000000^1553 ≤ 16110222836637^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4266643309 10000000000 16110222836637 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (886368599/2000000000 : ℝ)^2065 ≤ (33889777417221/100000000000000 : ℝ)^1553 := by
    have hnat : (886368599 : ℕ)^2065*100000000000000^1553 ≤ 33889777417221^1553*2000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886368599 2000000000 33889777417221 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4431842943/10000000000 : ℝ)^2065 ≤ (4236222111061/12500000000000 : ℝ)^1553 := by
    have hnat : (4431842943 : ℕ)^2065*12500000000000^1553 ≤ 4236222111061^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4431842943 10000000000 4236222111061 12500000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4266643309/10000000000 : ℝ), (886368599/2000000000 : ℝ), (4431842943/10000000000 : ℝ)] ![(16110222836637/50000000000000 : ℝ), (33889777417221/100000000000000 : ℝ), (4236222111061/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4266643309/10000000000 : ℝ)|^2065 ≤ (16110222836637/50000000000000 : ℝ)^1553
        have hw : |(4266643309/10000000000 : ℝ)|=(4266643309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(886368599/2000000000 : ℝ)|^2065 ≤ (33889777417221/100000000000000 : ℝ)^1553
        have hw : |(886368599/2000000000 : ℝ)|=(886368599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4431842943/10000000000 : ℝ)|^2065 ≤ (4236222111061/12500000000000 : ℝ)^1553
        have hw : |(4431842943/10000000000 : ℝ)|=(4431842943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_8 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2279765153/10000000000 : ℝ)*x 0 + (5214111403/10000000000 : ℝ)*x 1 + (336684707/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2279765153/10000000000 : ℝ)^2065 ≤ (3500551358431/25000000000000 : ℝ)^1553 := by
    have hnat : (2279765153 : ℕ)^2065*25000000000000^1553 ≤ 3500551358431^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2279765153 10000000000 3500551358431 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214111403/10000000000 : ℝ)^2065 ≤ (1682670314481/4000000000000 : ℝ)^1553 := by
    have hnat : (5214111403 : ℕ)^2065*4000000000000^1553 ≤ 1682670314481^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214111403 10000000000 1682670314481 4000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336684707/625000000 : ℝ)^2065 ≤ (2745689793371/6250000000000 : ℝ)^1553 := by
    have hnat : (336684707 : ℕ)^2065*6250000000000^1553 ≤ 2745689793371^1553*625000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336684707 625000000 2745689793371 6250000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2279765153/10000000000 : ℝ), (5214111403/10000000000 : ℝ), (336684707/625000000 : ℝ)] ![(3500551358431/25000000000000 : ℝ), (1682670314481/4000000000000 : ℝ), (2745689793371/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2279765153/10000000000 : ℝ)|^2065 ≤ (3500551358431/25000000000000 : ℝ)^1553
        have hw : |(-2279765153/10000000000 : ℝ)|=(2279765153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214111403/10000000000 : ℝ)|^2065 ≤ (1682670314481/4000000000000 : ℝ)^1553
        have hw : |(5214111403/10000000000 : ℝ)|=(5214111403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336684707/625000000 : ℝ)|^2065 ≤ (2745689793371/6250000000000 : ℝ)^1553
        have hw : |(336684707/625000000 : ℝ)|=(336684707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_9 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644207471/5000000000 : ℝ)*x 0 + (-218122507/1000000000 : ℝ)*x 1 + (2693477581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644207471/5000000000 : ℝ)^2065 ≤ (171462927173/400000000000 : ℝ)^1553 := by
    have hnat : (2644207471 : ℕ)^2065*400000000000^1553 ≤ 171462927173^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644207471 5000000000 171462927173 400000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (218122507/1000000000 : ℝ)^2065 ≤ (6601616559841/50000000000000 : ℝ)^1553 := by
    have hnat : (218122507 : ℕ)^2065*50000000000000^1553 ≤ 6601616559841^1553*1000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218122507 1000000000 6601616559841 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693477581/5000000000 : ℝ)^2065 ≤ (8786207013477/20000000000000 : ℝ)^1553 := by
    have hnat : (2693477581 : ℕ)^2065*20000000000000^1553 ≤ 8786207013477^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693477581 5000000000 8786207013477 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644207471/5000000000 : ℝ), (-218122507/1000000000 : ℝ), (2693477581/5000000000 : ℝ)] ![(171462927173/400000000000 : ℝ), (6601616559841/50000000000000 : ℝ), (8786207013477/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644207471/5000000000 : ℝ)|^2065 ≤ (171462927173/400000000000 : ℝ)^1553
        have hw : |(2644207471/5000000000 : ℝ)|=(2644207471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-218122507/1000000000 : ℝ)|^2065 ≤ (6601616559841/50000000000000 : ℝ)^1553
        have hw : |(-218122507/1000000000 : ℝ)|=(218122507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693477581/5000000000 : ℝ)|^2065 ≤ (8786207013477/20000000000000 : ℝ)^1553
        have hw : |(2693477581/5000000000 : ℝ)|=(2693477581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_10 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288415017/10000000000 : ℝ)*x 0 + (2693477633/5000000000 : ℝ)*x 1 + (-2181224829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288415017/10000000000 : ℝ)^2065 ≤ (42865732601591/100000000000000 : ℝ)^1553 := by
    have hnat : (5288415017 : ℕ)^2065*100000000000000^1553 ≤ 42865732601591^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288415017 10000000000 42865732601591 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693477633/5000000000 : ℝ)^2065 ≤ (43931036195127/100000000000000 : ℝ)^1553 := by
    have hnat : (2693477633 : ℕ)^2065*100000000000000^1553 ≤ 43931036195127^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693477633 5000000000 43931036195127 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2181224829/10000000000 : ℝ)^2065 ≤ (6601615589967/50000000000000 : ℝ)^1553 := by
    have hnat : (2181224829 : ℕ)^2065*50000000000000^1553 ≤ 6601615589967^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181224829 10000000000 6601615589967 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288415017/10000000000 : ℝ), (2693477633/5000000000 : ℝ), (-2181224829/10000000000 : ℝ)] ![(42865732601591/100000000000000 : ℝ), (43931036195127/100000000000000 : ℝ), (6601615589967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288415017/10000000000 : ℝ)|^2065 ≤ (42865732601591/100000000000000 : ℝ)^1553
        have hw : |(5288415017/10000000000 : ℝ)|=(5288415017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693477633/5000000000 : ℝ)|^2065 ≤ (43931036195127/100000000000000 : ℝ)^1553
        have hw : |(2693477633/5000000000 : ℝ)|=(2693477633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2181224829/10000000000 : ℝ)|^2065 ≤ (6601615589967/50000000000000 : ℝ)^1553
        have hw : |(-2181224829/10000000000 : ℝ)|=(2181224829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_11 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2252442479/5000000000 : ℝ)*x 0 + (2156301449/5000000000 : ℝ)*x 1 + (4312603233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2252442479/5000000000 : ℝ)^2065 ≤ (34634474017873/100000000000000 : ℝ)^1553 := by
    have hnat : (2252442479 : ℕ)^2065*100000000000000^1553 ≤ 34634474017873^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252442479 5000000000 34634474017873 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2156301449/5000000000 : ℝ)^2065 ≤ (6536552259473/20000000000000 : ℝ)^1553 := by
    have hnat : (2156301449 : ℕ)^2065*20000000000000^1553 ≤ 6536552259473^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156301449 5000000000 6536552259473 20000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4312603233/10000000000 : ℝ)^2065 ≤ (16341382336567/50000000000000 : ℝ)^1553 := by
    have hnat : (4312603233 : ℕ)^2065*50000000000000^1553 ≤ 16341382336567^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312603233 10000000000 16341382336567 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2252442479/5000000000 : ℝ), (2156301449/5000000000 : ℝ), (4312603233/10000000000 : ℝ)] ![(34634474017873/100000000000000 : ℝ), (6536552259473/20000000000000 : ℝ), (16341382336567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2252442479/5000000000 : ℝ)|^2065 ≤ (34634474017873/100000000000000 : ℝ)^1553
        have hw : |(2252442479/5000000000 : ℝ)|=(2252442479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2156301449/5000000000 : ℝ)|^2065 ≤ (6536552259473/20000000000000 : ℝ)^1553
        have hw : |(2156301449/5000000000 : ℝ)|=(2156301449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4312603233/10000000000 : ℝ)|^2065 ≤ (16341382336567/50000000000000 : ℝ)^1553
        have hw : |(4312603233/10000000000 : ℝ)|=(4312603233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_12 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-85141909/400000000 : ℝ)*x 0 + (5442012001/10000000000 : ℝ)*x 1 + (5272101709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85141909/400000000 : ℝ)^2065 ≤ (12780943456891/100000000000000 : ℝ)^1553 := by
    have hnat : (85141909 : ℕ)^2065*100000000000000^1553 ≤ 12780943456891^1553*400000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85141909 400000000 12780943456891 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442012001/10000000000 : ℝ)^2065 ≤ (44529057329511/100000000000000 : ℝ)^1553 := by
    have hnat : (5442012001 : ℕ)^2065*100000000000000^1553 ≤ 44529057329511^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442012001 10000000000 44529057329511 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272101709/10000000000 : ℝ)^2065 ≤ (42689999201251/100000000000000 : ℝ)^1553 := by
    have hnat : (5272101709 : ℕ)^2065*100000000000000^1553 ≤ 42689999201251^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272101709 10000000000 42689999201251 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85141909/400000000 : ℝ), (5442012001/10000000000 : ℝ), (5272101709/10000000000 : ℝ)] ![(12780943456891/100000000000000 : ℝ), (44529057329511/100000000000000 : ℝ), (42689999201251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85141909/400000000 : ℝ)|^2065 ≤ (12780943456891/100000000000000 : ℝ)^1553
        have hw : |(-85141909/400000000 : ℝ)|=(85141909/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442012001/10000000000 : ℝ)|^2065 ≤ (44529057329511/100000000000000 : ℝ)^1553
        have hw : |(5442012001/10000000000 : ℝ)|=(5442012001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272101709/10000000000 : ℝ)|^2065 ≤ (42689999201251/100000000000000 : ℝ)^1553
        have hw : |(5272101709/10000000000 : ℝ)|=(5272101709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_13 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369698061/10000000000 : ℝ)*x 0 + (-2226142879/10000000000 : ℝ)*x 1 + (5272102669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369698061/10000000000 : ℝ)^2065 ≤ (43744003483127/100000000000000 : ℝ)^1553 := by
    have hnat : (5369698061 : ℕ)^2065*100000000000000^1553 ≤ 43744003483127^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369698061 10000000000 43744003483127 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2226142879/10000000000 : ℝ)^2065 ≤ (6782993482471/50000000000000 : ℝ)^1553 := by
    have hnat : (2226142879 : ℕ)^2065*50000000000000^1553 ≤ 6782993482471^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2226142879 10000000000 6782993482471 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272102669/10000000000 : ℝ)^2065 ≤ (21345004768741/50000000000000 : ℝ)^1553 := by
    have hnat : (5272102669 : ℕ)^2065*50000000000000^1553 ≤ 21345004768741^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272102669 10000000000 21345004768741 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369698061/10000000000 : ℝ), (-2226142879/10000000000 : ℝ), (5272102669/10000000000 : ℝ)] ![(43744003483127/100000000000000 : ℝ), (6782993482471/50000000000000 : ℝ), (21345004768741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369698061/10000000000 : ℝ)|^2065 ≤ (43744003483127/100000000000000 : ℝ)^1553
        have hw : |(5369698061/10000000000 : ℝ)|=(5369698061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2226142879/10000000000 : ℝ)|^2065 ≤ (6782993482471/50000000000000 : ℝ)^1553
        have hw : |(-2226142879/10000000000 : ℝ)|=(2226142879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272102669/10000000000 : ℝ)|^2065 ≤ (21345004768741/50000000000000 : ℝ)^1553
        have hw : |(5272102669/10000000000 : ℝ)|=(5272102669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_14 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671212211/1250000000 : ℝ)*x 0 + (5272101863/10000000000 : ℝ)*x 1 + (-34783507/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671212211/1250000000 : ℝ)^2065 ≤ (43743999442711/100000000000000 : ℝ)^1553 := by
    have hnat : (671212211 : ℕ)^2065*100000000000000^1553 ≤ 43743999442711^1553*1250000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671212211 1250000000 43743999442711 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272101863/10000000000 : ℝ)^2065 ≤ (21345000429677/50000000000000 : ℝ)^1553 := by
    have hnat : (5272101863 : ℕ)^2065*50000000000000^1553 ≤ 21345000429677^1553*10000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272101863 10000000000 21345000429677 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34783507/156250000 : ℝ)^2065 ≤ (13565999678583/100000000000000 : ℝ)^1553 := by
    have hnat : (34783507 : ℕ)^2065*100000000000000^1553 ≤ 13565999678583^1553*156250000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34783507 156250000 13565999678583 100000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671212211/1250000000 : ℝ), (5272101863/10000000000 : ℝ), (-34783507/156250000 : ℝ)] ![(43743999442711/100000000000000 : ℝ), (21345000429677/50000000000000 : ℝ), (13565999678583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671212211/1250000000 : ℝ)|^2065 ≤ (43743999442711/100000000000000 : ℝ)^1553
        have hw : |(671212211/1250000000 : ℝ)|=(671212211/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272101863/10000000000 : ℝ)|^2065 ≤ (21345000429677/50000000000000 : ℝ)^1553
        have hw : |(5272101863/10000000000 : ℝ)|=(5272101863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34783507/156250000 : ℝ)|^2065 ≤ (13565999678583/100000000000000 : ℝ)^1553
        have hw : |(-34783507/156250000 : ℝ)|=(34783507/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1067_box_15 (p : ℝ) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062137837/2500000000 : ℝ)*x 0 + (2220383603/5000000000 : ℝ)*x 1 + (2220383549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062137837/2500000000 : ℝ)^2065 ≤ (16019452176561/50000000000000 : ℝ)^1553 := by
    have hnat : (1062137837 : ℕ)^2065*50000000000000^1553 ≤ 16019452176561^1553*2500000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062137837 2500000000 16019452176561 50000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220383603/5000000000 : ℝ)^2065 ≤ (8495137090169/25000000000000 : ℝ)^1553 := by
    have hnat : (2220383603 : ℕ)^2065*25000000000000^1553 ≤ 8495137090169^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220383603 5000000000 8495137090169 25000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2220383549/5000000000 : ℝ)^2065 ≤ (3398054726181/10000000000000 : ℝ)^1553 := by
    have hnat : (2220383549 : ℕ)^2065*10000000000000^1553 ≤ 3398054726181^1553*5000000000^2065 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220383549 5000000000 3398054726181 10000000000000 2065 1553 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2065/512 : ℝ)) 2065 1553 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062137837/2500000000 : ℝ), (2220383603/5000000000 : ℝ), (2220383549/5000000000 : ℝ)] ![(16019452176561/50000000000000 : ℝ), (8495137090169/25000000000000 : ℝ), (3398054726181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062137837/2500000000 : ℝ)|^2065 ≤ (16019452176561/50000000000000 : ℝ)^1553
        have hw : |(1062137837/2500000000 : ℝ)|=(1062137837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2220383603/5000000000 : ℝ)|^2065 ≤ (8495137090169/25000000000000 : ℝ)^1553
        have hw : |(2220383603/5000000000 : ℝ)|=(2220383603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2220383549/5000000000 : ℝ)|^2065 ≤ (3398054726181/10000000000000 : ℝ)^1553
        have hw : |(2220383549/5000000000 : ℝ)|=(2220383549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1067_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2489/4000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59241/100000 : ℝ) ∧ (3183/4000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16591/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11253/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14003/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11253/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14003/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11253/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11253/100000 : ℝ) ^ (8259/2048 : ℝ) ≤ (3732292528793319/25000000000000000000 : ℝ) := by
    have hpowers : (11253/100000 : ℝ)^8259 ≤ (3732292528793319/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11253 : ℕ)^8259*25000000000000000000^2048 ≤ 3732292528793319^2048*100000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11253 100000 3732292528793319 25000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11253/100000 : ℝ)) (X := (3732292528793319/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14003/100000 : ℝ) ^ (8259/2048 : ℝ) ≤ (18026985769746639/50000000000000000000 : ℝ) := by
    have hpowers : (14003/100000 : ℝ)^8259 ≤ (18026985769746639/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14003 : ℕ)^8259*50000000000000000000^2048 ≤ 18026985769746639^2048*100000^8259 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14003 100000 18026985769746639 50000000000000000000 8259 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14003/100000 : ℝ)) (X := (18026985769746639/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503732292528793319/12500000000000000000 : ℝ) ≤ (10000740319852241/10000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (12503732292528793319/12500000000000000000 : ℝ)^2048 ≤ (10000740319852241/10000000000000000 : ℝ)^8259 := by
      have hnat : (12503732292528793319 : ℕ)^2048*10000000000000000^8259 ≤ 10000740319852241^8259*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503732292528793319 12500000000000000000 10000740319852241 10000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000740319852241/10000000000000000 : ℝ)) (X := (12503732292528793319/12500000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025491570827333277/50000000000000000000 : ℝ) ≤ (1250157999551413/1250000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (50025491570827333277/50000000000000000000 : ℝ)^2048 ≤ (1250157999551413/1250000000000000 : ℝ)^8259 := by
      have hnat : (50025491570827333277 : ℕ)^2048*1250000000000000^8259 ≤ 1250157999551413^8259*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025491570827333277 50000000000000000000 1250157999551413 1250000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250157999551413/1250000000000000 : ℝ)) (X := (50025491570827333277/50000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018026985769746639/25000000000000000000 : ℝ) ≤ (10001787672970367/10000000000000000 : ℝ) ^ (8259/2048 : ℝ) := by
    have hpowers : (25018026985769746639/25000000000000000000 : ℝ)^2048 ≤ (10001787672970367/10000000000000000 : ℝ)^8259 := by
      have hnat : (25018026985769746639 : ℕ)^2048*10000000000000000^8259 ≤ 10001787672970367^8259*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018026985769746639 25000000000000000000 10001787672970367 10000000000000000 2048 8259 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001787672970367/10000000000000000 : ℝ)) (X := (25018026985769746639/25000000000000000000 : ℝ)) (by norm_num) 8259 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3732292528793319/25000000000000000000 : ℝ) ≤ ((312389204715402169/312500000000000000 : ℝ)+2*(523676559063/275000000000000 : ℝ)*(11253/100000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (312389204715402169/312500000000000000 : ℝ)+2*(523676559063/275000000000000 : ℝ)*(11253/100000 : ℝ)=(10000740319852241/10000000000000000 : ℝ) by norm_num, show 1+2*(3732292528793319/25000000000000000000 : ℝ)=(12503732292528793319/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18026985769746639/50000000000000000000 : ℝ)+(3732292528793319/25000000000000000000 : ℝ) ≤ ((312389204715402169/312500000000000000 : ℝ)+(523676559063/275000000000000 : ℝ)*((14003/100000 : ℝ)+(11253/100000 : ℝ)))^(8259/2048 : ℝ) := by
    rw [show (312389204715402169/312500000000000000 : ℝ)+(523676559063/275000000000000 : ℝ)*((14003/100000 : ℝ)+(11253/100000 : ℝ))=(1250157999551413/1250000000000000 : ℝ) by norm_num, show 1+(18026985769746639/50000000000000000000 : ℝ)+(3732292528793319/25000000000000000000 : ℝ)=(50025491570827333277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18026985769746639/50000000000000000000 : ℝ) ≤ ((312389204715402169/312500000000000000 : ℝ)+2*(523676559063/275000000000000 : ℝ)*(14003/100000 : ℝ))^(8259/2048 : ℝ) := by
    rw [show (312389204715402169/312500000000000000 : ℝ)+2*(523676559063/275000000000000 : ℝ)*(14003/100000 : ℝ)=(10001787672970367/10000000000000000 : ℝ) by norm_num, show 1+2*(18026985769746639/50000000000000000000 : ℝ)=(25018026985769746639/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (312389204715402169/312500000000000000 : ℝ)*(X 1 0+X 2 0)+(523676559063/275000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (312389204715402169/312500000000000000 : ℝ)) (alpha := (523676559063/275000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (312389204715402169/312500000000000000 : ℝ)*(X 0 1+X 2 1)+(523676559063/275000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (312389204715402169/312500000000000000 : ℝ)) (alpha := (523676559063/275000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (312389204715402169/312500000000000000 : ℝ)*(X 0 2+X 1 2)+(523676559063/275000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8259/2048 : ℝ)) (lo := (11253/100000 : ℝ)) (hi := (14003/100000 : ℝ)) (c := (312389204715402169/312500000000000000 : ℝ)) (alpha := (523676559063/275000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2073849799/10000000000 : ℝ)*X 0 0+(2688676993/5000000000 : ℝ)*X 0 1+(5377354407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295213221/10000000000 : ℝ)*X 1 0+(-437009953/2000000000 : ℝ)*X 1 1+(5377354173/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647606647/5000000000 : ℝ)*X 2 0+(268867709/500000000 : ℝ)*X 2 1+(-273131207/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120931763/2500000000 : ℝ)*X 0 0+(864664521/2000000000 : ℝ)*X 0 1+(540415311/1250000000 : ℝ)*X 0 2+(1120931763/2500000000 : ℝ)*X 1 0+(864664521/2000000000 : ℝ)*X 1 1+(540415311/1250000000 : ℝ)*X 1 2+(1120931763/2500000000 : ℝ)*X 2 0+(864664521/2000000000 : ℝ)*X 2 1+(540415311/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2334095373/10000000000 : ℝ)*X 0 0+(5280104067/10000000000 : ℝ)*X 0 1+(5280103209/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364038097/10000000000 : ℝ)*X 1 0+(-1111536629/5000000000 : ℝ)*X 1 1+(13200259/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((214561493/400000000 : ℝ)*X 2 0+(660013063/1250000000 : ℝ)*X 2 1+(-2223073089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4266643309/10000000000 : ℝ)*X 0 0+(886368599/2000000000 : ℝ)*X 0 1+(4431842943/10000000000 : ℝ)*X 0 2+(4266643309/10000000000 : ℝ)*X 1 0+(886368599/2000000000 : ℝ)*X 1 1+(4431842943/10000000000 : ℝ)*X 1 2+(4266643309/10000000000 : ℝ)*X 2 0+(886368599/2000000000 : ℝ)*X 2 1+(4431842943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2279765153/10000000000 : ℝ)*X 0 0+(5214111403/10000000000 : ℝ)*X 0 1+(336684707/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644207471/5000000000 : ℝ)*X 1 0+(-218122507/1000000000 : ℝ)*X 1 1+(2693477581/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288415017/10000000000 : ℝ)*X 2 0+(2693477633/5000000000 : ℝ)*X 2 1+(-2181224829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2252442479/5000000000 : ℝ)*X 0 0+(2156301449/5000000000 : ℝ)*X 0 1+(4312603233/10000000000 : ℝ)*X 0 2+(2252442479/5000000000 : ℝ)*X 1 0+(2156301449/5000000000 : ℝ)*X 1 1+(4312603233/10000000000 : ℝ)*X 1 2+(2252442479/5000000000 : ℝ)*X 2 0+(2156301449/5000000000 : ℝ)*X 2 1+(4312603233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-85141909/400000000 : ℝ)*X 0 0+(5442012001/10000000000 : ℝ)*X 0 1+(5272101709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369698061/10000000000 : ℝ)*X 1 0+(-2226142879/10000000000 : ℝ)*X 1 1+(5272102669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((671212211/1250000000 : ℝ)*X 2 0+(5272101863/10000000000 : ℝ)*X 2 1+(-34783507/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1062137837/2500000000 : ℝ)*X 0 0+(2220383603/5000000000 : ℝ)*X 0 1+(2220383549/5000000000 : ℝ)*X 0 2+(1062137837/2500000000 : ℝ)*X 1 0+(2220383603/5000000000 : ℝ)*X 1 1+(2220383549/5000000000 : ℝ)*X 1 2+(1062137837/2500000000 : ℝ)*X 2 0+(2220383603/5000000000 : ℝ)*X 2 1+(2220383549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1067_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2489/4000 : ℝ) ≤ (-53472143633069691773943940024893/85937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50475007/100000000000000 : ℝ)*(lower0) + (42471183/100000000000000 : ℝ)*(lower2) + (4615619/3125000000000 : ℝ)*(lower4) + (34498933/100000000000000 : ℝ)*(lower5) + (1928680798162797/50000000000000 : ℝ)*(major0) + (1928680798162797/50000000000000 : ℝ)*(major1) + (1928680798162797/50000000000000 : ℝ)*(major2) + (627762021/12500000000000 : ℝ)*(sp1) + (205173405155103/4000000000000 : ℝ)*(sp4) + (1282338361818909/25000000000000 : ℝ)*(sp5) + (1282226465000069/25000000000000 : ℝ)*(sp6) + (651526358384263/25000000000000 : ℝ)*(sp7) + (23340494229/100000000000000 : ℝ)*(sp8) + (56576171441/12500000000000 : ℝ)*(sp14) + (651526358384263/25000000000000 : ℝ)*(f.failure) + (1282339617342951/25000000000000 : ℝ)*(f.sum) + (56756720293289/6875000000000000000000000000 : ℝ)*base66 + (3086528823431888877/171875000000000000000000000000000 : ℝ)*base68 + (1097731419947513877/171875000000000000000000000000000 : ℝ)*base70 + (1813138803056888877/171875000000000000000000000000000 : ℝ)*base72 + (38745496128289/6875000000000000000000000000 : ℝ)*base74 + (770389645744388877/171875000000000000000000000000000 : ℝ)*base76 + (1420917843431888877/171875000000000000000000000000000 : ℝ)*base78 + (1503492862744388877/171875000000000000000000000000000 : ℝ)*base80 + (5503607149211/6875000000000000000000000000 : ℝ)*base81 + (2553349/625000000000000000000 : ℝ)*base89 + (2553349/625000000000000000000 : ℝ)*base91 + (2553349/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59241/100000 : ℝ) ≤ (50912801598555368055226356988143/85937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18237/16000000000 : ℝ)*(upper1) + (13789743/25000000000000 : ℝ)*(upper2) + (13131459/25000000000000 : ℝ)*(upper4) + (40523459/25000000000000 : ℝ)*(upper5) + (3920291163690109/100000000000000 : ℝ)*(major0) + (3920291163690109/100000000000000 : ℝ)*(major1) + (3920291163690109/100000000000000 : ℝ)*(major2) + (2586106185562487/50000000000000 : ℝ)*(sp0) + (206888267034599/4000000000000 : ℝ)*(sp1) + (2586073631664077/50000000000000 : ℝ)*(sp2) + (264862182287297/10000000000000 : ℝ)*(sp3) + (2916435353/50000000000000 : ℝ)*(sp9) + (8155675941/12500000000000 : ℝ)*(sp10) + (137610707/100000000000000 : ℝ)*(sp12) + (264862182287297/10000000000000 : ℝ)*(f.failure) + (2586106254367841/50000000000000 : ℝ)*(f.sum) + (15680031378383/13750000000000000000000000000 : ℝ)*base66 + (215014590998501869/343750000000000000000000000000000 : ℝ)*base68 + (678657757248501869/343750000000000000000000000000000 : ℝ)*base70 + (55557893188998131/343750000000000000000000000000000 : ℝ)*base71 + (4135177276617/13750000000000000000000000000 : ℝ)*base73 + (207038383061001869/343750000000000000000000000000000 : ℝ)*base76 + (2526005887279751869/343750000000000000000000000000000 : ℝ)*base78 + (2173043843092251869/343750000000000000000000000000000 : ℝ)*base80 + (101688470077867/13750000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (271469/250000000000000000000 : ℝ)*base90 + (271469/250000000000000000000 : ℝ)*base92 + (271469/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (3183/4000 : ℝ) ≤ (2137100524059036210743969585937/2685546875000000000000000000000 : ℝ) := by norm_num
    linear_combination (97796913/100000000000000 : ℝ)*(upper0) + (5350719/5000000000000 : ℝ)*(lower3) + (51862923/50000000000000 : ℝ)*(upper4) + (1097134445239073/25000000000000 : ℝ)*(major0) + (1097134445239073/25000000000000 : ℝ)*(major1) + (1097134445239073/25000000000000 : ℝ)*(major2) + (12924618937/25000000000000 : ℝ)*(sp1) + (175559419/125000000000 : ℝ)*(sp2) + (23053352643/50000000000000 : ℝ)*(sp3) + (2751920093/100000000000000 : ℝ)*(sp4) + (5785568889037097/100000000000000 : ℝ)*(sp8) + (2892759971240721/50000000000000 : ℝ)*(sp9) + (578543119342199/10000000000000 : ℝ)*(sp10) + (1482465931751497/50000000000000 : ℝ)*(sp11) + (74124449255207/2500000000000 : ℝ)*(f.failure) + (578557164095719/10000000000000 : ℝ)*(f.sum) + (1567611637069/859375000000000000000000000 : ℝ)*base66 + (283322612148519793/85937500000000000000000000000000 : ℝ)*base68 + (252477341156167707/85937500000000000000000000000000 : ℝ)*base69 + (311624394586019793/85937500000000000000000000000000 : ℝ)*base72 + (2582418259569/859375000000000000000000000 : ℝ)*base74 + (272438560226644793/85937500000000000000000000000000 : ℝ)*base76 + (253101125351644793/85937500000000000000000000000000 : ℝ)*base78 + (1808008551195394793/85937500000000000000000000000000 : ℝ)*base80 + (16330704599849/3437500000000000000000000000 : ℝ)*base81 + (511461/62500000000000000000 : ℝ)*base89 + (511461/62500000000000000000 : ℝ)*base91 + (511461/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-16591/20000 : ℝ) ≤ (-142574299627316092356707716221561/171875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (758421289/100000000000000 : ℝ)*(upper3) + (131122841/20000000000000 : ℝ)*(lower4) + (19686871/50000000000000 : ℝ)*(upper5) + (4423094867072931/100000000000000 : ℝ)*(major0) + (4423094867072931/100000000000000 : ℝ)*(major1) + (4423094867072931/100000000000000 : ℝ)*(major2) + (2887139363/50000000000000 : ℝ)*(sp4) + (247511353469/100000000000000 : ℝ)*(sp5) + (1017911794067/100000000000000 : ℝ)*(sp6) + (542963918747/100000000000000 : ℝ)*(sp7) + (5885509351056423/100000000000000 : ℝ)*(sp12) + (5885267613981681/100000000000000 : ℝ)*(sp13) + (5884497213541083/100000000000000 : ℝ)*(sp14) + (2987782418153011/100000000000000 : ℝ)*(sp15) + (2988325382071759/100000000000000 : ℝ)*(f.failure) + (5885515125335149/100000000000000 : ℝ)*(f.sum) + (9556872576153/13750000000000000000000000000 : ℝ)*base65 + (2362509334875123229/343750000000000000000000000000000 : ℝ)*base67 + (3051814866625123229/343750000000000000000000000000000 : ℝ)*base69 + (4275768179281373229/343750000000000000000000000000000 : ℝ)*base71 + (63226522236153/13750000000000000000000000000 : ℝ)*base73 + (1267808622000123229/343750000000000000000000000000000 : ℝ)*base75 + (3562370795062623229/343750000000000000000000000000000 : ℝ)*base77 + (2616814095750123229/343750000000000000000000000000000 : ℝ)*base79 + (460884816347/13750000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (18103357/2500000000000000000000 : ℝ)*base89 + (18103357/2500000000000000000000 : ℝ)*base91 + (18103357/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1067_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59241/100000 : ℝ) else (3183/4000 : ℝ) ≤ X j i ∧ X j i ≤ (16591/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1067_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1067_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59241/100000 : ℝ) else (3183/4000 : ℝ) ≤ X j i ∧ X j i ≤ (16591/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1067_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1067_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8259/2048 : ℝ) ≤ p) (hpb : p ≤ (2065/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37003123/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11253/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2489/4000 : ℝ) ≤ X j i ∧ X j i ≤ -(59241/100000 : ℝ) else (3183/4000 : ℝ) ≤ X j i ∧ X j i ≤ (16591/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1067_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
