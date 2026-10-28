-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:12:22.166281+00:00
-- url     : https://prove2.me/submissions/07bfe937-bad1-4abc-a309-4da4e56b290d

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
theorem support_rectangle_w1224_s6_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128258227/10000000000 : ℝ)*x 0 + (269587491/500000000 : ℝ)*x 1 + (2633382519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128258227/10000000000 : ℝ)^8417 ≤ (6470166786649/50000000000000 : ℝ)^6369 := by
    have hnat : (2128258227 : ℕ)^8417*50000000000000^6369 ≤ 6470166786649^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128258227 10000000000 6470166786649 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269587491/500000000 : ℝ)^8417 ≤ (22102195110939/50000000000000 : ℝ)^6369 := by
    have hnat : (269587491 : ℕ)^8417*50000000000000^6369 ≤ 22102195110939^6369*500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269587491 500000000 22102195110939 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633382519/5000000000 : ℝ)^8417 ≤ (8571055238227/20000000000000 : ℝ)^6369 := by
    have hnat : (2633382519 : ℕ)^8417*20000000000000^6369 ≤ 8571055238227^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633382519 5000000000 8571055238227 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128258227/10000000000 : ℝ), (269587491/500000000 : ℝ), (2633382519/5000000000 : ℝ)] ![(6470166786649/50000000000000 : ℝ), (22102195110939/50000000000000 : ℝ), (8571055238227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128258227/10000000000 : ℝ)|^8417 ≤ (6470166786649/50000000000000 : ℝ)^6369
        have hw : |(-2128258227/10000000000 : ℝ)|=(2128258227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269587491/500000000 : ℝ)|^8417 ≤ (22102195110939/50000000000000 : ℝ)^6369
        have hw : |(269587491/500000000 : ℝ)|=(269587491/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633382519/5000000000 : ℝ)|^8417 ≤ (8571055238227/20000000000000 : ℝ)^6369
        have hw : |(2633382519/5000000000 : ℝ)|=(2633382519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s6_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334028557/625000000 : ℝ)*x 0 + (-2191635949/10000000000 : ℝ)*x 1 + (5266764949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334028557/625000000 : ℝ)^8417 ≤ (2184635204091/5000000000000 : ℝ)^6369 := by
    have hnat : (334028557 : ℕ)^8417*5000000000000^6369 ≤ 2184635204091^6369*625000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334028557 625000000 2184635204091 5000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191635949/10000000000 : ℝ)^8417 ≤ (13452020670727/100000000000000 : ℝ)^6369 := by
    have hnat : (2191635949 : ℕ)^8417*100000000000000^6369 ≤ 13452020670727^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191635949 10000000000 13452020670727 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266764949/10000000000 : ℝ)^8417 ≤ (42855275234081/100000000000000 : ℝ)^6369 := by
    have hnat : (5266764949 : ℕ)^8417*100000000000000^6369 ≤ 42855275234081^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266764949 10000000000 42855275234081 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334028557/625000000 : ℝ), (-2191635949/10000000000 : ℝ), (5266764949/10000000000 : ℝ)] ![(2184635204091/5000000000000 : ℝ), (13452020670727/100000000000000 : ℝ), (42855275234081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334028557/625000000 : ℝ)|^8417 ≤ (2184635204091/5000000000000 : ℝ)^6369
        have hw : |(334028557/625000000 : ℝ)|=(334028557/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191635949/10000000000 : ℝ)|^8417 ≤ (13452020670727/100000000000000 : ℝ)^6369
        have hw : |(-2191635949/10000000000 : ℝ)|=(2191635949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266764949/10000000000 : ℝ)|^8417 ≤ (42855275234081/100000000000000 : ℝ)^6369
        have hw : |(5266764949/10000000000 : ℝ)|=(5266764949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s6_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668057099/1250000000 : ℝ)*x 0 + (1316691261/2500000000 : ℝ)*x 1 + (-2191635983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668057099/1250000000 : ℝ)^8417 ≤ (1092317569633/2500000000000 : ℝ)^6369 := by
    have hnat : (668057099 : ℕ)^8417*2500000000000^6369 ≤ 1092317569633^6369*1250000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668057099 1250000000 1092317569633 2500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316691261/2500000000 : ℝ)^8417 ≤ (8571055251131/20000000000000 : ℝ)^6369 := by
    have hnat : (1316691261 : ℕ)^8417*20000000000000^6369 ≤ 8571055251131^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316691261 2500000000 8571055251131 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2191635983/10000000000 : ℝ)^8417 ≤ (13452020946521/100000000000000 : ℝ)^6369 := by
    have hnat : (2191635983 : ℕ)^8417*100000000000000^6369 ≤ 13452020946521^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191635983 10000000000 13452020946521 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668057099/1250000000 : ℝ), (1316691261/2500000000 : ℝ), (-2191635983/10000000000 : ℝ)] ![(1092317569633/2500000000000 : ℝ), (8571055251131/20000000000000 : ℝ), (13452020946521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668057099/1250000000 : ℝ)|^8417 ≤ (1092317569633/2500000000000 : ℝ)^6369
        have hw : |(668057099/1250000000 : ℝ)|=(668057099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316691261/2500000000 : ℝ)|^8417 ≤ (8571055251131/20000000000000 : ℝ)^6369
        have hw : |(1316691261/2500000000 : ℝ)|=(1316691261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2191635983/10000000000 : ℝ)|^8417 ≤ (13452020946521/100000000000000 : ℝ)^6369
        have hw : |(-2191635983/10000000000 : ℝ)|=(2191635983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s6_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088309253/2500000000 : ℝ)*x 0 + (4228696833/10000000000 : ℝ)*x 1 + (4481356449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088309253/2500000000 : ℝ)^8417 ≤ (16658645699763/50000000000000 : ℝ)^6369 := by
    have hnat : (1088309253 : ℕ)^8417*50000000000000^6369 ≤ 16658645699763^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088309253 2500000000 16658645699763 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228696833/10000000000 : ℝ)^8417 ≤ (32063464508559/100000000000000 : ℝ)^6369 := by
    have hnat : (4228696833 : ℕ)^8417*100000000000000^6369 ≤ 32063464508559^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228696833 10000000000 32063464508559 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4481356449/10000000000 : ℝ)^8417 ≤ (216370275461/625000000000 : ℝ)^6369 := by
    have hnat : (4481356449 : ℕ)^8417*625000000000^6369 ≤ 216370275461^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481356449 10000000000 216370275461 625000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088309253/2500000000 : ℝ), (4228696833/10000000000 : ℝ), (4481356449/10000000000 : ℝ)] ![(16658645699763/50000000000000 : ℝ), (32063464508559/100000000000000 : ℝ), (216370275461/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088309253/2500000000 : ℝ)|^8417 ≤ (16658645699763/50000000000000 : ℝ)^6369
        have hw : |(1088309253/2500000000 : ℝ)|=(1088309253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228696833/10000000000 : ℝ)|^8417 ≤ (32063464508559/100000000000000 : ℝ)^6369
        have hw : |(4228696833/10000000000 : ℝ)|=(4228696833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4481356449/10000000000 : ℝ)|^8417 ≤ (216370275461/625000000000 : ℝ)^6369
        have hw : |(4481356449/10000000000 : ℝ)|=(4481356449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s6_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064131539/5000000000 : ℝ)*x 0 + (5267081037/10000000000 : ℝ)*x 1 + (336964537/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064131539/5000000000 : ℝ)^8417 ≤ (6470186276507/50000000000000 : ℝ)^6369 := by
    have hnat : (1064131539 : ℕ)^8417*50000000000000^6369 ≤ 6470186276507^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064131539 5000000000 6470186276507 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267081037/10000000000 : ℝ)^8417 ≤ (5357334286563/12500000000000 : ℝ)^6369 := by
    have hnat : (5267081037 : ℕ)^8417*12500000000000^6369 ≤ 5357334286563^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267081037 10000000000 5357334286563 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336964537/625000000 : ℝ)^8417 ≤ (11050238286431/25000000000000 : ℝ)^6369 := by
    have hnat : (336964537 : ℕ)^8417*25000000000000^6369 ≤ 11050238286431^6369*625000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336964537 625000000 11050238286431 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064131539/5000000000 : ℝ), (5267081037/10000000000 : ℝ), (336964537/625000000 : ℝ)] ![(6470186276507/50000000000000 : ℝ), (5357334286563/12500000000000 : ℝ), (11050238286431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064131539/5000000000 : ℝ)|^8417 ≤ (6470186276507/50000000000000 : ℝ)^6369
        have hw : |(-1064131539/5000000000 : ℝ)|=(1064131539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267081037/10000000000 : ℝ)|^8417 ≤ (5357334286563/12500000000000 : ℝ)^6369
        have hw : |(5267081037/10000000000 : ℝ)|=(5267081037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336964537/625000000 : ℝ)|^8417 ≤ (11050238286431/25000000000000 : ℝ)^6369
        have hw : |(336964537/625000000 : ℝ)|=(336964537/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s6_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312605483/10000000000 : ℝ)*x 0 + (-2066968307/10000000000 : ℝ)*x 1 + (1347858163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312605483/10000000000 : ℝ)^8417 ≤ (4334890600579/10000000000000 : ℝ)^6369 := by
    have hnat : (5312605483 : ℕ)^8417*10000000000000^6369 ≤ 4334890600579^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312605483 10000000000 4334890600579 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066968307/10000000000 : ℝ)^8417 ≤ (2490028035851/20000000000000 : ℝ)^6369 := by
    have hnat : (2066968307 : ℕ)^8417*20000000000000^6369 ≤ 2490028035851^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066968307 10000000000 2490028035851 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347858163/2500000000 : ℝ)^8417 ≤ (44200953795801/100000000000000 : ℝ)^6369 := by
    have hnat : (1347858163 : ℕ)^8417*100000000000000^6369 ≤ 44200953795801^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347858163 2500000000 44200953795801 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312605483/10000000000 : ℝ), (-2066968307/10000000000 : ℝ), (1347858163/2500000000 : ℝ)] ![(4334890600579/10000000000000 : ℝ), (2490028035851/20000000000000 : ℝ), (44200953795801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312605483/10000000000 : ℝ)|^8417 ≤ (4334890600579/10000000000000 : ℝ)^6369
        have hw : |(5312605483/10000000000 : ℝ)|=(5312605483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2066968307/10000000000 : ℝ)|^8417 ≤ (2490028035851/20000000000000 : ℝ)^6369
        have hw : |(-2066968307/10000000000 : ℝ)|=(2066968307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347858163/2500000000 : ℝ)|^8417 ≤ (44200953795801/100000000000000 : ℝ)^6369
        have hw : |(1347858163/2500000000 : ℝ)|=(1347858163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s6_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166018919/312500000 : ℝ)*x 0 + (1347858173/2500000000 : ℝ)*x 1 + (-1033484177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166018919/312500000 : ℝ)^8417 ≤ (43348905197033/100000000000000 : ℝ)^6369 := by
    have hnat : (166018919 : ℕ)^8417*100000000000000^6369 ≤ 43348905197033^6369*312500000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166018919 312500000 43348905197033 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1347858173/2500000000 : ℝ)^8417 ≤ (22100477114593/50000000000000 : ℝ)^6369 := by
    have hnat : (1347858173 : ℕ)^8417*50000000000000^6369 ≤ 22100477114593^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347858173 2500000000 22100477114593 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033484177/5000000000 : ℝ)^8417 ≤ (6225070276693/50000000000000 : ℝ)^6369 := by
    have hnat : (1033484177 : ℕ)^8417*50000000000000^6369 ≤ 6225070276693^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033484177 5000000000 6225070276693 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166018919/312500000 : ℝ), (1347858173/2500000000 : ℝ), (-1033484177/5000000000 : ℝ)] ![(43348905197033/100000000000000 : ℝ), (22100477114593/50000000000000 : ℝ), (6225070276693/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166018919/312500000 : ℝ)|^8417 ≤ (43348905197033/100000000000000 : ℝ)^6369
        have hw : |(166018919/312500000 : ℝ)|=(166018919/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1347858173/2500000000 : ℝ)|^8417 ≤ (22100477114593/50000000000000 : ℝ)^6369
        have hw : |(1347858173/2500000000 : ℝ)|=(1347858173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033484177/5000000000 : ℝ)|^8417 ≤ (6225070276693/50000000000000 : ℝ)^6369
        have hw : |(-1033484177/5000000000 : ℝ)|=(1033484177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s6_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (870649339/2000000000 : ℝ)*x 0 + (1120179379/2500000000 : ℝ)*x 1 + (2114668999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870649339/2000000000 : ℝ)^8417 ≤ (33317389338047/100000000000000 : ℝ)^6369 := by
    have hnat : (870649339 : ℕ)^8417*100000000000000^6369 ≤ 33317389338047^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870649339 2000000000 33317389338047 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120179379/2500000000 : ℝ)^8417 ≤ (34612721191593/100000000000000 : ℝ)^6369 := by
    have hnat : (1120179379 : ℕ)^8417*100000000000000^6369 ≤ 34612721191593^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120179379 2500000000 34612721191593 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114668999/5000000000 : ℝ)^8417 ≤ (32069889467671/100000000000000 : ℝ)^6369 := by
    have hnat : (2114668999 : ℕ)^8417*100000000000000^6369 ≤ 32069889467671^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114668999 5000000000 32069889467671 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870649339/2000000000 : ℝ), (1120179379/2500000000 : ℝ), (2114668999/5000000000 : ℝ)] ![(33317389338047/100000000000000 : ℝ), (34612721191593/100000000000000 : ℝ), (32069889467671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870649339/2000000000 : ℝ)|^8417 ≤ (33317389338047/100000000000000 : ℝ)^6369
        have hw : |(870649339/2000000000 : ℝ)|=(870649339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120179379/2500000000 : ℝ)|^8417 ≤ (34612721191593/100000000000000 : ℝ)^6369
        have hw : |(1120179379/2500000000 : ℝ)|=(1120179379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114668999/5000000000 : ℝ)|^8417 ≤ (32069889467671/100000000000000 : ℝ)^6369
        have hw : |(2114668999/5000000000 : ℝ)|=(2114668999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2863/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (141/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1143/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1143/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1143/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1143/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1143/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1143/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1143/10000 : ℝ) ^ (263/64 : ℝ) ≤ (13463523354547933/100000000000000000000 : ℝ) := by
    have hpowers : (1143/10000 : ℝ)^263 ≤ (13463523354547933/100000000000000000000 : ℝ)^64 := by
      have hnat : (1143 : ℕ)^263*100000000000000000000^64 ≤ 13463523354547933^64*10000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1143 10000 13463523354547933 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1143/10000 : ℝ)) (X := (13463523354547933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14123/100000 : ℝ) ^ (263/64 : ℝ) ≤ (32116713502728543/100000000000000000000 : ℝ) := by
    have hpowers : (14123/100000 : ℝ)^263 ≤ (32116713502728543/100000000000000000000 : ℝ)^64 := by
      have hnat : (14123 : ℕ)^263*100000000000000000000^64 ≤ 32116713502728543^64*100000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14123 100000 32116713502728543 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14123/100000 : ℝ)) (X := (32116713502728543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013463523354547933/50000000000000000000 : ℝ) ≤ (5000327596094561/5000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50013463523354547933/50000000000000000000 : ℝ)^64 ≤ (5000327596094561/5000000000000000 : ℝ)^263 := by
      have hnat : (50013463523354547933 : ℕ)^64*5000000000000000^263 ≤ 5000327596094561^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013463523354547933 50000000000000000000 5000327596094561 5000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000327596094561/5000000000000000 : ℝ)) (X := (50013463523354547933/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011395059214319119/25000000000000000000 : ℝ) ≤ (10001108985648467/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (25011395059214319119/25000000000000000000 : ℝ)^64 ≤ (10001108985648467/10000000000000000 : ℝ)^263 := by
      have hnat : (25011395059214319119 : ℕ)^64*10000000000000000^263 ≤ 10001108985648467^263*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011395059214319119 25000000000000000000 10001108985648467 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001108985648467/10000000000000000 : ℝ)) (X := (25011395059214319119/25000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032116713502728543/50000000000000000000 : ℝ) ≤ (2500390694776953/2500000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50032116713502728543/50000000000000000000 : ℝ)^64 ≤ (2500390694776953/2500000000000000 : ℝ)^263 := by
      have hnat : (50032116713502728543 : ℕ)^64*2500000000000000^263 ≤ 2500390694776953^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032116713502728543 50000000000000000000 2500390694776953 2500000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500390694776953/2500000000000000 : ℝ)) (X := (50032116713502728543/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13463523354547933/100000000000000000000 : ℝ) ≤ ((13460695357042339423/13465000000000000000 : ℝ)+2*(90758691869/53860000000000 : ℝ)*(1143/10000 : ℝ))^(263/64 : ℝ) := by
    rw [show (13460695357042339423/13465000000000000000 : ℝ)+2*(90758691869/53860000000000 : ℝ)*(1143/10000 : ℝ)=(5000327596094561/5000000000000000 : ℝ) by norm_num, show 1+2*(13463523354547933/100000000000000000000 : ℝ)=(50013463523354547933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32116713502728543/100000000000000000000 : ℝ)+(13463523354547933/100000000000000000000 : ℝ) ≤ ((13460695357042339423/13465000000000000000 : ℝ)+(90758691869/53860000000000 : ℝ)*((14123/100000 : ℝ)+(1143/10000 : ℝ)))^(263/64 : ℝ) := by
    rw [show (13460695357042339423/13465000000000000000 : ℝ)+(90758691869/53860000000000 : ℝ)*((14123/100000 : ℝ)+(1143/10000 : ℝ))=(10001108985648467/10000000000000000 : ℝ) by norm_num, show 1+(32116713502728543/100000000000000000000 : ℝ)+(13463523354547933/100000000000000000000 : ℝ)=(25011395059214319119/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32116713502728543/100000000000000000000 : ℝ) ≤ ((13460695357042339423/13465000000000000000 : ℝ)+2*(90758691869/53860000000000 : ℝ)*(14123/100000 : ℝ))^(263/64 : ℝ) := by
    rw [show (13460695357042339423/13465000000000000000 : ℝ)+2*(90758691869/53860000000000 : ℝ)*(14123/100000 : ℝ)=(2500390694776953/2500000000000000 : ℝ) by norm_num, show 1+2*(32116713502728543/100000000000000000000 : ℝ)=(50032116713502728543/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13460695357042339423/13465000000000000000 : ℝ)*(X 1 0+X 2 0)+(90758691869/53860000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (13460695357042339423/13465000000000000000 : ℝ)) (alpha := (90758691869/53860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13460695357042339423/13465000000000000000 : ℝ)*(X 0 1+X 2 1)+(90758691869/53860000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (13460695357042339423/13465000000000000000 : ℝ)) (alpha := (90758691869/53860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13460695357042339423/13465000000000000000 : ℝ)*(X 0 2+X 1 2)+(90758691869/53860000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (14123/100000 : ℝ)) (c := (13460695357042339423/13465000000000000000 : ℝ)) (alpha := (90758691869/53860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128258227/10000000000 : ℝ)*X 0 0+(269587491/500000000 : ℝ)*X 0 1+(2633382519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334028557/625000000 : ℝ)*X 1 0+(-2191635949/10000000000 : ℝ)*X 1 1+(5266764949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668057099/1250000000 : ℝ)*X 2 0+(1316691261/2500000000 : ℝ)*X 2 1+(-2191635983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1088309253/2500000000 : ℝ)*X 0 0+(4228696833/10000000000 : ℝ)*X 0 1+(4481356449/10000000000 : ℝ)*X 0 2+(1088309253/2500000000 : ℝ)*X 1 0+(4228696833/10000000000 : ℝ)*X 1 1+(4481356449/10000000000 : ℝ)*X 1 2+(1088309253/2500000000 : ℝ)*X 2 0+(4228696833/10000000000 : ℝ)*X 2 1+(4481356449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064131539/5000000000 : ℝ)*X 0 0+(5267081037/10000000000 : ℝ)*X 0 1+(336964537/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312605483/10000000000 : ℝ)*X 1 0+(-2066968307/10000000000 : ℝ)*X 1 1+(1347858163/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166018919/312500000 : ℝ)*X 2 0+(1347858173/2500000000 : ℝ)*X 2 1+(-1033484177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((870649339/2000000000 : ℝ)*X 0 0+(1120179379/2500000000 : ℝ)*X 0 1+(2114668999/5000000000 : ℝ)*X 0 2+(870649339/2000000000 : ℝ)*X 1 0+(1120179379/2500000000 : ℝ)*X 1 1+(2114668999/5000000000 : ℝ)*X 1 2+(870649339/2000000000 : ℝ)*X 2 0+(1120179379/2500000000 : ℝ)*X 2 1+(2114668999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2473401045198545145118557357/336625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1392206713/100000000000000 : ℝ)*(base19) + (1037496213/100000000000000 : ℝ)*(base23) + (93561001/100000000000000 : ℝ)*(lower2) + (223469903/100000000000000 : ℝ)*(upper3) + (672727/10000000000000 : ℝ)*(upper5) + (2989742957420349/50000000000000 : ℝ)*(major0) + (2989742957420349/50000000000000 : ℝ)*(major1) + (2989742957420349/50000000000000 : ℝ)*(major2) + (1600202626609751/20000000000000 : ℝ)*(sp0) + (2000260240338639/25000000000000 : ℝ)*(sp1) + (250032541127033/3125000000000 : ℝ)*(sp2) + (3957909396023551/100000000000000 : ℝ)*(sp3) + (29220512513/100000000000000 : ℝ)*(sp4) + (3967035013/20000000000000 : ℝ)*(sp7) + (494741153899827/12500000000000 : ℝ)*(f.failure) + (8001042353561269/100000000000000 : ℝ)*(f.sum) + (2803582310661/1346500000000000000000000000 : ℝ)*base66 + (10207651186572368627/673250000000000000000000000000000 : ℝ)*base67 + (290908230486618627/673250000000000000000000000000000 : ℝ)*base69 + (12355131351393618627/673250000000000000000000000000000 : ℝ)*base71 + (1496159291317/538600000000000000000000000 : ℝ)*base74 + (2723490917288118627/673250000000000000000000000000000 : ℝ)*base75 + (1881940383633618627/673250000000000000000000000000000 : ℝ)*base77 + (1384903574717618627/673250000000000000000000000000000 : ℝ)*base79 + (589259169409/2693000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (170781/31250000000000000000 : ℝ)*base89 + (170781/31250000000000000000 : ℝ)*base91 + (170781/31250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1482431014389208551204706641/168312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16538971/1000000000000 : ℝ)*(base19) + (82178507/5000000000000 : ℝ)*(base23) + (6756019/3125000000000 : ℝ)*(upper3) + (55032823/100000000000000 : ℝ)*(lower4) + (196164287/100000000000000 : ℝ)*(upper5) + (3004940345837889/50000000000000 : ℝ)*(major0) + (3004940345837889/50000000000000 : ℝ)*(major1) + (3004940345837889/50000000000000 : ℝ)*(major2) + (47668102789/100000000000000 : ℝ)*(sp1) + (5950425321/12500000000000 : ℝ)*(sp2) + (8041713009316213/100000000000000 : ℝ)*(sp4) + (2010415921829081/25000000000000 : ℝ)*(sp5) + (1608332752468701/20000000000000 : ℝ)*(sp6) + (1989024040224153/50000000000000 : ℝ)*(sp7) + (1989024040224153/50000000000000 : ℝ)*(f.failure) + (8041713009316213/100000000000000 : ℝ)*(f.sum) + (8212942823363/1346500000000000000000000000 : ℝ)*base66 + (918786607308201953/673250000000000000000000000000000 : ℝ)*base68 + (4032140146295951953/673250000000000000000000000000000 : ℝ)*base70 + (3524870000665451953/673250000000000000000000000000000 : ℝ)*base72 + (1947759606851/2693000000000000000000000000 : ℝ)*base73 + (1691602507276798047/673250000000000000000000000000000 : ℝ)*base75 + (7052151191502451953/673250000000000000000000000000000 : ℝ)*base78 + (9108297612983951953/673250000000000000000000000000000 : ℝ)*base80 + (10058381783/6732500000000000000000000 : ℝ)*base81 + (1638159/125000000000000000000 : ℝ)*base89 + (1638159/125000000000000000000 : ℝ)*base91 + (1638159/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1224_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (141/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1224_s7_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128276593/10000000000 : ℝ)*x 0 + (2695767551/5000000000 : ℝ)*x 1 + (1053393531/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128276593/10000000000 : ℝ)^8417 ≤ (12940481151567/100000000000000 : ℝ)^6369 := by
    have hnat : (2128276593 : ℕ)^8417*100000000000000^6369 ≤ 12940481151567^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128276593 10000000000 12940481151567 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695767551/5000000000 : ℝ)^8417 ≤ (4420206380563/10000000000000 : ℝ)^6369 := by
    have hnat : (2695767551 : ℕ)^8417*10000000000000^6369 ≤ 4420206380563^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695767551 5000000000 4420206380563 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053393531/2000000000 : ℝ)^8417 ≤ (42857455029429/100000000000000 : ℝ)^6369 := by
    have hnat : (1053393531 : ℕ)^8417*100000000000000^6369 ≤ 42857455029429^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053393531 2000000000 42857455029429 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128276593/10000000000 : ℝ), (2695767551/5000000000 : ℝ), (1053393531/2000000000 : ℝ)] ![(12940481151567/100000000000000 : ℝ), (4420206380563/10000000000000 : ℝ), (42857455029429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128276593/10000000000 : ℝ)|^8417 ≤ (12940481151567/100000000000000 : ℝ)^6369
        have hw : |(-2128276593/10000000000 : ℝ)|=(2128276593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695767551/5000000000 : ℝ)|^8417 ≤ (4420206380563/10000000000000 : ℝ)^6369
        have hw : |(2695767551/5000000000 : ℝ)|=(2695767551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053393531/2000000000 : ℝ)|^8417 ≤ (42857455029429/100000000000000 : ℝ)^6369
        have hw : |(1053393531/2000000000 : ℝ)|=(1053393531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s7_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344402499/10000000000 : ℝ)*x 0 + (-219143967/1000000000 : ℝ)*x 1 + (5266967673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344402499/10000000000 : ℝ)^8417 ≤ (43692116195463/100000000000000 : ℝ)^6369 := by
    have hnat : (5344402499 : ℕ)^8417*100000000000000^6369 ≤ 43692116195463^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344402499 10000000000 43692116195463 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219143967/1000000000 : ℝ)^8417 ≤ (13450428561821/100000000000000 : ℝ)^6369 := by
    have hnat : (219143967 : ℕ)^8417*100000000000000^6369 ≤ 13450428561821^6369*1000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219143967 1000000000 13450428561821 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266967673/10000000000 : ℝ)^8417 ≤ (42857455222993/100000000000000 : ℝ)^6369 := by
    have hnat : (5266967673 : ℕ)^8417*100000000000000^6369 ≤ 42857455222993^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266967673 10000000000 42857455222993 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344402499/10000000000 : ℝ), (-219143967/1000000000 : ℝ), (5266967673/10000000000 : ℝ)] ![(43692116195463/100000000000000 : ℝ), (13450428561821/100000000000000 : ℝ), (42857455222993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344402499/10000000000 : ℝ)|^8417 ≤ (43692116195463/100000000000000 : ℝ)^6369
        have hw : |(5344402499/10000000000 : ℝ)|=(5344402499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-219143967/1000000000 : ℝ)|^8417 ≤ (13450428561821/100000000000000 : ℝ)^6369
        have hw : |(-219143967/1000000000 : ℝ)|=(219143967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266967673/10000000000 : ℝ)|^8417 ≤ (42857455222993/100000000000000 : ℝ)^6369
        have hw : |(5266967673/10000000000 : ℝ)|=(5266967673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s7_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344402509/10000000000 : ℝ)*x 0 + (5266967671/10000000000 : ℝ)*x 1 + (-109571983/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344402509/10000000000 : ℝ)^8417 ≤ (8738423260701/20000000000000 : ℝ)^6369 := by
    have hnat : (5344402509 : ℕ)^8417*20000000000000^6369 ≤ 8738423260701^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344402509 10000000000 8738423260701 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266967671/10000000000 : ℝ)^8417 ≤ (21428727600743/50000000000000 : ℝ)^6369 := by
    have hnat : (5266967671 : ℕ)^8417*50000000000000^6369 ≤ 21428727600743^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266967671 10000000000 21428727600743 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109571983/500000000 : ℝ)^8417 ≤ (13450428480707/100000000000000 : ℝ)^6369 := by
    have hnat : (109571983 : ℕ)^8417*100000000000000^6369 ≤ 13450428480707^6369*500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109571983 500000000 13450428480707 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344402509/10000000000 : ℝ), (5266967671/10000000000 : ℝ), (-109571983/500000000 : ℝ)] ![(8738423260701/20000000000000 : ℝ), (21428727600743/50000000000000 : ℝ), (13450428480707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344402509/10000000000 : ℝ)|^8417 ≤ (8738423260701/20000000000000 : ℝ)^6369
        have hw : |(5344402509/10000000000 : ℝ)|=(5344402509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266967671/10000000000 : ℝ)|^8417 ≤ (21428727600743/50000000000000 : ℝ)^6369
        have hw : |(5266967671/10000000000 : ℝ)|=(5266967671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-109571983/500000000 : ℝ)|^8417 ≤ (13450428480707/100000000000000 : ℝ)^6369
        have hw : |(-109571983/500000000 : ℝ)|=(109571983/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s7_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4353247609/10000000000 : ℝ)*x 0 + (4229117363/10000000000 : ℝ)*x 1 + (2240466591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353247609/10000000000 : ℝ)^8417 ≤ (16658699291343/50000000000000 : ℝ)^6369 := by
    have hnat : (4353247609 : ℕ)^8417*50000000000000^6369 ≤ 16658699291343^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353247609 10000000000 16658699291343 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229117363/10000000000 : ℝ)^8417 ≤ (2004229906403/6250000000000 : ℝ)^6369 := by
    have hnat : (4229117363 : ℕ)^8417*6250000000000^6369 ≤ 2004229906403^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229117363 10000000000 2004229906403 6250000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2240466591/5000000000 : ℝ)^8417 ≤ (3461492289747/10000000000000 : ℝ)^6369 := by
    have hnat : (2240466591 : ℕ)^8417*10000000000000^6369 ≤ 3461492289747^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240466591 5000000000 3461492289747 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353247609/10000000000 : ℝ), (4229117363/10000000000 : ℝ), (2240466591/5000000000 : ℝ)] ![(16658699291343/50000000000000 : ℝ), (2004229906403/6250000000000 : ℝ), (3461492289747/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353247609/10000000000 : ℝ)|^8417 ≤ (16658699291343/50000000000000 : ℝ)^6369
        have hw : |(4353247609/10000000000 : ℝ)|=(4353247609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229117363/10000000000 : ℝ)|^8417 ≤ (2004229906403/6250000000000 : ℝ)^6369
        have hw : |(4229117363/10000000000 : ℝ)|=(4229117363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2240466591/5000000000 : ℝ)|^8417 ≤ (3461492289747/10000000000000 : ℝ)^6369
        have hw : |(2240466591/5000000000 : ℝ)|=(2240466591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s7_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1064140643/5000000000 : ℝ)*x 0 + (5267281613/10000000000 : ℝ)*x 1 + (5391220009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064140643/5000000000 : ℝ)^8417 ≤ (6470259430897/50000000000000 : ℝ)^6369 := by
    have hnat : (1064140643 : ℕ)^8417*50000000000000^6369 ≤ 6470259430897^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064140643 5000000000 6470259430897 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267281613/10000000000 : ℝ)^8417 ≤ (42860831224419/100000000000000 : ℝ)^6369 := by
    have hnat : (5267281613 : ℕ)^8417*100000000000000^6369 ≤ 42860831224419^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267281613 10000000000 42860831224419 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391220009/10000000000 : ℝ)^8417 ≤ (22099324952551/50000000000000 : ℝ)^6369 := by
    have hnat : (5391220009 : ℕ)^8417*50000000000000^6369 ≤ 22099324952551^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391220009 10000000000 22099324952551 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1064140643/5000000000 : ℝ), (5267281613/10000000000 : ℝ), (5391220009/10000000000 : ℝ)] ![(6470259430897/50000000000000 : ℝ), (42860831224419/100000000000000 : ℝ), (22099324952551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1064140643/5000000000 : ℝ)|^8417 ≤ (6470259430897/50000000000000 : ℝ)^6369
        have hw : |(-1064140643/5000000000 : ℝ)|=(1064140643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267281613/10000000000 : ℝ)|^8417 ≤ (42860831224419/100000000000000 : ℝ)^6369
        have hw : |(5267281613/10000000000 : ℝ)|=(5267281613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391220009/10000000000 : ℝ)|^8417 ≤ (22099324952551/50000000000000 : ℝ)^6369
        have hw : |(5391220009/10000000000 : ℝ)|=(5391220009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s7_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656328729/5000000000 : ℝ)*x 0 + (-2067187327/10000000000 : ℝ)*x 1 + (5391220003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656328729/5000000000 : ℝ)^8417 ≤ (21674733237549/50000000000000 : ℝ)^6369 := by
    have hnat : (2656328729 : ℕ)^8417*50000000000000^6369 ≤ 21674733237549^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656328729 5000000000 21674733237549 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067187327/10000000000 : ℝ)^8417 ≤ (6225941831043/50000000000000 : ℝ)^6369 := by
    have hnat : (2067187327 : ℕ)^8417*50000000000000^6369 ≤ 6225941831043^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067187327 10000000000 6225941831043 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391220003/10000000000 : ℝ)^8417 ≤ (1381207807503/3125000000000 : ℝ)^6369 := by
    have hnat : (5391220003 : ℕ)^8417*3125000000000^6369 ≤ 1381207807503^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391220003 10000000000 1381207807503 3125000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656328729/5000000000 : ℝ), (-2067187327/10000000000 : ℝ), (5391220003/10000000000 : ℝ)] ![(21674733237549/50000000000000 : ℝ), (6225941831043/50000000000000 : ℝ), (1381207807503/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656328729/5000000000 : ℝ)|^8417 ≤ (21674733237549/50000000000000 : ℝ)^6369
        have hw : |(2656328729/5000000000 : ℝ)|=(2656328729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067187327/10000000000 : ℝ)|^8417 ≤ (6225941831043/50000000000000 : ℝ)^6369
        have hw : |(-2067187327/10000000000 : ℝ)|=(2067187327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391220003/10000000000 : ℝ)|^8417 ≤ (1381207807503/3125000000000 : ℝ)^6369
        have hw : |(5391220003/10000000000 : ℝ)|=(5391220003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s7_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312657457/10000000000 : ℝ)*x 0 + (1078244001/2000000000 : ℝ)*x 1 + (-1033593663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312657457/10000000000 : ℝ)^8417 ≤ (8669893292863/20000000000000 : ℝ)^6369 := by
    have hnat : (5312657457 : ℕ)^8417*20000000000000^6369 ≤ 8669893292863^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312657457 10000000000 8669893292863 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078244001/2000000000 : ℝ)^8417 ≤ (8839729972353/20000000000000 : ℝ)^6369 := by
    have hnat : (1078244001 : ℕ)^8417*20000000000000^6369 ≤ 8839729972353^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078244001 2000000000 8839729972353 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1033593663/5000000000 : ℝ)^8417 ≤ (6225941827063/50000000000000 : ℝ)^6369 := by
    have hnat : (1033593663 : ℕ)^8417*50000000000000^6369 ≤ 6225941827063^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033593663 5000000000 6225941827063 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312657457/10000000000 : ℝ), (1078244001/2000000000 : ℝ), (-1033593663/5000000000 : ℝ)] ![(8669893292863/20000000000000 : ℝ), (8839729972353/20000000000000 : ℝ), (6225941827063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312657457/10000000000 : ℝ)|^8417 ≤ (8669893292863/20000000000000 : ℝ)^6369
        have hw : |(5312657457/10000000000 : ℝ)|=(5312657457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078244001/2000000000 : ℝ)|^8417 ≤ (8839729972353/20000000000000 : ℝ)^6369
        have hw : |(1078244001/2000000000 : ℝ)|=(1078244001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1033593663/5000000000 : ℝ)|^8417 ≤ (6225941827063/50000000000000 : ℝ)^6369
        have hw : |(-1033593663/5000000000 : ℝ)|=(1033593663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s7_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088314277/2500000000 : ℝ)*x 0 + (4480298533/10000000000 : ℝ)*x 1 + (4229754307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088314277/2500000000 : ℝ)^8417 ≤ (33317494660217/100000000000000 : ℝ)^6369 := by
    have hnat : (1088314277 : ℕ)^8417*100000000000000^6369 ≤ 33317494660217^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088314277 2500000000 33317494660217 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480298533/10000000000 : ℝ)^8417 ≤ (6921688789313/20000000000000 : ℝ)^6369 := by
    have hnat : (4480298533 : ℕ)^8417*20000000000000^6369 ≤ 6921688789313^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480298533 10000000000 6921688789313 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229754307/10000000000 : ℝ)^8417 ≤ (16037030683499/50000000000000 : ℝ)^6369 := by
    have hnat : (4229754307 : ℕ)^8417*50000000000000^6369 ≤ 16037030683499^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229754307 10000000000 16037030683499 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088314277/2500000000 : ℝ), (4480298533/10000000000 : ℝ), (4229754307/10000000000 : ℝ)] ![(33317494660217/100000000000000 : ℝ), (6921688789313/20000000000000 : ℝ), (16037030683499/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088314277/2500000000 : ℝ)|^8417 ≤ (33317494660217/100000000000000 : ℝ)^6369
        have hw : |(1088314277/2500000000 : ℝ)|=(1088314277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480298533/10000000000 : ℝ)|^8417 ≤ (6921688789313/20000000000000 : ℝ)^6369
        have hw : |(4480298533/10000000000 : ℝ)|=(4480298533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229754307/10000000000 : ℝ)|^8417 ≤ (16037030683499/50000000000000 : ℝ)^6369
        have hw : |(4229754307/10000000000 : ℝ)|=(4229754307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (358/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2819/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2863/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (141/1000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2863/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2863/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (141/1000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2863/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2863/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (141/1000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2863/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2863/25000 : ℝ) ^ (263/64 : ℝ) ≤ (6785166484746399/50000000000000000000 : ℝ) := by
    have hpowers : (2863/25000 : ℝ)^263 ≤ (6785166484746399/50000000000000000000 : ℝ)^64 := by
      have hnat : (2863 : ℕ)^263*50000000000000000000^64 ≤ 6785166484746399^64*25000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2863 25000 6785166484746399 50000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2863/25000 : ℝ)) (X := (6785166484746399/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (141/1000 : ℝ) ^ (263/64 : ℝ) ≤ (31902321770794723/100000000000000000000 : ℝ) := by
    have hpowers : (141/1000 : ℝ)^263 ≤ (31902321770794723/100000000000000000000 : ℝ)^64 := by
      have hnat : (141 : ℕ)^263*100000000000000000000^64 ≤ 31902321770794723^64*1000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        141 1000 31902321770794723 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (141/1000 : ℝ)) (X := (31902321770794723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006785166484746399/25000000000000000000 : ℝ) ≤ (5000330194732357/5000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (25006785166484746399/25000000000000000000 : ℝ)^64 ≤ (5000330194732357/5000000000000000 : ℝ)^263 := by
      have hnat : (25006785166484746399 : ℕ)^64*5000000000000000^263 ≤ 5000330194732357^263*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006785166484746399 25000000000000000000 5000330194732357 5000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000330194732357/5000000000000000 : ℝ)) (X := (25006785166484746399/25000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045472654740287521/100000000000000000000 : ℝ) ≤ (1250138296072759/1250000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (100045472654740287521/100000000000000000000 : ℝ)^64 ≤ (1250138296072759/1250000000000000 : ℝ)^263 := by
      have hnat : (100045472654740287521 : ℕ)^64*1250000000000000^263 ≤ 1250138296072759^263*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045472654740287521 100000000000000000000 1250138296072759 1250000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250138296072759/1250000000000000 : ℝ)) (X := (100045472654740287521/100000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031902321770794723/50000000000000000000 : ℝ) ≤ (1000155234769943/1000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50031902321770794723/50000000000000000000 : ℝ)^64 ≤ (1000155234769943/1000000000000000 : ℝ)^263 := by
      have hnat : (50031902321770794723 : ℕ)^64*1000000000000000^263 ≤ 1000155234769943^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031902321770794723 50000000000000000000 1000155234769943 1000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000155234769943/1000000000000000 : ℝ)) (X := (50031902321770794723/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6785166484746399/50000000000000000000 : ℝ) ≤ ((165447087534991219/165500000000000000 : ℝ)+2*(222989558679/132400000000000 : ℝ)*(2863/25000 : ℝ))^(263/64 : ℝ) := by
    rw [show (165447087534991219/165500000000000000 : ℝ)+2*(222989558679/132400000000000 : ℝ)*(2863/25000 : ℝ)=(5000330194732357/5000000000000000 : ℝ) by norm_num, show 1+2*(6785166484746399/50000000000000000000 : ℝ)=(25006785166484746399/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31902321770794723/100000000000000000000 : ℝ)+(6785166484746399/50000000000000000000 : ℝ) ≤ ((165447087534991219/165500000000000000 : ℝ)+(222989558679/132400000000000 : ℝ)*((141/1000 : ℝ)+(2863/25000 : ℝ)))^(263/64 : ℝ) := by
    rw [show (165447087534991219/165500000000000000 : ℝ)+(222989558679/132400000000000 : ℝ)*((141/1000 : ℝ)+(2863/25000 : ℝ))=(1250138296072759/1250000000000000 : ℝ) by norm_num, show 1+(31902321770794723/100000000000000000000 : ℝ)+(6785166484746399/50000000000000000000 : ℝ)=(100045472654740287521/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31902321770794723/100000000000000000000 : ℝ) ≤ ((165447087534991219/165500000000000000 : ℝ)+2*(222989558679/132400000000000 : ℝ)*(141/1000 : ℝ))^(263/64 : ℝ) := by
    rw [show (165447087534991219/165500000000000000 : ℝ)+2*(222989558679/132400000000000 : ℝ)*(141/1000 : ℝ)=(1000155234769943/1000000000000000 : ℝ) by norm_num, show 1+2*(31902321770794723/100000000000000000000 : ℝ)=(50031902321770794723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (165447087534991219/165500000000000000 : ℝ)*(X 1 0+X 2 0)+(222989558679/132400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (2863/25000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (165447087534991219/165500000000000000 : ℝ)) (alpha := (222989558679/132400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (165447087534991219/165500000000000000 : ℝ)*(X 0 1+X 2 1)+(222989558679/132400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (2863/25000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (165447087534991219/165500000000000000 : ℝ)) (alpha := (222989558679/132400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (165447087534991219/165500000000000000 : ℝ)*(X 0 2+X 1 2)+(222989558679/132400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (2863/25000 : ℝ)) (hi := (141/1000 : ℝ)) (c := (165447087534991219/165500000000000000 : ℝ)) (alpha := (222989558679/132400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128276593/10000000000 : ℝ)*X 0 0+(2695767551/5000000000 : ℝ)*X 0 1+(1053393531/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344402499/10000000000 : ℝ)*X 1 0+(-219143967/1000000000 : ℝ)*X 1 1+(5266967673/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344402509/10000000000 : ℝ)*X 2 0+(5266967671/10000000000 : ℝ)*X 2 1+(-109571983/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353247609/10000000000 : ℝ)*X 0 0+(4229117363/10000000000 : ℝ)*X 0 1+(2240466591/5000000000 : ℝ)*X 0 2+(4353247609/10000000000 : ℝ)*X 1 0+(4229117363/10000000000 : ℝ)*X 1 1+(2240466591/5000000000 : ℝ)*X 1 2+(4353247609/10000000000 : ℝ)*X 2 0+(4229117363/10000000000 : ℝ)*X 2 1+(2240466591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1064140643/5000000000 : ℝ)*X 0 0+(5267281613/10000000000 : ℝ)*X 0 1+(5391220009/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656328729/5000000000 : ℝ)*X 1 0+(-2067187327/10000000000 : ℝ)*X 1 1+(5391220003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312657457/10000000000 : ℝ)*X 2 0+(1078244001/2000000000 : ℝ)*X 2 1+(-1033593663/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088314277/2500000000 : ℝ)*X 0 0+(4480298533/10000000000 : ℝ)*X 0 1+(4229754307/10000000000 : ℝ)*X 0 2+(1088314277/2500000000 : ℝ)*X 1 0+(4480298533/10000000000 : ℝ)*X 1 1+(4229754307/10000000000 : ℝ)*X 1 2+(1088314277/2500000000 : ℝ)*X 2 0+(4480298533/10000000000 : ℝ)*X 2 1+(4229754307/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (82777979233618139709138999/8275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1923719873/100000000000000 : ℝ)*(base19) + (1816992683/100000000000000 : ℝ)*(base23) + (32533597/50000000000000 : ℝ)*(lower2) + (238798143/100000000000000 : ℝ)*(upper3) + (84457779/50000000000000 : ℝ)*(upper5) + (5999551088661293/100000000000000 : ℝ)*(major0) + (5999551088661293/100000000000000 : ℝ)*(major1) + (5999551088661293/100000000000000 : ℝ)*(major2) + (321113435627583/4000000000000 : ℝ)*(sp0) + (8027889189657829/100000000000000 : ℝ)*(sp1) + (4013944648192509/50000000000000 : ℝ)*(sp2) + (1985591204349441/50000000000000 : ℝ)*(sp3) + (55222688127/100000000000000 : ℝ)*(sp4) + (1770112497/6250000000000 : ℝ)*(sp7) + (1985605365249417/50000000000000 : ℝ)*(f.failure) + (4013945556688851/50000000000000 : ℝ)*(f.sum) + (39695918477393/6620000000000000000000000000 : ℝ)*base66 + (241784256286469917/16550000000000000000000000000000 : ℝ)*base67 + (21643690341680083/16550000000000000000000000000000 : ℝ)*base70 + (121948725966369917/16550000000000000000000000000000 : ℝ)*base71 + (13807851665707/6620000000000000000000000000 : ℝ)*base73 + (589803802592369917/16550000000000000000000000000000 : ℝ)*base75 + (19830084409680083/16550000000000000000000000000000 : ℝ)*base78 + (132615779637119917/16550000000000000000000000000000 : ℝ)*base79 + (7742609280987/6620000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2565551/125000000000000000000 : ℝ)*base89 + (2565551/125000000000000000000 : ℝ)*base91 + (2565551/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8278217653981687361357739/2068750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (737309229/100000000000000 : ℝ)*(base19) + (198637031/25000000000000 : ℝ)*(base23) + (78389173/100000000000000 : ℝ)*(upper3) + (1702853/6250000000000 : ℝ)*(lower4) + (85878423/100000000000000 : ℝ)*(upper5) + (6029917620349679/100000000000000 : ℝ)*(major0) + (6029917620349679/100000000000000 : ℝ)*(major1) + (6029917620349679/100000000000000 : ℝ)*(major2) + (5162464833/25000000000000 : ℝ)*(sp1) + (21900525249/100000000000000 : ℝ)*(sp2) + (8068524223536059/100000000000000 : ℝ)*(sp4) + (8068502836367497/100000000000000 : ℝ)*(sp5) + (4034250764231343/50000000000000 : ℝ)*(sp6) + (3991310883778111/100000000000000 : ℝ)*(sp7) + (3991310883778111/100000000000000 : ℝ)*(f.failure) + (8068524223536059/100000000000000 : ℝ)*(f.sum) + (8611753460639/6620000000000000000000000000 : ℝ)*base66 + (2132742544480049/16550000000000000000000000000000 : ℝ)*base68 + (257234182345380049/16550000000000000000000000000000 : ℝ)*base70 + (207628828850080049/16550000000000000000000000000000 : ℝ)*base72 + (16181916036439/6620000000000000000000000000 : ℝ)*base74 + (411364537499180049/16550000000000000000000000000000 : ℝ)*base76 + (227364471306030049/16550000000000000000000000000000 : ℝ)*base78 + (20238300545419951/16550000000000000000000000000000 : ℝ)*base79 + (39671535574579/6620000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1270233/250000000000000000000 : ℝ)*base89 + (1270233/250000000000000000000 : ℝ)*base91 + (1270233/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1224_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (141/1000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2863/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1224_s8_0 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128282653/10000000000 : ℝ)*x 0 + (5391491323/10000000000 : ℝ)*x 1 + (1316751809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128282653/10000000000 : ℝ)^8417 ≤ (6470264923109/50000000000000 : ℝ)^6369 := by
    have hnat : (2128282653 : ℕ)^8417*50000000000000^6369 ≤ 6470264923109^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128282653 10000000000 6470264923109 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391491323/10000000000 : ℝ)^8417 ≤ (8840317894937/20000000000000 : ℝ)^6369 := by
    have hnat : (5391491323 : ℕ)^8417*20000000000000^6369 ≤ 8840317894937^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391491323 10000000000 8840317894937 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316751809/2500000000 : ℝ)^8417 ≤ (42857880666153/100000000000000 : ℝ)^6369 := by
    have hnat : (1316751809 : ℕ)^8417*100000000000000^6369 ≤ 42857880666153^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316751809 2500000000 42857880666153 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128282653/10000000000 : ℝ), (5391491323/10000000000 : ℝ), (1316751809/2500000000 : ℝ)] ![(6470264923109/50000000000000 : ℝ), (8840317894937/20000000000000 : ℝ), (42857880666153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128282653/10000000000 : ℝ)|^8417 ≤ (6470264923109/50000000000000 : ℝ)^6369
        have hw : |(-2128282653/10000000000 : ℝ)|=(2128282653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391491323/10000000000 : ℝ)|^8417 ≤ (8840317894937/20000000000000 : ℝ)^6369
        have hw : |(5391491323/10000000000 : ℝ)|=(5391491323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316751809/2500000000 : ℝ)|^8417 ≤ (42857880666153/100000000000000 : ℝ)^6369
        have hw : |(1316751809/2500000000 : ℝ)|=(1316751809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s8_1 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336097683/2500000000 : ℝ)*x 0 + (-2191402889/10000000000 : ℝ)*x 1 + (5267007239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336097683/2500000000 : ℝ)^8417 ≤ (10922997265813/25000000000000 : ℝ)^6369 := by
    have hnat : (1336097683 : ℕ)^8417*25000000000000^6369 ≤ 10922997265813^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336097683 2500000000 10922997265813 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2191402889/10000000000 : ℝ)^8417 ≤ (6725065109689/50000000000000 : ℝ)^6369 := by
    have hnat : (2191402889 : ℕ)^8417*50000000000000^6369 ≤ 6725065109689^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191402889 10000000000 6725065109689 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267007239/10000000000 : ℝ)^8417 ≤ (21428940349207/50000000000000 : ℝ)^6369 := by
    have hnat : (5267007239 : ℕ)^8417*50000000000000^6369 ≤ 21428940349207^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267007239 10000000000 21428940349207 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336097683/2500000000 : ℝ), (-2191402889/10000000000 : ℝ), (5267007239/10000000000 : ℝ)] ![(10922997265813/25000000000000 : ℝ), (6725065109689/50000000000000 : ℝ), (21428940349207/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336097683/2500000000 : ℝ)|^8417 ≤ (10922997265813/25000000000000 : ℝ)^6369
        have hw : |(1336097683/2500000000 : ℝ)|=(1336097683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2191402889/10000000000 : ℝ)|^8417 ≤ (6725065109689/50000000000000 : ℝ)^6369
        have hw : |(-2191402889/10000000000 : ℝ)|=(2191402889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267007239/10000000000 : ℝ)|^8417 ≤ (21428940349207/50000000000000 : ℝ)^6369
        have hw : |(5267007239/10000000000 : ℝ)|=(5267007239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s8_2 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (267219537/500000000 : ℝ)*x 0 + (2633503617/5000000000 : ℝ)*x 1 + (-438280577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267219537/500000000 : ℝ)^8417 ≤ (8738397829937/20000000000000 : ℝ)^6369 := by
    have hnat : (267219537 : ℕ)^8417*20000000000000^6369 ≤ 8738397829937^6369*500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267219537 500000000 8738397829937 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633503617/5000000000 : ℝ)^8417 ≤ (21428940322323/50000000000000 : ℝ)^6369 := by
    have hnat : (2633503617 : ℕ)^8417*50000000000000^6369 ≤ 21428940322323^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633503617 5000000000 21428940322323 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438280577/2000000000 : ℝ)^8417 ≤ (3362532546733/25000000000000 : ℝ)^6369 := by
    have hnat : (438280577 : ℕ)^8417*25000000000000^6369 ≤ 3362532546733^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438280577 2000000000 3362532546733 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267219537/500000000 : ℝ), (2633503617/5000000000 : ℝ), (-438280577/2000000000 : ℝ)] ![(8738397829937/20000000000000 : ℝ), (21428940322323/50000000000000 : ℝ), (3362532546733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267219537/500000000 : ℝ)|^8417 ≤ (8738397829937/20000000000000 : ℝ)^6369
        have hw : |(267219537/500000000 : ℝ)|=(267219537/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633503617/5000000000 : ℝ)|^8417 ≤ (21428940322323/50000000000000 : ℝ)^6369
        have hw : |(2633503617/5000000000 : ℝ)|=(2633503617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438280577/2000000000 : ℝ)|^8417 ≤ (3362532546733/25000000000000 : ℝ)^6369
        have hw : |(-438280577/2000000000 : ℝ)|=(438280577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s8_3 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (68019527/156250000 : ℝ)*x 0 + (4229201307/10000000000 : ℝ)*x 1 + (896169737/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68019527/156250000 : ℝ)^8417 ≤ (33317420015283/100000000000000 : ℝ)^6369 := by
    have hnat : (68019527 : ℕ)^8417*100000000000000^6369 ≤ 33317420015283^6369*156250000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68019527 156250000 33317420015283 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229201307/10000000000 : ℝ)^8417 ≤ (3206851969401/10000000000000 : ℝ)^6369 := by
    have hnat : (4229201307 : ℕ)^8417*10000000000000^6369 ≤ 3206851969401^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229201307 10000000000 3206851969401 10000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896169737/2000000000 : ℝ)^8417 ≤ (34614060274631/100000000000000 : ℝ)^6369 := by
    have hnat : (896169737 : ℕ)^8417*100000000000000^6369 ≤ 34614060274631^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896169737 2000000000 34614060274631 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68019527/156250000 : ℝ), (4229201307/10000000000 : ℝ), (896169737/2000000000 : ℝ)] ![(33317420015283/100000000000000 : ℝ), (3206851969401/10000000000000 : ℝ), (34614060274631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68019527/156250000 : ℝ)|^8417 ≤ (33317420015283/100000000000000 : ℝ)^6369
        have hw : |(68019527/156250000 : ℝ)|=(68019527/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229201307/10000000000 : ℝ)|^8417 ≤ (3206851969401/10000000000000 : ℝ)^6369
        have hw : |(4229201307/10000000000 : ℝ)|=(4229201307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(896169737/2000000000 : ℝ)|^8417 ≤ (34614060274631/100000000000000 : ℝ)^6369
        have hw : |(896169737/2000000000 : ℝ)|=(896169737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s8_4 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128287419/10000000000 : ℝ)*x 0 + (658415141/1250000000 : ℝ)*x 1 + (2695588119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128287419/10000000000 : ℝ)^8417 ≤ (6470284071533/50000000000000 : ℝ)^6369 := by
    have hnat : (2128287419 : ℕ)^8417*50000000000000^6369 ≤ 6470284071533^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128287419 10000000000 6470284071533 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658415141/1250000000 : ℝ)^8417 ≤ (669707127493/1562500000000 : ℝ)^6369 := by
    have hnat : (658415141 : ℕ)^8417*1562500000000^6369 ≤ 669707127493^6369*1250000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658415141 1250000000 669707127493 1562500000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695588119/5000000000 : ℝ)^8417 ≤ (44198175669747/100000000000000 : ℝ)^6369 := by
    have hnat : (2695588119 : ℕ)^8417*100000000000000^6369 ≤ 44198175669747^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695588119 5000000000 44198175669747 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128287419/10000000000 : ℝ), (658415141/1250000000 : ℝ), (2695588119/5000000000 : ℝ)] ![(6470284071533/50000000000000 : ℝ), (669707127493/1562500000000 : ℝ), (44198175669747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128287419/10000000000 : ℝ)|^8417 ≤ (6470284071533/50000000000000 : ℝ)^6369
        have hw : |(-2128287419/10000000000 : ℝ)|=(2128287419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658415141/1250000000 : ℝ)|^8417 ≤ (669707127493/1562500000000 : ℝ)^6369
        have hw : |(658415141/1250000000 : ℝ)|=(658415141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695588119/5000000000 : ℝ)|^8417 ≤ (44198175669747/100000000000000 : ℝ)^6369
        have hw : |(2695588119/5000000000 : ℝ)|=(2695588119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s8_5 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312666733/10000000000 : ℝ)*x 0 + (-2067233257/10000000000 : ℝ)*x 1 + (2695588513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312666733/10000000000 : ℝ)^8417 ≤ (10837391622923/25000000000000 : ℝ)^6369 := by
    have hnat : (5312666733 : ℕ)^8417*25000000000000^6369 ≤ 10837391622923^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312666733 10000000000 10837391622923 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2067233257/10000000000 : ℝ)^8417 ≤ (12452249289959/100000000000000 : ℝ)^6369 := by
    have hnat : (2067233257 : ℕ)^8417*100000000000000^6369 ≤ 12452249289959^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067233257 10000000000 12452249289959 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695588513/5000000000 : ℝ)^8417 ≤ (22099092103647/50000000000000 : ℝ)^6369 := by
    have hnat : (2695588513 : ℕ)^8417*50000000000000^6369 ≤ 22099092103647^6369*5000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695588513 5000000000 22099092103647 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312666733/10000000000 : ℝ), (-2067233257/10000000000 : ℝ), (2695588513/5000000000 : ℝ)] ![(10837391622923/25000000000000 : ℝ), (12452249289959/100000000000000 : ℝ), (22099092103647/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312666733/10000000000 : ℝ)|^8417 ≤ (10837391622923/25000000000000 : ℝ)^6369
        have hw : |(5312666733/10000000000 : ℝ)|=(5312666733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2067233257/10000000000 : ℝ)|^8417 ≤ (12452249289959/100000000000000 : ℝ)^6369
        have hw : |(-2067233257/10000000000 : ℝ)|=(2067233257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695588513/5000000000 : ℝ)|^8417 ≤ (22099092103647/50000000000000 : ℝ)^6369
        have hw : |(2695588513/5000000000 : ℝ)|=(2695588513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s8_6 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328166797/2500000000 : ℝ)*x 0 + (1078235279/2000000000 : ℝ)*x 1 + (-2067233499/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328166797/2500000000 : ℝ)^8417 ≤ (5418696424771/12500000000000 : ℝ)^6369 := by
    have hnat : (1328166797 : ℕ)^8417*12500000000000^6369 ≤ 5418696424771^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328166797 2500000000 5418696424771 12500000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078235279/2000000000 : ℝ)^8417 ≤ (11049544342689/25000000000000 : ℝ)^6369 := by
    have hnat : (1078235279 : ℕ)^8417*25000000000000^6369 ≤ 11049544342689^6369*2000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078235279 2000000000 11049544342689 25000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2067233499/10000000000 : ℝ)^8417 ≤ (6226125608209/50000000000000 : ℝ)^6369 := by
    have hnat : (2067233499 : ℕ)^8417*50000000000000^6369 ≤ 6226125608209^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067233499 10000000000 6226125608209 50000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328166797/2500000000 : ℝ), (1078235279/2000000000 : ℝ), (-2067233499/10000000000 : ℝ)] ![(5418696424771/12500000000000 : ℝ), (11049544342689/25000000000000 : ℝ), (6226125608209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328166797/2500000000 : ℝ)|^8417 ≤ (5418696424771/12500000000000 : ℝ)^6369
        have hw : |(1328166797/2500000000 : ℝ)|=(1328166797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078235279/2000000000 : ℝ)|^8417 ≤ (11049544342689/25000000000000 : ℝ)^6369
        have hw : |(1078235279/2000000000 : ℝ)|=(1078235279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2067233499/10000000000 : ℝ)|^8417 ≤ (6226125608209/50000000000000 : ℝ)^6369
        have hw : |(-2067233499/10000000000 : ℝ)|=(2067233499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1224_s8_7 (p : ℝ) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1088314767/2500000000 : ℝ)*x 0 + (448021517/1000000000 : ℝ)*x 1 + (4229837249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1088314767/2500000000 : ℝ)^8417 ≤ (2082344655289/6250000000000 : ℝ)^6369 := by
    have hnat : (1088314767 : ℕ)^8417*6250000000000^6369 ≤ 2082344655289^6369*2500000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088314767 2500000000 2082344655289 6250000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448021517/1000000000 : ℝ)^8417 ≤ (6921518587873/20000000000000 : ℝ)^6369 := by
    have hnat : (448021517 : ℕ)^8417*20000000000000^6369 ≤ 6921518587873^6369*1000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448021517 1000000000 6921518587873 20000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229837249/10000000000 : ℝ)^8417 ≤ (32074892557871/100000000000000 : ℝ)^6369 := by
    have hnat : (4229837249 : ℕ)^8417*100000000000000^6369 ≤ 32074892557871^6369*10000000000^8417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229837249 10000000000 32074892557871 100000000000000 8417 6369 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8417/2048 : ℝ)) 8417 6369 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1088314767/2500000000 : ℝ), (448021517/1000000000 : ℝ), (4229837249/10000000000 : ℝ)] ![(2082344655289/6250000000000 : ℝ), (6921518587873/20000000000000 : ℝ), (32074892557871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1088314767/2500000000 : ℝ)|^8417 ≤ (2082344655289/6250000000000 : ℝ)^6369
        have hw : |(1088314767/2500000000 : ℝ)|=(1088314767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448021517/1000000000 : ℝ)|^8417 ≤ (6921518587873/20000000000000 : ℝ)^6369
        have hw : |(448021517/1000000000 : ℝ)|=(448021517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4229837249/10000000000 : ℝ)|^8417 ≤ (32074892557871/100000000000000 : ℝ)^6369
        have hw : |(4229837249/10000000000 : ℝ)|=(4229837249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1224_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11457/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7047/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (358/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2819/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (358/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2819/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (358/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (358/3125 : ℝ) ^ (263/64 : ℝ) ≤ (849363848419161/6250000000000000000 : ℝ) := by
    have hpowers : (358/3125 : ℝ)^263 ≤ (849363848419161/6250000000000000000 : ℝ)^64 := by
      have hnat : (358 : ℕ)^263*6250000000000000000^64 ≤ 849363848419161^64*3125^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        358 3125 849363848419161 6250000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (358/3125 : ℝ)) (X := (849363848419161/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2819/20000 : ℝ) ^ (263/64 : ℝ) ≤ (31855858527572627/100000000000000000000 : ℝ) := by
    have hpowers : (2819/20000 : ℝ)^263 ≤ (31855858527572627/100000000000000000000 : ℝ)^64 := by
      have hnat : (2819 : ℕ)^263*100000000000000000000^64 ≤ 31855858527572627^64*20000^263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2819 20000 31855858527572627 100000000000000000000 263 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2819/20000 : ℝ)) (X := (31855858527572627/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125849363848419161/3125000000000000000 : ℝ) ≤ (10000661337764691/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (3125849363848419161/3125000000000000000 : ℝ)^64 ≤ (10000661337764691/10000000000000000 : ℝ)^263 := by
      have hnat : (3125849363848419161 : ℕ)^64*10000000000000000^263 ≤ 10000661337764691^263*3125000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125849363848419161 3125000000000000000 10000661337764691 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000661337764691/10000000000000000 : ℝ)) (X := (3125849363848419161/3125000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045445680102279203/100000000000000000000 : ℝ) ≤ (5000552856195361/5000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (100045445680102279203/100000000000000000000 : ℝ)^64 ≤ (5000552856195361/5000000000000000 : ℝ)^263 := by
      have hnat : (100045445680102279203 : ℕ)^64*5000000000000000^263 ≤ 5000552856195361^263*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045445680102279203 100000000000000000000 5000552856195361 5000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000552856195361/5000000000000000 : ℝ)) (X := (100045445680102279203/100000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031855858527572627/50000000000000000000 : ℝ) ≤ (10001550087016753/10000000000000000 : ℝ) ^ (263/64 : ℝ) := by
    have hpowers : (50031855858527572627/50000000000000000000 : ℝ)^64 ≤ (10001550087016753/10000000000000000 : ℝ)^263 := by
      have hnat : (50031855858527572627 : ℕ)^64*10000000000000000^263 ≤ 10001550087016753^263*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031855858527572627 50000000000000000000 10001550087016753 10000000000000000 64 263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001550087016753/10000000000000000 : ℝ)) (X := (50031855858527572627/50000000000000000000 : ℝ)) (by norm_num) 263 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(849363848419161/6250000000000000000 : ℝ) ≤ ((3768794822704199611/3770000000000000000 : ℝ)+2*(63482089433/37700000000000 : ℝ)*(358/3125 : ℝ))^(263/64 : ℝ) := by
    rw [show (3768794822704199611/3770000000000000000 : ℝ)+2*(63482089433/37700000000000 : ℝ)*(358/3125 : ℝ)=(10000661337764691/10000000000000000 : ℝ) by norm_num, show 1+2*(849363848419161/6250000000000000000 : ℝ)=(3125849363848419161/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31855858527572627/100000000000000000000 : ℝ)+(849363848419161/6250000000000000000 : ℝ) ≤ ((3768794822704199611/3770000000000000000 : ℝ)+(63482089433/37700000000000 : ℝ)*((2819/20000 : ℝ)+(358/3125 : ℝ)))^(263/64 : ℝ) := by
    rw [show (3768794822704199611/3770000000000000000 : ℝ)+(63482089433/37700000000000 : ℝ)*((2819/20000 : ℝ)+(358/3125 : ℝ))=(5000552856195361/5000000000000000 : ℝ) by norm_num, show 1+(31855858527572627/100000000000000000000 : ℝ)+(849363848419161/6250000000000000000 : ℝ)=(100045445680102279203/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31855858527572627/100000000000000000000 : ℝ) ≤ ((3768794822704199611/3770000000000000000 : ℝ)+2*(63482089433/37700000000000 : ℝ)*(2819/20000 : ℝ))^(263/64 : ℝ) := by
    rw [show (3768794822704199611/3770000000000000000 : ℝ)+2*(63482089433/37700000000000 : ℝ)*(2819/20000 : ℝ)=(10001550087016753/10000000000000000 : ℝ) by norm_num, show 1+2*(31855858527572627/100000000000000000000 : ℝ)=(50031855858527572627/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3768794822704199611/3770000000000000000 : ℝ)*(X 1 0+X 2 0)+(63482089433/37700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (3768794822704199611/3770000000000000000 : ℝ)) (alpha := (63482089433/37700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3768794822704199611/3770000000000000000 : ℝ)*(X 0 1+X 2 1)+(63482089433/37700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (3768794822704199611/3770000000000000000 : ℝ)) (alpha := (63482089433/37700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3768794822704199611/3770000000000000000 : ℝ)*(X 0 2+X 1 2)+(63482089433/37700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (263/64 : ℝ)) (lo := (358/3125 : ℝ)) (hi := (2819/20000 : ℝ)) (c := (3768794822704199611/3770000000000000000 : ℝ)) (alpha := (63482089433/37700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2128282653/10000000000 : ℝ)*X 0 0+(5391491323/10000000000 : ℝ)*X 0 1+(1316751809/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336097683/2500000000 : ℝ)*X 1 0+(-2191402889/10000000000 : ℝ)*X 1 1+(5267007239/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267219537/500000000 : ℝ)*X 2 0+(2633503617/5000000000 : ℝ)*X 2 1+(-438280577/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((68019527/156250000 : ℝ)*X 0 0+(4229201307/10000000000 : ℝ)*X 0 1+(896169737/2000000000 : ℝ)*X 0 2+(68019527/156250000 : ℝ)*X 1 0+(4229201307/10000000000 : ℝ)*X 1 1+(896169737/2000000000 : ℝ)*X 1 2+(68019527/156250000 : ℝ)*X 2 0+(4229201307/10000000000 : ℝ)*X 2 1+(896169737/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2128287419/10000000000 : ℝ)*X 0 0+(658415141/1250000000 : ℝ)*X 0 1+(2695588119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312666733/10000000000 : ℝ)*X 1 0+(-2067233257/10000000000 : ℝ)*X 1 1+(2695588513/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328166797/2500000000 : ℝ)*X 2 0+(1078235279/2000000000 : ℝ)*X 2 1+(-2067233499/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1088314767/2500000000 : ℝ)*X 0 0+(448021517/1000000000 : ℝ)*X 0 1+(4229837249/10000000000 : ℝ)*X 0 2+(1088314767/2500000000 : ℝ)*X 1 0+(448021517/1000000000 : ℝ)*X 1 1+(4229837249/10000000000 : ℝ)*X 1 2+(1088314767/2500000000 : ℝ)*X 2 0+(448021517/1000000000 : ℝ)*X 2 1+(4229837249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1224_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1607859474919303521639360369/188500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (331452867/20000000000000 : ℝ)*(base19) + (309789557/20000000000000 : ℝ)*(base23) + (12863039/20000000000000 : ℝ)*(lower2) + (53580513/25000000000000 : ℝ)*(upper3) + (13465493/10000000000000 : ℝ)*(upper5) + (6003555361481131/100000000000000 : ℝ)*(major0) + (6003555361481131/100000000000000 : ℝ)*(major1) + (6003555361481131/100000000000000 : ℝ)*(major2) + (8033203103872613/100000000000000 : ℝ)*(sp0) + (1606649510140441/20000000000000 : ℝ)*(sp1) + (1606649531803751/20000000000000 : ℝ)*(sp2) + (1986918314487927/50000000000000 : ℝ)*(sp3) + (46104093927/100000000000000 : ℝ)*(sp4) + (12300847287/50000000000000 : ℝ)*(sp7) + (993465307667607/25000000000000 : ℝ)*(f.failure) + (401662460398327/5000000000000 : ℝ)*(f.sum) + (8771183879553/1885000000000000000000000000 : ℝ)*base65 + (5002920532994659959/377000000000000000000000000000000 : ℝ)*base68 + (8554870442463659959/377000000000000000000000000000000 : ℝ)*base70 + (1817939101401659959/377000000000000000000000000000000 : ℝ)*base72 + (3672891845859/942500000000000000000000000 : ℝ)*base73 + (7503993385740659959/377000000000000000000000000000000 : ℝ)*base76 + (767754570681659959/377000000000000000000000000000000 : ℝ)*base78 + (8115525657649659959/377000000000000000000000000000000 : ℝ)*base80 + (1779529770969/942500000000000000000000000 : ℝ)*base81 + (1006121/62500000000000000000 : ℝ)*base89 + (1006121/62500000000000000000 : ℝ)*base91 + (1006121/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2230086716615785468997037/812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (259733991/100000000000000 : ℝ)*(base19) + (2801301/250000000000 : ℝ)*(base23) + (611915049/100000000000000 : ℝ)*(lower1) + (47186041/50000000000000 : ℝ)*(upper2) + (15835787/12500000000000 : ℝ)*(upper3) + (754241734861781/12500000000000 : ℝ)*(major0) + (754241734861781/12500000000000 : ℝ)*(major1) + (754241734861781/12500000000000 : ℝ)*(major2) + (1395560563/100000000000000 : ℝ)*(sp1) + (1640279803/12500000000000 : ℝ)*(sp3) + (8073898348781353/100000000000000 : ℝ)*(sp4) + (8073896693486799/100000000000000 : ℝ)*(sp5) + (1009237153532619/12500000000000 : ℝ)*(sp6) + (399395619527797/10000000000000 : ℝ)*(sp7) + (1996984658758197/50000000000000 : ℝ)*(f.failure) + (8073898348781353/100000000000000 : ℝ)*(f.sum) + (1299546371/65000000000000000000000000 : ℝ)*base65 + (8819238738421821/1625000000000000000000000000000 : ℝ)*base68 + (11057701802921821/1625000000000000000000000000000 : ℝ)*base70 + (6357346128296821/1625000000000000000000000000000 : ℝ)*base72 + (90001974663/32500000000000000000000000 : ℝ)*base73 + (28208952056953179/1625000000000000000000000000000 : ℝ)*base75 + (38609356183078179/1625000000000000000000000000000 : ℝ)*base77 + (69940854254421821/1625000000000000000000000000000 : ℝ)*base80 + (58390469283/32500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (523891/125000000000000000000 : ℝ)*base89 + (523891/125000000000000000000 : ℝ)*base91 + (523891/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1224_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2819/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (358/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11457/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1224_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1224_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11457/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1224_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1224_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1224_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (263/64 : ℝ) ≤ p) (hpb : p ≤ (8417/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3776903/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11457/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7047/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1224_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
