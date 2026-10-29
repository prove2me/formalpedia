-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1459_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:46.960703+00:00
-- url     : https://prove2.me/submissions/8a831911-573e-4f6a-9da0-c81eab5d31d7

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
theorem support_rectangle_w1459_s0_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1741953503/10000000000 : ℝ)*x 0 + (5947898607/10000000000 : ℝ)*x 1 + (2419024117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1741953503/10000000000 : ℝ)^4419 ≤ (2570739031681/25000000000000 : ℝ)^3395 := by
    have hnat : (1741953503 : ℕ)^4419*25000000000000^3395 ≤ 2570739031681^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741953503 10000000000 2570739031681 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5947898607/10000000000 : ℝ)^4419 ≤ (6356486059141/12500000000000 : ℝ)^3395 := by
    have hnat : (5947898607 : ℕ)^4419*12500000000000^3395 ≤ 6356486059141^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947898607 10000000000 6356486059141 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2419024117/5000000000 : ℝ)^4419 ≤ (2429072211809/6250000000000 : ℝ)^3395 := by
    have hnat : (2419024117 : ℕ)^4419*6250000000000^3395 ≤ 2429072211809^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419024117 5000000000 2429072211809 6250000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1741953503/10000000000 : ℝ), (5947898607/10000000000 : ℝ), (2419024117/5000000000 : ℝ)] ![(2570739031681/25000000000000 : ℝ), (6356486059141/12500000000000 : ℝ), (2429072211809/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1741953503/10000000000 : ℝ)|^4419 ≤ (2570739031681/25000000000000 : ℝ)^3395
        have hw : |(-1741953503/10000000000 : ℝ)|=(1741953503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5947898607/10000000000 : ℝ)|^4419 ≤ (6356486059141/12500000000000 : ℝ)^3395
        have hw : |(5947898607/10000000000 : ℝ)|=(5947898607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2419024117/5000000000 : ℝ)|^4419 ≤ (2429072211809/6250000000000 : ℝ)^3395
        have hw : |(2419024117/5000000000 : ℝ)|=(2419024117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s0_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1097753623/2000000000 : ℝ)*x 0 + (-2367613243/10000000000 : ℝ)*x 1 + (1209512037/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1097753623/2000000000 : ℝ)^4419 ≤ (45803144046151/100000000000000 : ℝ)^3395 := by
    have hnat : (1097753623 : ℕ)^4419*100000000000000^3395 ≤ 45803144046151^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097753623 2000000000 45803144046151 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2367613243/10000000000 : ℝ)^4419 ≤ (15331701445367/100000000000000 : ℝ)^3395 := by
    have hnat : (2367613243 : ℕ)^4419*100000000000000^3395 ≤ 15331701445367^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2367613243 10000000000 15331701445367 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209512037/2500000000 : ℝ)^4419 ≤ (38865154489709/100000000000000 : ℝ)^3395 := by
    have hnat : (1209512037 : ℕ)^4419*100000000000000^3395 ≤ 38865154489709^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209512037 2500000000 38865154489709 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1097753623/2000000000 : ℝ), (-2367613243/10000000000 : ℝ), (1209512037/2500000000 : ℝ)] ![(45803144046151/100000000000000 : ℝ), (15331701445367/100000000000000 : ℝ), (38865154489709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1097753623/2000000000 : ℝ)|^4419 ≤ (45803144046151/100000000000000 : ℝ)^3395
        have hw : |(1097753623/2000000000 : ℝ)|=(1097753623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2367613243/10000000000 : ℝ)|^4419 ≤ (15331701445367/100000000000000 : ℝ)^3395
        have hw : |(-2367613243/10000000000 : ℝ)|=(2367613243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1209512037/2500000000 : ℝ)|^4419 ≤ (38865154489709/100000000000000 : ℝ)^3395
        have hw : |(1209512037/2500000000 : ℝ)|=(1209512037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s0_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5488768143/10000000000 : ℝ)*x 0 + (2419024059/5000000000 : ℝ)*x 1 + (-591903311/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5488768143/10000000000 : ℝ)^4419 ≤ (45803144350283/100000000000000 : ℝ)^3395 := by
    have hnat : (5488768143 : ℕ)^4419*100000000000000^3395 ≤ 45803144350283^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5488768143 10000000000 45803144350283 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2419024059/5000000000 : ℝ)^4419 ≤ (38865154176023/100000000000000 : ℝ)^3395 := by
    have hnat : (2419024059 : ℕ)^4419*100000000000000^3395 ≤ 38865154176023^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2419024059 5000000000 38865154176023 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591903311/2500000000 : ℝ)^4419 ≤ (3066340290759/20000000000000 : ℝ)^3395 := by
    have hnat : (591903311 : ℕ)^4419*20000000000000^3395 ≤ 3066340290759^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591903311 2500000000 3066340290759 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5488768143/10000000000 : ℝ), (2419024059/5000000000 : ℝ), (-591903311/2500000000 : ℝ)] ![(45803144350283/100000000000000 : ℝ), (38865154176023/100000000000000 : ℝ), (3066340290759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5488768143/10000000000 : ℝ)|^4419 ≤ (45803144350283/100000000000000 : ℝ)^3395
        have hw : |(5488768143/10000000000 : ℝ)|=(5488768143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2419024059/5000000000 : ℝ)|^4419 ≤ (38865154176023/100000000000000 : ℝ)^3395
        have hw : |(2419024059/5000000000 : ℝ)|=(2419024059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-591903311/2500000000 : ℝ)|^4419 ≤ (3066340290759/20000000000000 : ℝ)^3395
        have hw : |(-591903311/2500000000 : ℝ)|=(591903311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s0_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4161727627/10000000000 : ℝ)*x 0 + (3102736851/10000000000 : ℝ)*x 1 + (1382532513/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4161727627/10000000000 : ℝ)^4419 ≤ (15973826608679/50000000000000 : ℝ)^3395 := by
    have hnat : (4161727627 : ℕ)^4419*50000000000000^3395 ≤ 15973826608679^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161727627 10000000000 15973826608679 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3102736851/10000000000 : ℝ)^4419 ≤ (4359885003501/20000000000000 : ℝ)^3395 := by
    have hnat : (3102736851 : ℕ)^4419*20000000000000^3395 ≤ 4359885003501^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3102736851 10000000000 4359885003501 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1382532513/2500000000 : ℝ)^4419 ≤ (2312646087171/5000000000000 : ℝ)^3395 := by
    have hnat : (1382532513 : ℕ)^4419*5000000000000^3395 ≤ 2312646087171^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382532513 2500000000 2312646087171 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4161727627/10000000000 : ℝ), (3102736851/10000000000 : ℝ), (1382532513/2500000000 : ℝ)] ![(15973826608679/50000000000000 : ℝ), (4359885003501/20000000000000 : ℝ), (2312646087171/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4161727627/10000000000 : ℝ)|^4419 ≤ (15973826608679/50000000000000 : ℝ)^3395
        have hw : |(4161727627/10000000000 : ℝ)|=(4161727627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3102736851/10000000000 : ℝ)|^4419 ≤ (4359885003501/20000000000000 : ℝ)^3395
        have hw : |(3102736851/10000000000 : ℝ)|=(3102736851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1382532513/2500000000 : ℝ)|^4419 ≤ (2312646087171/5000000000000 : ℝ)^3395
        have hw : |(1382532513/2500000000 : ℝ)|=(1382532513/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s0_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-872914351/5000000000 : ℝ)*x 0 + (4866377047/10000000000 : ℝ)*x 1 + (5918558741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872914351/5000000000 : ℝ)^4419 ≤ (5156370825921/50000000000000 : ℝ)^3395 := by
    have hnat : (872914351 : ℕ)^4419*50000000000000^3395 ≤ 5156370825921^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872914351 5000000000 5156370825921 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4866377047/10000000000 : ℝ)^4419 ≤ (39161628718909/100000000000000 : ℝ)^3395 := by
    have hnat : (4866377047 : ℕ)^4419*100000000000000^3395 ≤ 39161628718909^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4866377047 10000000000 39161628718909 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5918558741/10000000000 : ℝ)^4419 ≤ (404205036951/800000000000 : ℝ)^3395 := by
    have hnat : (5918558741 : ℕ)^4419*800000000000^3395 ≤ 404205036951^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5918558741 10000000000 404205036951 800000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-872914351/5000000000 : ℝ), (4866377047/10000000000 : ℝ), (5918558741/10000000000 : ℝ)] ![(5156370825921/50000000000000 : ℝ), (39161628718909/100000000000000 : ℝ), (404205036951/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-872914351/5000000000 : ℝ)|^4419 ≤ (5156370825921/50000000000000 : ℝ)^3395
        have hw : |(-872914351/5000000000 : ℝ)|=(872914351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4866377047/10000000000 : ℝ)|^4419 ≤ (39161628718909/100000000000000 : ℝ)^3395
        have hw : |(4866377047/10000000000 : ℝ)|=(4866377047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5918558741/10000000000 : ℝ)|^4419 ≤ (404205036951/800000000000 : ℝ)^3395
        have hw : |(5918558741/10000000000 : ℝ)|=(5918558741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s0_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324107473/625000000 : ℝ)*x 0 + (-1287102529/10000000000 : ℝ)*x 1 + (1479639703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324107473/625000000 : ℝ)^4419 ≤ (8507847828711/20000000000000 : ℝ)^3395 := by
    have hnat : (324107473 : ℕ)^4419*20000000000000^3395 ≤ 8507847828711^3395*625000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324107473 625000000 8507847828711 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287102529/10000000000 : ℝ)^4419 ≤ (6935130437663/100000000000000 : ℝ)^3395 := by
    have hnat : (1287102529 : ℕ)^4419*100000000000000^3395 ≤ 6935130437663^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287102529 10000000000 6935130437663 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1479639703/2500000000 : ℝ)^4419 ≤ (10105126081561/20000000000000 : ℝ)^3395 := by
    have hnat : (1479639703 : ℕ)^4419*20000000000000^3395 ≤ 10105126081561^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479639703 2500000000 10105126081561 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324107473/625000000 : ℝ), (-1287102529/10000000000 : ℝ), (1479639703/2500000000 : ℝ)] ![(8507847828711/20000000000000 : ℝ), (6935130437663/100000000000000 : ℝ), (10105126081561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324107473/625000000 : ℝ)|^4419 ≤ (8507847828711/20000000000000 : ℝ)^3395
        have hw : |(324107473/625000000 : ℝ)|=(324107473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1287102529/10000000000 : ℝ)|^4419 ≤ (6935130437663/100000000000000 : ℝ)^3395
        have hw : |(-1287102529/10000000000 : ℝ)|=(1287102529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1479639703/2500000000 : ℝ)|^4419 ≤ (10105126081561/20000000000000 : ℝ)^3395
        have hw : |(1479639703/2500000000 : ℝ)|=(1479639703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s0_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5185719603/10000000000 : ℝ)*x 0 + (1479639663/2500000000 : ℝ)*x 1 + (-1287102729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5185719603/10000000000 : ℝ)^4419 ≤ (42539239517263/100000000000000 : ℝ)^3395 := by
    have hnat : (5185719603 : ℕ)^4419*100000000000000^3395 ≤ 42539239517263^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185719603 10000000000 42539239517263 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1479639663/2500000000 : ℝ)^4419 ≤ (10105125725987/20000000000000 : ℝ)^3395 := by
    have hnat : (1479639663 : ℕ)^4419*20000000000000^3395 ≤ 10105125725987^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479639663 2500000000 10105125725987 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287102729/10000000000 : ℝ)^4419 ≤ (6935131840333/100000000000000 : ℝ)^3395 := by
    have hnat : (1287102729 : ℕ)^4419*100000000000000^3395 ≤ 6935131840333^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287102729 10000000000 6935131840333 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5185719603/10000000000 : ℝ), (1479639663/2500000000 : ℝ), (-1287102729/10000000000 : ℝ)] ![(42539239517263/100000000000000 : ℝ), (10105125725987/20000000000000 : ℝ), (6935131840333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5185719603/10000000000 : ℝ)|^4419 ≤ (42539239517263/100000000000000 : ℝ)^3395
        have hw : |(5185719603/10000000000 : ℝ)|=(5185719603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1479639663/2500000000 : ℝ)|^4419 ≤ (10105125725987/20000000000000 : ℝ)^3395
        have hw : |(1479639663/2500000000 : ℝ)|=(1479639663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1287102729/10000000000 : ℝ)|^4419 ≤ (6935131840333/100000000000000 : ℝ)^3395
        have hw : |(-1287102729/10000000000 : ℝ)|=(1287102729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s0_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (208510173/500000000 : ℝ)*x 0 + (2734085439/5000000000 : ℝ)*x 1 + (3166907119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208510173/500000000 : ℝ)^4419 ≤ (16016184587899/50000000000000 : ℝ)^3395 := by
    have hnat : (208510173 : ℕ)^4419*50000000000000^3395 ≤ 16016184587899^3395*500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208510173 500000000 16016184587899 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734085439/5000000000 : ℝ)^4419 ≤ (45579546244229/100000000000000 : ℝ)^3395 := by
    have hnat : (2734085439 : ℕ)^4419*100000000000000^3395 ≤ 45579546244229^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734085439 5000000000 45579546244229 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3166907119/10000000000 : ℝ)^4419 ≤ (11194042283651/50000000000000 : ℝ)^3395 := by
    have hnat : (3166907119 : ℕ)^4419*50000000000000^3395 ≤ 11194042283651^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3166907119 10000000000 11194042283651 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(208510173/500000000 : ℝ), (2734085439/5000000000 : ℝ), (3166907119/10000000000 : ℝ)] ![(16016184587899/50000000000000 : ℝ), (45579546244229/100000000000000 : ℝ), (11194042283651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(208510173/500000000 : ℝ)|^4419 ≤ (16016184587899/50000000000000 : ℝ)^3395
        have hw : |(208510173/500000000 : ℝ)|=(208510173/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734085439/5000000000 : ℝ)|^4419 ≤ (45579546244229/100000000000000 : ℝ)^3395
        have hw : |(2734085439/5000000000 : ℝ)|=(2734085439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3166907119/10000000000 : ℝ)|^4419 ≤ (11194042283651/50000000000000 : ℝ)^3395
        have hw : |(3166907119/10000000000 : ℝ)|=(3166907119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2257/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26053/100000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2209/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2209 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2209*1^512 ≤ 0^512*1^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2209/512 : ℝ) ≤ (1919139242739589023/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2209 ≤ (1919139242739589023/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2209*100000000000000000000^512 ≤ 1919139242739589023^512*5^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1919139242739589023 100000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1919139242739589023/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2209 := by
      have hnat : (1 : ℕ)^512*1^2209 ≤ 1^2209*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (101919139242739589023/100000000000000000000 : ℝ) ≤ (10044157392926521/10000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (101919139242739589023/100000000000000000000 : ℝ)^512 ≤ (10044157392926521/10000000000000000 : ℝ)^2209 := by
      have hnat : (101919139242739589023 : ℕ)^512*10000000000000000^2209 ≤ 10044157392926521^2209*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101919139242739589023 100000000000000000000 10044157392926521 10000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10044157392926521/10000000000000000 : ℝ)) (X := (101919139242739589023/100000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (51919139242739589023/50000000000000000000 : ℝ) ≤ (5044157392926521/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (51919139242739589023/50000000000000000000 : ℝ)^512 ≤ (5044157392926521/5000000000000000 : ℝ)^2209 := by
      have hnat : (51919139242739589023 : ℕ)^512*5000000000000000^2209 ≤ 5044157392926521^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51919139242739589023 50000000000000000000 5044157392926521 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5044157392926521/5000000000000000 : ℝ)) (X := (51919139242739589023/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(44157392926521/4000000000000000 : ℝ)*(0 : ℝ))^(2209/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(44157392926521/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1919139242739589023/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(44157392926521/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (1 : ℝ)+(44157392926521/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10044157392926521/10000000000000000 : ℝ) by norm_num, show 1+(1919139242739589023/100000000000000000000 : ℝ)+(0 : ℝ)=(101919139242739589023/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1919139242739589023/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(44157392926521/4000000000000000 : ℝ)*(2/5 : ℝ))^(2209/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(44157392926521/4000000000000000 : ℝ)*(2/5 : ℝ)=(5044157392926521/5000000000000000 : ℝ) by norm_num, show 1+2*(1919139242739589023/100000000000000000000 : ℝ)=(51919139242739589023/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(44157392926521/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44157392926521/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(44157392926521/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44157392926521/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(44157392926521/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (44157392926521/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1741953503/10000000000 : ℝ)*X 0 0+(5947898607/10000000000 : ℝ)*X 0 1+(2419024117/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1097753623/2000000000 : ℝ)*X 1 0+(-2367613243/10000000000 : ℝ)*X 1 1+(1209512037/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5488768143/10000000000 : ℝ)*X 2 0+(2419024059/5000000000 : ℝ)*X 2 1+(-591903311/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4161727627/10000000000 : ℝ)*X 0 0+(3102736851/10000000000 : ℝ)*X 0 1+(1382532513/2500000000 : ℝ)*X 0 2+(4161727627/10000000000 : ℝ)*X 1 0+(3102736851/10000000000 : ℝ)*X 1 1+(1382532513/2500000000 : ℝ)*X 1 2+(4161727627/10000000000 : ℝ)*X 2 0+(3102736851/10000000000 : ℝ)*X 2 1+(1382532513/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-872914351/5000000000 : ℝ)*X 0 0+(4866377047/10000000000 : ℝ)*X 0 1+(5918558741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324107473/625000000 : ℝ)*X 1 0+(-1287102529/10000000000 : ℝ)*X 1 1+(1479639703/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5185719603/10000000000 : ℝ)*X 2 0+(1479639663/2500000000 : ℝ)*X 2 1+(-1287102729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((208510173/500000000 : ℝ)*X 0 0+(2734085439/5000000000 : ℝ)*X 0 1+(3166907119/10000000000 : ℝ)*X 0 2+(208510173/500000000 : ℝ)*X 1 0+(2734085439/5000000000 : ℝ)*X 1 1+(3166907119/10000000000 : ℝ)*X 1 2+(208510173/500000000 : ℝ)*X 2 0+(2734085439/5000000000 : ℝ)*X 2 1+(3166907119/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138775745145503780935803/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8621517/10000000000000 : ℝ)*(base1) + (776822933/50000000000000 : ℝ)*(base19) + (1558242319/100000000000000 : ℝ)*(base23) + (23266519/12500000000000 : ℝ)*(upper3) + (187245041/100000000000000 : ℝ)*(upper5) + (131300200697519/20000000000000 : ℝ)*(major0) + (131300200697519/20000000000000 : ℝ)*(major1) + (131300200697519/20000000000000 : ℝ)*(major2) + (450513657209857/50000000000000 : ℝ)*(sp0) + (450515458226409/50000000000000 : ℝ)*(sp1) + (180206182371273/20000000000000 : ℝ)*(sp2) + (411966833708183/100000000000000 : ℝ)*(sp3) + (262094707/5000000000000 : ℝ)*(sp4) + (596415059/25000000000000 : ℝ)*(sp7) + (102992326395897/25000000000000 : ℝ)*(f.failure) + (225258117524671/25000000000000 : ℝ)*(f.sum) + (16099958841399/40000000000000000000000000000 : ℝ)*base65 + (110288760481399/80000000000000000000000000000 : ℝ)*base67 + (48649040721399/80000000000000000000000000000 : ℝ)*base69 + (458042004321399/80000000000000000000000000000 : ℝ)*base71 + (74466692678601/40000000000000000000000000000 : ℝ)*base74 + (279999580881399/80000000000000000000000000000 : ℝ)*base75 + (388963434321399/80000000000000000000000000000 : ℝ)*base77 + (353422513121399/80000000000000000000000000000 : ℝ)*base79 + (103260587598601/40000000000000000000000000000 : ℝ)*base82 + (3681491/312500000000000000000 : ℝ)*base90 + (3681491/312500000000000000000 : ℝ)*base92 + (3681491/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1808051225188443258302199/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1031222767/50000000000000 : ℝ)*(base19) + (2080925603/100000000000000 : ℝ)*(base23) + (178813679/100000000000000 : ℝ)*(base32) + (30968343/10000000000000 : ℝ)*(upper3) + (19483279/10000000000000 : ℝ)*(upper5) + (692474632566409/100000000000000 : ℝ)*(major0) + (692474632566409/100000000000000 : ℝ)*(major1) + (692474632566409/100000000000000 : ℝ)*(major2) + (4986896301/100000000000000 : ℝ)*(sp1) + (649169939/12500000000000 : ℝ)*(sp2) + (118800673510131/12500000000000 : ℝ)*(sp4) + (950398338739213/100000000000000 : ℝ)*(sp5) + (237599528448983/25000000000000 : ℝ)*(sp6) + (434543396896217/100000000000000 : ℝ)*(sp7) + (54317946963737/12500000000000 : ℝ)*(f.failure) + (118800673510131/12500000000000 : ℝ)*(f.sum) + (158551165033089/200000000000000000000000000000 : ℝ)*base65 + (322984122966911/400000000000000000000000000000 : ℝ)*base68 + (785961633433089/400000000000000000000000000000 : ℝ)*base69 + (602256022233089/400000000000000000000000000000 : ℝ)*base71 + (12451551366911/200000000000000000000000000000 : ℝ)*base74 + (971819659033089/400000000000000000000000000000 : ℝ)*base75 + (2649288577033089/400000000000000000000000000000 : ℝ)*base77 + (610177147433089/400000000000000000000000000000 : ℝ)*base79 + (371166696433089/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (591489/156250000000000000000 : ℝ)*base89 + (591489/156250000000000000000 : ℝ)*base91 + (591489/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1459_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2257/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26053/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1459_s1_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-382014473/2000000000 : ℝ)*x 0 + (2796724679/5000000000 : ℝ)*x 1 + (5084667573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (382014473/2000000000 : ℝ)^4419 ≤ (5796556207961/50000000000000 : ℝ)^3395 := by
    have hnat : (382014473 : ℕ)^4419*50000000000000^3395 ≤ 5796556207961^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382014473 2000000000 5796556207961 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2796724679/5000000000 : ℝ)^4419 ≤ (23471717073657/50000000000000 : ℝ)^3395 := by
    have hnat : (2796724679 : ℕ)^4419*50000000000000^3395 ≤ 23471717073657^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2796724679 5000000000 23471717073657 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084667573/10000000000 : ℝ)^4419 ≤ (41463453416571/100000000000000 : ℝ)^3395 := by
    have hnat : (5084667573 : ℕ)^4419*100000000000000^3395 ≤ 41463453416571^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084667573 10000000000 41463453416571 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-382014473/2000000000 : ℝ), (2796724679/5000000000 : ℝ), (5084667573/10000000000 : ℝ)] ![(5796556207961/50000000000000 : ℝ), (23471717073657/50000000000000 : ℝ), (41463453416571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-382014473/2000000000 : ℝ)|^4419 ≤ (5796556207961/50000000000000 : ℝ)^3395
        have hw : |(-382014473/2000000000 : ℝ)|=(382014473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2796724679/5000000000 : ℝ)|^4419 ≤ (23471717073657/50000000000000 : ℝ)^3395
        have hw : |(2796724679/5000000000 : ℝ)|=(2796724679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084667573/10000000000 : ℝ)|^4419 ≤ (41463453416571/100000000000000 : ℝ)^3395
        have hw : |(5084667573/10000000000 : ℝ)|=(5084667573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s1_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348456323/2500000000 : ℝ)*x 0 + (-1089533141/5000000000 : ℝ)*x 1 + (5084669601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348456323/2500000000 : ℝ)^4419 ≤ (2238729424371/5000000000000 : ℝ)^3395 := by
    have hnat : (1348456323 : ℕ)^4419*5000000000000^3395 ≤ 2238729424371^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348456323 2500000000 2238729424371 5000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089533141/5000000000 : ℝ)^4419 ≤ (1720242069881/12500000000000 : ℝ)^3395 := by
    have hnat : (1089533141 : ℕ)^4419*12500000000000^3395 ≤ 1720242069881^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089533141 5000000000 1720242069881 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084669601/10000000000 : ℝ)^4419 ≤ (41463474942163/100000000000000 : ℝ)^3395 := by
    have hnat : (5084669601 : ℕ)^4419*100000000000000^3395 ≤ 41463474942163^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084669601 10000000000 41463474942163 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348456323/2500000000 : ℝ), (-1089533141/5000000000 : ℝ), (5084669601/10000000000 : ℝ)] ![(2238729424371/5000000000000 : ℝ), (1720242069881/12500000000000 : ℝ), (41463474942163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348456323/2500000000 : ℝ)|^4419 ≤ (2238729424371/5000000000000 : ℝ)^3395
        have hw : |(1348456323/2500000000 : ℝ)|=(1348456323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089533141/5000000000 : ℝ)|^4419 ≤ (1720242069881/12500000000000 : ℝ)^3395
        have hw : |(-1089533141/5000000000 : ℝ)|=(1089533141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084669601/10000000000 : ℝ)|^4419 ≤ (41463474942163/100000000000000 : ℝ)^3395
        have hw : |(5084669601/10000000000 : ℝ)|=(5084669601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s1_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078765399/2000000000 : ℝ)*x 0 + (5084667721/10000000000 : ℝ)*x 1 + (-272383309/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078765399/2000000000 : ℝ)^4419 ≤ (44774606888089/100000000000000 : ℝ)^3395 := by
    have hnat : (1078765399 : ℕ)^4419*100000000000000^3395 ≤ 44774606888089^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078765399 2000000000 44774606888089 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084667721/10000000000 : ℝ)^4419 ≤ (2591465936717/6250000000000 : ℝ)^3395 := by
    have hnat : (5084667721 : ℕ)^4419*6250000000000^3395 ≤ 2591465936717^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084667721 10000000000 2591465936717 6250000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272383309/1250000000 : ℝ)^4419 ≤ (550477524837/4000000000000 : ℝ)^3395 := by
    have hnat : (272383309 : ℕ)^4419*4000000000000^3395 ≤ 550477524837^3395*1250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272383309 1250000000 550477524837 4000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078765399/2000000000 : ℝ), (5084667721/10000000000 : ℝ), (-272383309/1250000000 : ℝ)] ![(44774606888089/100000000000000 : ℝ), (2591465936717/6250000000000 : ℝ), (550477524837/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078765399/2000000000 : ℝ)|^4419 ≤ (44774606888089/100000000000000 : ℝ)^3395
        have hw : |(1078765399/2000000000 : ℝ)|=(1078765399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084667721/10000000000 : ℝ)|^4419 ≤ (2591465936717/6250000000000 : ℝ)^3395
        have hw : |(5084667721/10000000000 : ℝ)|=(5084667721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272383309/1250000000 : ℝ)|^4419 ≤ (550477524837/4000000000000 : ℝ)^3395
        have hw : |(-272383309/1250000000 : ℝ)|=(272383309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s1_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427117031/1000000000 : ℝ)*x 0 + (3746729151/10000000000 : ℝ)*x 1 + (2429749771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427117031/1000000000 : ℝ)^4419 ≤ (33045507861701/100000000000000 : ℝ)^3395 := by
    have hnat : (427117031 : ℕ)^4419*100000000000000^3395 ≤ 33045507861701^3395*1000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427117031 1000000000 33045507861701 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3746729151/10000000000 : ℝ)^4419 ≤ (5572977490743/20000000000000 : ℝ)^3395 := by
    have hnat : (3746729151 : ℕ)^4419*20000000000000^3395 ≤ 5572977490743^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3746729151 10000000000 5572977490743 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2429749771/5000000000 : ℝ)^4419 ≤ (7817920934249/20000000000000 : ℝ)^3395 := by
    have hnat : (2429749771 : ℕ)^4419*20000000000000^3395 ≤ 7817920934249^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2429749771 5000000000 7817920934249 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427117031/1000000000 : ℝ), (3746729151/10000000000 : ℝ), (2429749771/5000000000 : ℝ)] ![(33045507861701/100000000000000 : ℝ), (5572977490743/20000000000000 : ℝ), (7817920934249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427117031/1000000000 : ℝ)|^4419 ≤ (33045507861701/100000000000000 : ℝ)^3395
        have hw : |(427117031/1000000000 : ℝ)|=(427117031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3746729151/10000000000 : ℝ)|^4419 ≤ (5572977490743/20000000000000 : ℝ)^3395
        have hw : |(3746729151/10000000000 : ℝ)|=(3746729151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2429749771/5000000000 : ℝ)|^4419 ≤ (7817920934249/20000000000000 : ℝ)^3395
        have hw : |(2429749771/5000000000 : ℝ)|=(2429749771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s1_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-955215767/5000000000 : ℝ)*x 0 + (1018098991/2000000000 : ℝ)*x 1 + (5587525529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (955215767/5000000000 : ℝ)^4419 ≤ (2319189995911/20000000000000 : ℝ)^3395 := by
    have hnat : (955215767 : ℕ)^4419*20000000000000^3395 ≤ 2319189995911^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      955215767 5000000000 2319189995911 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1018098991/2000000000 : ℝ)^4419 ≤ (41525317082743/100000000000000 : ℝ)^3395 := by
    have hnat : (1018098991 : ℕ)^4419*100000000000000^3395 ≤ 41525317082743^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1018098991 2000000000 41525317082743 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5587525529/10000000000 : ℝ)^4419 ≤ (46878732923391/100000000000000 : ℝ)^3395 := by
    have hnat : (5587525529 : ℕ)^4419*100000000000000^3395 ≤ 46878732923391^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5587525529 10000000000 46878732923391 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-955215767/5000000000 : ℝ), (1018098991/2000000000 : ℝ), (5587525529/10000000000 : ℝ)] ![(2319189995911/20000000000000 : ℝ), (41525317082743/100000000000000 : ℝ), (46878732923391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-955215767/5000000000 : ℝ)|^4419 ≤ (2319189995911/20000000000000 : ℝ)^3395
        have hw : |(-955215767/5000000000 : ℝ)|=(955215767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1018098991/2000000000 : ℝ)|^4419 ≤ (41525317082743/100000000000000 : ℝ)^3395
        have hw : |(1018098991/2000000000 : ℝ)|=(1018098991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5587525529/10000000000 : ℝ)|^4419 ≤ (46878732923391/100000000000000 : ℝ)^3395
        have hw : |(5587525529/10000000000 : ℝ)|=(5587525529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s1_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5260605499/10000000000 : ℝ)*x 0 + (-1676209591/10000000000 : ℝ)*x 1 + (1117505113/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5260605499/10000000000 : ℝ)^4419 ≤ (43340560613357/100000000000000 : ℝ)^3395 := by
    have hnat : (5260605499 : ℕ)^4419*100000000000000^3395 ≤ 43340560613357^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260605499 10000000000 43340560613357 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1676209591/10000000000 : ℝ)^4419 ≤ (4890353024127/50000000000000 : ℝ)^3395 := by
    have hnat : (1676209591 : ℕ)^4419*50000000000000^3395 ≤ 4890353024127^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676209591 10000000000 4890353024127 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117505113/2000000000 : ℝ)^4419 ≤ (46878733316527/100000000000000 : ℝ)^3395 := by
    have hnat : (1117505113 : ℕ)^4419*100000000000000^3395 ≤ 46878733316527^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117505113 2000000000 46878733316527 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5260605499/10000000000 : ℝ), (-1676209591/10000000000 : ℝ), (1117505113/2000000000 : ℝ)] ![(43340560613357/100000000000000 : ℝ), (4890353024127/50000000000000 : ℝ), (46878733316527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5260605499/10000000000 : ℝ)|^4419 ≤ (43340560613357/100000000000000 : ℝ)^3395
        have hw : |(5260605499/10000000000 : ℝ)|=(5260605499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1676209591/10000000000 : ℝ)|^4419 ≤ (4890353024127/50000000000000 : ℝ)^3395
        have hw : |(-1676209591/10000000000 : ℝ)|=(1676209591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1117505113/2000000000 : ℝ)|^4419 ≤ (46878733316527/100000000000000 : ℝ)^3395
        have hw : |(1117505113/2000000000 : ℝ)|=(1117505113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s1_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630302691/5000000000 : ℝ)*x 0 + (558752553/1000000000 : ℝ)*x 1 + (-104763113/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630302691/5000000000 : ℝ)^4419 ≤ (43340559358689/100000000000000 : ℝ)^3395 := by
    have hnat : (2630302691 : ℕ)^4419*100000000000000^3395 ≤ 43340559358689^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630302691 5000000000 43340559358689 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (558752553/1000000000 : ℝ)^4419 ≤ (46878732934311/100000000000000 : ℝ)^3395 := by
    have hnat : (558752553 : ℕ)^4419*100000000000000^3395 ≤ 46878732934311^3395*1000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      558752553 1000000000 46878732934311 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104763113/625000000 : ℝ)^4419 ≤ (9780707696363/100000000000000 : ℝ)^3395 := by
    have hnat : (104763113 : ℕ)^4419*100000000000000^3395 ≤ 9780707696363^3395*625000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104763113 625000000 9780707696363 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630302691/5000000000 : ℝ), (558752553/1000000000 : ℝ), (-104763113/625000000 : ℝ)] ![(43340559358689/100000000000000 : ℝ), (46878732934311/100000000000000 : ℝ), (9780707696363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630302691/5000000000 : ℝ)|^4419 ≤ (43340559358689/100000000000000 : ℝ)^3395
        have hw : |(2630302691/5000000000 : ℝ)|=(2630302691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(558752553/1000000000 : ℝ)|^4419 ≤ (46878732934311/100000000000000 : ℝ)^3395
        have hw : |(558752553/1000000000 : ℝ)|=(558752553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104763113/625000000 : ℝ)|^4419 ≤ (9780707696363/100000000000000 : ℝ)^3395
        have hw : |(-104763113/625000000 : ℝ)|=(104763113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s1_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4271956609/10000000000 : ℝ)*x 0 + (2423378019/5000000000 : ℝ)*x 1 + (469960281/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4271956609/10000000000 : ℝ)^4419 ≤ (33053426482473/100000000000000 : ℝ)^3395 := by
    have hnat : (4271956609 : ℕ)^4419*100000000000000^3395 ≤ 33053426482473^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271956609 10000000000 33053426482473 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2423378019/5000000000 : ℝ)^4419 ≤ (38956230749829/100000000000000 : ℝ)^3395 := by
    have hnat : (2423378019 : ℕ)^4419*100000000000000^3395 ≤ 38956230749829^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2423378019 5000000000 38956230749829 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (469960281/1250000000 : ℝ)^4419 ≤ (27990342757029/100000000000000 : ℝ)^3395 := by
    have hnat : (469960281 : ℕ)^4419*100000000000000^3395 ≤ 27990342757029^3395*1250000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      469960281 1250000000 27990342757029 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4271956609/10000000000 : ℝ), (2423378019/5000000000 : ℝ), (469960281/1250000000 : ℝ)] ![(33053426482473/100000000000000 : ℝ), (38956230749829/100000000000000 : ℝ), (27990342757029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4271956609/10000000000 : ℝ)|^4419 ≤ (33053426482473/100000000000000 : ℝ)^3395
        have hw : |(4271956609/10000000000 : ℝ)|=(4271956609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2423378019/5000000000 : ℝ)|^4419 ≤ (38956230749829/100000000000000 : ℝ)^3395
        have hw : |(2423378019/5000000000 : ℝ)|=(2423378019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(469960281/1250000000 : ℝ)|^4419 ≤ (27990342757029/100000000000000 : ℝ)^3395
        have hw : |(469960281/1250000000 : ℝ)|=(469960281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7893/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18651/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26053/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26053/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26053/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2257/100000 : ℝ) ^ (2209/512 : ℝ) ≤ (7877512298047/100000000000000000000 : ℝ) := by
    have hpowers : (2257/100000 : ℝ)^2209 ≤ (7877512298047/100000000000000000000 : ℝ)^512 := by
      have hnat : (2257 : ℕ)^2209*100000000000000000000^512 ≤ 7877512298047^512*100000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2257 100000 7877512298047 100000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2257/100000 : ℝ)) (X := (7877512298047/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26053/100000 : ℝ) ^ (2209/512 : ℝ) ≤ (150909160436393723/50000000000000000000 : ℝ) := by
    have hpowers : (26053/100000 : ℝ)^2209 ≤ (150909160436393723/50000000000000000000 : ℝ)^512 := by
      have hnat : (26053 : ℕ)^2209*50000000000000000000^512 ≤ 150909160436393723^512*100000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26053 100000 150909160436393723 50000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26053/100000 : ℝ)) (X := (150909160436393723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000007877512298047/50000000000000000000 : ℝ) ≤ (5000000182584249/5000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50000007877512298047/50000000000000000000 : ℝ)^512 ≤ (5000000182584249/5000000000000000 : ℝ)^2209 := by
      have hnat : (50000007877512298047 : ℕ)^512*5000000000000000^2209 ≤ 5000000182584249^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000007877512298047 50000000000000000000 5000000182584249 5000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000182584249/5000000000000000 : ℝ)) (X := (50000007877512298047/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100301826198385085493/100000000000000000000 : ℝ) ≤ (2501746900996861/2500000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (100301826198385085493/100000000000000000000 : ℝ)^512 ≤ (2501746900996861/2500000000000000 : ℝ)^2209 := by
      have hnat : (100301826198385085493 : ℕ)^512*2500000000000000^2209 ≤ 2501746900996861^2209*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100301826198385085493 100000000000000000000 2501746900996861 2500000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501746900996861/2500000000000000 : ℝ)) (X := (100301826198385085493/100000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25150909160436393723/25000000000000000000 : ℝ) ≤ (1001397484280639/1000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25150909160436393723/25000000000000000000 : ℝ)^512 ≤ (1001397484280639/1000000000000000 : ℝ)^2209 := by
      have hnat : (25150909160436393723 : ℕ)^512*1000000000000000^2209 ≤ 1001397484280639^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25150909160436393723 25000000000000000000 1001397484280639 1000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001397484280639/1000000000000000 : ℝ)) (X := (25150909160436393723/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7877512298047/100000000000000000000 : ℝ) ≤ ((59482117073380214041/59490000000000000000 : ℝ)+2*(3493619409473/1189800000000000 : ℝ)*(2257/100000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (59482117073380214041/59490000000000000000 : ℝ)+2*(3493619409473/1189800000000000 : ℝ)*(2257/100000 : ℝ)=(5000000182584249/5000000000000000 : ℝ) by norm_num, show 1+2*(7877512298047/100000000000000000000 : ℝ)=(50000007877512298047/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(150909160436393723/50000000000000000000 : ℝ)+(7877512298047/100000000000000000000 : ℝ) ≤ ((59482117073380214041/59490000000000000000 : ℝ)+(3493619409473/1189800000000000 : ℝ)*((26053/100000 : ℝ)+(2257/100000 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (59482117073380214041/59490000000000000000 : ℝ)+(3493619409473/1189800000000000 : ℝ)*((26053/100000 : ℝ)+(2257/100000 : ℝ))=(2501746900996861/2500000000000000 : ℝ) by norm_num, show 1+(150909160436393723/50000000000000000000 : ℝ)+(7877512298047/100000000000000000000 : ℝ)=(100301826198385085493/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(150909160436393723/50000000000000000000 : ℝ) ≤ ((59482117073380214041/59490000000000000000 : ℝ)+2*(3493619409473/1189800000000000 : ℝ)*(26053/100000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (59482117073380214041/59490000000000000000 : ℝ)+2*(3493619409473/1189800000000000 : ℝ)*(26053/100000 : ℝ)=(1001397484280639/1000000000000000 : ℝ) by norm_num, show 1+2*(150909160436393723/50000000000000000000 : ℝ)=(25150909160436393723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (59482117073380214041/59490000000000000000 : ℝ)*(X 1 0+X 2 0)+(3493619409473/1189800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (2257/100000 : ℝ)) (hi := (26053/100000 : ℝ)) (c := (59482117073380214041/59490000000000000000 : ℝ)) (alpha := (3493619409473/1189800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (59482117073380214041/59490000000000000000 : ℝ)*(X 0 1+X 2 1)+(3493619409473/1189800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (2257/100000 : ℝ)) (hi := (26053/100000 : ℝ)) (c := (59482117073380214041/59490000000000000000 : ℝ)) (alpha := (3493619409473/1189800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (59482117073380214041/59490000000000000000 : ℝ)*(X 0 2+X 1 2)+(3493619409473/1189800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (2257/100000 : ℝ)) (hi := (26053/100000 : ℝ)) (c := (59482117073380214041/59490000000000000000 : ℝ)) (alpha := (3493619409473/1189800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-382014473/2000000000 : ℝ)*X 0 0+(2796724679/5000000000 : ℝ)*X 0 1+(5084667573/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1348456323/2500000000 : ℝ)*X 1 0+(-1089533141/5000000000 : ℝ)*X 1 1+(5084669601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1078765399/2000000000 : ℝ)*X 2 0+(5084667721/10000000000 : ℝ)*X 2 1+(-272383309/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427117031/1000000000 : ℝ)*X 0 0+(3746729151/10000000000 : ℝ)*X 0 1+(2429749771/5000000000 : ℝ)*X 0 2+(427117031/1000000000 : ℝ)*X 1 0+(3746729151/10000000000 : ℝ)*X 1 1+(2429749771/5000000000 : ℝ)*X 1 2+(427117031/1000000000 : ℝ)*X 2 0+(3746729151/10000000000 : ℝ)*X 2 1+(2429749771/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-955215767/5000000000 : ℝ)*X 0 0+(1018098991/2000000000 : ℝ)*X 0 1+(5587525529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5260605499/10000000000 : ℝ)*X 1 0+(-1676209591/10000000000 : ℝ)*X 1 1+(1117505113/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2630302691/5000000000 : ℝ)*X 2 0+(558752553/1000000000 : ℝ)*X 2 1+(-104763113/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4271956609/10000000000 : ℝ)*X 0 0+(2423378019/5000000000 : ℝ)*X 0 1+(469960281/1250000000 : ℝ)*X 0 2+(4271956609/10000000000 : ℝ)*X 1 0+(2423378019/5000000000 : ℝ)*X 1 1+(469960281/1250000000 : ℝ)*X 1 2+(4271956609/10000000000 : ℝ)*X 2 0+(2423378019/5000000000 : ℝ)*X 2 1+(469960281/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (824401494166070448588144869/99150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (168845461/12500000000000 : ℝ)*(base19) + (957595161/50000000000000 : ℝ)*(base23) + (117987123/100000000000000 : ℝ)*(upper3) + (757123/2500000000000 : ℝ)*(upper4) + (119955667/100000000000000 : ℝ)*(upper5) + (143209274390497/10000000000000 : ℝ)*(major0) + (143209274390497/10000000000000 : ℝ)*(major1) + (143209274390497/10000000000000 : ℝ)*(major2) + (1965495670555951/100000000000000 : ℝ)*(sp0) + (39310262074177/2000000000000 : ℝ)*(sp1) + (245689067410277/12500000000000 : ℝ)*(sp2) + (449331958410579/50000000000000 : ℝ)*(sp3) + (18783916587/100000000000000 : ℝ)*(sp4) + (6839359909/100000000000000 : ℝ)*(sp7) + (224667689045267/25000000000000 : ℝ)*(f.failure) + (982757227236269/50000000000000 : ℝ)*(f.sum) + (6119733241531/5949000000000000000000000000 : ℝ)*base66 + (5087808330539718377/594900000000000000000000000000000 : ℝ)*base67 + (5821066560901818377/594900000000000000000000000000000 : ℝ)*base69 + (283195854961518377/594900000000000000000000000000000 : ℝ)*base71 + (26223178924781/5949000000000000000000000000 : ℝ)*base73 + (5494619704762218377/594900000000000000000000000000000 : ℝ)*base75 + (15498755233518377/594900000000000000000000000000000 : ℝ)*base77 + (9063999943374018377/594900000000000000000000000000000 : ℝ)*base79 + (35964182080997/5949000000000000000000000000 : ℝ)*base81 + (2147399/312500000000000000000 : ℝ)*base89 + (2147399/312500000000000000000 : ℝ)*base91 + (2147399/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10463275182376157243681/2478750000000000000000000000 : ℝ) := by norm_num
    linear_combination (205019653/20000000000000 : ℝ)*(base19) + (99121081/10000000000000 : ℝ)*(base23) + (60102909/50000000000000 : ℝ)*(upper3) + (10614293/100000000000000 : ℝ)*(lower4) + (14692781/20000000000000 : ℝ)*(upper5) + (732962209262867/50000000000000 : ℝ)*(major0) + (732962209262867/50000000000000 : ℝ)*(major1) + (732962209262867/50000000000000 : ℝ)*(major2) + (6748635923/100000000000000 : ℝ)*(sp1) + (3190316389/50000000000000 : ℝ)*(sp2) + (251493474394829/12500000000000 : ℝ)*(sp4) + (502985005356111/25000000000000 : ℝ)*(sp5) + (402388084663009/20000000000000 : ℝ)*(sp6) + (114987612648311/12500000000000 : ℝ)*(sp7) + (114987612648311/12500000000000 : ℝ)*(f.failure) + (251493474394829/12500000000000 : ℝ)*(f.sum) + (49917524766389/29745000000000000000000000000 : ℝ)*base66 + (16490737008899865547/2974500000000000000000000000000000 : ℝ)*base67 + (16056265928723865547/2974500000000000000000000000000000 : ℝ)*base69 + (1063893840479865547/2974500000000000000000000000000000 : ℝ)*base71 + (128191782901861/29745000000000000000000000000 : ℝ)*base73 + (469673119273634453/2974500000000000000000000000000000 : ℝ)*base76 + (2714411921706134453/2974500000000000000000000000000000 : ℝ)*base78 + (5523704741286134453/2974500000000000000000000000000000 : ℝ)*base80 + (133428075033331/29745000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1524333/156250000000000000000 : ℝ)*base90 + (1524333/156250000000000000000 : ℝ)*base92 + (1524333/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1459_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26053/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7893/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18651/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1459_s2_0 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1941032597/10000000000 : ℝ)*x 0 + (5451681151/10000000000 : ℝ)*x 1 + (2603237221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1941032597/10000000000 : ℝ)^4419 ≤ (11838298044393/100000000000000 : ℝ)^3395 := by
    have hnat : (1941032597 : ℕ)^4419*100000000000000^3395 ≤ 11838298044393^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941032597 10000000000 11838298044393 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5451681151/10000000000 : ℝ)^4419 ≤ (22700360687537/50000000000000 : ℝ)^3395 := by
    have hnat : (5451681151 : ℕ)^4419*50000000000000^3395 ≤ 22700360687537^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451681151 10000000000 22700360687537 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2603237221/5000000000 : ℝ)^4419 ≤ (42760980564981/100000000000000 : ℝ)^3395 := by
    have hnat : (2603237221 : ℕ)^4419*100000000000000^3395 ≤ 42760980564981^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603237221 5000000000 42760980564981 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1941032597/10000000000 : ℝ), (5451681151/10000000000 : ℝ), (2603237221/5000000000 : ℝ)] ![(11838298044393/100000000000000 : ℝ), (22700360687537/50000000000000 : ℝ), (42760980564981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1941032597/10000000000 : ℝ)|^4419 ≤ (11838298044393/100000000000000 : ℝ)^3395
        have hw : |(-1941032597/10000000000 : ℝ)|=(1941032597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5451681151/10000000000 : ℝ)|^4419 ≤ (22700360687537/50000000000000 : ℝ)^3395
        have hw : |(5451681151/10000000000 : ℝ)|=(5451681151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2603237221/5000000000 : ℝ)|^4419 ≤ (42760980564981/100000000000000 : ℝ)^3395
        have hw : |(2603237221/5000000000 : ℝ)|=(2603237221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s2_1 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358274539/10000000000 : ℝ)*x 0 + (-413406729/2000000000 : ℝ)*x 1 + (32540441/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358274539/10000000000 : ℝ)^4419 ≤ (44390850149187/100000000000000 : ℝ)^3395 := by
    have hnat : (5358274539 : ℕ)^4419*100000000000000^3395 ≤ 44390850149187^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358274539 10000000000 44390850149187 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413406729/2000000000 : ℝ)^4419 ≤ (12848210764227/100000000000000 : ℝ)^3395 := by
    have hnat : (413406729 : ℕ)^4419*100000000000000^3395 ≤ 12848210764227^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413406729 2000000000 12848210764227 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32540441/62500000 : ℝ)^4419 ≤ (42760939065409/100000000000000 : ℝ)^3395 := by
    have hnat : (32540441 : ℕ)^4419*100000000000000^3395 ≤ 42760939065409^3395*62500000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32540441 62500000 42760939065409 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358274539/10000000000 : ℝ), (-413406729/2000000000 : ℝ), (32540441/62500000 : ℝ)] ![(44390850149187/100000000000000 : ℝ), (12848210764227/100000000000000 : ℝ), (42760939065409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358274539/10000000000 : ℝ)|^4419 ≤ (44390850149187/100000000000000 : ℝ)^3395
        have hw : |(5358274539/10000000000 : ℝ)|=(5358274539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-413406729/2000000000 : ℝ)|^4419 ≤ (12848210764227/100000000000000 : ℝ)^3395
        have hw : |(-413406729/2000000000 : ℝ)|=(413406729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32540441/62500000 : ℝ)|^4419 ≤ (42760939065409/100000000000000 : ℝ)^3395
        have hw : |(32540441/62500000 : ℝ)|=(32540441/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s2_2 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679136161/5000000000 : ℝ)*x 0 + (325404529/625000000 : ℝ)*x 1 + (-413406817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679136161/5000000000 : ℝ)^4419 ≤ (8878165248511/20000000000000 : ℝ)^3395 := by
    have hnat : (2679136161 : ℕ)^4419*20000000000000^3395 ≤ 8878165248511^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679136161 5000000000 8878165248511 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325404529/625000000 : ℝ)^4419 ≤ (8552191883931/20000000000000 : ℝ)^3395 := by
    have hnat : (325404529 : ℕ)^4419*20000000000000^3395 ≤ 8552191883931^3395*625000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325404529 625000000 8552191883931 20000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (413406817/2000000000 : ℝ)^4419 ≤ (12848214324079/100000000000000 : ℝ)^3395 := by
    have hnat : (413406817 : ℕ)^4419*100000000000000^3395 ≤ 12848214324079^3395*2000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413406817 2000000000 12848214324079 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679136161/5000000000 : ℝ), (325404529/625000000 : ℝ), (-413406817/2000000000 : ℝ)] ![(8878165248511/20000000000000 : ℝ), (8552191883931/20000000000000 : ℝ), (12848214324079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679136161/5000000000 : ℝ)|^4419 ≤ (8878165248511/20000000000000 : ℝ)^3395
        have hw : |(2679136161/5000000000 : ℝ)|=(2679136161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325404529/625000000 : ℝ)|^4419 ≤ (8552191883931/20000000000000 : ℝ)^3395
        have hw : |(325404529/625000000 : ℝ)|=(325404529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-413406817/2000000000 : ℝ)|^4419 ≤ (12848214324079/100000000000000 : ℝ)^3395
        have hw : |(-413406817/2000000000 : ℝ)|=(413406817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s2_3 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4293093853/10000000000 : ℝ)*x 0 + (2016179513/5000000000 : ℝ)*x 1 + (4568668177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293093853/10000000000 : ℝ)^4419 ≤ (16633229478731/50000000000000 : ℝ)^3395 := by
    have hnat : (4293093853 : ℕ)^4419*50000000000000^3395 ≤ 16633229478731^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293093853 10000000000 16633229478731 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016179513/5000000000 : ℝ)^4419 ≤ (15330557544327/50000000000000 : ℝ)^3395 := by
    have hnat : (2016179513 : ℕ)^4419*50000000000000^3395 ≤ 15330557544327^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016179513 5000000000 15330557544327 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4568668177/10000000000 : ℝ)^4419 ≤ (36072425935929/100000000000000 : ℝ)^3395 := by
    have hnat : (4568668177 : ℕ)^4419*100000000000000^3395 ≤ 36072425935929^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4568668177 10000000000 36072425935929 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293093853/10000000000 : ℝ), (2016179513/5000000000 : ℝ), (4568668177/10000000000 : ℝ)] ![(16633229478731/50000000000000 : ℝ), (15330557544327/50000000000000 : ℝ), (36072425935929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293093853/10000000000 : ℝ)|^4419 ≤ (16633229478731/50000000000000 : ℝ)^3395
        have hw : |(4293093853/10000000000 : ℝ)|=(4293093853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016179513/5000000000 : ℝ)|^4419 ≤ (15330557544327/50000000000000 : ℝ)^3395
        have hw : |(2016179513/5000000000 : ℝ)|=(2016179513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4568668177/10000000000 : ℝ)|^4419 ≤ (36072425935929/100000000000000 : ℝ)^3395
        have hw : |(4568668177/10000000000 : ℝ)|=(4568668177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s2_4 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-485268231/2500000000 : ℝ)*x 0 + (2603917613/5000000000 : ℝ)*x 1 + (5450309487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (485268231/2500000000 : ℝ)^4419 ≤ (5919309091459/50000000000000 : ℝ)^3395 := by
    have hnat : (485268231 : ℕ)^4419*50000000000000^3395 ≤ 5919309091459^3395*2500000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485268231 2500000000 5919309091459 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603917613/5000000000 : ℝ)^4419 ≤ (42775528268743/100000000000000 : ℝ)^3395 := by
    have hnat : (2603917613 : ℕ)^4419*100000000000000^3395 ≤ 42775528268743^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603917613 5000000000 42775528268743 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450309487/10000000000 : ℝ)^4419 ≤ (45385853538149/100000000000000 : ℝ)^3395 := by
    have hnat : (5450309487 : ℕ)^4419*100000000000000^3395 ≤ 45385853538149^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450309487 10000000000 45385853538149 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-485268231/2500000000 : ℝ), (2603917613/5000000000 : ℝ), (5450309487/10000000000 : ℝ)] ![(5919309091459/50000000000000 : ℝ), (42775528268743/100000000000000 : ℝ), (45385853538149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-485268231/2500000000 : ℝ)|^4419 ≤ (5919309091459/50000000000000 : ℝ)^3395
        have hw : |(-485268231/2500000000 : ℝ)|=(485268231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603917613/5000000000 : ℝ)|^4419 ≤ (42775528268743/100000000000000 : ℝ)^3395
        have hw : |(2603917613/5000000000 : ℝ)|=(2603917613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450309487/10000000000 : ℝ)|^4419 ≤ (45385853538149/100000000000000 : ℝ)^3395
        have hw : |(5450309487/10000000000 : ℝ)|=(5450309487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s2_5 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647167781/5000000000 : ℝ)*x 0 + (-911596563/5000000000 : ℝ)*x 1 + (2725155349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647167781/5000000000 : ℝ)^4419 ≤ (43702619562281/100000000000000 : ℝ)^3395 := by
    have hnat : (2647167781 : ℕ)^4419*100000000000000^3395 ≤ 43702619562281^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647167781 5000000000 43702619562281 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911596563/5000000000 : ℝ)^4419 ≤ (681969609481/6250000000000 : ℝ)^3395 := by
    have hnat : (911596563 : ℕ)^4419*6250000000000^3395 ≤ 681969609481^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911596563 5000000000 681969609481 6250000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725155349/5000000000 : ℝ)^4419 ≤ (45385866664007/100000000000000 : ℝ)^3395 := by
    have hnat : (2725155349 : ℕ)^4419*100000000000000^3395 ≤ 45385866664007^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725155349 5000000000 45385866664007 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647167781/5000000000 : ℝ), (-911596563/5000000000 : ℝ), (2725155349/5000000000 : ℝ)] ![(43702619562281/100000000000000 : ℝ), (681969609481/6250000000000 : ℝ), (45385866664007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647167781/5000000000 : ℝ)|^4419 ≤ (43702619562281/100000000000000 : ℝ)^3395
        have hw : |(2647167781/5000000000 : ℝ)|=(2647167781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-911596563/5000000000 : ℝ)|^4419 ≤ (681969609481/6250000000000 : ℝ)^3395
        have hw : |(-911596563/5000000000 : ℝ)|=(911596563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725155349/5000000000 : ℝ)|^4419 ≤ (45385866664007/100000000000000 : ℝ)^3395
        have hw : |(2725155349/5000000000 : ℝ)|=(2725155349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s2_6 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647167341/5000000000 : ℝ)*x 0 + (5450309749/10000000000 : ℝ)*x 1 + (-1823195661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647167341/5000000000 : ℝ)^4419 ≤ (10925652526813/25000000000000 : ℝ)^3395 := by
    have hnat : (2647167341 : ℕ)^4419*25000000000000^3395 ≤ 10925652526813^3395*5000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647167341 5000000000 10925652526813 25000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450309749/10000000000 : ℝ)^4419 ≤ (4538585637793/10000000000000 : ℝ)^3395 := by
    have hnat : (5450309749 : ℕ)^4419*10000000000000^3395 ≤ 4538585637793^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450309749 10000000000 4538585637793 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1823195661/10000000000 : ℝ)^4419 ≤ (10911533499309/100000000000000 : ℝ)^3395 := by
    have hnat : (1823195661 : ℕ)^4419*100000000000000^3395 ≤ 10911533499309^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1823195661 10000000000 10911533499309 100000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647167341/5000000000 : ℝ), (5450309749/10000000000 : ℝ), (-1823195661/10000000000 : ℝ)] ![(10925652526813/25000000000000 : ℝ), (4538585637793/10000000000000 : ℝ), (10911533499309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647167341/5000000000 : ℝ)|^4419 ≤ (10925652526813/25000000000000 : ℝ)^3395
        have hw : |(2647167341/5000000000 : ℝ)|=(2647167341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450309749/10000000000 : ℝ)|^4419 ≤ (4538585637793/10000000000000 : ℝ)^3395
        have hw : |(5450309749/10000000000 : ℝ)|=(5450309749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1823195661/10000000000 : ℝ)|^4419 ≤ (10911533499309/100000000000000 : ℝ)^3395
        have hw : |(-1823195661/10000000000 : ℝ)|=(1823195661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1459_s2_7 (p : ℝ) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4293180533/10000000000 : ℝ)*x 0 + (4565691469/10000000000 : ℝ)*x 1 + (403536101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293180533/10000000000 : ℝ)^4419 ≤ (16633666608763/50000000000000 : ℝ)^3395 := by
    have hnat : (4293180533 : ℕ)^4419*50000000000000^3395 ≤ 16633666608763^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293180533 10000000000 16633666608763 50000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4565691469/10000000000 : ℝ)^4419 ≤ (3604183706061/10000000000000 : ℝ)^3395 := by
    have hnat : (4565691469 : ℕ)^4419*10000000000000^3395 ≤ 3604183706061^3395*10000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565691469 10000000000 3604183706061 10000000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403536101/1000000000 : ℝ)^4419 ≤ (3836353712867/12500000000000 : ℝ)^3395 := by
    have hnat : (403536101 : ℕ)^4419*12500000000000^3395 ≤ 3836353712867^3395*1000000000^4419 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403536101 1000000000 3836353712867 12500000000000 4419 3395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4419/1024 : ℝ)) 4419 3395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293180533/10000000000 : ℝ), (4565691469/10000000000 : ℝ), (403536101/1000000000 : ℝ)] ![(16633666608763/50000000000000 : ℝ), (3604183706061/10000000000000 : ℝ), (3836353712867/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293180533/10000000000 : ℝ)|^4419 ≤ (16633666608763/50000000000000 : ℝ)^3395
        have hw : |(4293180533/10000000000 : ℝ)|=(4293180533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4565691469/10000000000 : ℝ)|^4419 ≤ (3604183706061/10000000000000 : ℝ)^3395
        have hw : |(4565691469/10000000000 : ℝ)|=(4565691469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403536101/1000000000 : ℝ)|^4419 ≤ (3836353712867/12500000000000 : ℝ)^3395
        have hw : |(403536101/1000000000 : ℝ)|=(403536101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1459_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18651/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5261/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (491/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18651/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18651/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7893/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18651/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18651/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7893/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18651/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18651/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7893/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7893/100000 : ℝ) ^ (2209/512 : ℝ) ≤ (17466373559457/1000000000000000000 : ℝ) := by
    have hpowers : (7893/100000 : ℝ)^2209 ≤ (17466373559457/1000000000000000000 : ℝ)^512 := by
      have hnat : (7893 : ℕ)^2209*1000000000000000000^512 ≤ 17466373559457^512*100000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7893 100000 17466373559457 1000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7893/100000 : ℝ)) (X := (17466373559457/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hpowhi : (18651/100000 : ℝ) ^ (2209/512 : ℝ) ≤ (35681943065788053/50000000000000000000 : ℝ) := by
    have hpowers : (18651/100000 : ℝ)^2209 ≤ (35681943065788053/50000000000000000000 : ℝ)^512 := by
      have hnat : (18651 : ℕ)^2209*50000000000000000000^512 ≤ 35681943065788053^512*100000^2209 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18651 100000 35681943065788053 50000000000000000000 2209 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18651/100000 : ℝ)) (X := (35681943065788053/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (500017466373559457/500000000000000000 : ℝ) ≤ (125001012071443/125000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (500017466373559457/500000000000000000 : ℝ)^512 ≤ (125001012071443/125000000000000 : ℝ)^2209 := by
      have hnat : (500017466373559457 : ℕ)^512*125000000000000^2209 ≤ 125001012071443^2209*500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500017466373559457 500000000000000000 125001012071443 125000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125001012071443/125000000000000 : ℝ)) (X := (500017466373559457/500000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50036555261743760903/50000000000000000000 : ℝ) ≤ (2000338814672163/2000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (50036555261743760903/50000000000000000000 : ℝ)^512 ≤ (2000338814672163/2000000000000000 : ℝ)^2209 := by
      have hnat : (50036555261743760903 : ℕ)^512*2000000000000000^2209 ≤ 2000338814672163^2209*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036555261743760903 50000000000000000000 2000338814672163 2000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000338814672163/2000000000000000 : ℝ)) (X := (50036555261743760903/50000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25035681943065788053/25000000000000000000 : ℝ) ≤ (1000330718100619/1000000000000000 : ℝ) ^ (2209/512 : ℝ) := by
    have hpowers : (25035681943065788053/25000000000000000000 : ℝ)^512 ≤ (1000330718100619/1000000000000000 : ℝ)^2209 := by
      have hnat : (25035681943065788053 : ℕ)^512*1000000000000000^2209 ≤ 1000330718100619^2209*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25035681943065788053 25000000000000000000 1000330718100619 1000000000000000 512 2209 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000330718100619/1000000000000000 : ℝ)) (X := (25035681943065788053/25000000000000000000 : ℝ)) (by norm_num) 2209 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(17466373559457/1000000000000000000 : ℝ) ≤ ((3585180217062560459/3586000000000000000 : ℝ)+2*(12904861163/8606400000000 : ℝ)*(7893/100000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (3585180217062560459/3586000000000000000 : ℝ)+2*(12904861163/8606400000000 : ℝ)*(7893/100000 : ℝ)=(125001012071443/125000000000000 : ℝ) by norm_num, show 1+2*(17466373559457/1000000000000000000 : ℝ)=(500017466373559457/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35681943065788053/50000000000000000000 : ℝ)+(17466373559457/1000000000000000000 : ℝ) ≤ ((3585180217062560459/3586000000000000000 : ℝ)+(12904861163/8606400000000 : ℝ)*((18651/100000 : ℝ)+(7893/100000 : ℝ)))^(2209/512 : ℝ) := by
    rw [show (3585180217062560459/3586000000000000000 : ℝ)+(12904861163/8606400000000 : ℝ)*((18651/100000 : ℝ)+(7893/100000 : ℝ))=(2000338814672163/2000000000000000 : ℝ) by norm_num, show 1+(35681943065788053/50000000000000000000 : ℝ)+(17466373559457/1000000000000000000 : ℝ)=(50036555261743760903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35681943065788053/50000000000000000000 : ℝ) ≤ ((3585180217062560459/3586000000000000000 : ℝ)+2*(12904861163/8606400000000 : ℝ)*(18651/100000 : ℝ))^(2209/512 : ℝ) := by
    rw [show (3585180217062560459/3586000000000000000 : ℝ)+2*(12904861163/8606400000000 : ℝ)*(18651/100000 : ℝ)=(1000330718100619/1000000000000000 : ℝ) by norm_num, show 1+2*(35681943065788053/50000000000000000000 : ℝ)=(25035681943065788053/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3585180217062560459/3586000000000000000 : ℝ)*(X 1 0+X 2 0)+(12904861163/8606400000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (7893/100000 : ℝ)) (hi := (18651/100000 : ℝ)) (c := (3585180217062560459/3586000000000000000 : ℝ)) (alpha := (12904861163/8606400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3585180217062560459/3586000000000000000 : ℝ)*(X 0 1+X 2 1)+(12904861163/8606400000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (7893/100000 : ℝ)) (hi := (18651/100000 : ℝ)) (c := (3585180217062560459/3586000000000000000 : ℝ)) (alpha := (12904861163/8606400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3585180217062560459/3586000000000000000 : ℝ)*(X 0 2+X 1 2)+(12904861163/8606400000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2209/512 : ℝ)) (lo := (7893/100000 : ℝ)) (hi := (18651/100000 : ℝ)) (c := (3585180217062560459/3586000000000000000 : ℝ)) (alpha := (12904861163/8606400000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1941032597/10000000000 : ℝ)*X 0 0+(5451681151/10000000000 : ℝ)*X 0 1+(2603237221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358274539/10000000000 : ℝ)*X 1 0+(-413406729/2000000000 : ℝ)*X 1 1+(32540441/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679136161/5000000000 : ℝ)*X 2 0+(325404529/625000000 : ℝ)*X 2 1+(-413406817/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4293093853/10000000000 : ℝ)*X 0 0+(2016179513/5000000000 : ℝ)*X 0 1+(4568668177/10000000000 : ℝ)*X 0 2+(4293093853/10000000000 : ℝ)*X 1 0+(2016179513/5000000000 : ℝ)*X 1 1+(4568668177/10000000000 : ℝ)*X 1 2+(4293093853/10000000000 : ℝ)*X 2 0+(2016179513/5000000000 : ℝ)*X 2 1+(4568668177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-485268231/2500000000 : ℝ)*X 0 0+(2603917613/5000000000 : ℝ)*X 0 1+(5450309487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647167781/5000000000 : ℝ)*X 1 0+(-911596563/5000000000 : ℝ)*X 1 1+(2725155349/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647167341/5000000000 : ℝ)*X 2 0+(5450309749/10000000000 : ℝ)*X 2 1+(-1823195661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4293180533/10000000000 : ℝ)*X 0 0+(4565691469/10000000000 : ℝ)*X 0 1+(403536101/1000000000 : ℝ)*X 0 2+(4293180533/10000000000 : ℝ)*X 1 0+(4565691469/10000000000 : ℝ)*X 1 1+(403536101/1000000000 : ℝ)*X 1 2+(4293180533/10000000000 : ℝ)*X 2 0+(4565691469/10000000000 : ℝ)*X 2 1+(403536101/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1459_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (136849913227485924775785567/16300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143821191/25000000000000 : ℝ)*(base19) + (4422893/100000000000000 : ℝ)*(upper2) + (623959497/100000000000000 : ℝ)*(lower4) + (61495757/12500000000000 : ℝ)*(upper5) + (2971413544456181/100000000000000 : ℝ)*(major0) + (2971413544456181/100000000000000 : ℝ)*(major1) + (2971413544456181/100000000000000 : ℝ)*(major2) + (1019549313315461/25000000000000 : ℝ)*(sp0) + (4078143061220687/100000000000000 : ℝ)*(sp1) + (2039069276197701/50000000000000 : ℝ)*(sp2) + (1864619027039853/100000000000000 : ℝ)*(sp3) + (53616756393/100000000000000 : ℝ)*(sp5) + (58700866443/100000000000000 : ℝ)*(sp6) + (2105750797/20000000000000 : ℝ)*(sp7) + (932314777896919/50000000000000 : ℝ)*(f.failure) + (1019549313315461/25000000000000 : ℝ)*(f.sum) + (9594563235737/978000000000000000000000000 : ℝ)*base65 + (722112527799964433/97800000000000000000000000000000 : ℝ)*base68 + (470840297557564433/97800000000000000000000000000000 : ℝ)*base70 + (382053535190764433/97800000000000000000000000000000 : ℝ)*base72 + (784118914691/195600000000000000000000000 : ℝ)*base74 + (171072351011635567/97800000000000000000000000000000 : ℝ)*base75 + (987283051213435567/97800000000000000000000000000000 : ℝ)*base77 + (974510942939764433/97800000000000000000000000000000 : ℝ)*base80 + (1139329671761/978000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2771643/625000000000000000000 : ℝ)*base89 + (2771643/625000000000000000000 : ℝ)*base91 + (2771643/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (467267599746846451896565457/44825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670554453/50000000000000 : ℝ)*(base19) + (949632889/100000000000000 : ℝ)*(base23) + (265009537/100000000000000 : ℝ)*(upper3) + (352134329/100000000000000 : ℝ)*(lower4) + (1502440582677041/50000000000000 : ℝ)*(major0) + (1502440582677041/50000000000000 : ℝ)*(major1) + (1502440582677041/50000000000000 : ℝ)*(major2) + (17318428097/50000000000000 : ℝ)*(sp1) + (781795119/20000000000000 : ℝ)*(sp2) + (4083519019/50000000000000 : ℝ)*(sp3) + (1031032683605377/25000000000000 : ℝ)*(sp4) + (4124094756456409/100000000000000 : ℝ)*(sp5) + (128878933619157/3125000000000 : ℝ)*(sp6) + (471405770443293/25000000000000 : ℝ)*(sp7) + (188563124881121/10000000000000 : ℝ)*(f.failure) + (1031032683605377/25000000000000 : ℝ)*(f.sum) + (24630813876467/5379000000000000000000000000 : ℝ)*base66 + (530695299730684543/537900000000000000000000000000000 : ℝ)*base68 + (1206860008556884543/537900000000000000000000000000000 : ℝ)*base70 + (3892226608525684543/537900000000000000000000000000000 : ℝ)*base72 + (6616635900893/5379000000000000000000000000 : ℝ)*base74 + (2846791092572284543/537900000000000000000000000000000 : ℝ)*base76 + (1410527347964284543/537900000000000000000000000000000 : ℝ)*base78 + (1766435563470115457/537900000000000000000000000000000 : ℝ)*base79 + (8777919177289/2689500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (728237/125000000000000000000 : ℝ)*base89 + (728237/125000000000000000000 : ℝ)*base91 + (728237/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1459_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18651/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7893/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (491/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1459_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1459_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (491/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1459_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1459_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1459_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2209/512 : ℝ) ≤ p) (hpb : p ≤ (4419/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19919597/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5261/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (491/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1459_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
