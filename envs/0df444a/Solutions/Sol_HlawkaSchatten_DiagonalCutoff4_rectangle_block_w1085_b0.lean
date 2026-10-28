-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1085_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:51.395718+00:00
-- url     : https://prove2.me/submissions/ab308df7-caae-4db0-9968-6ac79944fa75

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
theorem support_rectangle_w1085_s0_0 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1909982809/10000000000 : ℝ)*x 0 + (6067598581/10000000000 : ℝ)*x 1 + (2386610629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1909982809/10000000000 : ℝ)^4139 ≤ (11083600811997/100000000000000 : ℝ)^3115 := by
    have hnat : (1909982809 : ℕ)^4139*100000000000000^3115 ≤ 11083600811997^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1909982809 10000000000 11083600811997 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6067598581/10000000000 : ℝ)^4139 ≤ (51485809546651/100000000000000 : ℝ)^3115 := by
    have hnat : (6067598581 : ℕ)^4139*100000000000000^3115 ≤ 51485809546651^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6067598581 10000000000 51485809546651 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2386610629/5000000000 : ℝ)^4139 ≤ (18715294814957/50000000000000 : ℝ)^3115 := by
    have hnat : (2386610629 : ℕ)^4139*50000000000000^3115 ≤ 18715294814957^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386610629 5000000000 18715294814957 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1909982809/10000000000 : ℝ), (6067598581/10000000000 : ℝ), (2386610629/5000000000 : ℝ)] ![(11083600811997/100000000000000 : ℝ), (51485809546651/100000000000000 : ℝ), (18715294814957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1909982809/10000000000 : ℝ)|^4139 ≤ (11083600811997/100000000000000 : ℝ)^3115
        have hw : |(-1909982809/10000000000 : ℝ)|=(1909982809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6067598581/10000000000 : ℝ)|^4139 ≤ (51485809546651/100000000000000 : ℝ)^3115
        have hw : |(6067598581/10000000000 : ℝ)|=(6067598581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2386610629/5000000000 : ℝ)|^4139 ≤ (18715294814957/50000000000000 : ℝ)^3115
        have hw : |(2386610629/5000000000 : ℝ)|=(2386610629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s0_1 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (345000229/625000000 : ℝ)*x 0 + (-2654471323/10000000000 : ℝ)*x 1 + (1193305281/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345000229/625000000 : ℝ)^4139 ≤ (45405304506271/100000000000000 : ℝ)^3115 := by
    have hnat : (345000229 : ℕ)^4139*100000000000000^3115 ≤ 45405304506271^3115*625000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345000229 625000000 45405304506271 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2654471323/10000000000 : ℝ)^4139 ≤ (4291026812267/25000000000000 : ℝ)^3115 := by
    have hnat : (2654471323 : ℕ)^4139*25000000000000^3115 ≤ 4291026812267^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654471323 10000000000 4291026812267 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193305281/2500000000 : ℝ)^4139 ≤ (37430588233683/100000000000000 : ℝ)^3115 := by
    have hnat : (1193305281 : ℕ)^4139*100000000000000^3115 ≤ 37430588233683^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193305281 2500000000 37430588233683 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(345000229/625000000 : ℝ), (-2654471323/10000000000 : ℝ), (1193305281/2500000000 : ℝ)] ![(45405304506271/100000000000000 : ℝ), (4291026812267/25000000000000 : ℝ), (37430588233683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(345000229/625000000 : ℝ)|^4139 ≤ (45405304506271/100000000000000 : ℝ)^3115
        have hw : |(345000229/625000000 : ℝ)|=(345000229/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2654471323/10000000000 : ℝ)|^4139 ≤ (4291026812267/25000000000000 : ℝ)^3115
        have hw : |(-2654471323/10000000000 : ℝ)|=(2654471323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193305281/2500000000 : ℝ)|^4139 ≤ (37430588233683/100000000000000 : ℝ)^3115
        have hw : |(1193305281/2500000000 : ℝ)|=(1193305281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s0_2 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5520003547/10000000000 : ℝ)*x 0 + (4773221321/10000000000 : ℝ)*x 1 + (-41476113/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5520003547/10000000000 : ℝ)^4139 ≤ (22702651613753/50000000000000 : ℝ)^3115 := by
    have hnat : (5520003547 : ℕ)^4139*50000000000000^3115 ≤ 22702651613753^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5520003547 10000000000 22702651613753 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4773221321/10000000000 : ℝ)^4139 ≤ (37430590286351/100000000000000 : ℝ)^3115 := by
    have hnat : (4773221321 : ℕ)^4139*100000000000000^3115 ≤ 37430590286351^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4773221321 10000000000 37430590286351 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41476113/156250000 : ℝ)^4139 ≤ (17164106467221/100000000000000 : ℝ)^3115 := by
    have hnat : (41476113 : ℕ)^4139*100000000000000^3115 ≤ 17164106467221^3115*156250000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41476113 156250000 17164106467221 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5520003547/10000000000 : ℝ), (4773221321/10000000000 : ℝ), (-41476113/156250000 : ℝ)] ![(22702651613753/50000000000000 : ℝ), (37430590286351/100000000000000 : ℝ), (17164106467221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5520003547/10000000000 : ℝ)|^4139 ≤ (22702651613753/50000000000000 : ℝ)^3115
        have hw : |(5520003547/10000000000 : ℝ)|=(5520003547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4773221321/10000000000 : ℝ)|^4139 ≤ (37430590286351/100000000000000 : ℝ)^3115
        have hw : |(4773221321/10000000000 : ℝ)|=(4773221321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41476113/156250000 : ℝ)|^4139 ≤ (17164106467221/100000000000000 : ℝ)^3115
        have hw : |(-41476113/156250000 : ℝ)|=(41476113/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s0_3 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2102820593/5000000000 : ℝ)*x 0 + (3123869007/10000000000 : ℝ)*x 1 + (1417559843/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2102820593/5000000000 : ℝ)^4139 ≤ (31635437961721/100000000000000 : ℝ)^3115 := by
    have hnat : (2102820593 : ℕ)^4139*100000000000000^3115 ≤ 31635437961721^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102820593 5000000000 31635437961721 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123869007/10000000000 : ℝ)^4139 ≤ (10654969383377/50000000000000 : ℝ)^3115 := by
    have hnat : (3123869007 : ℕ)^4139*50000000000000^3115 ≤ 10654969383377^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123869007 10000000000 10654969383377 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1417559843/2500000000 : ℝ)^4139 ≤ (47054623267047/100000000000000 : ℝ)^3115 := by
    have hnat : (1417559843 : ℕ)^4139*100000000000000^3115 ≤ 47054623267047^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417559843 2500000000 47054623267047 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2102820593/5000000000 : ℝ), (3123869007/10000000000 : ℝ), (1417559843/2500000000 : ℝ)] ![(31635437961721/100000000000000 : ℝ), (10654969383377/50000000000000 : ℝ), (47054623267047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2102820593/5000000000 : ℝ)|^4139 ≤ (31635437961721/100000000000000 : ℝ)^3115
        have hw : |(2102820593/5000000000 : ℝ)|=(2102820593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123869007/10000000000 : ℝ)|^4139 ≤ (10654969383377/50000000000000 : ℝ)^3115
        have hw : |(3123869007/10000000000 : ℝ)|=(3123869007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1417559843/2500000000 : ℝ)|^4139 ≤ (47054623267047/100000000000000 : ℝ)^3115
        have hw : |(1417559843/2500000000 : ℝ)|=(1417559843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s0_4 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-957649509/5000000000 : ℝ)*x 0 + (1201659097/2500000000 : ℝ)*x 1 + (603301261/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (957649509/5000000000 : ℝ)^4139 ≤ (5562305386529/50000000000000 : ℝ)^3115 := by
    have hnat : (957649509 : ℕ)^4139*50000000000000^3115 ≤ 5562305386529^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957649509 5000000000 5562305386529 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201659097/2500000000 : ℝ)^4139 ≤ (7555832613139/20000000000000 : ℝ)^3115 := by
    have hnat : (1201659097 : ℕ)^4139*20000000000000^3115 ≤ 7555832613139^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201659097 2500000000 7555832613139 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (603301261/1000000000 : ℝ)^4139 ≤ (25548113070611/50000000000000 : ℝ)^3115 := by
    have hnat : (603301261 : ℕ)^4139*50000000000000^3115 ≤ 25548113070611^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603301261 1000000000 25548113070611 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-957649509/5000000000 : ℝ), (1201659097/2500000000 : ℝ), (603301261/1000000000 : ℝ)] ![(5562305386529/50000000000000 : ℝ), (7555832613139/20000000000000 : ℝ), (25548113070611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-957649509/5000000000 : ℝ)|^4139 ≤ (5562305386529/50000000000000 : ℝ)^3115
        have hw : |(-957649509/5000000000 : ℝ)|=(957649509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1201659097/2500000000 : ℝ)|^4139 ≤ (7555832613139/20000000000000 : ℝ)^3115
        have hw : |(1201659097/2500000000 : ℝ)|=(1201659097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(603301261/1000000000 : ℝ)|^4139 ≤ (25548113070611/50000000000000 : ℝ)^3115
        have hw : |(603301261/1000000000 : ℝ)|=(603301261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s0_5 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2584293193/5000000000 : ℝ)*x 0 + (-1394682713/10000000000 : ℝ)*x 1 + (1508252801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2584293193/5000000000 : ℝ)^4139 ≤ (41605230042649/100000000000000 : ℝ)^3115 := by
    have hnat : (2584293193 : ℕ)^4139*100000000000000^3115 ≤ 41605230042649^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584293193 5000000000 41605230042649 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1394682713/10000000000 : ℝ)^4139 ≤ (1459711925289/20000000000000 : ℝ)^3115 := by
    have hnat : (1394682713 : ℕ)^4139*20000000000000^3115 ≤ 1459711925289^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1394682713 10000000000 1459711925289 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1508252801/2500000000 : ℝ)^4139 ≤ (51096210318643/100000000000000 : ℝ)^3115 := by
    have hnat : (1508252801 : ℕ)^4139*100000000000000^3115 ≤ 51096210318643^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1508252801 2500000000 51096210318643 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2584293193/5000000000 : ℝ), (-1394682713/10000000000 : ℝ), (1508252801/2500000000 : ℝ)] ![(41605230042649/100000000000000 : ℝ), (1459711925289/20000000000000 : ℝ), (51096210318643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2584293193/5000000000 : ℝ)|^4139 ≤ (41605230042649/100000000000000 : ℝ)^3115
        have hw : |(2584293193/5000000000 : ℝ)|=(2584293193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1394682713/10000000000 : ℝ)|^4139 ≤ (1459711925289/20000000000000 : ℝ)^3115
        have hw : |(-1394682713/10000000000 : ℝ)|=(1394682713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1508252801/2500000000 : ℝ)|^4139 ≤ (51096210318643/100000000000000 : ℝ)^3115
        have hw : |(1508252801/2500000000 : ℝ)|=(1508252801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s0_6 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1033717301/2000000000 : ℝ)*x 0 + (6033012477/10000000000 : ℝ)*x 1 + (-139468047/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033717301/2000000000 : ℝ)^4139 ≤ (832104626309/2000000000000 : ℝ)^3115 := by
    have hnat : (1033717301 : ℕ)^4139*2000000000000^3115 ≤ 832104626309^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033717301 2000000000 832104626309 2000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6033012477/10000000000 : ℝ)^4139 ≤ (12774056161123/25000000000000 : ℝ)^3115 := by
    have hnat : (6033012477 : ℕ)^4139*25000000000000^3115 ≤ 12774056161123^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033012477 10000000000 12774056161123 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (139468047/1000000000 : ℝ)^4139 ≤ (1459708805981/20000000000000 : ℝ)^3115 := by
    have hnat : (139468047 : ℕ)^4139*20000000000000^3115 ≤ 1459708805981^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139468047 1000000000 1459708805981 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033717301/2000000000 : ℝ), (6033012477/10000000000 : ℝ), (-139468047/1000000000 : ℝ)] ![(832104626309/2000000000000 : ℝ), (12774056161123/25000000000000 : ℝ), (1459708805981/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033717301/2000000000 : ℝ)|^4139 ≤ (832104626309/2000000000000 : ℝ)^3115
        have hw : |(1033717301/2000000000 : ℝ)|=(1033717301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6033012477/10000000000 : ℝ)|^4139 ≤ (12774056161123/25000000000000 : ℝ)^3115
        have hw : |(6033012477/10000000000 : ℝ)|=(6033012477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-139468047/1000000000 : ℝ)|^4139 ≤ (1459708805981/20000000000000 : ℝ)^3115
        have hw : |(-139468047/1000000000 : ℝ)|=(139468047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s0_7 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2108048429/5000000000 : ℝ)*x 0 + (2802250941/5000000000 : ℝ)*x 1 + (1595954659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108048429/5000000000 : ℝ)^4139 ≤ (31739984171319/100000000000000 : ℝ)^3115 := by
    have hnat : (2108048429 : ℕ)^4139*100000000000000^3115 ≤ 31739984171319^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108048429 5000000000 31739984171319 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2802250941/5000000000 : ℝ)^4139 ≤ (23165576344857/50000000000000 : ℝ)^3115 := by
    have hnat : (2802250941 : ℕ)^4139*50000000000000^3115 ≤ 23165576344857^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802250941 5000000000 23165576344857 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595954659/5000000000 : ℝ)^4139 ≤ (21928863127309/100000000000000 : ℝ)^3115 := by
    have hnat : (1595954659 : ℕ)^4139*100000000000000^3115 ≤ 21928863127309^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595954659 5000000000 21928863127309 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2108048429/5000000000 : ℝ), (2802250941/5000000000 : ℝ), (1595954659/5000000000 : ℝ)] ![(31739984171319/100000000000000 : ℝ), (23165576344857/50000000000000 : ℝ), (21928863127309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2108048429/5000000000 : ℝ)|^4139 ≤ (31739984171319/100000000000000 : ℝ)^3115
        have hw : |(2108048429/5000000000 : ℝ)|=(2108048429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2802250941/5000000000 : ℝ)|^4139 ≤ (23165576344857/50000000000000 : ℝ)^3115
        have hw : |(2802250941/5000000000 : ℝ)|=(2802250941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595954659/5000000000 : ℝ)|^4139 ≤ (21928863127309/100000000000000 : ℝ)^3115
        have hw : |(1595954659/5000000000 : ℝ)|=(1595954659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1085_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (177/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5607/20000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8277/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8277 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8277*1^2048 ≤ 0^2048*1^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8277/2048 : ℝ) ≤ (1232236034613714339/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8277 ≤ (1232236034613714339/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8277*50000000000000000000^2048 ≤ 1232236034613714339^2048*5^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1232236034613714339 50000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1232236034613714339/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8277 := by
      have hnat : (1 : ℕ)^2048*1^8277 ≤ 1^8277*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51232236034613714339/50000000000000000000 : ℝ) ≤ (402416864246989/400000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (51232236034613714339/50000000000000000000 : ℝ)^2048 ≤ (402416864246989/400000000000000 : ℝ)^8277 := by
      have hnat : (51232236034613714339 : ℕ)^2048*400000000000000^8277 ≤ 402416864246989^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51232236034613714339 50000000000000000000 402416864246989 400000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (402416864246989/400000000000000 : ℝ)) (X := (51232236034613714339/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26232236034613714339/25000000000000000000 : ℝ) ≤ (202416864246989/200000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (26232236034613714339/25000000000000000000 : ℝ)^2048 ≤ (202416864246989/200000000000000 : ℝ)^8277 := by
      have hnat : (26232236034613714339 : ℕ)^2048*200000000000000^8277 ≤ 202416864246989^8277*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26232236034613714339 25000000000000000000 202416864246989 200000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (202416864246989/200000000000000 : ℝ)) (X := (26232236034613714339/25000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2416864246989/160000000000000 : ℝ)*(0 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(2416864246989/160000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1232236034613714339/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2416864246989/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8277/2048 : ℝ) := by
    rw [show (1 : ℝ)+(2416864246989/160000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(402416864246989/400000000000000 : ℝ) by norm_num, show 1+(1232236034613714339/50000000000000000000 : ℝ)+(0 : ℝ)=(51232236034613714339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1232236034613714339/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2416864246989/160000000000000 : ℝ)*(2/5 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(2416864246989/160000000000000 : ℝ)*(2/5 : ℝ)=(202416864246989/200000000000000 : ℝ) by norm_num, show 1+2*(1232236034613714339/50000000000000000000 : ℝ)=(26232236034613714339/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2416864246989/160000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2416864246989/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2416864246989/160000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2416864246989/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2416864246989/160000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2416864246989/160000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1909982809/10000000000 : ℝ)*X 0 0+(6067598581/10000000000 : ℝ)*X 0 1+(2386610629/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((345000229/625000000 : ℝ)*X 1 0+(-2654471323/10000000000 : ℝ)*X 1 1+(1193305281/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5520003547/10000000000 : ℝ)*X 2 0+(4773221321/10000000000 : ℝ)*X 2 1+(-41476113/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2102820593/5000000000 : ℝ)*X 0 0+(3123869007/10000000000 : ℝ)*X 0 1+(1417559843/2500000000 : ℝ)*X 0 2+(2102820593/5000000000 : ℝ)*X 1 0+(3123869007/10000000000 : ℝ)*X 1 1+(1417559843/2500000000 : ℝ)*X 1 2+(2102820593/5000000000 : ℝ)*X 2 0+(3123869007/10000000000 : ℝ)*X 2 1+(1417559843/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-957649509/5000000000 : ℝ)*X 0 0+(1201659097/2500000000 : ℝ)*X 0 1+(603301261/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2584293193/5000000000 : ℝ)*X 1 0+(-1394682713/10000000000 : ℝ)*X 1 1+(1508252801/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033717301/2000000000 : ℝ)*X 2 0+(6033012477/10000000000 : ℝ)*X 2 1+(-139468047/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2108048429/5000000000 : ℝ)*X 0 0+(2802250941/5000000000 : ℝ)*X 0 1+(1595954659/5000000000 : ℝ)*X 0 2+(2108048429/5000000000 : ℝ)*X 1 0+(2802250941/5000000000 : ℝ)*X 1 1+(1595954659/5000000000 : ℝ)*X 1 2+(2108048429/5000000000 : ℝ)*X 2 0+(2802250941/5000000000 : ℝ)*X 2 1+(1595954659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14583472174897738273107/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44881123/100000000000000 : ℝ)*(base1) + (362434401/100000000000000 : ℝ)*(base19) + (7935419/2500000000000 : ℝ)*(base23) + (28642453/100000000000000 : ℝ)*(base24) + (39950403/50000000000000 : ℝ)*(upper3) + (582645227455193/100000000000000 : ℝ)*(major0) + (582645227455193/100000000000000 : ℝ)*(major1) + (582645227455193/100000000000000 : ℝ)*(major2) + (772573281685637/100000000000000 : ℝ)*(sp0) + (386286745809171/50000000000000 : ℝ)*(sp1) + (77257350799353/10000000000000 : ℝ)*(sp2) + (392716054661289/100000000000000 : ℝ)*(sp3) + (61724823/10000000000000 : ℝ)*(sp4) + (220275379/50000000000000 : ℝ)*(sp7) + (392716540093171/100000000000000 : ℝ)*(f.failure) + (772573854052743/100000000000000 : ℝ)*(f.sum) + (22473765503877/8000000000000000000000000000 : ℝ)*base65 + (34552051992123/16000000000000000000000000000 : ℝ)*base68 + (37798680504123/16000000000000000000000000000 : ℝ)*base70 + (2680072632123/16000000000000000000000000000 : ℝ)*base72 + (19918761759877/8000000000000000000000000000 : ℝ)*base73 + (5586843303877/16000000000000000000000000000 : ℝ)*base75 + (40144794215877/16000000000000000000000000000 : ℝ)*base77 + (57765087319877/16000000000000000000000000000 : ℝ)*base79 + (52881845927877/8000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (29786603/10000000000000000000000 : ℝ)*base89 + (29786603/10000000000000000000000 : ℝ)*base91 + (29786603/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2217035699874403088133/500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (640451247/100000000000000 : ℝ)*(base19) + (40246717/4000000000000 : ℝ)*(base23) + (79650541/25000000000000 : ℝ)*(base39) + (467667/400000000000 : ℝ)*(base45) + (11251533/50000000000000 : ℝ)*(upper3) + (60372789/20000000000000 : ℝ)*(upper5) + (76868747824799/12500000000000 : ℝ)*(major0) + (76868747824799/12500000000000 : ℝ)*(major1) + (153737415999057/25000000000000 : ℝ)*(major2) + (27689039/5000000000000 : ℝ)*(sp2) + (40770439826607/5000000000000 : ℝ)*(sp4) + (815408156080893/100000000000000 : ℝ)*(sp5) + (509629721991/62500000000 : ℝ)*(sp6) + (3238208611407/781250000000 : ℝ)*(sp7) + (3238208611407/781250000000 : ℝ)*(f.failure) + (25481534847947/3125000000000 : ℝ)*(f.sum) + (583329948441/800000000000000000000000000 : ℝ)*base66 + (3453395121373/4000000000000000000000000000 : ℝ)*base67 + (7777684575789/2000000000000000000000000000 : ℝ)*base70 + (8138165174627/4000000000000000000000000000 : ℝ)*base72 + (1263183559559/800000000000000000000000000 : ℝ)*base73 + (5604235880211/2000000000000000000000000000 : ℝ)*base75 + (7903430775789/2000000000000000000000000000 : ℝ)*base78 + (15417649223789/2000000000000000000000000000 : ℝ)*base80 + (1025386287789/1000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (429751/78125000000000000000 : ℝ)*base89 + (429751/78125000000000000000 : ℝ)*base91 + (429751/78125000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1085_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (177/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5607/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1085_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1085_s1_0 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2118754611/10000000000 : ℝ)*x 0 + (114340319/200000000 : ℝ)*x 1 + (1247529673/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118754611/10000000000 : ℝ)^4139 ≤ (12721603259497/100000000000000 : ℝ)^3115 := by
    have hnat : (2118754611 : ℕ)^4139*100000000000000^3115 ≤ 12721603259497^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118754611 10000000000 12721603259497 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114340319/200000000 : ℝ)^4139 ≤ (9514220799913/20000000000000 : ℝ)^3115 := by
    have hnat : (114340319 : ℕ)^4139*20000000000000^3115 ≤ 9514220799913^3115*200000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114340319 200000000 9514220799913 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1247529673/2500000000 : ℝ)^4139 ≤ (19853646357789/50000000000000 : ℝ)^3115 := by
    have hnat : (1247529673 : ℕ)^4139*50000000000000^3115 ≤ 19853646357789^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247529673 2500000000 19853646357789 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2118754611/10000000000 : ℝ), (114340319/200000000 : ℝ), (1247529673/2500000000 : ℝ)] ![(12721603259497/100000000000000 : ℝ), (9514220799913/20000000000000 : ℝ), (19853646357789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2118754611/10000000000 : ℝ)|^4139 ≤ (12721603259497/100000000000000 : ℝ)^3115
        have hw : |(-2118754611/10000000000 : ℝ)|=(2118754611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(114340319/200000000 : ℝ)|^4139 ≤ (9514220799913/20000000000000 : ℝ)^3115
        have hw : |(114340319/200000000 : ℝ)|=(114340319/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1247529673/2500000000 : ℝ)|^4139 ≤ (19853646357789/50000000000000 : ℝ)^3115
        have hw : |(1247529673/2500000000 : ℝ)|=(1247529673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s1_1 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1355565387/2500000000 : ℝ)*x 0 + (-2512189391/10000000000 : ℝ)*x 1 + (998023789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355565387/2500000000 : ℝ)^4139 ≤ (4434014300663/10000000000000 : ℝ)^3115 := by
    have hnat : (1355565387 : ℕ)^4139*10000000000000^3115 ≤ 4434014300663^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355565387 2500000000 4434014300663 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2512189391/10000000000 : ℝ)^4139 ≤ (3190512317731/20000000000000 : ℝ)^3115 := by
    have hnat : (2512189391 : ℕ)^4139*20000000000000^3115 ≤ 3190512317731^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512189391 10000000000 3190512317731 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998023789/2000000000 : ℝ)^4139 ≤ (19853647695269/50000000000000 : ℝ)^3115 := by
    have hnat : (998023789 : ℕ)^4139*50000000000000^3115 ≤ 19853647695269^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998023789 2000000000 19853647695269 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355565387/2500000000 : ℝ), (-2512189391/10000000000 : ℝ), (998023789/2000000000 : ℝ)] ![(4434014300663/10000000000000 : ℝ), (3190512317731/20000000000000 : ℝ), (19853647695269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355565387/2500000000 : ℝ)|^4139 ≤ (4434014300663/10000000000000 : ℝ)^3115
        have hw : |(1355565387/2500000000 : ℝ)|=(1355565387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2512189391/10000000000 : ℝ)|^4139 ≤ (3190512317731/20000000000000 : ℝ)^3115
        have hw : |(-2512189391/10000000000 : ℝ)|=(2512189391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(998023789/2000000000 : ℝ)|^4139 ≤ (19853647695269/50000000000000 : ℝ)^3115
        have hw : |(998023789/2000000000 : ℝ)|=(998023789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s1_2 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1355565591/2500000000 : ℝ)*x 0 + (4990118091/10000000000 : ℝ)*x 1 + (-2512189411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355565591/2500000000 : ℝ)^4139 ≤ (22170075936483/50000000000000 : ℝ)^3115 := by
    have hnat : (1355565591 : ℕ)^4139*50000000000000^3115 ≤ 22170075936483^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355565591 2500000000 22170075936483 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4990118091/10000000000 : ℝ)^4139 ≤ (39707286361227/100000000000000 : ℝ)^3115 := by
    have hnat : (4990118091 : ℕ)^4139*100000000000000^3115 ≤ 39707286361227^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990118091 10000000000 39707286361227 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2512189411/10000000000 : ℝ)^4139 ≤ (3190512351481/20000000000000 : ℝ)^3115 := by
    have hnat : (2512189411 : ℕ)^4139*20000000000000^3115 ≤ 3190512351481^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2512189411 10000000000 3190512351481 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355565591/2500000000 : ℝ), (4990118091/10000000000 : ℝ), (-2512189411/10000000000 : ℝ)] ![(22170075936483/50000000000000 : ℝ), (39707286361227/100000000000000 : ℝ), (3190512351481/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355565591/2500000000 : ℝ)|^4139 ≤ (22170075936483/50000000000000 : ℝ)^3115
        have hw : |(1355565591/2500000000 : ℝ)|=(1355565591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4990118091/10000000000 : ℝ)|^4139 ≤ (39707286361227/100000000000000 : ℝ)^3115
        have hw : |(4990118091/10000000000 : ℝ)|=(4990118091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2512189411/10000000000 : ℝ)|^4139 ≤ (3190512351481/20000000000000 : ℝ)^3115
        have hw : |(-2512189411/10000000000 : ℝ)|=(2512189411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s1_3 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161113697/5000000000 : ℝ)*x 0 + (733244251/2000000000 : ℝ)*x 1 + (1019242537/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161113697/5000000000 : ℝ)^4139 ≤ (1640299193977/5000000000000 : ℝ)^3115 := by
    have hnat : (2161113697 : ℕ)^4139*5000000000000^3115 ≤ 1640299193977^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161113697 5000000000 1640299193977 5000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733244251/2000000000 : ℝ)^4139 ≤ (26361093907069/100000000000000 : ℝ)^3115 := by
    have hnat : (733244251 : ℕ)^4139*100000000000000^3115 ≤ 26361093907069^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733244251 2000000000 26361093907069 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019242537/2000000000 : ℝ)^4139 ≤ (40832922201053/100000000000000 : ℝ)^3115 := by
    have hnat : (1019242537 : ℕ)^4139*100000000000000^3115 ≤ 40832922201053^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019242537 2000000000 40832922201053 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161113697/5000000000 : ℝ), (733244251/2000000000 : ℝ), (1019242537/2000000000 : ℝ)] ![(1640299193977/5000000000000 : ℝ), (26361093907069/100000000000000 : ℝ), (40832922201053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161113697/5000000000 : ℝ)|^4139 ≤ (1640299193977/5000000000000 : ℝ)^3115
        have hw : |(2161113697/5000000000 : ℝ)|=(2161113697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733244251/2000000000 : ℝ)|^4139 ≤ (26361093907069/100000000000000 : ℝ)^3115
        have hw : |(733244251/2000000000 : ℝ)|=(733244251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019242537/2000000000 : ℝ)|^4139 ≤ (40832922201053/100000000000000 : ℝ)^3115
        have hw : |(1019242537/2000000000 : ℝ)|=(1019242537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s1_4 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-42392877/200000000 : ℝ)*x 0 + (2500130813/5000000000 : ℝ)*x 1 + (570666843/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42392877/200000000 : ℝ)^4139 ≤ (6364349085799/50000000000000 : ℝ)^3115 := by
    have hnat : (42392877 : ℕ)^4139*50000000000000^3115 ≤ 6364349085799^3115*200000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42392877 200000000 6364349085799 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500130813/5000000000 : ℝ)^4139 ≤ (39814569409397/100000000000000 : ℝ)^3115 := by
    have hnat : (2500130813 : ℕ)^4139*100000000000000^3115 ≤ 39814569409397^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500130813 5000000000 39814569409397 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (570666843/1000000000 : ℝ)^4139 ≤ (1186418309937/2500000000000 : ℝ)^3115 := by
    have hnat : (570666843 : ℕ)^4139*2500000000000^3115 ≤ 1186418309937^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570666843 1000000000 1186418309937 2500000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42392877/200000000 : ℝ), (2500130813/5000000000 : ℝ), (570666843/1000000000 : ℝ)] ![(6364349085799/50000000000000 : ℝ), (39814569409397/100000000000000 : ℝ), (1186418309937/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42392877/200000000 : ℝ)|^4139 ≤ (6364349085799/50000000000000 : ℝ)^3115
        have hw : |(-42392877/200000000 : ℝ)|=(42392877/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2500130813/5000000000 : ℝ)|^4139 ≤ (39814569409397/100000000000000 : ℝ)^3115
        have hw : |(2500130813/5000000000 : ℝ)|=(2500130813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(570666843/1000000000 : ℝ)|^4139 ≤ (1186418309937/2500000000000 : ℝ)^3115
        have hw : |(570666843/1000000000 : ℝ)|=(570666843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s1_5 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (523643893/1000000000 : ℝ)*x 0 + (-1795639687/10000000000 : ℝ)*x 1 + (142666707/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (523643893/1000000000 : ℝ)^4139 ≤ (42332529104987/100000000000000 : ℝ)^3115 := by
    have hnat : (523643893 : ℕ)^4139*100000000000000^3115 ≤ 42332529104987^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523643893 1000000000 42332529104987 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1795639687/10000000000 : ℝ)^4139 ≤ (2552685032447/25000000000000 : ℝ)^3115 := by
    have hnat : (1795639687 : ℕ)^4139*25000000000000^3115 ≤ 2552685032447^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795639687 10000000000 2552685032447 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142666707/250000000 : ℝ)^4139 ≤ (47456730740017/100000000000000 : ℝ)^3115 := by
    have hnat : (142666707 : ℕ)^4139*100000000000000^3115 ≤ 47456730740017^3115*250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142666707 250000000 47456730740017 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(523643893/1000000000 : ℝ), (-1795639687/10000000000 : ℝ), (142666707/250000000 : ℝ)] ![(42332529104987/100000000000000 : ℝ), (2552685032447/25000000000000 : ℝ), (47456730740017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(523643893/1000000000 : ℝ)|^4139 ≤ (42332529104987/100000000000000 : ℝ)^3115
        have hw : |(523643893/1000000000 : ℝ)|=(523643893/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1795639687/10000000000 : ℝ)|^4139 ≤ (2552685032447/25000000000000 : ℝ)^3115
        have hw : |(-1795639687/10000000000 : ℝ)|=(1795639687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(142666707/250000000 : ℝ)|^4139 ≤ (47456730740017/100000000000000 : ℝ)^3115
        have hw : |(142666707/250000000 : ℝ)|=(142666707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s1_6 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1309109737/2500000000 : ℝ)*x 0 + (1426667099/2500000000 : ℝ)*x 1 + (-448909873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309109737/2500000000 : ℝ)^4139 ≤ (42332529298339/100000000000000 : ℝ)^3115 := by
    have hnat : (1309109737 : ℕ)^4139*100000000000000^3115 ≤ 42332529298339^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309109737 2500000000 42332529298339 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1426667099/2500000000 : ℝ)^4139 ≤ (11864183005447/25000000000000 : ℝ)^3115 := by
    have hnat : (1426667099 : ℕ)^4139*25000000000000^3115 ≤ 11864183005447^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1426667099 2500000000 11864183005447 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448909873/2500000000 : ℝ)^4139 ≤ (1276342332053/12500000000000 : ℝ)^3115 := by
    have hnat : (448909873 : ℕ)^4139*12500000000000^3115 ≤ 1276342332053^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448909873 2500000000 1276342332053 12500000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309109737/2500000000 : ℝ), (1426667099/2500000000 : ℝ), (-448909873/2500000000 : ℝ)] ![(42332529298339/100000000000000 : ℝ), (11864183005447/25000000000000 : ℝ), (1276342332053/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309109737/2500000000 : ℝ)|^4139 ≤ (42332529298339/100000000000000 : ℝ)^3115
        have hw : |(1309109737/2500000000 : ℝ)|=(1309109737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1426667099/2500000000 : ℝ)|^4139 ≤ (11864183005447/25000000000000 : ℝ)^3115
        have hw : |(1426667099/2500000000 : ℝ)|=(1426667099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-448909873/2500000000 : ℝ)|^4139 ≤ (1276342332053/12500000000000 : ℝ)^3115
        have hw : |(-448909873/2500000000 : ℝ)|=(448909873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s1_7 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2161988027/5000000000 : ℝ)*x 0 + (126906493/250000000 : ℝ)*x 1 + (460822097/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2161988027/5000000000 : ℝ)^4139 ≤ (32823620569607/100000000000000 : ℝ)^3115 := by
    have hnat : (2161988027 : ℕ)^4139*100000000000000^3115 ≤ 32823620569607^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161988027 5000000000 32823620569607 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126906493/250000000 : ℝ)^4139 ≤ (40620632994401/100000000000000 : ℝ)^3115 := by
    have hnat : (126906493 : ℕ)^4139*100000000000000^3115 ≤ 40620632994401^3115*250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126906493 250000000 40620632994401 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (460822097/1250000000 : ℝ)^4139 ≤ (26555746420737/100000000000000 : ℝ)^3115 := by
    have hnat : (460822097 : ℕ)^4139*100000000000000^3115 ≤ 26555746420737^3115*1250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      460822097 1250000000 26555746420737 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2161988027/5000000000 : ℝ), (126906493/250000000 : ℝ), (460822097/1250000000 : ℝ)] ![(32823620569607/100000000000000 : ℝ), (40620632994401/100000000000000 : ℝ), (26555746420737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2161988027/5000000000 : ℝ)|^4139 ≤ (32823620569607/100000000000000 : ℝ)^3115
        have hw : |(2161988027/5000000000 : ℝ)|=(2161988027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126906493/250000000 : ℝ)|^4139 ≤ (40620632994401/100000000000000 : ℝ)^3115
        have hw : |(126906493/250000000 : ℝ)|=(126906493/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(460822097/1250000000 : ℝ)|^4139 ≤ (26555746420737/100000000000000 : ℝ)^3115
        have hw : |(460822097/1250000000 : ℝ)|=(460822097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1085_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5607/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1331/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20701/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5607/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5607/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (177/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5607/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5607/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (177/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5607/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5607/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (177/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (177/100000 : ℝ) ^ (8277/2048 : ℝ) ≤ (754524257/100000000000000000000 : ℝ) := by
    have hpowers : (177/100000 : ℝ)^8277 ≤ (754524257/100000000000000000000 : ℝ)^2048 := by
      have hnat : (177 : ℕ)^8277*100000000000000000000^2048 ≤ 754524257^2048*100000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        177 100000 754524257 100000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (177/100000 : ℝ)) (X := (754524257/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5607/20000 : ℝ) ^ (8277/2048 : ℝ) ≤ (585975768908674657/100000000000000000000 : ℝ) := by
    have hpowers : (5607/20000 : ℝ)^8277 ≤ (585975768908674657/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5607 : ℕ)^8277*100000000000000000000^2048 ≤ 585975768908674657^2048*20000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 20000 585975768908674657 100000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/20000 : ℝ)) (X := (585975768908674657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000000754524257/50000000000000000000 : ℝ) ≤ (10000000000037339/10000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50000000000754524257/50000000000000000000 : ℝ)^2048 ≤ (10000000000037339/10000000000000000 : ℝ)^8277 := by
      have hnat : (50000000000754524257 : ℕ)^2048*10000000000000000^8277 ≤ 10000000000037339^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000000754524257 50000000000000000000 10000000000037339 10000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000037339/10000000000000000 : ℝ)) (X := (50000000000754524257/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50292987884831599457/50000000000000000000 : ℝ) ≤ (31295209666387/31250000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50292987884831599457/50000000000000000000 : ℝ)^2048 ≤ (31295209666387/31250000000000 : ℝ)^8277 := by
      have hnat : (50292987884831599457 : ℕ)^2048*31250000000000^8277 ≤ 31295209666387^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50292987884831599457 50000000000000000000 31295209666387 31250000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31295209666387/31250000000000 : ℝ)) (X := (50292987884831599457/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50585975768908674657/50000000000000000000 : ℝ) ≤ (10028934186450341/10000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50585975768908674657/50000000000000000000 : ℝ)^2048 ≤ (10028934186450341/10000000000000000 : ℝ)^8277 := by
      have hnat : (50585975768908674657 : ℕ)^2048*10000000000000000^8277 ≤ 10028934186450341^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50585975768908674657 50000000000000000000 10028934186450341 10000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10028934186450341/10000000000000000 : ℝ)) (X := (50585975768908674657/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(754524257/100000000000000000000 : ℝ) ≤ ((23214573220837090709/23215000000000000000 : ℝ)+2*(4822364402167/928600000000000 : ℝ)*(177/100000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (23214573220837090709/23215000000000000000 : ℝ)+2*(4822364402167/928600000000000 : ℝ)*(177/100000 : ℝ)=(10000000000037339/10000000000000000 : ℝ) by norm_num, show 1+2*(754524257/100000000000000000000 : ℝ)=(50000000000754524257/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(585975768908674657/100000000000000000000 : ℝ)+(754524257/100000000000000000000 : ℝ) ≤ ((23214573220837090709/23215000000000000000 : ℝ)+(4822364402167/928600000000000 : ℝ)*((5607/20000 : ℝ)+(177/100000 : ℝ)))^(8277/2048 : ℝ) := by
    rw [show (23214573220837090709/23215000000000000000 : ℝ)+(4822364402167/928600000000000 : ℝ)*((5607/20000 : ℝ)+(177/100000 : ℝ))=(31295209666387/31250000000000 : ℝ) by norm_num, show 1+(585975768908674657/100000000000000000000 : ℝ)+(754524257/100000000000000000000 : ℝ)=(50292987884831599457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(585975768908674657/100000000000000000000 : ℝ) ≤ ((23214573220837090709/23215000000000000000 : ℝ)+2*(4822364402167/928600000000000 : ℝ)*(5607/20000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (23214573220837090709/23215000000000000000 : ℝ)+2*(4822364402167/928600000000000 : ℝ)*(5607/20000 : ℝ)=(10028934186450341/10000000000000000 : ℝ) by norm_num, show 1+2*(585975768908674657/100000000000000000000 : ℝ)=(50585975768908674657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23214573220837090709/23215000000000000000 : ℝ)*(X 1 0+X 2 0)+(4822364402167/928600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (177/100000 : ℝ)) (hi := (5607/20000 : ℝ)) (c := (23214573220837090709/23215000000000000000 : ℝ)) (alpha := (4822364402167/928600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23214573220837090709/23215000000000000000 : ℝ)*(X 0 1+X 2 1)+(4822364402167/928600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (177/100000 : ℝ)) (hi := (5607/20000 : ℝ)) (c := (23214573220837090709/23215000000000000000 : ℝ)) (alpha := (4822364402167/928600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23214573220837090709/23215000000000000000 : ℝ)*(X 0 2+X 1 2)+(4822364402167/928600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (177/100000 : ℝ)) (hi := (5607/20000 : ℝ)) (c := (23214573220837090709/23215000000000000000 : ℝ)) (alpha := (4822364402167/928600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2118754611/10000000000 : ℝ)*X 0 0+(114340319/200000000 : ℝ)*X 0 1+(1247529673/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1355565387/2500000000 : ℝ)*X 1 0+(-2512189391/10000000000 : ℝ)*X 1 1+(998023789/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355565591/2500000000 : ℝ)*X 2 0+(4990118091/10000000000 : ℝ)*X 2 1+(-2512189411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2161113697/5000000000 : ℝ)*X 0 0+(733244251/2000000000 : ℝ)*X 0 1+(1019242537/2000000000 : ℝ)*X 0 2+(2161113697/5000000000 : ℝ)*X 1 0+(733244251/2000000000 : ℝ)*X 1 1+(1019242537/2000000000 : ℝ)*X 1 2+(2161113697/5000000000 : ℝ)*X 2 0+(733244251/2000000000 : ℝ)*X 2 1+(1019242537/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-42392877/200000000 : ℝ)*X 0 0+(2500130813/5000000000 : ℝ)*X 0 1+(570666843/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((523643893/1000000000 : ℝ)*X 1 0+(-1795639687/10000000000 : ℝ)*X 1 1+(142666707/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1309109737/2500000000 : ℝ)*X 2 0+(1426667099/2500000000 : ℝ)*X 2 1+(-448909873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2161988027/5000000000 : ℝ)*X 0 0+(126906493/250000000 : ℝ)*X 0 1+(460822097/1250000000 : ℝ)*X 0 2+(2161988027/5000000000 : ℝ)*X 1 0+(126906493/250000000 : ℝ)*X 1 1+(460822097/1250000000 : ℝ)*X 1 2+(2161988027/5000000000 : ℝ)*X 2 0+(126906493/250000000 : ℝ)*X 2 1+(460822097/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (411057421585825546336377/46430000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44641159/25000000000000 : ℝ)*(base1) + (370454103/20000000000000 : ℝ)*(base19) + (257413071/12500000000000 : ℝ)*(base23) + (171530793/100000000000000 : ℝ)*(upper3) + (44170393/20000000000000 : ℝ)*(upper5) + (1037521212004867/100000000000000 : ℝ)*(major0) + (1037521212004867/100000000000000 : ℝ)*(major1) + (1037521212004867/100000000000000 : ℝ)*(major2) + (1375718892989177/100000000000000 : ℝ)*(sp0) + (343931665245501/25000000000000 : ℝ)*(sp1) + (27514529078959/2000000000000 : ℝ)*(sp2) + (699309102790201/100000000000000 : ℝ)*(sp3) + (4899413989/50000000000000 : ℝ)*(sp4) + (866858661/20000000000000 : ℝ)*(sp7) + (699313615648141/100000000000000 : ℝ)*(f.failure) + (1375728513252519/100000000000000 : ℝ)*(f.sum) + (81177593551479/46430000000000000000000000000 : ℝ)*base65 + (19937990626811294297/2321500000000000000000000000000000 : ℝ)*base68 + (13586072158465294297/2321500000000000000000000000000000 : ℝ)*base70 + (932005060894205703/2321500000000000000000000000000000 : ℝ)*base71 + (111338508274341/46430000000000000000000000000 : ℝ)*base74 + (7804921394519294297/2321500000000000000000000000000000 : ℝ)*base76 + (9542978772922205703/2321500000000000000000000000000000 : ℝ)*base77 + (9284080819040705703/2321500000000000000000000000000000 : ℝ)*base79 + (168059700316661/46430000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (4017813/10000000000000000000000 : ℝ)*base89 + (4017813/10000000000000000000000 : ℝ)*base91 + (4017813/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2686629459130819304702457357/290187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53636343/50000000000000 : ℝ)*(base1) + (2063630493/100000000000000 : ℝ)*(base19) + (1041157069/50000000000000 : ℝ)*(base23) + (211995761/100000000000000 : ℝ)*(upper3) + (211446791/100000000000000 : ℝ)*(upper5) + (533800969184491/50000000000000 : ℝ)*(major0) + (533800969184491/50000000000000 : ℝ)*(major1) + (533800969184491/50000000000000 : ℝ)*(major2) + (8255371233/100000000000000 : ℝ)*(sp1) + (4322354707/50000000000000 : ℝ)*(sp2) + (1415614945113877/100000000000000 : ℝ)*(sp4) + (283120903767893/20000000000000 : ℝ)*(sp5) + (35390102770441/2500000000000 : ℝ)*(sp6) + (71958862301563/10000000000000 : ℝ)*(sp7) + (179897182572079/25000000000000 : ℝ)*(f.failure) + (1415614837841191/100000000000000 : ℝ)*(f.sum) + (7067510304447/23215000000000000000000000000 : ℝ)*base65 + (4922680016498580881/1160750000000000000000000000000000 : ℝ)*base68 + (4697731759869580881/1160750000000000000000000000000000 : ℝ)*base70 + (1349737245017419119/1160750000000000000000000000000000 : ℝ)*base71 + (90420851988033/23215000000000000000000000000 : ℝ)*base74 + (5275989871075830881/1160750000000000000000000000000000 : ℝ)*base76 + (7196303529314080881/1160750000000000000000000000000000 : ℝ)*base78 + (5832162594002580881/1160750000000000000000000000000000 : ℝ)*base80 + (1543798557893/23215000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (14256647/2500000000000000000000 : ℝ)*base89 + (14256647/2500000000000000000000 : ℝ)*base91 + (14256647/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1085_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5607/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (177/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1331/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20701/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1085_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1085_s2_0 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087553479/5000000000 : ℝ)*x 0 + (5522016303/10000000000 : ℝ)*x 1 + (643668149/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087553479/5000000000 : ℝ)^4139 ≤ (13173140818021/100000000000000 : ℝ)^3115 := by
    have hnat : (1087553479 : ℕ)^4139*100000000000000^3115 ≤ 13173140818021^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087553479 5000000000 13173140818021 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5522016303/10000000000 : ℝ)^4139 ≤ (22713651590289/50000000000000 : ℝ)^3115 := by
    have hnat : (5522016303 : ℕ)^4139*50000000000000^3115 ≤ 22713651590289^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522016303 10000000000 22713651590289 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (643668149/1250000000 : ℝ)^4139 ≤ (20699777996501/50000000000000 : ℝ)^3115 := by
    have hnat : (643668149 : ℕ)^4139*50000000000000^3115 ≤ 20699777996501^3115*1250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643668149 1250000000 20699777996501 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087553479/5000000000 : ℝ), (5522016303/10000000000 : ℝ), (643668149/1250000000 : ℝ)] ![(13173140818021/100000000000000 : ℝ), (22713651590289/50000000000000 : ℝ), (20699777996501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087553479/5000000000 : ℝ)|^4139 ≤ (13173140818021/100000000000000 : ℝ)^3115
        have hw : |(-1087553479/5000000000 : ℝ)|=(1087553479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5522016303/10000000000 : ℝ)|^4139 ≤ (22713651590289/50000000000000 : ℝ)^3115
        have hw : |(5522016303/10000000000 : ℝ)|=(5522016303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(643668149/1250000000 : ℝ)|^4139 ≤ (20699777996501/50000000000000 : ℝ)^3115
        have hw : |(643668149/1250000000 : ℝ)|=(643668149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s2_1 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376356181/10000000000 : ℝ)*x 0 + (-473861047/2000000000 : ℝ)*x 1 + (5149345741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376356181/10000000000 : ℝ)^4139 ≤ (10960512180659/25000000000000 : ℝ)^3115 := by
    have hnat : (5376356181 : ℕ)^4139*25000000000000^3115 ≤ 10960512180659^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376356181 10000000000 10960512180659 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473861047/2000000000 : ℝ)^4139 ≤ (14758389410459/100000000000000 : ℝ)^3115 := by
    have hnat : (473861047 : ℕ)^4139*100000000000000^3115 ≤ 14758389410459^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473861047 2000000000 14758389410459 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5149345741/10000000000 : ℝ)^4139 ≤ (8279912371561/20000000000000 : ℝ)^3115 := by
    have hnat : (5149345741 : ℕ)^4139*20000000000000^3115 ≤ 8279912371561^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149345741 10000000000 8279912371561 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376356181/10000000000 : ℝ), (-473861047/2000000000 : ℝ), (5149345741/10000000000 : ℝ)] ![(10960512180659/25000000000000 : ℝ), (14758389410459/100000000000000 : ℝ), (8279912371561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376356181/10000000000 : ℝ)|^4139 ≤ (10960512180659/25000000000000 : ℝ)^3115
        have hw : |(5376356181/10000000000 : ℝ)|=(5376356181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473861047/2000000000 : ℝ)|^4139 ≤ (14758389410459/100000000000000 : ℝ)^3115
        have hw : |(-473861047/2000000000 : ℝ)|=(473861047/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5149345741/10000000000 : ℝ)|^4139 ≤ (8279912371561/20000000000000 : ℝ)^3115
        have hw : |(5149345741/10000000000 : ℝ)|=(5149345741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s2_2 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376356321/10000000000 : ℝ)*x 0 + (5149345583/10000000000 : ℝ)*x 1 + (-473861051/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376356321/10000000000 : ℝ)^4139 ≤ (1753682009583/4000000000000 : ℝ)^3115 := by
    have hnat : (5376356321 : ℕ)^4139*4000000000000^3115 ≤ 1753682009583^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376356321 10000000000 1753682009583 4000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5149345583/10000000000 : ℝ)^4139 ≤ (20699780084969/50000000000000 : ℝ)^3115 := by
    have hnat : (5149345583 : ℕ)^4139*50000000000000^3115 ≤ 20699780084969^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5149345583 10000000000 20699780084969 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473861051/2000000000 : ℝ)^4139 ≤ (1844798696999/12500000000000 : ℝ)^3115 := by
    have hnat : (473861051 : ℕ)^4139*12500000000000^3115 ≤ 1844798696999^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473861051 2000000000 1844798696999 12500000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376356321/10000000000 : ℝ), (5149345583/10000000000 : ℝ), (-473861051/2000000000 : ℝ)] ![(1753682009583/4000000000000 : ℝ), (20699780084969/50000000000000 : ℝ), (1844798696999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376356321/10000000000 : ℝ)|^4139 ≤ (1753682009583/4000000000000 : ℝ)^3115
        have hw : |(5376356321/10000000000 : ℝ)|=(5376356321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5149345583/10000000000 : ℝ)|^4139 ≤ (20699780084969/50000000000000 : ℝ)^3115
        have hw : |(5149345583/10000000000 : ℝ)|=(5149345583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-473861051/2000000000 : ℝ)|^4139 ≤ (1844798696999/12500000000000 : ℝ)^3115
        have hw : |(-473861051/2000000000 : ℝ)|=(473861051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s2_3 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (218036563/500000000 : ℝ)*x 0 + (4009631307/10000000000 : ℝ)*x 1 + (4742769563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (218036563/500000000 : ℝ)^4139 ≤ (8298717254863/25000000000000 : ℝ)^3115 := by
    have hnat : (218036563 : ℕ)^4139*25000000000000^3115 ≤ 8298717254863^3115*500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218036563 500000000 8298717254863 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4009631307/10000000000 : ℝ)^4139 ≤ (14845751831497/50000000000000 : ℝ)^3115 := by
    have hnat : (4009631307 : ℕ)^4139*50000000000000^3115 ≤ 14845751831497^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009631307 10000000000 14845751831497 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4742769563/10000000000 : ℝ)^4139 ≤ (18556813648637/50000000000000 : ℝ)^3115 := by
    have hnat : (4742769563 : ℕ)^4139*50000000000000^3115 ≤ 18556813648637^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4742769563 10000000000 18556813648637 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(218036563/500000000 : ℝ), (4009631307/10000000000 : ℝ), (4742769563/10000000000 : ℝ)] ![(8298717254863/25000000000000 : ℝ), (14845751831497/50000000000000 : ℝ), (18556813648637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(218036563/500000000 : ℝ)|^4139 ≤ (8298717254863/25000000000000 : ℝ)^3115
        have hw : |(218036563/500000000 : ℝ)|=(218036563/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4009631307/10000000000 : ℝ)|^4139 ≤ (14845751831497/50000000000000 : ℝ)^3115
        have hw : |(4009631307/10000000000 : ℝ)|=(4009631307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4742769563/10000000000 : ℝ)|^4139 ≤ (18556813648637/50000000000000 : ℝ)^3115
        have hw : |(4742769563/10000000000 : ℝ)|=(4742769563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s2_4 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087613303/5000000000 : ℝ)*x 0 + (5152020049/10000000000 : ℝ)*x 1 + (5519313661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087613303/5000000000 : ℝ)^4139 ≤ (13174103660987/100000000000000 : ℝ)^3115 := by
    have hnat : (1087613303 : ℕ)^4139*100000000000000^3115 ≤ 13174103660987^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087613303 5000000000 13174103660987 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152020049/10000000000 : ℝ)^4139 ≤ (20714066564327/50000000000000 : ℝ)^3115 := by
    have hnat : (5152020049 : ℕ)^4139*50000000000000^3115 ≤ 20714066564327^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152020049 10000000000 20714066564327 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5519313661/10000000000 : ℝ)^4139 ≤ (5674720399829/12500000000000 : ℝ)^3115 := by
    have hnat : (5519313661 : ℕ)^4139*12500000000000^3115 ≤ 5674720399829^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519313661 10000000000 5674720399829 12500000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087613303/5000000000 : ℝ), (5152020049/10000000000 : ℝ), (5519313661/10000000000 : ℝ)] ![(13174103660987/100000000000000 : ℝ), (20714066564327/50000000000000 : ℝ), (5674720399829/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087613303/5000000000 : ℝ)|^4139 ≤ (13174103660987/100000000000000 : ℝ)^3115
        have hw : |(-1087613303/5000000000 : ℝ)|=(1087613303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152020049/10000000000 : ℝ)|^4139 ≤ (20714066564327/50000000000000 : ℝ)^3115
        have hw : |(5152020049/10000000000 : ℝ)|=(5152020049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5519313661/10000000000 : ℝ)|^4139 ≤ (5674720399829/12500000000000 : ℝ)^3115
        have hw : |(5519313661/10000000000 : ℝ)|=(5519313661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s2_5 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660270661/1250000000 : ℝ)*x 0 + (-499834303/2500000000 : ℝ)*x 1 + (1379828439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660270661/1250000000 : ℝ)^4139 ≤ (42824414405339/100000000000000 : ℝ)^3115 := by
    have hnat : (660270661 : ℕ)^4139*100000000000000^3115 ≤ 42824414405339^3115*1250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660270661 1250000000 42824414405339 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499834303/2500000000 : ℝ)^4139 ≤ (368056917061/3125000000000 : ℝ)^3115 := by
    have hnat : (499834303 : ℕ)^4139*3125000000000^3115 ≤ 368056917061^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499834303 2500000000 368056917061 3125000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1379828439/2500000000 : ℝ)^4139 ≤ (22698882118451/50000000000000 : ℝ)^3115 := by
    have hnat : (1379828439 : ℕ)^4139*50000000000000^3115 ≤ 22698882118451^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379828439 2500000000 22698882118451 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660270661/1250000000 : ℝ), (-499834303/2500000000 : ℝ), (1379828439/2500000000 : ℝ)] ![(42824414405339/100000000000000 : ℝ), (368056917061/3125000000000 : ℝ), (22698882118451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660270661/1250000000 : ℝ)|^4139 ≤ (42824414405339/100000000000000 : ℝ)^3115
        have hw : |(660270661/1250000000 : ℝ)|=(660270661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-499834303/2500000000 : ℝ)|^4139 ≤ (368056917061/3125000000000 : ℝ)^3115
        have hw : |(-499834303/2500000000 : ℝ)|=(499834303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1379828439/2500000000 : ℝ)|^4139 ≤ (22698882118451/50000000000000 : ℝ)^3115
        have hw : |(1379828439/2500000000 : ℝ)|=(1379828439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s2_6 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056433103/2000000000 : ℝ)*x 0 + (5519313609/10000000000 : ℝ)*x 1 + (-124958569/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056433103/2000000000 : ℝ)^4139 ≤ (21412208425349/50000000000000 : ℝ)^3115 := by
    have hnat : (1056433103 : ℕ)^4139*50000000000000^3115 ≤ 21412208425349^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056433103 2000000000 21412208425349 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5519313609/10000000000 : ℝ)^4139 ≤ (11349440657579/25000000000000 : ℝ)^3115 := by
    have hnat : (5519313609 : ℕ)^4139*25000000000000^3115 ≤ 11349440657579^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5519313609 10000000000 11349440657579 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124958569/625000000 : ℝ)^4139 ≤ (2355564100119/20000000000000 : ℝ)^3115 := by
    have hnat : (124958569 : ℕ)^4139*20000000000000^3115 ≤ 2355564100119^3115*625000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124958569 625000000 2355564100119 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056433103/2000000000 : ℝ), (5519313609/10000000000 : ℝ), (-124958569/625000000 : ℝ)] ![(21412208425349/50000000000000 : ℝ), (11349440657579/25000000000000 : ℝ), (2355564100119/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056433103/2000000000 : ℝ)|^4139 ≤ (21412208425349/50000000000000 : ℝ)^3115
        have hw : |(1056433103/2000000000 : ℝ)|=(1056433103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5519313609/10000000000 : ℝ)|^4139 ≤ (11349440657579/25000000000000 : ℝ)^3115
        have hw : |(5519313609/10000000000 : ℝ)|=(5519313609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124958569/625000000 : ℝ)|^4139 ≤ (2355564100119/20000000000000 : ℝ)^3115
        have hw : |(-124958569/625000000 : ℝ)|=(124958569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s2_7 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174438673/400000000 : ℝ)*x 0 + (118437701/250000000 : ℝ)*x 1 + (401494711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174438673/400000000 : ℝ)^4139 ≤ (33197251687997/100000000000000 : ℝ)^3115 := by
    have hnat : (174438673 : ℕ)^4139*100000000000000^3115 ≤ 33197251687997^3115*400000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174438673 400000000 33197251687997 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (118437701/250000000 : ℝ)^4139 ≤ (9264732338113/25000000000000 : ℝ)^3115 := by
    have hnat : (118437701 : ℕ)^4139*25000000000000^3115 ≤ 9264732338113^3115*250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118437701 250000000 9264732338113 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (401494711/1000000000 : ℝ)^4139 ≤ (2974381894897/10000000000000 : ℝ)^3115 := by
    have hnat : (401494711 : ℕ)^4139*10000000000000^3115 ≤ 2974381894897^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401494711 1000000000 2974381894897 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174438673/400000000 : ℝ), (118437701/250000000 : ℝ), (401494711/1000000000 : ℝ)] ![(33197251687997/100000000000000 : ℝ), (9264732338113/25000000000000 : ℝ), (2974381894897/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174438673/400000000 : ℝ)|^4139 ≤ (33197251687997/100000000000000 : ℝ)^3115
        have hw : |(174438673/400000000 : ℝ)|=(174438673/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(118437701/250000000 : ℝ)|^4139 ≤ (9264732338113/25000000000000 : ℝ)^3115
        have hw : |(118437701/250000000 : ℝ)|=(118437701/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(401494711/1000000000 : ℝ)|^4139 ≤ (2974381894897/10000000000000 : ℝ)^3115
        have hw : |(401494711/1000000000 : ℝ)|=(401494711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1085_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1331/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2201/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16679/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1331/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1331/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1331/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1331/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1331/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1331/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1331/25000 : ℝ) ^ (8277/2048 : ℝ) ≤ (711354512015149/100000000000000000000 : ℝ) := by
    have hpowers : (1331/25000 : ℝ)^8277 ≤ (711354512015149/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1331 : ℕ)^8277*100000000000000000000^2048 ≤ 711354512015149^2048*25000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1331 25000 711354512015149 100000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1331/25000 : ℝ)) (X := (711354512015149/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20701/100000 : ℝ) ^ (8277/2048 : ℝ) ≤ (172018940937200011/100000000000000000000 : ℝ) := by
    have hpowers : (20701/100000 : ℝ)^8277 ≤ (172018940937200011/100000000000000000000 : ℝ)^2048 := by
      have hnat : (20701 : ℕ)^8277*100000000000000000000^2048 ≤ 172018940937200011^2048*100000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20701 100000 172018940937200011 100000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20701/100000 : ℝ)) (X := (172018940937200011/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000711354512015149/50000000000000000000 : ℝ) ≤ (10000035202277191/10000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50000711354512015149/50000000000000000000 : ℝ)^2048 ≤ (10000035202277191/10000000000000000 : ℝ)^8277 := by
      have hnat : (50000711354512015149 : ℕ)^2048*10000000000000000^8277 ≤ 10000035202277191^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000711354512015149 50000000000000000000 10000035202277191 10000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000035202277191/10000000000000000 : ℝ)) (X := (50000711354512015149/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2504318257386230379/2500000000000000000 : ℝ) ≤ (400170845453107/400000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (2504318257386230379/2500000000000000000 : ℝ)^2048 ≤ (400170845453107/400000000000000 : ℝ)^8277 := by
      have hnat : (2504318257386230379 : ℕ)^2048*400000000000000^8277 ≤ 400170845453107^8277*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2504318257386230379 2500000000000000000 400170845453107 400000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400170845453107/400000000000000 : ℝ)) (X := (2504318257386230379/2500000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50172018940937200011/50000000000000000000 : ℝ) ≤ (10008507070378159/10000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50172018940937200011/50000000000000000000 : ℝ)^2048 ≤ (10008507070378159/10000000000000000 : ℝ)^8277 := by
      have hnat : (50172018940937200011 : ℕ)^2048*10000000000000000^8277 ≤ 10008507070378159^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50172018940937200011 50000000000000000000 10008507070378159 10000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008507070378159/10000000000000000 : ℝ)) (X := (50172018940937200011/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(711354512015149/100000000000000000000 : ℝ) ≤ ((1229803496637174499/1230160000000000000 : ℝ)+2*(1058983512621/384425000000000 : ℝ)*(1331/25000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (1229803496637174499/1230160000000000000 : ℝ)+2*(1058983512621/384425000000000 : ℝ)*(1331/25000 : ℝ)=(10000035202277191/10000000000000000 : ℝ) by norm_num, show 1+2*(711354512015149/100000000000000000000 : ℝ)=(50000711354512015149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(172018940937200011/100000000000000000000 : ℝ)+(711354512015149/100000000000000000000 : ℝ) ≤ ((1229803496637174499/1230160000000000000 : ℝ)+(1058983512621/384425000000000 : ℝ)*((20701/100000 : ℝ)+(1331/25000 : ℝ)))^(8277/2048 : ℝ) := by
    rw [show (1229803496637174499/1230160000000000000 : ℝ)+(1058983512621/384425000000000 : ℝ)*((20701/100000 : ℝ)+(1331/25000 : ℝ))=(400170845453107/400000000000000 : ℝ) by norm_num, show 1+(172018940937200011/100000000000000000000 : ℝ)+(711354512015149/100000000000000000000 : ℝ)=(2504318257386230379/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(172018940937200011/100000000000000000000 : ℝ) ≤ ((1229803496637174499/1230160000000000000 : ℝ)+2*(1058983512621/384425000000000 : ℝ)*(20701/100000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (1229803496637174499/1230160000000000000 : ℝ)+2*(1058983512621/384425000000000 : ℝ)*(20701/100000 : ℝ)=(10008507070378159/10000000000000000 : ℝ) by norm_num, show 1+2*(172018940937200011/100000000000000000000 : ℝ)=(50172018940937200011/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1229803496637174499/1230160000000000000 : ℝ)*(X 1 0+X 2 0)+(1058983512621/384425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (1331/25000 : ℝ)) (hi := (20701/100000 : ℝ)) (c := (1229803496637174499/1230160000000000000 : ℝ)) (alpha := (1058983512621/384425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1229803496637174499/1230160000000000000 : ℝ)*(X 0 1+X 2 1)+(1058983512621/384425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (1331/25000 : ℝ)) (hi := (20701/100000 : ℝ)) (c := (1229803496637174499/1230160000000000000 : ℝ)) (alpha := (1058983512621/384425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1229803496637174499/1230160000000000000 : ℝ)*(X 0 2+X 1 2)+(1058983512621/384425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (1331/25000 : ℝ)) (hi := (20701/100000 : ℝ)) (c := (1229803496637174499/1230160000000000000 : ℝ)) (alpha := (1058983512621/384425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1087553479/5000000000 : ℝ)*X 0 0+(5522016303/10000000000 : ℝ)*X 0 1+(643668149/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5376356181/10000000000 : ℝ)*X 1 0+(-473861047/2000000000 : ℝ)*X 1 1+(5149345741/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5376356321/10000000000 : ℝ)*X 2 0+(5149345583/10000000000 : ℝ)*X 2 1+(-473861051/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((218036563/500000000 : ℝ)*X 0 0+(4009631307/10000000000 : ℝ)*X 0 1+(4742769563/10000000000 : ℝ)*X 0 2+(218036563/500000000 : ℝ)*X 1 0+(4009631307/10000000000 : ℝ)*X 1 1+(4742769563/10000000000 : ℝ)*X 1 2+(218036563/500000000 : ℝ)*X 2 0+(4009631307/10000000000 : ℝ)*X 2 1+(4742769563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1087613303/5000000000 : ℝ)*X 0 0+(5152020049/10000000000 : ℝ)*X 0 1+(5519313661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((660270661/1250000000 : ℝ)*X 1 0+(-499834303/2500000000 : ℝ)*X 1 1+(1379828439/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056433103/2000000000 : ℝ)*X 2 0+(5519313609/10000000000 : ℝ)*X 2 1+(-124958569/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174438673/400000000 : ℝ)*X 0 0+(118437701/250000000 : ℝ)*X 0 1+(401494711/1000000000 : ℝ)*X 0 2+(174438673/400000000 : ℝ)*X 1 0+(118437701/250000000 : ℝ)*X 1 1+(401494711/1000000000 : ℝ)*X 1 2+(174438673/400000000 : ℝ)*X 2 0+(118437701/250000000 : ℝ)*X 2 1+(401494711/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47716558123656346904764761/7688500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3572547/25000000000000 : ℝ)*(base1) + (1062895821/100000000000000 : ℝ)*(base19) + (141596291/12500000000000 : ℝ)*(base23) + (112302523/100000000000000 : ℝ)*(upper3) + (2313777/2000000000000 : ℝ)*(upper5) + (505921494984787/25000000000000 : ℝ)*(major0) + (505921494984787/25000000000000 : ℝ)*(major1) + (505921494984787/25000000000000 : ℝ)*(major2) + (1341672649965959/50000000000000 : ℝ)*(sp0) + (335419863234251/12500000000000 : ℝ)*(sp1) + (5366717671999/200000000000 : ℝ)*(sp2) + (1364005389364959/100000000000000 : ℝ)*(sp3) + (7341564049/50000000000000 : ℝ)*(sp4) + (6380579157/100000000000000 : ℝ)*(sp7) + (21312684128661/1562500000000 : ℝ)*(f.failure) + (670839992192457/25000000000000 : ℝ)*(f.sum) + (53634225329573/76885000000000000000000000000 : ℝ)*base66 + (344946837593527113/30754000000000000000000000000000 : ℝ)*base67 + (27773929106239113/30754000000000000000000000000000 : ℝ)*base69 + (47022424320871113/30754000000000000000000000000000 : ℝ)*base71 + (345034660455127/76885000000000000000000000000 : ℝ)*base73 + (144215198543836887/30754000000000000000000000000000 : ℝ)*base76 + (229707456537663113/30754000000000000000000000000000 : ℝ)*base77 + (105129835215351113/30754000000000000000000000000000 : ℝ)*base79 + (288935589932363/76885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1439827/156250000000000000000 : ℝ)*base90 + (1439827/156250000000000000000 : ℝ)*base92 + (1439827/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (370380551886176035907127/76885000000000000000000000000 : ℝ) := by norm_num
    linear_combination (117260949/12500000000000 : ℝ)*(base19) + (1140335367/100000000000000 : ℝ)*(base23) + (142524739/100000000000000 : ℝ)*(upper3) + (4924869/20000000000000 : ℝ)*(lower4) + (9062977/10000000000000 : ℝ)*(upper5) + (1026645979266707/50000000000000 : ℝ)*(major0) + (1026645979266707/50000000000000 : ℝ)*(major1) + (1026645979266707/50000000000000 : ℝ)*(major2) + (4103972851/50000000000000 : ℝ)*(sp1) + (10374077241/100000000000000 : ℝ)*(sp2) + (1361308424369623/50000000000000 : ℝ)*(sp4) + (2722607702705953/100000000000000 : ℝ)*(sp5) + (1361302667163319/50000000000000 : ℝ)*(sp6) + (345991726937463/25000000000000 : ℝ)*(sp7) + (345991726937463/25000000000000 : ℝ)*(f.failure) + (1361308424369623/50000000000000 : ℝ)*(f.sum) + (7106522258777/2402656250000000000000000000 : ℝ)*base66 + (376441583002983193/61508000000000000000000000000000 : ℝ)*base67 + (90680692881447193/61508000000000000000000000000000 : ℝ)*base69 + (307419755957352807/61508000000000000000000000000000 : ℝ)*base72 + (179513650218943/38442500000000000000000000000 : ℝ)*base73 + (321072621764904807/61508000000000000000000000000000 : ℝ)*base76 + (19220048848092807/61508000000000000000000000000000 : ℝ)*base78 + (324550359356555193/61508000000000000000000000000000 : ℝ)*base79 + (134791210811371/76885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2985841/2500000000000000000000 : ℝ)*base90 + (2985841/2500000000000000000000 : ℝ)*base92 + (2985841/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1085_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1331/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16679/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1085_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1085_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16679/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1085_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1085_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1085_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2201/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16679/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1085_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
