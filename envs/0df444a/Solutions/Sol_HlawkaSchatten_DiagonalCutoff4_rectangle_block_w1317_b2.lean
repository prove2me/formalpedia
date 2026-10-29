-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:18.49824+00:00
-- url     : https://prove2.me/submissions/937dd941-7d74-4f3d-b5b1-0acc024a4dc4

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
theorem support_rectangle_w1317_s6_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-413152239/2000000000 : ℝ)*x 0 + (2707010143/5000000000 : ℝ)*x 1 + (5243787391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (413152239/2000000000 : ℝ)^4277 ≤ (12574093449043/100000000000000 : ℝ)^3253 := by
    have hnat : (413152239 : ℕ)^4277*100000000000000^3253 ≤ 12574093449043^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413152239 2000000000 12574093449043 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707010143/5000000000 : ℝ)^4277 ≤ (44630892708777/100000000000000 : ℝ)^3253 := by
    have hnat : (2707010143 : ℕ)^4277*100000000000000^3253 ≤ 44630892708777^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707010143 5000000000 44630892708777 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243787391/10000000000 : ℝ)^4277 ≤ (21397506915439/50000000000000 : ℝ)^3253 := by
    have hnat : (5243787391 : ℕ)^4277*50000000000000^3253 ≤ 21397506915439^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243787391 10000000000 21397506915439 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-413152239/2000000000 : ℝ), (2707010143/5000000000 : ℝ), (5243787391/10000000000 : ℝ)] ![(12574093449043/100000000000000 : ℝ), (44630892708777/100000000000000 : ℝ), (21397506915439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-413152239/2000000000 : ℝ)|^4277 ≤ (12574093449043/100000000000000 : ℝ)^3253
        have hw : |(-413152239/2000000000 : ℝ)|=(413152239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707010143/5000000000 : ℝ)|^4277 ≤ (44630892708777/100000000000000 : ℝ)^3253
        have hw : |(2707010143/5000000000 : ℝ)|=(2707010143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243787391/10000000000 : ℝ)|^4277 ≤ (21397506915439/50000000000000 : ℝ)^3253
        have hw : |(5243787391/10000000000 : ℝ)|=(5243787391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s6_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349421211/10000000000 : ℝ)*x 0 + (-538129323/2500000000 : ℝ)*x 1 + (327736641/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349421211/10000000000 : ℝ)^4277 ≤ (10983012846367/25000000000000 : ℝ)^3253 := by
    have hnat : (5349421211 : ℕ)^4277*25000000000000^3253 ≤ 10983012846367^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349421211 10000000000 10983012846367 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (538129323/2500000000 : ℝ)^4277 ≤ (1327294695251/10000000000000 : ℝ)^3253 := by
    have hnat : (538129323 : ℕ)^4277*10000000000000^3253 ≤ 1327294695251^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538129323 2500000000 1327294695251 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327736641/625000000 : ℝ)^4277 ≤ (10698750413057/25000000000000 : ℝ)^3253 := by
    have hnat : (327736641 : ℕ)^4277*25000000000000^3253 ≤ 10698750413057^3253*625000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327736641 625000000 10698750413057 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349421211/10000000000 : ℝ), (-538129323/2500000000 : ℝ), (327736641/625000000 : ℝ)] ![(10983012846367/25000000000000 : ℝ), (1327294695251/10000000000000 : ℝ), (10698750413057/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349421211/10000000000 : ℝ)|^4277 ≤ (10983012846367/25000000000000 : ℝ)^3253
        have hw : |(5349421211/10000000000 : ℝ)|=(5349421211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-538129323/2500000000 : ℝ)|^4277 ≤ (1327294695251/10000000000000 : ℝ)^3253
        have hw : |(-538129323/2500000000 : ℝ)|=(538129323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327736641/625000000 : ℝ)|^4277 ≤ (10698750413057/25000000000000 : ℝ)^3253
        have hw : |(327736641/625000000 : ℝ)|=(327736641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s6_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337354949/2500000000 : ℝ)*x 0 + (2621893649/5000000000 : ℝ)*x 1 + (-2152517797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337354949/2500000000 : ℝ)^4277 ≤ (10983009026693/25000000000000 : ℝ)^3253 := by
    have hnat : (1337354949 : ℕ)^4277*25000000000000^3253 ≤ 10983009026693^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337354949 2500000000 10983009026693 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621893649/5000000000 : ℝ)^4277 ≤ (42795012832979/100000000000000 : ℝ)^3253 := by
    have hnat : (2621893649 : ℕ)^4277*100000000000000^3253 ≤ 42795012832979^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621893649 5000000000 42795012832979 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2152517797/10000000000 : ℝ)^4277 ≤ (13272951046693/100000000000000 : ℝ)^3253 := by
    have hnat : (2152517797 : ℕ)^4277*100000000000000^3253 ≤ 13272951046693^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2152517797 10000000000 13272951046693 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337354949/2500000000 : ℝ), (2621893649/5000000000 : ℝ), (-2152517797/10000000000 : ℝ)] ![(10983009026693/25000000000000 : ℝ), (42795012832979/100000000000000 : ℝ), (13272951046693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337354949/2500000000 : ℝ)|^4277 ≤ (10983009026693/25000000000000 : ℝ)^3253
        have hw : |(1337354949/2500000000 : ℝ)|=(1337354949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621893649/5000000000 : ℝ)|^4277 ≤ (42795012832979/100000000000000 : ℝ)^3253
        have hw : |(2621893649/5000000000 : ℝ)|=(2621893649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2152517797/10000000000 : ℝ)|^4277 ≤ (13272951046693/100000000000000 : ℝ)^3253
        have hw : |(-2152517797/10000000000 : ℝ)|=(2152517797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s6_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4333195941/10000000000 : ℝ)*x 0 + (207999477/500000000 : ℝ)*x 1 + (564150767/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333195941/10000000000 : ℝ)^4277 ≤ (33302784446143/100000000000000 : ℝ)^3253 := by
    have hnat : (4333195941 : ℕ)^4277*100000000000000^3253 ≤ 33302784446143^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333195941 10000000000 33302784446143 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207999477/500000000 : ℝ)^4277 ≤ (31563683094529/100000000000000 : ℝ)^3253 := by
    have hnat : (207999477 : ℕ)^4277*100000000000000^3253 ≤ 31563683094529^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207999477 500000000 31563683094529 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564150767/1250000000 : ℝ)^4277 ≤ (17566766218103/50000000000000 : ℝ)^3253 := by
    have hnat : (564150767 : ℕ)^4277*50000000000000^3253 ≤ 17566766218103^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564150767 1250000000 17566766218103 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333195941/10000000000 : ℝ), (207999477/500000000 : ℝ), (564150767/1250000000 : ℝ)] ![(33302784446143/100000000000000 : ℝ), (31563683094529/100000000000000 : ℝ), (17566766218103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333195941/10000000000 : ℝ)|^4277 ≤ (33302784446143/100000000000000 : ℝ)^3253
        have hw : |(4333195941/10000000000 : ℝ)|=(4333195941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207999477/500000000 : ℝ)|^4277 ≤ (31563683094529/100000000000000 : ℝ)^3253
        have hw : |(207999477/500000000 : ℝ)|=(207999477/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564150767/1250000000 : ℝ)|^4277 ≤ (17566766218103/50000000000000 : ℝ)^3253
        have hw : |(564150767/1250000000 : ℝ)|=(564150767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s6_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2065774343/10000000000 : ℝ)*x 0 + (5244395197/10000000000 : ℝ)*x 1 + (84584513/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2065774343/10000000000 : ℝ)^4277 ≤ (2514839734467/20000000000000 : ℝ)^3253 := by
    have hnat : (2065774343 : ℕ)^4277*20000000000000^3253 ≤ 2514839734467^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065774343 10000000000 2514839734467 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244395197/10000000000 : ℝ)^4277 ≤ (2675095985107/6250000000000 : ℝ)^3253 := by
    have hnat : (5244395197 : ℕ)^4277*6250000000000^3253 ≤ 2675095985107^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244395197 10000000000 2675095985107 6250000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84584513/156250000 : ℝ)^4277 ≤ (2789016597279/6250000000000 : ℝ)^3253 := by
    have hnat : (84584513 : ℕ)^4277*6250000000000^3253 ≤ 2789016597279^3253*156250000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84584513 156250000 2789016597279 6250000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2065774343/10000000000 : ℝ), (5244395197/10000000000 : ℝ), (84584513/156250000 : ℝ)] ![(2514839734467/20000000000000 : ℝ), (2675095985107/6250000000000 : ℝ), (2789016597279/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2065774343/10000000000 : ℝ)|^4277 ≤ (2514839734467/20000000000000 : ℝ)^3253
        have hw : |(-2065774343/10000000000 : ℝ)|=(2065774343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244395197/10000000000 : ℝ)|^4277 ≤ (2675095985107/6250000000000 : ℝ)^3253
        have hw : |(5244395197/10000000000 : ℝ)|=(5244395197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84584513/156250000 : ℝ)|^4277 ≤ (2789016597279/6250000000000 : ℝ)^3253
        have hw : |(84584513/156250000 : ℝ)|=(84584513/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s6_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305700881/10000000000 : ℝ)*x 0 + (-991447947/5000000000 : ℝ)*x 1 + (2706704511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305700881/10000000000 : ℝ)^4277 ≤ (43460582280157/100000000000000 : ℝ)^3253 := by
    have hnat : (5305700881 : ℕ)^4277*100000000000000^3253 ≤ 43460582280157^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305700881 10000000000 43460582280157 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (991447947/5000000000 : ℝ)^4277 ≤ (11915150090299/100000000000000 : ℝ)^3253 := by
    have hnat : (991447947 : ℕ)^4277*100000000000000^3253 ≤ 11915150090299^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991447947 5000000000 11915150090299 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706704511/5000000000 : ℝ)^4277 ≤ (22312133807857/50000000000000 : ℝ)^3253 := by
    have hnat : (2706704511 : ℕ)^4277*50000000000000^3253 ≤ 22312133807857^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706704511 5000000000 22312133807857 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305700881/10000000000 : ℝ), (-991447947/5000000000 : ℝ), (2706704511/5000000000 : ℝ)] ![(43460582280157/100000000000000 : ℝ), (11915150090299/100000000000000 : ℝ), (22312133807857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305700881/10000000000 : ℝ)|^4277 ≤ (43460582280157/100000000000000 : ℝ)^3253
        have hw : |(5305700881/10000000000 : ℝ)|=(5305700881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-991447947/5000000000 : ℝ)|^4277 ≤ (11915150090299/100000000000000 : ℝ)^3253
        have hw : |(-991447947/5000000000 : ℝ)|=(991447947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706704511/5000000000 : ℝ)|^4277 ≤ (22312133807857/50000000000000 : ℝ)^3253
        have hw : |(2706704511/5000000000 : ℝ)|=(2706704511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s6_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305700997/10000000000 : ℝ)*x 0 + (676676099/1250000000 : ℝ)*x 1 + (-1982896051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305700997/10000000000 : ℝ)^4277 ≤ (21730291764727/50000000000000 : ℝ)^3253 := by
    have hnat : (5305700997 : ℕ)^4277*50000000000000^3253 ≤ 21730291764727^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305700997 10000000000 21730291764727 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676676099/1250000000 : ℝ)^4277 ≤ (22312132561469/50000000000000 : ℝ)^3253 := by
    have hnat : (676676099 : ℕ)^4277*50000000000000^3253 ≤ 22312132561469^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676676099 1250000000 22312132561469 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1982896051/10000000000 : ℝ)^4277 ≤ (5957575665339/50000000000000 : ℝ)^3253 := by
    have hnat : (1982896051 : ℕ)^4277*50000000000000^3253 ≤ 5957575665339^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982896051 10000000000 5957575665339 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305700997/10000000000 : ℝ), (676676099/1250000000 : ℝ), (-1982896051/10000000000 : ℝ)] ![(21730291764727/50000000000000 : ℝ), (22312132561469/50000000000000 : ℝ), (5957575665339/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305700997/10000000000 : ℝ)|^4277 ≤ (21730291764727/50000000000000 : ℝ)^3253
        have hw : |(5305700997/10000000000 : ℝ)|=(5305700997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676676099/1250000000 : ℝ)|^4277 ≤ (22312132561469/50000000000000 : ℝ)^3253
        have hw : |(676676099/1250000000 : ℝ)|=(676676099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1982896051/10000000000 : ℝ)|^4277 ≤ (5957575665339/50000000000000 : ℝ)^3253
        have hw : |(-1982896051/10000000000 : ℝ)|=(1982896051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s6_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4333222243/10000000000 : ℝ)*x 0 + (563992861/1250000000 : ℝ)*x 1 + (520157357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333222243/10000000000 : ℝ)^4277 ≤ (33303050222653/100000000000000 : ℝ)^3253 := by
    have hnat : (4333222243 : ℕ)^4277*100000000000000^3253 ≤ 33303050222653^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333222243 10000000000 33303050222653 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563992861/1250000000 : ℝ)^4277 ≤ (17560301771927/50000000000000 : ℝ)^3253 := by
    have hnat : (563992861 : ℕ)^4277*50000000000000^3253 ≤ 17560301771927^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563992861 1250000000 17560301771927 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (520157357/1250000000 : ℝ)^4277 ≤ (7894086557347/25000000000000 : ℝ)^3253 := by
    have hnat : (520157357 : ℕ)^4277*25000000000000^3253 ≤ 7894086557347^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520157357 1250000000 7894086557347 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333222243/10000000000 : ℝ), (563992861/1250000000 : ℝ), (520157357/1250000000 : ℝ)] ![(33303050222653/100000000000000 : ℝ), (17560301771927/50000000000000 : ℝ), (7894086557347/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333222243/10000000000 : ℝ)|^4277 ≤ (33303050222653/100000000000000 : ℝ)^3253
        have hw : |(4333222243/10000000000 : ℝ)|=(4333222243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563992861/1250000000 : ℝ)|^4277 ≤ (17560301771927/50000000000000 : ℝ)^3253
        have hw : |(563992861/1250000000 : ℝ)|=(563992861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(520157357/1250000000 : ℝ)|^4277 ≤ (7894086557347/25000000000000 : ℝ)^3253
        have hw : |(520157357/1250000000 : ℝ)|=(520157357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (693/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3673/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14701/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14701/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11079/100000 : ℝ) ^ (1069/256 : ℝ) ≤ (2558487930952149/25000000000000000000 : ℝ) := by
    have hpowers : (11079/100000 : ℝ)^1069 ≤ (2558487930952149/25000000000000000000 : ℝ)^256 := by
      have hnat : (11079 : ℕ)^1069*25000000000000000000^256 ≤ 2558487930952149^256*100000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11079 100000 2558487930952149 25000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11079/100000 : ℝ)) (X := (2558487930952149/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14701/100000 : ℝ) ^ (1069/256 : ℝ) ≤ (4168048047425643/12500000000000000000 : ℝ) := by
    have hpowers : (14701/100000 : ℝ)^1069 ≤ (4168048047425643/12500000000000000000 : ℝ)^256 := by
      have hnat : (14701 : ℕ)^1069*12500000000000000000^256 ≤ 4168048047425643^256*100000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14701 100000 4168048047425643 12500000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14701/100000 : ℝ)) (X := (4168048047425643/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502558487930952149/12500000000000000000 : ℝ) ≤ (10000490119318113/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (12502558487930952149/12500000000000000000 : ℝ)^256 ≤ (10000490119318113/10000000000000000 : ℝ)^1069 := by
      have hnat : (12502558487930952149 : ℕ)^256*10000000000000000^1069 ≤ 10000490119318113^1069*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502558487930952149 12500000000000000000 10000490119318113 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000490119318113/10000000000000000 : ℝ)) (X := (12502558487930952149/12500000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (5002178916805160687/5000000000000000000 : ℝ) ≤ (10001043424305429/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (5002178916805160687/5000000000000000000 : ℝ)^256 ≤ (10001043424305429/10000000000000000 : ℝ)^1069 := by
      have hnat : (5002178916805160687 : ℕ)^256*10000000000000000^1069 ≤ 10001043424305429^1069*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002178916805160687 5000000000000000000 10001043424305429 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001043424305429/10000000000000000 : ℝ)) (X := (5002178916805160687/5000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254168048047425643/6250000000000000000 : ℝ) ≤ (2000319345858549/2000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (6254168048047425643/6250000000000000000 : ℝ)^256 ≤ (2000319345858549/2000000000000000 : ℝ)^1069 := by
      have hnat : (6254168048047425643 : ℕ)^256*2000000000000000^1069 ≤ 2000319345858549^1069*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254168048047425643 6250000000000000000 2000319345858549 2000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000319345858549/2000000000000000 : ℝ)) (X := (6254168048047425643/6250000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2558487930952149/25000000000000000000 : ℝ) ≤ ((18104757540130628679/18110000000000000000 : ℝ)+2*(138326246829/90550000000000 : ℝ)*(11079/100000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (18104757540130628679/18110000000000000000 : ℝ)+2*(138326246829/90550000000000 : ℝ)*(11079/100000 : ℝ)=(10000490119318113/10000000000000000 : ℝ) by norm_num, show 1+2*(2558487930952149/25000000000000000000 : ℝ)=(12502558487930952149/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4168048047425643/12500000000000000000 : ℝ)+(2558487930952149/25000000000000000000 : ℝ) ≤ ((18104757540130628679/18110000000000000000 : ℝ)+(138326246829/90550000000000 : ℝ)*((14701/100000 : ℝ)+(11079/100000 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (18104757540130628679/18110000000000000000 : ℝ)+(138326246829/90550000000000 : ℝ)*((14701/100000 : ℝ)+(11079/100000 : ℝ))=(10001043424305429/10000000000000000 : ℝ) by norm_num, show 1+(4168048047425643/12500000000000000000 : ℝ)+(2558487930952149/25000000000000000000 : ℝ)=(5002178916805160687/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4168048047425643/12500000000000000000 : ℝ) ≤ ((18104757540130628679/18110000000000000000 : ℝ)+2*(138326246829/90550000000000 : ℝ)*(14701/100000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (18104757540130628679/18110000000000000000 : ℝ)+2*(138326246829/90550000000000 : ℝ)*(14701/100000 : ℝ)=(2000319345858549/2000000000000000 : ℝ) by norm_num, show 1+2*(4168048047425643/12500000000000000000 : ℝ)=(6254168048047425643/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18104757540130628679/18110000000000000000 : ℝ)*(X 1 0+X 2 0)+(138326246829/90550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (18104757540130628679/18110000000000000000 : ℝ)) (alpha := (138326246829/90550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18104757540130628679/18110000000000000000 : ℝ)*(X 0 1+X 2 1)+(138326246829/90550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (18104757540130628679/18110000000000000000 : ℝ)) (alpha := (138326246829/90550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18104757540130628679/18110000000000000000 : ℝ)*(X 0 2+X 1 2)+(138326246829/90550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14701/100000 : ℝ)) (c := (18104757540130628679/18110000000000000000 : ℝ)) (alpha := (138326246829/90550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-413152239/2000000000 : ℝ)*X 0 0+(2707010143/5000000000 : ℝ)*X 0 1+(5243787391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349421211/10000000000 : ℝ)*X 1 0+(-538129323/2500000000 : ℝ)*X 1 1+(327736641/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337354949/2500000000 : ℝ)*X 2 0+(2621893649/5000000000 : ℝ)*X 2 1+(-2152517797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4333195941/10000000000 : ℝ)*X 0 0+(207999477/500000000 : ℝ)*X 0 1+(564150767/1250000000 : ℝ)*X 0 2+(4333195941/10000000000 : ℝ)*X 1 0+(207999477/500000000 : ℝ)*X 1 1+(564150767/1250000000 : ℝ)*X 1 2+(4333195941/10000000000 : ℝ)*X 2 0+(207999477/500000000 : ℝ)*X 2 1+(564150767/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2065774343/10000000000 : ℝ)*X 0 0+(5244395197/10000000000 : ℝ)*X 0 1+(84584513/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305700881/10000000000 : ℝ)*X 1 0+(-991447947/5000000000 : ℝ)*X 1 1+(2706704511/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305700997/10000000000 : ℝ)*X 2 0+(676676099/1250000000 : ℝ)*X 2 1+(-1982896051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4333222243/10000000000 : ℝ)*X 0 0+(563992861/1250000000 : ℝ)*X 0 1+(520157357/1250000000 : ℝ)*X 0 2+(4333222243/10000000000 : ℝ)*X 1 0+(563992861/1250000000 : ℝ)*X 1 1+(520157357/1250000000 : ℝ)*X 1 2+(4333222243/10000000000 : ℝ)*X 2 0+(563992861/1250000000 : ℝ)*X 2 1+(520157357/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16230875641290389604511821/1811000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1120469791/50000000000000 : ℝ)*(base19) + (610747907/50000000000000 : ℝ)*(base23) + (335829627/100000000000000 : ℝ)*(lower4) + (8652363/20000000000000 : ℝ)*(lower5) + (8705550832167/200000000000 : ℝ)*(major0) + (8705550832167/200000000000 : ℝ)*(major1) + (8705550832167/200000000000 : ℝ)*(major2) + (5874350075783253/100000000000000 : ℝ)*(sp0) + (5874371363553233/100000000000000 : ℝ)*(sp1) + (2937180478927643/50000000000000 : ℝ)*(sp2) + (176947147422813/6250000000000 : ℝ)*(sp3) + (11764354781/50000000000000 : ℝ)*(sp4) + (5712570857/50000000000000 : ℝ)*(sp6) + (22570163061/100000000000000 : ℝ)*(sp7) + (707794232232017/25000000000000 : ℝ)*(f.failure) + (1174874720898563/20000000000000 : ℝ)*(f.sum) + (70485444857/36220000000000000000000000 : ℝ)*base65 + (33806511653802607/3622000000000000000000000000000 : ℝ)*base68 + (3374400415075393/3622000000000000000000000000000 : ℝ)*base69 + (30616626953190607/3622000000000000000000000000000 : ℝ)*base72 + (2713000977743/452750000000000000000000000 : ℝ)*base74 + (84848569782373393/3622000000000000000000000000000 : ℝ)*base75 + (25416055865487393/3622000000000000000000000000000 : ℝ)*base77 + (79125048249629393/3622000000000000000000000000000 : ℝ)*base79 + (2479490409557/452750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1509277/125000000000000000000 : ℝ)*base90 + (1509277/125000000000000000000 : ℝ)*base92 + (1509277/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1265570776486761193431722019/113187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1990067489/100000000000000 : ℝ)*(base19) + (2224808217/100000000000000 : ℝ)*(base23) + (256658533/100000000000000 : ℝ)*(upper3) + (73993397/100000000000000 : ℝ)*(lower4) + (161910123/50000000000000 : ℝ)*(upper5) + (1096031607281013/25000000000000 : ℝ)*(major0) + (1096031607281013/25000000000000 : ℝ)*(major1) + (1096031607281013/25000000000000 : ℝ)*(major2) + (22653828823/50000000000000 : ℝ)*(sp1) + (4117360973/10000000000000 : ℝ)*(sp2) + (5916683908450373/100000000000000 : ℝ)*(sp4) + (5916636610725237/100000000000000 : ℝ)*(sp5) + (236665620401297/4000000000000 : ℝ)*(sp6) + (1425784288545719/50000000000000 : ℝ)*(sp7) + (1425784288545719/50000000000000 : ℝ)*(f.failure) + (5916683908450373/100000000000000 : ℝ)*(f.sum) + (41843539345009/9055000000000000000000000000 : ℝ)*base66 + (470120359396621827/452750000000000000000000000000000 : ℝ)*base67 + (1963145957789371827/452750000000000000000000000000000 : ℝ)*base69 + (7545577125561378173/452750000000000000000000000000000 : ℝ)*base72 + (7986200388673/4527500000000000000000000000 : ℝ)*base73 + (7869221148540871827/452750000000000000000000000000000 : ℝ)*base75 + (591934189358121827/452750000000000000000000000000000 : ℝ)*base77 + (2820240725784371827/452750000000000000000000000000000 : ℝ)*base79 + (1863307170851/9055000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3465461/250000000000000000000 : ℝ)*base89 + (3465461/250000000000000000000 : ℝ)*base91 + (3465461/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1317_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1317_s7_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-516442409/2500000000 : ℝ)*x 0 + (2706971539/5000000000 : ℝ)*x 1 + (5243859083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516442409/2500000000 : ℝ)^4277 ≤ (3143540250561/25000000000000 : ℝ)^3253 := by
    have hnat : (516442409 : ℕ)^4277*25000000000000^3253 ≤ 3143540250561^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516442409 2500000000 3143540250561 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706971539/5000000000 : ℝ)^4277 ≤ (5578756986059/12500000000000 : ℝ)^3253 := by
    have hnat : (2706971539 : ℕ)^4277*12500000000000^3253 ≤ 5578756986059^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706971539 5000000000 5578756986059 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243859083/10000000000 : ℝ)^4277 ≤ (42795783094001/100000000000000 : ℝ)^3253 := by
    have hnat : (5243859083 : ℕ)^4277*100000000000000^3253 ≤ 42795783094001^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243859083 10000000000 42795783094001 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-516442409/2500000000 : ℝ), (2706971539/5000000000 : ℝ), (5243859083/10000000000 : ℝ)] ![(3143540250561/25000000000000 : ℝ), (5578756986059/12500000000000 : ℝ), (42795783094001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-516442409/2500000000 : ℝ)|^4277 ≤ (3143540250561/25000000000000 : ℝ)^3253
        have hw : |(-516442409/2500000000 : ℝ)|=(516442409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706971539/5000000000 : ℝ)|^4277 ≤ (5578756986059/12500000000000 : ℝ)^3253
        have hw : |(2706971539/5000000000 : ℝ)|=(2706971539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243859083/10000000000 : ℝ)|^4277 ≤ (42795783094001/100000000000000 : ℝ)^3253
        have hw : |(5243859083/10000000000 : ℝ)|=(5243859083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s7_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26747001/50000000 : ℝ)*x 0 + (-269056031/1250000000 : ℝ)*x 1 + (2621929783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26747001/50000000 : ℝ)^4277 ≤ (2745739032241/6250000000000 : ℝ)^3253 := by
    have hnat : (26747001 : ℕ)^4277*6250000000000^3253 ≤ 2745739032241^3253*50000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26747001 50000000 2745739032241 6250000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269056031/1250000000 : ℝ)^4277 ≤ (6636193597681/50000000000000 : ℝ)^3253 := by
    have hnat : (269056031 : ℕ)^4277*50000000000000^3253 ≤ 6636193597681^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269056031 1250000000 6636193597681 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621929783/5000000000 : ℝ)^4277 ≤ (2674736767291/6250000000000 : ℝ)^3253 := by
    have hnat : (2621929783 : ℕ)^4277*6250000000000^3253 ≤ 2674736767291^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621929783 5000000000 2674736767291 6250000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26747001/50000000 : ℝ), (-269056031/1250000000 : ℝ), (2621929783/5000000000 : ℝ)] ![(2745739032241/6250000000000 : ℝ), (6636193597681/50000000000000 : ℝ), (2674736767291/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26747001/50000000 : ℝ)|^4277 ≤ (2745739032241/6250000000000 : ℝ)^3253
        have hw : |(26747001/50000000 : ℝ)|=(26747001/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-269056031/1250000000 : ℝ)|^4277 ≤ (6636193597681/50000000000000 : ℝ)^3253
        have hw : |(-269056031/1250000000 : ℝ)|=(269056031/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621929783/5000000000 : ℝ)|^4277 ≤ (2674736767291/6250000000000 : ℝ)^3253
        have hw : |(2621929783/5000000000 : ℝ)|=(2621929783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s7_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349400477/10000000000 : ℝ)*x 0 + (163870629/312500000 : ℝ)*x 1 + (-67263973/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349400477/10000000000 : ℝ)^4277 ≤ (21965913753403/50000000000000 : ℝ)^3253 := by
    have hnat : (5349400477 : ℕ)^4277*50000000000000^3253 ≤ 21965913753403^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349400477 10000000000 21965913753403 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163870629/312500000 : ℝ)^4277 ≤ (42795794306991/100000000000000 : ℝ)^3253 := by
    have hnat : (163870629 : ℕ)^4277*100000000000000^3253 ≤ 42795794306991^3253*312500000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163870629 312500000 42795794306991 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67263973/312500000 : ℝ)^4277 ≤ (13272378180143/100000000000000 : ℝ)^3253 := by
    have hnat : (67263973 : ℕ)^4277*100000000000000^3253 ≤ 13272378180143^3253*312500000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67263973 312500000 13272378180143 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349400477/10000000000 : ℝ), (163870629/312500000 : ℝ), (-67263973/312500000 : ℝ)] ![(21965913753403/50000000000000 : ℝ), (42795794306991/100000000000000 : ℝ), (13272378180143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349400477/10000000000 : ℝ)|^4277 ≤ (21965913753403/50000000000000 : ℝ)^3253
        have hw : |(5349400477/10000000000 : ℝ)|=(5349400477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163870629/312500000 : ℝ)|^4277 ≤ (42795794306991/100000000000000 : ℝ)^3253
        have hw : |(163870629/312500000 : ℝ)|=(163870629/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67263973/312500000 : ℝ)|^4277 ≤ (13272378180143/100000000000000 : ℝ)^3253
        have hw : |(-67263973/312500000 : ℝ)|=(67263973/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s7_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1083300701/2500000000 : ℝ)*x 0 + (416014399/1000000000 : ℝ)*x 1 + (4513048821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083300701/2500000000 : ℝ)^4277 ≤ (33302853795353/100000000000000 : ℝ)^3253 := by
    have hnat : (1083300701 : ℕ)^4277*100000000000000^3253 ≤ 33302853795353^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083300701 2500000000 33302853795353 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416014399/1000000000 : ℝ)^4277 ≤ (31565223876093/100000000000000 : ℝ)^3253 := by
    have hnat : (416014399 : ℕ)^4277*100000000000000^3253 ≤ 31565223876093^3253*1000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416014399 1000000000 31565223876093 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513048821/10000000000 : ℝ)^4277 ≤ (548936286113/1562500000000 : ℝ)^3253 := by
    have hnat : (4513048821 : ℕ)^4277*1562500000000^3253 ≤ 548936286113^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513048821 10000000000 548936286113 1562500000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083300701/2500000000 : ℝ), (416014399/1000000000 : ℝ), (4513048821/10000000000 : ℝ)] ![(33302853795353/100000000000000 : ℝ), (31565223876093/100000000000000 : ℝ), (548936286113/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083300701/2500000000 : ℝ)|^4277 ≤ (33302853795353/100000000000000 : ℝ)^3253
        have hw : |(1083300701/2500000000 : ℝ)|=(1083300701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416014399/1000000000 : ℝ)|^4277 ≤ (31565223876093/100000000000000 : ℝ)^3253
        have hw : |(416014399/1000000000 : ℝ)|=(416014399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513048821/10000000000 : ℝ)|^4277 ≤ (548936286113/1562500000000 : ℝ)^3253
        have hw : |(4513048821/10000000000 : ℝ)|=(4513048821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s7_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1032890863/5000000000 : ℝ)*x 0 + (2622233401/5000000000 : ℝ)*x 1 + (2706666243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1032890863/5000000000 : ℝ)^4277 ≤ (12574257758491/100000000000000 : ℝ)^3253 := by
    have hnat : (1032890863 : ℕ)^4277*100000000000000^3253 ≤ 12574257758491^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032890863 5000000000 12574257758491 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622233401/5000000000 : ℝ)^4277 ≤ (21401152059673/50000000000000 : ℝ)^3253 := by
    have hnat : (2622233401 : ℕ)^4277*50000000000000^3253 ≤ 21401152059673^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622233401 5000000000 21401152059673 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706666243/5000000000 : ℝ)^4277 ≤ (1115585952709/2500000000000 : ℝ)^3253 := by
    have hnat : (2706666243 : ℕ)^4277*2500000000000^3253 ≤ 1115585952709^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706666243 5000000000 1115585952709 2500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1032890863/5000000000 : ℝ), (2622233401/5000000000 : ℝ), (2706666243/5000000000 : ℝ)] ![(12574257758491/100000000000000 : ℝ), (21401152059673/50000000000000 : ℝ), (1115585952709/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1032890863/5000000000 : ℝ)|^4277 ≤ (12574257758491/100000000000000 : ℝ)^3253
        have hw : |(-1032890863/5000000000 : ℝ)|=(1032890863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622233401/5000000000 : ℝ)|^4277 ≤ (21401152059673/50000000000000 : ℝ)^3253
        have hw : |(2622233401/5000000000 : ℝ)|=(2622233401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706666243/5000000000 : ℝ)|^4277 ≤ (1115585952709/2500000000000 : ℝ)^3253
        have hw : |(2706666243/5000000000 : ℝ)|=(2706666243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s7_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652860101/5000000000 : ℝ)*x 0 + (-1982974487/10000000000 : ℝ)*x 1 + (1353333133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652860101/5000000000 : ℝ)^4277 ≤ (21730395181869/50000000000000 : ℝ)^3253 := by
    have hnat : (2652860101 : ℕ)^4277*50000000000000^3253 ≤ 21730395181869^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652860101 5000000000 21730395181869 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1982974487/10000000000 : ℝ)^4277 ≤ (5957885509237/50000000000000 : ℝ)^3253 := by
    have hnat : (1982974487 : ℕ)^4277*50000000000000^3253 ≤ 5957885509237^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1982974487 10000000000 5957885509237 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353333133/2500000000 : ℝ)^4277 ≤ (44623438606913/100000000000000 : ℝ)^3253 := by
    have hnat : (1353333133 : ℕ)^4277*100000000000000^3253 ≤ 44623438606913^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353333133 2500000000 44623438606913 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652860101/5000000000 : ℝ), (-1982974487/10000000000 : ℝ), (1353333133/2500000000 : ℝ)] ![(21730395181869/50000000000000 : ℝ), (5957885509237/50000000000000 : ℝ), (44623438606913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652860101/5000000000 : ℝ)|^4277 ≤ (21730395181869/50000000000000 : ℝ)^3253
        have hw : |(2652860101/5000000000 : ℝ)|=(2652860101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1982974487/10000000000 : ℝ)|^4277 ≤ (5957885509237/50000000000000 : ℝ)^3253
        have hw : |(-1982974487/10000000000 : ℝ)|=(1982974487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353333133/2500000000 : ℝ)|^4277 ≤ (44623438606913/100000000000000 : ℝ)^3253
        have hw : |(1353333133/2500000000 : ℝ)|=(1353333133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s7_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305720211/10000000000 : ℝ)*x 0 + (270666623/500000000 : ℝ)*x 1 + (-991487287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305720211/10000000000 : ℝ)^4277 ≤ (43460790460667/100000000000000 : ℝ)^3253 := by
    have hnat : (5305720211 : ℕ)^4277*100000000000000^3253 ≤ 43460790460667^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305720211 10000000000 43460790460667 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270666623/500000000 : ℝ)^4277 ≤ (4462343782657/10000000000000 : ℝ)^3253 := by
    have hnat : (270666623 : ℕ)^4277*10000000000000^3253 ≤ 4462343782657^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270666623 500000000 4462343782657 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (991487287/5000000000 : ℝ)^4277 ≤ (11915771705827/100000000000000 : ℝ)^3253 := by
    have hnat : (991487287 : ℕ)^4277*100000000000000^3253 ≤ 11915771705827^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      991487287 5000000000 11915771705827 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305720211/10000000000 : ℝ), (270666623/500000000 : ℝ), (-991487287/5000000000 : ℝ)] ![(43460790460667/100000000000000 : ℝ), (4462343782657/10000000000000 : ℝ), (11915771705827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305720211/10000000000 : ℝ)|^4277 ≤ (43460790460667/100000000000000 : ℝ)^3253
        have hw : |(5305720211/10000000000 : ℝ)|=(5305720211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270666623/500000000 : ℝ)|^4277 ≤ (4462343782657/10000000000000 : ℝ)^3253
        have hw : |(270666623/500000000 : ℝ)|=(270666623/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-991487287/5000000000 : ℝ)|^4277 ≤ (11915771705827/100000000000000 : ℝ)^3253
        have hw : |(-991487287/5000000000 : ℝ)|=(991487287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_s7_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173329091/400000000 : ℝ)*x 0 + (4511789177/10000000000 : ℝ)*x 1 + (4161411433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173329091/400000000 : ℝ)^4277 ≤ (8325775267519/25000000000000 : ℝ)^3253 := by
    have hnat : (173329091 : ℕ)^4277*25000000000000^3253 ≤ 8325775267519^3253*400000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173329091 400000000 8325775267519 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511789177/10000000000 : ℝ)^4277 ≤ (3511903044439/10000000000000 : ℝ)^3253 := by
    have hnat : (4511789177 : ℕ)^4277*10000000000000^3253 ≤ 3511903044439^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511789177 10000000000 3511903044439 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4161411433/10000000000 : ℝ)^4277 ≤ (15788934236057/50000000000000 : ℝ)^3253 := by
    have hnat : (4161411433 : ℕ)^4277*50000000000000^3253 ≤ 15788934236057^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4161411433 10000000000 15788934236057 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173329091/400000000 : ℝ), (4511789177/10000000000 : ℝ), (4161411433/10000000000 : ℝ)] ![(8325775267519/25000000000000 : ℝ), (3511903044439/10000000000000 : ℝ), (15788934236057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173329091/400000000 : ℝ)|^4277 ≤ (8325775267519/25000000000000 : ℝ)^3253
        have hw : |(173329091/400000000 : ℝ)|=(173329091/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511789177/10000000000 : ℝ)|^4277 ≤ (3511903044439/10000000000000 : ℝ)^3253
        have hw : |(4511789177/10000000000 : ℝ)|=(4511789177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4161411433/10000000000 : ℝ)|^4277 ≤ (15788934236057/50000000000000 : ℝ)^3253
        have hw : |(4161411433/10000000000 : ℝ)|=(4161411433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (1109/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1469/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3673/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3673/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (693/6250 : ℝ) ^ (1069/256 : ℝ) ≤ (1283589000059367/12500000000000000000 : ℝ) := by
    have hpowers : (693/6250 : ℝ)^1069 ≤ (1283589000059367/12500000000000000000 : ℝ)^256 := by
      have hnat : (693 : ℕ)^1069*12500000000000000000^256 ≤ 1283589000059367^256*6250^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        693 6250 1283589000059367 12500000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (693/6250 : ℝ)) (X := (1283589000059367/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3673/25000 : ℝ) ^ (1069/256 : ℝ) ≤ (2078701545501559/6250000000000000000 : ℝ) := by
    have hpowers : (3673/25000 : ℝ)^1069 ≤ (2078701545501559/6250000000000000000 : ℝ)^256 := by
      have hnat : (3673 : ℕ)^1069*6250000000000000000^256 ≤ 2078701545501559^256*25000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3673 25000 2078701545501559 6250000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3673/25000 : ℝ)) (X := (2078701545501559/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251283589000059367/6250000000000000000 : ℝ) ≤ (10000491783909981/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (6251283589000059367/6250000000000000000 : ℝ)^256 ≤ (10000491783909981/10000000000000000 : ℝ)^1069 := by
      have hnat : (6251283589000059367 : ℕ)^256*10000000000000000^1069 ≤ 10000491783909981^1069*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251283589000059367 6250000000000000000 10000491783909981 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000491783909981/10000000000000000 : ℝ)) (X := (6251283589000059367/6250000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501088198418212497/2500000000000000000 : ℝ) ≤ (10001042217760253/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (2501088198418212497/2500000000000000000 : ℝ)^256 ≤ (10001042217760253/10000000000000000 : ℝ)^1069 := by
      have hnat : (2501088198418212497 : ℕ)^256*10000000000000000^1069 ≤ 10001042217760253^1069*2500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501088198418212497 2500000000000000000 10001042217760253 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001042217760253/10000000000000000 : ℝ)) (X := (2501088198418212497/2500000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127078701545501559/3125000000000000000 : ℝ) ≤ (400063706064421/400000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (3127078701545501559/3125000000000000000 : ℝ)^256 ≤ (400063706064421/400000000000000 : ℝ)^1069 := by
      have hnat : (3127078701545501559 : ℕ)^256*400000000000000^1069 ≤ 400063706064421^1069*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127078701545501559 3125000000000000000 400063706064421 400000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400063706064421/400000000000000 : ℝ)) (X := (3127078701545501559/3125000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1283589000059367/12500000000000000000 : ℝ) ≤ ((9007391492036984913/9010000000000000000 : ℝ)+2*(17201057821/11262500000000 : ℝ)*(693/6250 : ℝ))^(1069/256 : ℝ) := by
    rw [show (9007391492036984913/9010000000000000000 : ℝ)+2*(17201057821/11262500000000 : ℝ)*(693/6250 : ℝ)=(10000491783909981/10000000000000000 : ℝ) by norm_num, show 1+2*(1283589000059367/12500000000000000000 : ℝ)=(6251283589000059367/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2078701545501559/6250000000000000000 : ℝ)+(1283589000059367/12500000000000000000 : ℝ) ≤ ((9007391492036984913/9010000000000000000 : ℝ)+(17201057821/11262500000000 : ℝ)*((3673/25000 : ℝ)+(693/6250 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (9007391492036984913/9010000000000000000 : ℝ)+(17201057821/11262500000000 : ℝ)*((3673/25000 : ℝ)+(693/6250 : ℝ))=(10001042217760253/10000000000000000 : ℝ) by norm_num, show 1+(2078701545501559/6250000000000000000 : ℝ)+(1283589000059367/12500000000000000000 : ℝ)=(2501088198418212497/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2078701545501559/6250000000000000000 : ℝ) ≤ ((9007391492036984913/9010000000000000000 : ℝ)+2*(17201057821/11262500000000 : ℝ)*(3673/25000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (9007391492036984913/9010000000000000000 : ℝ)+2*(17201057821/11262500000000 : ℝ)*(3673/25000 : ℝ)=(400063706064421/400000000000000 : ℝ) by norm_num, show 1+2*(2078701545501559/6250000000000000000 : ℝ)=(3127078701545501559/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9007391492036984913/9010000000000000000 : ℝ)*(X 1 0+X 2 0)+(17201057821/11262500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (9007391492036984913/9010000000000000000 : ℝ)) (alpha := (17201057821/11262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9007391492036984913/9010000000000000000 : ℝ)*(X 0 1+X 2 1)+(17201057821/11262500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (9007391492036984913/9010000000000000000 : ℝ)) (alpha := (17201057821/11262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9007391492036984913/9010000000000000000 : ℝ)*(X 0 2+X 1 2)+(17201057821/11262500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (3673/25000 : ℝ)) (c := (9007391492036984913/9010000000000000000 : ℝ)) (alpha := (17201057821/11262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-516442409/2500000000 : ℝ)*X 0 0+(2706971539/5000000000 : ℝ)*X 0 1+(5243859083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((26747001/50000000 : ℝ)*X 1 0+(-269056031/1250000000 : ℝ)*X 1 1+(2621929783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349400477/10000000000 : ℝ)*X 2 0+(163870629/312500000 : ℝ)*X 2 1+(-67263973/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083300701/2500000000 : ℝ)*X 0 0+(416014399/1000000000 : ℝ)*X 0 1+(4513048821/10000000000 : ℝ)*X 0 2+(1083300701/2500000000 : ℝ)*X 1 0+(416014399/1000000000 : ℝ)*X 1 1+(4513048821/10000000000 : ℝ)*X 1 2+(1083300701/2500000000 : ℝ)*X 2 0+(416014399/1000000000 : ℝ)*X 2 1+(4513048821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1032890863/5000000000 : ℝ)*X 0 0+(2622233401/5000000000 : ℝ)*X 0 1+(2706666243/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652860101/5000000000 : ℝ)*X 1 0+(-1982974487/10000000000 : ℝ)*X 1 1+(1353333133/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305720211/10000000000 : ℝ)*X 2 0+(270666623/500000000 : ℝ)*X 2 1+(-991487287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173329091/400000000 : ℝ)*X 0 0+(4511789177/10000000000 : ℝ)*X 0 1+(4161411433/10000000000 : ℝ)*X 0 2+(173329091/400000000 : ℝ)*X 1 0+(4511789177/10000000000 : ℝ)*X 1 1+(4161411433/10000000000 : ℝ)*X 1 2+(173329091/400000000 : ℝ)*X 2 0+(4511789177/10000000000 : ℝ)*X 2 1+(4161411433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30008153438496138996485301/6625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (904308079/100000000000000 : ℝ)*(base19) + (35052293/4000000000000 : ℝ)*(base23) + (44543857/20000000000000 : ℝ)*(lower2) + (375896007/50000000000000 : ℝ)*(upper5) + (1089146541452701/25000000000000 : ℝ)*(major0) + (1089146541452701/25000000000000 : ℝ)*(major1) + (1089146541452701/25000000000000 : ℝ)*(major2) + (734933026888153/12500000000000 : ℝ)*(sp0) + (293975272306503/5000000000000 : ℝ)*(sp1) + (587951574839291/10000000000000 : ℝ)*(sp2) + (2833644246551803/100000000000000 : ℝ)*(sp3) + (13102398753/25000000000000 : ℝ)*(sp4) + (642141381/6250000000000 : ℝ)*(sp5) + (11309385139/100000000000000 : ℝ)*(sp7) + (1416827777968471/50000000000000 : ℝ)*(f.failure) + (1469879156175059/25000000000000 : ℝ)*(f.sum) + (2968716953133/4505000000000000000000000000 : ℝ)*base66 + (3534642451285349987/225250000000000000000000000000000 : ℝ)*base68 + (3351016895461599987/225250000000000000000000000000000 : ℝ)*base70 + (1936090855175349987/225250000000000000000000000000000 : ℝ)*base72 + (22078396624533/4505000000000000000000000000 : ℝ)*base74 + (2933437545163599987/225250000000000000000000000000000 : ℝ)*base76 + (1746282293394849987/225250000000000000000000000000000 : ℝ)*base78 + (2095669178031349987/225250000000000000000000000000000 : ℝ)*base80 + (776092783111/2252500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1672149/250000000000000000000 : ℝ)*base89 + (1672149/250000000000000000000 : ℝ)*base91 + (1672149/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1730809280270273076906309183/225250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (641848109/50000000000000 : ℝ)*(base19) + (1449934963/100000000000000 : ℝ)*(base23) + (417861417/100000000000000 : ℝ)*(lower1) + (99083899/50000000000000 : ℝ)*(upper3) + (8813091/12500000000000 : ℝ)*(lower4) + (5884939/6250000000000 : ℝ)*(upper5) + (2193972045929403/50000000000000 : ℝ)*(major0) + (2193972045929403/50000000000000 : ℝ)*(major1) + (2193972045929403/50000000000000 : ℝ)*(major2) + (2831314841/100000000000000 : ℝ)*(sp2) + (5921836227056319/100000000000000 : ℝ)*(sp4) + (5921834943360101/100000000000000 : ℝ)*(sp5) + (1184366389161303/20000000000000 : ℝ)*(sp6) + (114162068021187/4000000000000 : ℝ)*(sp7) + (114162068021187/4000000000000 : ℝ)*(f.failure) + (5921836227056319/100000000000000 : ℝ)*(f.sum) + (13208842760847/4505000000000000000000000000 : ℝ)*base66 + (15364310449842003061/450500000000000000000000000000000 : ℝ)*base68 + (340182300040003061/450500000000000000000000000000000 : ℝ)*base70 + (52538474830500996939/450500000000000000000000000000000 : ℝ)*base71 + (1032274059773/281562500000000000000000000 : ℝ)*base73 + (407725772510996939/450500000000000000000000000000000 : ℝ)*base75 + (2678444244790996939/450500000000000000000000000000000 : ℝ)*base77 + (906076073302996939/450500000000000000000000000000000 : ℝ)*base79 + (1145797976863/4505000000000000000000000000 : ℝ)*base81 + (91047/20000000000000000000 : ℝ)*base90 + (91047/20000000000000000000 : ℝ)*base92 + (91047/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1317_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3673/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1317_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1317_box_0 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-379298897/2000000000 : ℝ)*x 0 + (5390982939/10000000000 : ℝ)*x 1 + (21563931/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (379298897/2000000000 : ℝ)^4277 ≤ (11237264362491/100000000000000 : ℝ)^3253 := by
    have hnat : (379298897 : ℕ)^4277*100000000000000^3253 ≤ 11237264362491^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379298897 2000000000 11237264362491 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390982939/10000000000 : ℝ)^4277 ≤ (1775254753359/4000000000000 : ℝ)^3253 := by
    have hnat : (5390982939 : ℕ)^4277*4000000000000^3253 ≤ 1775254753359^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390982939 10000000000 1775254753359 4000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21563931/40000000 : ℝ)^4277 ≤ (22190683394119/50000000000000 : ℝ)^3253 := by
    have hnat : (21563931 : ℕ)^4277*50000000000000^3253 ≤ 22190683394119^3253*40000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21563931 40000000 22190683394119 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-379298897/2000000000 : ℝ), (5390982939/10000000000 : ℝ), (21563931/40000000 : ℝ)] ![(11237264362491/100000000000000 : ℝ), (1775254753359/4000000000000 : ℝ), (22190683394119/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-379298897/2000000000 : ℝ)|^4277 ≤ (11237264362491/100000000000000 : ℝ)^3253
        have hw : |(-379298897/2000000000 : ℝ)|=(379298897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390982939/10000000000 : ℝ)|^4277 ≤ (1775254753359/4000000000000 : ℝ)^3253
        have hw : |(5390982939/10000000000 : ℝ)|=(5390982939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21563931/40000000 : ℝ)|^4277 ≤ (22190683394119/50000000000000 : ℝ)^3253
        have hw : |(21563931/40000000 : ℝ)|=(21563931/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_1 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330299569/625000000 : ℝ)*x 0 + (-2041849597/10000000000 : ℝ)*x 1 + (1078196641/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330299569/625000000 : ℝ)^4277 ≤ (21617774659019/50000000000000 : ℝ)^3253 := by
    have hnat : (330299569 : ℕ)^4277*50000000000000^3253 ≤ 21617774659019^3253*625000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330299569 625000000 21617774659019 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2041849597/10000000000 : ℝ)^4277 ≤ (6191539481081/50000000000000 : ℝ)^3253 := by
    have hnat : (2041849597 : ℕ)^4277*50000000000000^3253 ≤ 6191539481081^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041849597 10000000000 6191539481081 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078196641/2000000000 : ℝ)^4277 ≤ (1109534292829/2500000000000 : ℝ)^3253 := by
    have hnat : (1078196641 : ℕ)^4277*2500000000000^3253 ≤ 1109534292829^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078196641 2000000000 1109534292829 2500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330299569/625000000 : ℝ), (-2041849597/10000000000 : ℝ), (1078196641/2000000000 : ℝ)] ![(21617774659019/50000000000000 : ℝ), (6191539481081/50000000000000 : ℝ), (1109534292829/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330299569/625000000 : ℝ)|^4277 ≤ (21617774659019/50000000000000 : ℝ)^3253
        have hw : |(330299569/625000000 : ℝ)|=(330299569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2041849597/10000000000 : ℝ)|^4277 ≤ (6191539481081/50000000000000 : ℝ)^3253
        have hw : |(-2041849597/10000000000 : ℝ)|=(2041849597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078196641/2000000000 : ℝ)|^4277 ≤ (1109534292829/2500000000000 : ℝ)^3253
        have hw : |(1078196641/2000000000 : ℝ)|=(1078196641/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_2 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66059919/125000000 : ℝ)*x 0 + (5390982763/10000000000 : ℝ)*x 1 + (-1020924817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66059919/125000000 : ℝ)^4277 ≤ (43235553792713/100000000000000 : ℝ)^3253 := by
    have hnat : (66059919 : ℕ)^4277*100000000000000^3253 ≤ 43235553792713^3253*125000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66059919 125000000 43235553792713 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390982763/10000000000 : ℝ)^4277 ≤ (887627338579/2000000000000 : ℝ)^3253 := by
    have hnat : (5390982763 : ℕ)^4277*2000000000000^3253 ≤ 887627338579^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390982763 10000000000 887627338579 2000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1020924817/5000000000 : ℝ)^4277 ≤ (12383079257189/100000000000000 : ℝ)^3253 := by
    have hnat : (1020924817 : ℕ)^4277*100000000000000^3253 ≤ 12383079257189^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020924817 5000000000 12383079257189 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66059919/125000000 : ℝ), (5390982763/10000000000 : ℝ), (-1020924817/5000000000 : ℝ)] ![(43235553792713/100000000000000 : ℝ), (887627338579/2000000000000 : ℝ), (12383079257189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66059919/125000000 : ℝ)|^4277 ≤ (43235553792713/100000000000000 : ℝ)^3253
        have hw : |(66059919/125000000 : ℝ)|=(66059919/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390982763/10000000000 : ℝ)|^4277 ≤ (887627338579/2000000000000 : ℝ)^3253
        have hw : |(5390982763/10000000000 : ℝ)|=(5390982763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1020924817/5000000000 : ℝ)|^4277 ≤ (12383079257189/100000000000000 : ℝ)^3253
        have hw : |(-1020924817/5000000000 : ℝ)|=(1020924817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_3 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4481997923/10000000000 : ℝ)*x 0 + (1065687483/2500000000 : ℝ)*x 1 + (4262749689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4481997923/10000000000 : ℝ)^4277 ≤ (34814461634653/100000000000000 : ℝ)^3253 := by
    have hnat : (4481997923 : ℕ)^4277*100000000000000^3253 ≤ 34814461634653^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481997923 10000000000 34814461634653 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065687483/2500000000 : ℝ)^4277 ≤ (6518554079081/20000000000000 : ℝ)^3253 := by
    have hnat : (1065687483 : ℕ)^4277*20000000000000^3253 ≤ 6518554079081^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065687483 2500000000 6518554079081 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4262749689/10000000000 : ℝ)^4277 ≤ (32592767952577/100000000000000 : ℝ)^3253 := by
    have hnat : (4262749689 : ℕ)^4277*100000000000000^3253 ≤ 32592767952577^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4262749689 10000000000 32592767952577 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4481997923/10000000000 : ℝ), (1065687483/2500000000 : ℝ), (4262749689/10000000000 : ℝ)] ![(34814461634653/100000000000000 : ℝ), (6518554079081/20000000000000 : ℝ), (32592767952577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4481997923/10000000000 : ℝ)|^4277 ≤ (34814461634653/100000000000000 : ℝ)^3253
        have hw : |(4481997923/10000000000 : ℝ)|=(4481997923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1065687483/2500000000 : ℝ)|^4277 ≤ (6518554079081/20000000000000 : ℝ)^3253
        have hw : |(1065687483/2500000000 : ℝ)|=(1065687483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4262749689/10000000000 : ℝ)|^4277 ≤ (32592767952577/100000000000000 : ℝ)^3253
        have hw : |(4262749689/10000000000 : ℝ)|=(4262749689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_4 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2237800989/10000000000 : ℝ)*x 0 + (5264339641/10000000000 : ℝ)*x 1 + (263217007/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237800989/10000000000 : ℝ)^4277 ≤ (1396864022227/10000000000000 : ℝ)^3253 := by
    have hnat : (2237800989 : ℕ)^4277*10000000000000^3253 ≤ 1396864022227^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237800989 10000000000 1396864022227 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264339641/10000000000 : ℝ)^4277 ≤ (43015677198899/100000000000000 : ℝ)^3253 := by
    have hnat : (5264339641 : ℕ)^4277*100000000000000^3253 ≤ 43015677198899^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264339641 10000000000 43015677198899 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263217007/500000000 : ℝ)^4277 ≤ (4301568255981/10000000000000 : ℝ)^3253 := by
    have hnat : (263217007 : ℕ)^4277*10000000000000^3253 ≤ 4301568255981^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263217007 500000000 4301568255981 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2237800989/10000000000 : ℝ), (5264339641/10000000000 : ℝ), (263217007/500000000 : ℝ)] ![(1396864022227/10000000000000 : ℝ), (43015677198899/100000000000000 : ℝ), (4301568255981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2237800989/10000000000 : ℝ)|^4277 ≤ (1396864022227/10000000000000 : ℝ)^3253
        have hw : |(-2237800989/10000000000 : ℝ)|=(2237800989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264339641/10000000000 : ℝ)|^4277 ≤ (43015677198899/100000000000000 : ℝ)^3253
        have hw : |(5264339641/10000000000 : ℝ)|=(5264339641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263217007/500000000 : ℝ)|^4277 ≤ (4301568255981/10000000000000 : ℝ)^3253
        have hw : |(263217007/500000000 : ℝ)|=(263217007/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_5 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373839607/10000000000 : ℝ)*x 0 + (-523121831/2500000000 : ℝ)*x 1 + (2632170011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373839607/10000000000 : ℝ)^4277 ≤ (22097951145553/50000000000000 : ℝ)^3253 := by
    have hnat : (5373839607 : ℕ)^4277*50000000000000^3253 ≤ 22097951145553^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373839607 10000000000 22097951145553 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523121831/2500000000 : ℝ)^4277 ≤ (12788416398299/100000000000000 : ℝ)^3253 := by
    have hnat : (523121831 : ℕ)^4277*100000000000000^3253 ≤ 12788416398299^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523121831 2500000000 12788416398299 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632170011/5000000000 : ℝ)^4277 ≤ (43015681292099/100000000000000 : ℝ)^3253 := by
    have hnat : (2632170011 : ℕ)^4277*100000000000000^3253 ≤ 43015681292099^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632170011 5000000000 43015681292099 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373839607/10000000000 : ℝ), (-523121831/2500000000 : ℝ), (2632170011/5000000000 : ℝ)] ![(22097951145553/50000000000000 : ℝ), (12788416398299/100000000000000 : ℝ), (43015681292099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373839607/10000000000 : ℝ)|^4277 ≤ (22097951145553/50000000000000 : ℝ)^3253
        have hw : |(5373839607/10000000000 : ℝ)|=(5373839607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-523121831/2500000000 : ℝ)|^4277 ≤ (12788416398299/100000000000000 : ℝ)^3253
        have hw : |(-523121831/2500000000 : ℝ)|=(523121831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632170011/5000000000 : ℝ)|^4277 ≤ (43015681292099/100000000000000 : ℝ)^3253
        have hw : |(2632170011/5000000000 : ℝ)|=(2632170011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_6 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2686919807/5000000000 : ℝ)*x 0 + (658042471/1250000000 : ℝ)*x 1 + (-1046243827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686919807/5000000000 : ℝ)^4277 ≤ (22097951183399/50000000000000 : ℝ)^3253 := by
    have hnat : (2686919807 : ℕ)^4277*50000000000000^3253 ≤ 22097951183399^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686919807 5000000000 22097951183399 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658042471/1250000000 : ℝ)^4277 ≤ (43015678563299/100000000000000 : ℝ)^3253 := by
    have hnat : (658042471 : ℕ)^4277*100000000000000^3253 ≤ 43015678563299^3253*1250000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658042471 1250000000 43015678563299 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046243827/5000000000 : ℝ)^4277 ≤ (12788419049991/100000000000000 : ℝ)^3253 := by
    have hnat : (1046243827 : ℕ)^4277*100000000000000^3253 ≤ 12788419049991^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046243827 5000000000 12788419049991 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686919807/5000000000 : ℝ), (658042471/1250000000 : ℝ), (-1046243827/5000000000 : ℝ)] ![(22097951183399/50000000000000 : ℝ), (43015678563299/100000000000000 : ℝ), (12788419049991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686919807/5000000000 : ℝ)|^4277 ≤ (22097951183399/50000000000000 : ℝ)^3253
        have hw : |(2686919807/5000000000 : ℝ)|=(2686919807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658042471/1250000000 : ℝ)|^4277 ≤ (43015678563299/100000000000000 : ℝ)^3253
        have hw : |(658042471/1250000000 : ℝ)|=(658042471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1046243827/5000000000 : ℝ)|^4277 ≤ (12788419049991/100000000000000 : ℝ)^3253
        have hw : |(-1046243827/5000000000 : ℝ)|=(1046243827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_7 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2091758331/5000000000 : ℝ)*x 0 + (882387197/2000000000 : ℝ)*x 1 + (137872999/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2091758331/5000000000 : ℝ)^4277 ≤ (31798595171171/100000000000000 : ℝ)^3253 := by
    have hnat : (2091758331 : ℕ)^4277*100000000000000^3253 ≤ 31798595171171^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091758331 5000000000 31798595171171 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882387197/2000000000 : ℝ)^4277 ≤ (4262587811477/12500000000000 : ℝ)^3253 := by
    have hnat : (882387197 : ℕ)^4277*12500000000000^3253 ≤ 4262587811477^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882387197 2000000000 4262587811477 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137872999/312500000 : ℝ)^4277 ≤ (17050351159529/50000000000000 : ℝ)^3253 := by
    have hnat : (137872999 : ℕ)^4277*50000000000000^3253 ≤ 17050351159529^3253*312500000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137872999 312500000 17050351159529 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2091758331/5000000000 : ℝ), (882387197/2000000000 : ℝ), (137872999/312500000 : ℝ)] ![(31798595171171/100000000000000 : ℝ), (4262587811477/12500000000000 : ℝ), (17050351159529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2091758331/5000000000 : ℝ)|^4277 ≤ (31798595171171/100000000000000 : ℝ)^3253
        have hw : |(2091758331/5000000000 : ℝ)|=(2091758331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(882387197/2000000000 : ℝ)|^4277 ≤ (4262587811477/12500000000000 : ℝ)^3253
        have hw : |(882387197/2000000000 : ℝ)|=(882387197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(137872999/312500000 : ℝ)|^4277 ≤ (17050351159529/50000000000000 : ℝ)^3253
        have hw : |(137872999/312500000 : ℝ)|=(137872999/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_8 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083097833/5000000000 : ℝ)*x 0 + (5177274891/10000000000 : ℝ)*x 1 + (2702506383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083097833/5000000000 : ℝ)^4277 ≤ (13383952298261/100000000000000 : ℝ)^3253 := by
    have hnat : (1083097833 : ℕ)^4277*100000000000000^3253 ≤ 13383952298261^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083097833 5000000000 13383952298261 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177274891/10000000000 : ℝ)^4277 ≤ (1683310311723/4000000000000 : ℝ)^3253 := by
    have hnat : (5177274891 : ℕ)^4277*4000000000000^3253 ≤ 1683310311723^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177274891 10000000000 1683310311723 4000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702506383/5000000000 : ℝ)^4277 ≤ (5566661236989/12500000000000 : ℝ)^3253 := by
    have hnat : (2702506383 : ℕ)^4277*12500000000000^3253 ≤ 5566661236989^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702506383 5000000000 5566661236989 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083097833/5000000000 : ℝ), (5177274891/10000000000 : ℝ), (2702506383/5000000000 : ℝ)] ![(13383952298261/100000000000000 : ℝ), (1683310311723/4000000000000 : ℝ), (5566661236989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083097833/5000000000 : ℝ)|^4277 ≤ (13383952298261/100000000000000 : ℝ)^3253
        have hw : |(-1083097833/5000000000 : ℝ)|=(1083097833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177274891/10000000000 : ℝ)|^4277 ≤ (1683310311723/4000000000000 : ℝ)^3253
        have hw : |(5177274891/10000000000 : ℝ)|=(5177274891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702506383/5000000000 : ℝ)|^4277 ≤ (5566661236989/12500000000000 : ℝ)^3253
        have hw : |(2702506383/5000000000 : ℝ)|=(2702506383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_9 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054984551/2000000000 : ℝ)*x 0 + (-25451317/125000000 : ℝ)*x 1 + (5405013029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054984551/2000000000 : ℝ)^4277 ≤ (8625882163481/20000000000000 : ℝ)^3253 := by
    have hnat : (1054984551 : ℕ)^4277*20000000000000^3253 ≤ 8625882163481^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054984551 2000000000 8625882163481 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25451317/125000000 : ℝ)^4277 ≤ (12337296413633/100000000000000 : ℝ)^3253 := by
    have hnat : (25451317 : ℕ)^4277*100000000000000^3253 ≤ 12337296413633^3253*125000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25451317 125000000 12337296413633 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5405013029/10000000000 : ℝ)^4277 ≤ (8906658548991/20000000000000 : ℝ)^3253 := by
    have hnat : (5405013029 : ℕ)^4277*20000000000000^3253 ≤ 8906658548991^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405013029 10000000000 8906658548991 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054984551/2000000000 : ℝ), (-25451317/125000000 : ℝ), (5405013029/10000000000 : ℝ)] ![(8625882163481/20000000000000 : ℝ), (12337296413633/100000000000000 : ℝ), (8906658548991/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054984551/2000000000 : ℝ)|^4277 ≤ (8625882163481/20000000000000 : ℝ)^3253
        have hw : |(1054984551/2000000000 : ℝ)|=(1054984551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-25451317/125000000 : ℝ)|^4277 ≤ (12337296413633/100000000000000 : ℝ)^3253
        have hw : |(-25451317/125000000 : ℝ)|=(25451317/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5405013029/10000000000 : ℝ)|^4277 ≤ (8906658548991/20000000000000 : ℝ)^3253
        have hw : |(5405013029/10000000000 : ℝ)|=(5405013029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_10 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318730693/2500000000 : ℝ)*x 0 + (1081002619/2000000000 : ℝ)*x 1 + (-63628289/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318730693/2500000000 : ℝ)^4277 ≤ (43129411000157/100000000000000 : ℝ)^3253 := by
    have hnat : (1318730693 : ℕ)^4277*100000000000000^3253 ≤ 43129411000157^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318730693 2500000000 43129411000157 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081002619/2000000000 : ℝ)^4277 ≤ (11133323364981/25000000000000 : ℝ)^3253 := by
    have hnat : (1081002619 : ℕ)^4277*25000000000000^3253 ≤ 11133323364981^3253*2000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081002619 2000000000 11133323364981 25000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63628289/312500000 : ℝ)^4277 ≤ (1233729552137/10000000000000 : ℝ)^3253 := by
    have hnat : (63628289 : ℕ)^4277*10000000000000^3253 ≤ 1233729552137^3253*312500000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63628289 312500000 1233729552137 10000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318730693/2500000000 : ℝ), (1081002619/2000000000 : ℝ), (-63628289/312500000 : ℝ)] ![(43129411000157/100000000000000 : ℝ), (11133323364981/25000000000000 : ℝ), (1233729552137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318730693/2500000000 : ℝ)|^4277 ≤ (43129411000157/100000000000000 : ℝ)^3253
        have hw : |(1318730693/2500000000 : ℝ)|=(1318730693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081002619/2000000000 : ℝ)|^4277 ≤ (11133323364981/25000000000000 : ℝ)^3253
        have hw : |(1081002619/2000000000 : ℝ)|=(1081002619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-63628289/312500000 : ℝ)|^4277 ≤ (1233729552137/10000000000000 : ℝ)^3253
        have hw : |(-63628289/312500000 : ℝ)|=(63628289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_11 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1128626323/2500000000 : ℝ)*x 0 + (1061552147/2500000000 : ℝ)*x 1 + (4246208507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1128626323/2500000000 : ℝ)^4277 ≤ (35146830022351/100000000000000 : ℝ)^3253 := by
    have hnat : (1128626323 : ℕ)^4277*100000000000000^3253 ≤ 35146830022351^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128626323 2500000000 35146830022351 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061552147/2500000000 : ℝ)^4277 ≤ (32426585389269/100000000000000 : ℝ)^3253 := by
    have hnat : (1061552147 : ℕ)^4277*100000000000000^3253 ≤ 32426585389269^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061552147 2500000000 32426585389269 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4246208507/10000000000 : ℝ)^4277 ≤ (32426584575989/100000000000000 : ℝ)^3253 := by
    have hnat : (4246208507 : ℕ)^4277*100000000000000^3253 ≤ 32426584575989^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246208507 10000000000 32426584575989 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1128626323/2500000000 : ℝ), (1061552147/2500000000 : ℝ), (4246208507/10000000000 : ℝ)] ![(35146830022351/100000000000000 : ℝ), (32426585389269/100000000000000 : ℝ), (32426584575989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1128626323/2500000000 : ℝ)|^4277 ≤ (35146830022351/100000000000000 : ℝ)^3253
        have hw : |(1128626323/2500000000 : ℝ)|=(1128626323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061552147/2500000000 : ℝ)|^4277 ≤ (32426585389269/100000000000000 : ℝ)^3253
        have hw : |(1061552147/2500000000 : ℝ)|=(1061552147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4246208507/10000000000 : ℝ)|^4277 ≤ (32426584575989/100000000000000 : ℝ)^3253
        have hw : |(4246208507/10000000000 : ℝ)|=(4246208507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_12 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-98424357/500000000 : ℝ)*x 0 + (273789227/500000000 : ℝ)*x 1 + (5253292149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (98424357/500000000 : ℝ)^4277 ≤ (11801444084923/100000000000000 : ℝ)^3253 := by
    have hnat : (98424357 : ℕ)^4277*100000000000000^3253 ≤ 11801444084923^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98424357 500000000 11801444084923 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273789227/500000000 : ℝ)^4277 ≤ (22650763049003/50000000000000 : ℝ)^3253 := by
    have hnat : (273789227 : ℕ)^4277*50000000000000^3253 ≤ 22650763049003^3253*500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273789227 500000000 22650763049003 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253292149/10000000000 : ℝ)^4277 ≤ (42897029803981/100000000000000 : ℝ)^3253 := by
    have hnat : (5253292149 : ℕ)^4277*100000000000000^3253 ≤ 42897029803981^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253292149 10000000000 42897029803981 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-98424357/500000000 : ℝ), (273789227/500000000 : ℝ), (5253292149/10000000000 : ℝ)] ![(11801444084923/100000000000000 : ℝ), (22650763049003/50000000000000 : ℝ), (42897029803981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-98424357/500000000 : ℝ)|^4277 ≤ (11801444084923/100000000000000 : ℝ)^3253
        have hw : |(-98424357/500000000 : ℝ)|=(98424357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273789227/500000000 : ℝ)|^4277 ≤ (22650763049003/50000000000000 : ℝ)^3253
        have hw : |(273789227/500000000 : ℝ)|=(273789227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253292149/10000000000 : ℝ)|^4277 ≤ (42897029803981/100000000000000 : ℝ)^3253
        have hw : |(5253292149/10000000000 : ℝ)|=(5253292149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_13 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381605083/10000000000 : ℝ)*x 0 + (-1048399851/5000000000 : ℝ)*x 1 + (5253292153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381605083/10000000000 : ℝ)^4277 ≤ (22139945345399/50000000000000 : ℝ)^3253 := by
    have hnat : (5381605083 : ℕ)^4277*50000000000000^3253 ≤ 22139945345399^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381605083 10000000000 22139945345399 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048399851/5000000000 : ℝ)^4277 ≤ (1602884930547/12500000000000 : ℝ)^3253 := by
    have hnat : (1048399851 : ℕ)^4277*12500000000000^3253 ≤ 1602884930547^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048399851 5000000000 1602884930547 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253292153/10000000000 : ℝ)^4277 ≤ (21448514923463/50000000000000 : ℝ)^3253 := by
    have hnat : (5253292153 : ℕ)^4277*50000000000000^3253 ≤ 21448514923463^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253292153 10000000000 21448514923463 50000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381605083/10000000000 : ℝ), (-1048399851/5000000000 : ℝ), (5253292153/10000000000 : ℝ)] ![(22139945345399/50000000000000 : ℝ), (1602884930547/12500000000000 : ℝ), (21448514923463/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381605083/10000000000 : ℝ)|^4277 ≤ (22139945345399/50000000000000 : ℝ)^3253
        have hw : |(5381605083/10000000000 : ℝ)|=(5381605083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1048399851/5000000000 : ℝ)|^4277 ≤ (1602884930547/12500000000000 : ℝ)^3253
        have hw : |(-1048399851/5000000000 : ℝ)|=(1048399851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253292153/10000000000 : ℝ)|^4277 ≤ (21448514923463/50000000000000 : ℝ)^3253
        have hw : |(5253292153/10000000000 : ℝ)|=(5253292153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_14 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2690802499/5000000000 : ℝ)*x 0 + (5253292059/10000000000 : ℝ)*x 1 + (-1048399971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690802499/5000000000 : ℝ)^4277 ≤ (44279889771261/100000000000000 : ℝ)^3253 := by
    have hnat : (2690802499 : ℕ)^4277*100000000000000^3253 ≤ 44279889771261^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690802499 5000000000 44279889771261 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253292059/10000000000 : ℝ)^4277 ≤ (42897028837723/100000000000000 : ℝ)^3253 := by
    have hnat : (5253292059 : ℕ)^4277*100000000000000^3253 ≤ 42897028837723^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253292059 10000000000 42897028837723 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048399971/5000000000 : ℝ)^4277 ≤ (12823081374129/100000000000000 : ℝ)^3253 := by
    have hnat : (1048399971 : ℕ)^4277*100000000000000^3253 ≤ 12823081374129^3253*5000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048399971 5000000000 12823081374129 100000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690802499/5000000000 : ℝ), (5253292059/10000000000 : ℝ), (-1048399971/5000000000 : ℝ)] ![(44279889771261/100000000000000 : ℝ), (42897028837723/100000000000000 : ℝ), (12823081374129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690802499/5000000000 : ℝ)|^4277 ≤ (44279889771261/100000000000000 : ℝ)^3253
        have hw : |(2690802499/5000000000 : ℝ)|=(2690802499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253292059/10000000000 : ℝ)|^4277 ≤ (42897028837723/100000000000000 : ℝ)^3253
        have hw : |(5253292059/10000000000 : ℝ)|=(5253292059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048399971/5000000000 : ℝ)|^4277 ≤ (12823081374129/100000000000000 : ℝ)^3253
        have hw : |(-1048399971/5000000000 : ℝ)|=(1048399971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1317_box_15 (p : ℝ) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4157030783/10000000000 : ℝ)*x 0 + (1106235041/2500000000 : ℝ)*x 1 + (55311751/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4157030783/10000000000 : ℝ)^4277 ≤ (3941771279351/12500000000000 : ℝ)^3253 := by
    have hnat : (4157030783 : ℕ)^4277*12500000000000^3253 ≤ 3941771279351^3253*10000000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157030783 10000000000 3941771279351 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106235041/2500000000 : ℝ)^4277 ≤ (6846583060831/20000000000000 : ℝ)^3253 := by
    have hnat : (1106235041 : ℕ)^4277*20000000000000^3253 ≤ 6846583060831^3253*2500000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106235041 2500000000 6846583060831 20000000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55311751/125000000 : ℝ)^4277 ≤ (4279114306217/12500000000000 : ℝ)^3253 := by
    have hnat : (55311751 : ℕ)^4277*12500000000000^3253 ≤ 4279114306217^3253*125000000^4277 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55311751 125000000 4279114306217 12500000000000 4277 3253 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4277/1024 : ℝ)) 4277 3253 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4157030783/10000000000 : ℝ), (1106235041/2500000000 : ℝ), (55311751/125000000 : ℝ)] ![(3941771279351/12500000000000 : ℝ), (6846583060831/20000000000000 : ℝ), (4279114306217/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4157030783/10000000000 : ℝ)|^4277 ≤ (3941771279351/12500000000000 : ℝ)^3253
        have hw : |(4157030783/10000000000 : ℝ)|=(4157030783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106235041/2500000000 : ℝ)|^4277 ≤ (6846583060831/20000000000000 : ℝ)^3253
        have hw : |(1106235041/2500000000 : ℝ)|=(1106235041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55311751/125000000 : ℝ)|^4277 ≤ (4279114306217/12500000000000 : ℝ)^3253
        have hw : |(55311751/125000000 : ℝ)|=(55311751/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1317_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31423/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58893/100000 : ℝ) ∧ (79807/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42127/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1109/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1109/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1109/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1469/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1109/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1109/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1469/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1109/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1109/10000 : ℝ) ^ (1069/256 : ℝ) ≤ (642278042802619/6250000000000000000 : ℝ) := by
    have hpowers : (1109/10000 : ℝ)^1069 ≤ (642278042802619/6250000000000000000 : ℝ)^256 := by
      have hnat : (1109 : ℕ)^1069*6250000000000000000^256 ≤ 642278042802619^256*10000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1109 10000 642278042802619 6250000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1109/10000 : ℝ)) (X := (642278042802619/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1469/10000 : ℝ) ^ (1069/256 : ℝ) ≤ (16620161422727287/50000000000000000000 : ℝ) := by
    have hpowers : (1469/10000 : ℝ)^1069 ≤ (16620161422727287/50000000000000000000 : ℝ)^256 := by
      have hnat : (1469 : ℕ)^1069*50000000000000000000^256 ≤ 16620161422727287^256*10000^1069 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1469 10000 16620161422727287 50000000000000000000 1069 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1469/10000 : ℝ)) (X := (16620161422727287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125642278042802619/3125000000000000000 : ℝ) ≤ (10000492154402363/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (3125642278042802619/3125000000000000000 : ℝ)^256 ≤ (10000492154402363/10000000000000000 : ℝ)^1069 := by
      have hnat : (3125642278042802619 : ℕ)^256*10000000000000000^1069 ≤ 10000492154402363^1069*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125642278042802619 3125000000000000000 10000492154402363 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000492154402363/10000000000000000 : ℝ)) (X := (3125642278042802619/3125000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021758385765148239/50000000000000000000 : ℝ) ≤ (5000520975234429/5000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (50021758385765148239/50000000000000000000 : ℝ)^256 ≤ (5000520975234429/5000000000000000 : ℝ)^1069 := by
      have hnat : (50021758385765148239 : ℕ)^256*5000000000000000^1069 ≤ 5000520975234429^1069*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021758385765148239 50000000000000000000 5000520975234429 5000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000520975234429/5000000000000000 : ℝ)) (X := (50021758385765148239/50000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016620161422727287/25000000000000000000 : ℝ) ≤ (10001591746535353/10000000000000000 : ℝ) ^ (1069/256 : ℝ) := by
    have hpowers : (25016620161422727287/25000000000000000000 : ℝ)^256 ≤ (10001591746535353/10000000000000000 : ℝ)^1069 := by
      have hnat : (25016620161422727287 : ℕ)^256*10000000000000000^1069 ≤ 10001591746535353^1069*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016620161422727287 25000000000000000000 10001591746535353 10000000000000000 256 1069 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001591746535353/10000000000000000 : ℝ)) (X := (25016620161422727287/25000000000000000000 : ℝ)) (by norm_num) 1069 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(642278042802619/6250000000000000000 : ℝ) ≤ ((359895772790936477/360000000000000000 : ℝ)+2*(109959213299/72000000000000 : ℝ)*(1109/10000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (359895772790936477/360000000000000000 : ℝ)+2*(109959213299/72000000000000 : ℝ)*(1109/10000 : ℝ)=(10000492154402363/10000000000000000 : ℝ) by norm_num, show 1+2*(642278042802619/6250000000000000000 : ℝ)=(3125642278042802619/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16620161422727287/50000000000000000000 : ℝ)+(642278042802619/6250000000000000000 : ℝ) ≤ ((359895772790936477/360000000000000000 : ℝ)+(109959213299/72000000000000 : ℝ)*((1469/10000 : ℝ)+(1109/10000 : ℝ)))^(1069/256 : ℝ) := by
    rw [show (359895772790936477/360000000000000000 : ℝ)+(109959213299/72000000000000 : ℝ)*((1469/10000 : ℝ)+(1109/10000 : ℝ))=(5000520975234429/5000000000000000 : ℝ) by norm_num, show 1+(16620161422727287/50000000000000000000 : ℝ)+(642278042802619/6250000000000000000 : ℝ)=(50021758385765148239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16620161422727287/50000000000000000000 : ℝ) ≤ ((359895772790936477/360000000000000000 : ℝ)+2*(109959213299/72000000000000 : ℝ)*(1469/10000 : ℝ))^(1069/256 : ℝ) := by
    rw [show (359895772790936477/360000000000000000 : ℝ)+2*(109959213299/72000000000000 : ℝ)*(1469/10000 : ℝ)=(10001591746535353/10000000000000000 : ℝ) by norm_num, show 1+2*(16620161422727287/50000000000000000000 : ℝ)=(25016620161422727287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (359895772790936477/360000000000000000 : ℝ)*(X 1 0+X 2 0)+(109959213299/72000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (359895772790936477/360000000000000000 : ℝ)) (alpha := (109959213299/72000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (359895772790936477/360000000000000000 : ℝ)*(X 0 1+X 2 1)+(109959213299/72000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (359895772790936477/360000000000000000 : ℝ)) (alpha := (109959213299/72000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (359895772790936477/360000000000000000 : ℝ)*(X 0 2+X 1 2)+(109959213299/72000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1069/256 : ℝ)) (lo := (1109/10000 : ℝ)) (hi := (1469/10000 : ℝ)) (c := (359895772790936477/360000000000000000 : ℝ)) (alpha := (109959213299/72000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-379298897/2000000000 : ℝ)*X 0 0+(5390982939/10000000000 : ℝ)*X 0 1+(21563931/40000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((330299569/625000000 : ℝ)*X 1 0+(-2041849597/10000000000 : ℝ)*X 1 1+(1078196641/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66059919/125000000 : ℝ)*X 2 0+(5390982763/10000000000 : ℝ)*X 2 1+(-1020924817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4481997923/10000000000 : ℝ)*X 0 0+(1065687483/2500000000 : ℝ)*X 0 1+(4262749689/10000000000 : ℝ)*X 0 2+(4481997923/10000000000 : ℝ)*X 1 0+(1065687483/2500000000 : ℝ)*X 1 1+(4262749689/10000000000 : ℝ)*X 1 2+(4481997923/10000000000 : ℝ)*X 2 0+(1065687483/2500000000 : ℝ)*X 2 1+(4262749689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2237800989/10000000000 : ℝ)*X 0 0+(5264339641/10000000000 : ℝ)*X 0 1+(263217007/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5373839607/10000000000 : ℝ)*X 1 0+(-523121831/2500000000 : ℝ)*X 1 1+(2632170011/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2686919807/5000000000 : ℝ)*X 2 0+(658042471/1250000000 : ℝ)*X 2 1+(-1046243827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2091758331/5000000000 : ℝ)*X 0 0+(882387197/2000000000 : ℝ)*X 0 1+(137872999/312500000 : ℝ)*X 0 2+(2091758331/5000000000 : ℝ)*X 1 0+(882387197/2000000000 : ℝ)*X 1 1+(137872999/312500000 : ℝ)*X 1 2+(2091758331/5000000000 : ℝ)*X 2 0+(882387197/2000000000 : ℝ)*X 2 1+(137872999/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1083097833/5000000000 : ℝ)*X 0 0+(5177274891/10000000000 : ℝ)*X 0 1+(2702506383/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1054984551/2000000000 : ℝ)*X 1 0+(-25451317/125000000 : ℝ)*X 1 1+(5405013029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1318730693/2500000000 : ℝ)*X 2 0+(1081002619/2000000000 : ℝ)*X 2 1+(-63628289/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1128626323/2500000000 : ℝ)*X 0 0+(1061552147/2500000000 : ℝ)*X 0 1+(4246208507/10000000000 : ℝ)*X 0 2+(1128626323/2500000000 : ℝ)*X 1 0+(1061552147/2500000000 : ℝ)*X 1 1+(4246208507/10000000000 : ℝ)*X 1 2+(1128626323/2500000000 : ℝ)*X 2 0+(1061552147/2500000000 : ℝ)*X 2 1+(4246208507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-98424357/500000000 : ℝ)*X 0 0+(273789227/500000000 : ℝ)*X 0 1+(5253292149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5381605083/10000000000 : ℝ)*X 1 0+(-1048399851/5000000000 : ℝ)*X 1 1+(5253292153/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690802499/5000000000 : ℝ)*X 2 0+(5253292059/10000000000 : ℝ)*X 2 1+(-1048399971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4157030783/10000000000 : ℝ)*X 0 0+(1106235041/2500000000 : ℝ)*X 0 1+(55311751/125000000 : ℝ)*X 0 2+(4157030783/10000000000 : ℝ)*X 1 0+(1106235041/2500000000 : ℝ)*X 1 1+(55311751/125000000 : ℝ)*X 1 2+(4157030783/10000000000 : ℝ)*X 2 0+(1106235041/2500000000 : ℝ)*X 2 1+(55311751/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1317_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31423/50000 : ℝ) ≤ (-628439048542308519009499842819/1000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65738179/100000000000000 : ℝ)*(upper1) + (120408663/100000000000000 : ℝ)*(lower4) + (2791359/100000000000000 : ℝ)*(upper5) + (1446203934869247/50000000000000 : ℝ)*(major0) + (1446203934869247/50000000000000 : ℝ)*(major1) + (1446203934869247/50000000000000 : ℝ)*(major2) + (2300407691/20000000000000 : ℝ)*(sp2) + (6571444397/100000000000000 : ℝ)*(sp3) + (196222246774197/5000000000000 : ℝ)*(sp4) + (1962213674312059/50000000000000 : ℝ)*(sp5) + (981110636903779/25000000000000 : ℝ)*(sp6) + (235162885832969/12500000000000 : ℝ)*(sp7) + (911416963/10000000000000 : ℝ)*(sp12) + (26701029453/100000000000000 : ℝ)*(sp13) + (1881309658108149/100000000000000 : ℝ)*(f.failure) + (392445404965357/10000000000000 : ℝ)*(f.sum) + (140477621683/200000000000000000000000000 : ℝ)*base66 + (18007606878343091/2000000000000000000000000000000 : ℝ)*base67 + (35187749928343091/2000000000000000000000000000000 : ℝ)*base69 + (32791722846343091/2000000000000000000000000000000 : ℝ)*base71 + (417543360117/200000000000000000000000000 : ℝ)*base73 + (23411657058343091/2000000000000000000000000000000 : ℝ)*base75 + (17792791648343091/2000000000000000000000000000000 : ℝ)*base77 + (15542609852343091/2000000000000000000000000000000 : ℝ)*base79 + (498427830317/200000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2952369/500000000000000000000 : ℝ)*base90 + (2952369/500000000000000000000 : ℝ)*base92 + (2952369/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58893/100000 : ℝ) ≤ (1766858603640036132170379712771/3000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7615323/50000000000000 : ℝ)*(upper0) + (8649353/25000000000000 : ℝ)*(upper3) + (91291499/100000000000000 : ℝ)*(upper4) + (2960258260473077/100000000000000 : ℝ)*(major0) + (2960258260473077/100000000000000 : ℝ)*(major1) + (2960258260473077/100000000000000 : ℝ)*(major2) + (1987719475884099/50000000000000 : ℝ)*(sp0) + (496929008291177/12500000000000 : ℝ)*(sp1) + (1987720193172167/50000000000000 : ℝ)*(sp2) + (1925440762720983/100000000000000 : ℝ)*(sp3) + (11085660489/100000000000000 : ℝ)*(sp5) + (2765645571/100000000000000 : ℝ)*(sp6) + (843972593/100000000000000 : ℝ)*(sp7) + (4200221707/100000000000000 : ℝ)*(sp8) + (240680200836697/12500000000000 : ℝ)*(f.failure) + (795088630397981/20000000000000 : ℝ)*(f.sum) + (15209940887777/3600000000000000000000000000 : ℝ)*base66 + (1955290936948243/12000000000000000000000000000000 : ℝ)*base67 + (113493727900948243/12000000000000000000000000000000 : ℝ)*base69 + (21467496832948243/12000000000000000000000000000000 : ℝ)*base71 + (68584413851777/3600000000000000000000000000 : ℝ)*base74 + (36473492188948243/12000000000000000000000000000000 : ℝ)*base75 + (60791134588948243/12000000000000000000000000000000 : ℝ)*base77 + (108445303195051757/12000000000000000000000000000000 : ℝ)*base80 + (12750027415423/3600000000000000000000000000 : ℝ)*base81 + (49357/62500000000000000000 : ℝ)*base90 + (49357/62500000000000000000 : ℝ)*base92 + (49357/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79807/100000 : ℝ) ≤ (299284581965218984220356800457/375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4155761/20000000000000 : ℝ)*(lower3) + (22725673/50000000000000 : ℝ)*(upper4) + (10951521/100000000000000 : ℝ)*(lower5) + (409169836193759/12500000000000 : ℝ)*(major0) + (409169836193759/12500000000000 : ℝ)*(major1) + (409169836193759/12500000000000 : ℝ)*(major2) + (8036150953/100000000000000 : ℝ)*(sp0) + (10515986127/10000000000000 : ℝ)*(sp1) + (17954953901/12500000000000 : ℝ)*(sp2) + (21502509797/50000000000000 : ℝ)*(sp3) + (2195507331409469/50000000000000 : ℝ)*(sp8) + (219545876955431/5000000000000 : ℝ)*(sp9) + (4390879059338681/100000000000000 : ℝ)*(sp10) + (2129048601158187/100000000000000 : ℝ)*(sp11) + (1064545803088891/50000000000000 : ℝ)*(f.failure) + (439102269896989/10000000000000 : ℝ)*(f.sum) + (680501777909/450000000000000000000000000 : ℝ)*base66 + (2826506337649319/1500000000000000000000000000000 : ℝ)*base68 + (3962835446350681/1500000000000000000000000000000 : ℝ)*base69 + (6445136376850681/1500000000000000000000000000000 : ℝ)*base71 + (1241136177359/450000000000000000000000000 : ℝ)*base74 + (10876999838350681/1500000000000000000000000000000 : ℝ)*base75 + (19122857808850681/1500000000000000000000000000000 : ℝ)*base77 + (16656065501350681/1500000000000000000000000000000 : ℝ)*base79 + (166121309191/450000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (1584129/250000000000000000000 : ℝ)*base89 + (1584129/250000000000000000000 : ℝ)*base91 + (1584129/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42127/50000 : ℝ) ≤ (-421257929771820619607783520229/500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (127663641/100000000000000 : ℝ)*(lower0) + (9524327/20000000000000 : ℝ)*(lower1) + (120874049/100000000000000 : ℝ)*(lower4) + (1654769492863769/50000000000000 : ℝ)*(major0) + (1654769492863769/50000000000000 : ℝ)*(major1) + (1654769492863769/50000000000000 : ℝ)*(major2) + (1951821699/100000000000000 : ℝ)*(sp0) + (16450812627/25000000000000 : ℝ)*(sp5) + (86132145791/50000000000000 : ℝ)*(sp6) + (34432095289/50000000000000 : ℝ)*(sp7) + (1123633878824551/25000000000000 : ℝ)*(sp12) + (1123617915967349/25000000000000 : ℝ)*(sp13) + (4494365202828321/100000000000000 : ℝ)*(sp14) + (1076277751064687/50000000000000 : ℝ)*(sp15) + (134539022894997/6250000000000 : ℝ)*(f.failure) + (140454295847497/3125000000000 : ℝ)*(f.sum) + (6864786961469/1800000000000000000000000000 : ℝ)*base66 + (32407145650847729/6000000000000000000000000000000 : ℝ)*base68 + (56950900948847729/6000000000000000000000000000000 : ℝ)*base70 + (65449472740847729/6000000000000000000000000000000 : ℝ)*base72 + (27654142883669/1800000000000000000000000000 : ℝ)*base74 + (19320029656847729/6000000000000000000000000000000 : ℝ)*base76 + (1553322367152271/6000000000000000000000000000000 : ℝ)*base77 + (10134404014847729/6000000000000000000000000000000 : ℝ)*base80 + (143460081269/1800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (318343/31250000000000000000 : ℝ)*base89 + (318343/31250000000000000000 : ℝ)*base91 + (318343/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1317_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1469/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1109/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58893/100000 : ℝ) else (79807/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42127/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1317_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1317_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58893/100000 : ℝ) else (79807/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42127/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1317_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1317_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1317_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1069/256 : ℝ) ≤ p) (hpb : p ≤ (4277/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7687219/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14701/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58893/100000 : ℝ) else (79807/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42127/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1317_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
