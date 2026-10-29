-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1413_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:49:26.207885+00:00
-- url     : https://prove2.me/submissions/2b41a927-1ccb-4c49-bdb4-4d40f6fbf9d4

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
theorem support_rectangle_w1413_s0_0 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1767908063/10000000000 : ℝ)*x 0 + (2983405889/5000000000 : ℝ)*x 1 + (4827564043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1767908063/10000000000 : ℝ)^4373 ≤ (2081568704151/20000000000000 : ℝ)^3349 := by
    have hnat : (1767908063 : ℕ)^4373*20000000000000^3349 ≤ 2081568704151^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1767908063 10000000000 2081568704151 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2983405889/5000000000 : ℝ)^4373 ≤ (6369167570059/12500000000000 : ℝ)^3349 := by
    have hnat : (2983405889 : ℕ)^4373*12500000000000^3349 ≤ 6369167570059^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983405889 5000000000 6369167570059 12500000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4827564043/10000000000 : ℝ)^4373 ≤ (19319407951517/50000000000000 : ℝ)^3349 := by
    have hnat : (4827564043 : ℕ)^4373*50000000000000^3349 ≤ 19319407951517^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827564043 10000000000 19319407951517 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1767908063/10000000000 : ℝ), (2983405889/5000000000 : ℝ), (4827564043/10000000000 : ℝ)] ![(2081568704151/20000000000000 : ℝ), (6369167570059/12500000000000 : ℝ), (19319407951517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1767908063/10000000000 : ℝ)|^4373 ≤ (2081568704151/20000000000000 : ℝ)^3349
        have hw : |(-1767908063/10000000000 : ℝ)|=(1767908063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2983405889/5000000000 : ℝ)|^4373 ≤ (6369167570059/12500000000000 : ℝ)^3349
        have hw : |(2983405889/5000000000 : ℝ)|=(2983405889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4827564043/10000000000 : ℝ)|^4373 ≤ (19319407951517/50000000000000 : ℝ)^3349
        have hw : |(4827564043/10000000000 : ℝ)|=(4827564043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s0_1 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2746940137/5000000000 : ℝ)*x 0 + (-1206091171/5000000000 : ℝ)*x 1 + (482756437/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2746940137/5000000000 : ℝ)^4373 ≤ (45745027612399/100000000000000 : ℝ)^3349 := by
    have hnat : (2746940137 : ℕ)^4373*100000000000000^3349 ≤ 45745027612399^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746940137 5000000000 45745027612399 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1206091171/5000000000 : ℝ)^4373 ≤ (15616153046863/100000000000000 : ℝ)^3349 := by
    have hnat : (1206091171 : ℕ)^4373*100000000000000^3349 ≤ 15616153046863^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206091171 5000000000 15616153046863 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (482756437/1000000000 : ℝ)^4373 ≤ (38638819320529/100000000000000 : ℝ)^3349 := by
    have hnat : (482756437 : ℕ)^4373*100000000000000^3349 ≤ 38638819320529^3349*1000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482756437 1000000000 38638819320529 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2746940137/5000000000 : ℝ), (-1206091171/5000000000 : ℝ), (482756437/1000000000 : ℝ)] ![(45745027612399/100000000000000 : ℝ), (15616153046863/100000000000000 : ℝ), (38638819320529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2746940137/5000000000 : ℝ)|^4373 ≤ (45745027612399/100000000000000 : ℝ)^3349
        have hw : |(2746940137/5000000000 : ℝ)|=(2746940137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1206091171/5000000000 : ℝ)|^4373 ≤ (15616153046863/100000000000000 : ℝ)^3349
        have hw : |(-1206091171/5000000000 : ℝ)|=(1206091171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(482756437/1000000000 : ℝ)|^4373 ≤ (38638819320529/100000000000000 : ℝ)^3349
        have hw : |(482756437/1000000000 : ℝ)|=(482756437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s0_2 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1373470133/2500000000 : ℝ)*x 0 + (603445529/1250000000 : ℝ)*x 1 + (-1206091091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1373470133/2500000000 : ℝ)^4373 ≤ (45745030417501/100000000000000 : ℝ)^3349 := by
    have hnat : (1373470133 : ℕ)^4373*100000000000000^3349 ≤ 45745030417501^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373470133 2500000000 45745030417501 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603445529/1250000000 : ℝ)^4373 ≤ (38638817878283/100000000000000 : ℝ)^3349 := by
    have hnat : (603445529 : ℕ)^4373*100000000000000^3349 ≤ 38638817878283^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603445529 1250000000 38638817878283 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206091091/5000000000 : ℝ)^4373 ≤ (15616151694329/100000000000000 : ℝ)^3349 := by
    have hnat : (1206091091 : ℕ)^4373*100000000000000^3349 ≤ 15616151694329^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206091091 5000000000 15616151694329 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1373470133/2500000000 : ℝ), (603445529/1250000000 : ℝ), (-1206091091/5000000000 : ℝ)] ![(45745030417501/100000000000000 : ℝ), (38638817878283/100000000000000 : ℝ), (15616151694329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1373470133/2500000000 : ℝ)|^4373 ≤ (45745030417501/100000000000000 : ℝ)^3349
        have hw : |(1373470133/2500000000 : ℝ)|=(1373470133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603445529/1250000000 : ℝ)|^4373 ≤ (38638817878283/100000000000000 : ℝ)^3349
        have hw : |(603445529/1250000000 : ℝ)|=(603445529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1206091091/5000000000 : ℝ)|^4373 ≤ (15616151694329/100000000000000 : ℝ)^3349
        have hw : |(-1206091091/5000000000 : ℝ)|=(1206091091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s0_3 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2084152219/5000000000 : ℝ)*x 0 + (1551893091/5000000000 : ℝ)*x 1 + (5553919977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2084152219/5000000000 : ℝ)^4373 ≤ (3189753471467/10000000000000 : ℝ)^3349 := by
    have hnat : (2084152219 : ℕ)^4373*10000000000000^3349 ≤ 3189753471467^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084152219 5000000000 3189753471467 10000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1551893091/5000000000 : ℝ)^4373 ≤ (21703568673909/100000000000000 : ℝ)^3349 := by
    have hnat : (1551893091 : ℕ)^4373*100000000000000^3349 ≤ 21703568673909^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1551893091 5000000000 21703568673909 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5553919977/10000000000 : ℝ)^4373 ≤ (46398896602483/100000000000000 : ℝ)^3349 := by
    have hnat : (5553919977 : ℕ)^4373*100000000000000^3349 ≤ 46398896602483^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553919977 10000000000 46398896602483 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2084152219/5000000000 : ℝ), (1551893091/5000000000 : ℝ), (5553919977/10000000000 : ℝ)] ![(3189753471467/10000000000000 : ℝ), (21703568673909/100000000000000 : ℝ), (46398896602483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2084152219/5000000000 : ℝ)|^4373 ≤ (3189753471467/10000000000000 : ℝ)^3349
        have hw : |(2084152219/5000000000 : ℝ)|=(2084152219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1551893091/5000000000 : ℝ)|^4373 ≤ (21703568673909/100000000000000 : ℝ)^3349
        have hw : |(1551893091/5000000000 : ℝ)|=(1551893091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5553919977/10000000000 : ℝ)|^4373 ≤ (46398896602483/100000000000000 : ℝ)^3349
        have hw : |(5553919977/10000000000 : ℝ)|=(5553919977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s0_4 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1772003151/10000000000 : ℝ)*x 0 + (1214186963/2500000000 : ℝ)*x 1 + (2968292897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1772003151/10000000000 : ℝ)^4373 ≤ (10439334222003/100000000000000 : ℝ)^3349 := by
    have hnat : (1772003151 : ℕ)^4373*100000000000000^3349 ≤ 10439334222003^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772003151 10000000000 10439334222003 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1214186963/2500000000 : ℝ)^4373 ≤ (19472049479947/50000000000000 : ℝ)^3349 := by
    have hnat : (1214186963 : ℕ)^4373*50000000000000^3349 ≤ 19472049479947^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1214186963 2500000000 19472049479947 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2968292897/5000000000 : ℝ)^4373 ≤ (10123313361451/20000000000000 : ℝ)^3349 := by
    have hnat : (2968292897 : ℕ)^4373*20000000000000^3349 ≤ 10123313361451^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2968292897 5000000000 10123313361451 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1772003151/10000000000 : ℝ), (1214186963/2500000000 : ℝ), (2968292897/5000000000 : ℝ)] ![(10439334222003/100000000000000 : ℝ), (19472049479947/50000000000000 : ℝ), (10123313361451/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1772003151/10000000000 : ℝ)|^4373 ≤ (10439334222003/100000000000000 : ℝ)^3349
        have hw : |(-1772003151/10000000000 : ℝ)|=(1772003151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1214186963/2500000000 : ℝ)|^4373 ≤ (19472049479947/50000000000000 : ℝ)^3349
        have hw : |(1214186963/2500000000 : ℝ)|=(1214186963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2968292897/5000000000 : ℝ)|^4373 ≤ (10123313361451/20000000000000 : ℝ)^3349
        have hw : |(2968292897/5000000000 : ℝ)|=(2968292897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s0_5 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183009707/10000000000 : ℝ)*x 0 + (-651580189/5000000000 : ℝ)*x 1 + (5936585897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183009707/10000000000 : ℝ)^4373 ≤ (42394721781923/100000000000000 : ℝ)^3349 := by
    have hnat : (5183009707 : ℕ)^4373*100000000000000^3349 ≤ 42394721781923^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183009707 10000000000 42394721781923 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651580189/5000000000 : ℝ)^4373 ≤ (6988710258029/100000000000000 : ℝ)^3349 := by
    have hnat : (651580189 : ℕ)^4373*100000000000000^3349 ≤ 6988710258029^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651580189 5000000000 6988710258029 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5936585897/10000000000 : ℝ)^4373 ≤ (2024662718159/4000000000000 : ℝ)^3349 := by
    have hnat : (5936585897 : ℕ)^4373*4000000000000^3349 ≤ 2024662718159^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5936585897 10000000000 2024662718159 4000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183009707/10000000000 : ℝ), (-651580189/5000000000 : ℝ), (5936585897/10000000000 : ℝ)] ![(42394721781923/100000000000000 : ℝ), (6988710258029/100000000000000 : ℝ), (2024662718159/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183009707/10000000000 : ℝ)|^4373 ≤ (42394721781923/100000000000000 : ℝ)^3349
        have hw : |(5183009707/10000000000 : ℝ)|=(5183009707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-651580189/5000000000 : ℝ)|^4373 ≤ (6988710258029/100000000000000 : ℝ)^3349
        have hw : |(-651580189/5000000000 : ℝ)|=(651580189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5936585897/10000000000 : ℝ)|^4373 ≤ (2024662718159/4000000000000 : ℝ)^3349
        have hw : |(5936585897/10000000000 : ℝ)|=(5936585897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s0_6 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5183009727/10000000000 : ℝ)*x 0 + (2968292847/5000000000 : ℝ)*x 1 + (-130316067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5183009727/10000000000 : ℝ)^4373 ≤ (21197360997767/50000000000000 : ℝ)^3349 := by
    have hnat : (5183009727 : ℕ)^4373*50000000000000^3349 ≤ 21197360997767^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183009727 10000000000 21197360997767 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2968292847/5000000000 : ℝ)^4373 ≤ (25308282846967/50000000000000 : ℝ)^3349 := by
    have hnat : (2968292847 : ℕ)^4373*50000000000000^3349 ≤ 25308282846967^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2968292847 5000000000 25308282846967 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130316067/1000000000 : ℝ)^4373 ≤ (6988712302807/100000000000000 : ℝ)^3349 := by
    have hnat : (130316067 : ℕ)^4373*100000000000000^3349 ≤ 6988712302807^3349*1000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130316067 1000000000 6988712302807 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5183009727/10000000000 : ℝ), (2968292847/5000000000 : ℝ), (-130316067/1000000000 : ℝ)] ![(21197360997767/50000000000000 : ℝ), (25308282846967/50000000000000 : ℝ), (6988712302807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5183009727/10000000000 : ℝ)|^4373 ≤ (21197360997767/50000000000000 : ℝ)^3349
        have hw : |(5183009727/10000000000 : ℝ)|=(5183009727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2968292847/5000000000 : ℝ)|^4373 ≤ (25308282846967/50000000000000 : ℝ)^3349
        have hw : |(2968292847/5000000000 : ℝ)|=(2968292847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130316067/1000000000 : ℝ)|^4373 ≤ (6988712302807/100000000000000 : ℝ)^3349
        have hw : |(-130316067/1000000000 : ℝ)|=(130316067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s0_7 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4177113467/10000000000 : ℝ)*x 0 + (1098231103/2000000000 : ℝ)*x 1 + (3168792217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177113467/10000000000 : ℝ)^4373 ≤ (31985584901637/100000000000000 : ℝ)^3349 := by
    have hnat : (4177113467 : ℕ)^4373*100000000000000^3349 ≤ 31985584901637^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177113467 10000000000 31985584901637 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098231103/2000000000 : ℝ)^4373 ≤ (9143080988567/20000000000000 : ℝ)^3349 := by
    have hnat : (1098231103 : ℕ)^4373*20000000000000^3349 ≤ 9143080988567^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098231103 2000000000 9143080988567 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3168792217/10000000000 : ℝ)^4373 ≤ (1393688133877/6250000000000 : ℝ)^3349 := by
    have hnat : (3168792217 : ℕ)^4373*6250000000000^3349 ≤ 1393688133877^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3168792217 10000000000 1393688133877 6250000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177113467/10000000000 : ℝ), (1098231103/2000000000 : ℝ), (3168792217/10000000000 : ℝ)] ![(31985584901637/100000000000000 : ℝ), (9143080988567/20000000000000 : ℝ), (1393688133877/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177113467/10000000000 : ℝ)|^4373 ≤ (31985584901637/100000000000000 : ℝ)^3349
        have hw : |(4177113467/10000000000 : ℝ)|=(4177113467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098231103/2000000000 : ℝ)|^4373 ≤ (9143080988567/20000000000000 : ℝ)^3349
        have hw : |(1098231103/2000000000 : ℝ)|=(1098231103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3168792217/10000000000 : ℝ)|^4373 ≤ (1393688133877/6250000000000 : ℝ)^3349
        have hw : |(3168792217/10000000000 : ℝ)|=(3168792217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1413_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (967/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26369/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1093/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1093 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1093*1^256 ≤ 0^256*1^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1093/256 : ℝ) ≤ (1999782195072747573/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1093 ≤ (1999782195072747573/100000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1093*100000000000000000000^256 ≤ 1999782195072747573^256*5^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1999782195072747573 100000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1999782195072747573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1093 := by
      have hnat : (1 : ℕ)^256*1^1093 ≤ 1^1093*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (101999782195072747573/100000000000000000000 : ℝ) ≤ (627905248183759/625000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (101999782195072747573/100000000000000000000 : ℝ)^256 ≤ (627905248183759/625000000000000 : ℝ)^1093 := by
      have hnat : (101999782195072747573 : ℕ)^256*625000000000000^1093 ≤ 627905248183759^1093*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101999782195072747573 100000000000000000000 627905248183759 625000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627905248183759/625000000000000 : ℝ)) (X := (101999782195072747573/100000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (51999782195072747573/50000000000000000000 : ℝ) ≤ (315405248183759/312500000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (51999782195072747573/50000000000000000000 : ℝ)^256 ≤ (315405248183759/312500000000000 : ℝ)^1093 := by
      have hnat : (51999782195072747573 : ℕ)^256*312500000000000^1093 ≤ 315405248183759^1093*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51999782195072747573 50000000000000000000 315405248183759 312500000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315405248183759/312500000000000 : ℝ)) (X := (51999782195072747573/50000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(2905248183759/250000000000000 : ℝ)*(0 : ℝ))^(1093/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2905248183759/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1999782195072747573/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(2905248183759/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1093/256 : ℝ) := by
    rw [show (1 : ℝ)+(2905248183759/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(627905248183759/625000000000000 : ℝ) by norm_num, show 1+(1999782195072747573/100000000000000000000 : ℝ)+(0 : ℝ)=(101999782195072747573/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1999782195072747573/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(2905248183759/250000000000000 : ℝ)*(2/5 : ℝ))^(1093/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(2905248183759/250000000000000 : ℝ)*(2/5 : ℝ)=(315405248183759/312500000000000 : ℝ) by norm_num, show 1+2*(1999782195072747573/100000000000000000000 : ℝ)=(51999782195072747573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(2905248183759/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2905248183759/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(2905248183759/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2905248183759/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(2905248183759/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (2905248183759/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1767908063/10000000000 : ℝ)*X 0 0+(2983405889/5000000000 : ℝ)*X 0 1+(4827564043/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2746940137/5000000000 : ℝ)*X 1 0+(-1206091171/5000000000 : ℝ)*X 1 1+(482756437/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1373470133/2500000000 : ℝ)*X 2 0+(603445529/1250000000 : ℝ)*X 2 1+(-1206091091/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2084152219/5000000000 : ℝ)*X 0 0+(1551893091/5000000000 : ℝ)*X 0 1+(5553919977/10000000000 : ℝ)*X 0 2+(2084152219/5000000000 : ℝ)*X 1 0+(1551893091/5000000000 : ℝ)*X 1 1+(5553919977/10000000000 : ℝ)*X 1 2+(2084152219/5000000000 : ℝ)*X 2 0+(1551893091/5000000000 : ℝ)*X 2 1+(5553919977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1772003151/10000000000 : ℝ)*X 0 0+(1214186963/2500000000 : ℝ)*X 0 1+(2968292897/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5183009707/10000000000 : ℝ)*X 1 0+(-651580189/5000000000 : ℝ)*X 1 1+(5936585897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5183009727/10000000000 : ℝ)*X 2 0+(2968292847/5000000000 : ℝ)*X 2 1+(-130316067/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4177113467/10000000000 : ℝ)*X 0 0+(1098231103/2000000000 : ℝ)*X 0 1+(3168792217/10000000000 : ℝ)*X 0 2+(4177113467/10000000000 : ℝ)*X 1 0+(1098231103/2000000000 : ℝ)*X 1 1+(3168792217/10000000000 : ℝ)*X 1 2+(4177113467/10000000000 : ℝ)*X 2 0+(1098231103/2000000000 : ℝ)*X 2 1+(3168792217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16058882745101121/3125000000000000000000 : ℝ) := by norm_num
    linear_combination (613033223/50000000000000 : ℝ)*(base19) + (1248714953/100000000000000 : ℝ)*(base23) + (35545001/25000000000000 : ℝ)*(upper3) + (10203899/100000000000000 : ℝ)*(upper4) + (7233247/4000000000000 : ℝ)*(upper5) + (128592637909541/20000000000000 : ℝ)*(major0) + (128592637909541/20000000000000 : ℝ)*(major1) + (128592637909541/20000000000000 : ℝ)*(major2) + (5486101972947/625000000000 : ℝ)*(sp0) + (87777978471959/10000000000000 : ℝ)*(sp1) + (877779762071083/100000000000000 : ℝ)*(sp2) + (408143070446991/100000000000000 : ℝ)*(sp3) + (1173778629/25000000000000 : ℝ)*(sp4) + (2126567631/100000000000000 : ℝ)*(sp7) + (204072598507311/50000000000000 : ℝ)*(f.failure) + (219445252696509/25000000000000 : ℝ)*(f.sum) + (120469697119/2500000000000000000000000000 : ℝ)*base65 + (1682809749619/5000000000000000000000000000 : ℝ)*base67 + (16835753645381/5000000000000000000000000000 : ℝ)*base70 + (16281785369619/5000000000000000000000000000 : ℝ)*base71 + (6769046522881/2500000000000000000000000000 : ℝ)*base74 + (11261089825381/5000000000000000000000000000 : ℝ)*base76 + (2424342889619/5000000000000000000000000000 : ℝ)*base77 + (8982204429619/5000000000000000000000000000 : ℝ)*base79 + (11882522725381/2500000000000000000000000000 : ℝ)*base82 + (8186801/1000000000000000000000 : ℝ)*base89 + (8186801/1000000000000000000000 : ℝ)*base91 + (8186801/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10564623123665997064809/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (765354987/50000000000000 : ℝ)*(base19) + (1543305343/100000000000000 : ℝ)*(base23) + (9419051/5000000000000 : ℝ)*(base32) + (59686867/25000000000000 : ℝ)*(upper3) + (59004281/50000000000000 : ℝ)*(upper5) + (339164960117817/50000000000000 : ℝ)*(major0) + (339164960117817/50000000000000 : ℝ)*(major1) + (339164960117817/50000000000000 : ℝ)*(major2) + (3541697177/100000000000000 : ℝ)*(sp1) + (923028199/25000000000000 : ℝ)*(sp2) + (185212809689429/20000000000000 : ℝ)*(sp4) + (463029488019997/50000000000000 : ℝ)*(sp5) + (926058813029007/100000000000000 : ℝ)*(sp6) + (43059537826447/10000000000000 : ℝ)*(sp7) + (43059556664549/10000000000000 : ℝ)*(f.failure) + (185212809689429/20000000000000 : ℝ)*(f.sum) + (13037991534647/6250000000000000000000000000 : ℝ)*base66 + (5781776440897/12500000000000000000000000000 : ℝ)*base68 + (71871195565897/12500000000000000000000000000 : ℝ)*base70 + (59097915890897/12500000000000000000000000000 : ℝ)*base72 + (25420869784103/6250000000000000000000000000 : ℝ)*base73 + (91074820290897/12500000000000000000000000000 : ℝ)*base76 + (96380794703397/12500000000000000000000000000 : ℝ)*base78 + (166132476315897/12500000000000000000000000000 : ℝ)*base80 + (3281809240897/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1542459/200000000000000000000 : ℝ)*base89 + (1542459/200000000000000000000 : ℝ)*base91 + (1542459/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1413_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (967/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26369/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1413_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1413_s1_0 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-242817171/1250000000 : ℝ)*x 0 + (5611703329/10000000000 : ℝ)*x 1 + (2535373831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (242817171/1250000000 : ℝ)^4373 ≤ (11770072291021/100000000000000 : ℝ)^3349 := by
    have hnat : (242817171 : ℕ)^4373*100000000000000^3349 ≤ 11770072291021^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      242817171 1250000000 11770072291021 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5611703329/10000000000 : ℝ)^4373 ≤ (47030237143621/100000000000000 : ℝ)^3349 := by
    have hnat : (5611703329 : ℕ)^4373*100000000000000^3349 ≤ 47030237143621^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5611703329 10000000000 47030237143621 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2535373831/5000000000 : ℝ)^4373 ≤ (41199690544983/100000000000000 : ℝ)^3349 := by
    have hnat : (2535373831 : ℕ)^4373*100000000000000^3349 ≤ 41199690544983^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2535373831 5000000000 41199690544983 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-242817171/1250000000 : ℝ), (5611703329/10000000000 : ℝ), (2535373831/5000000000 : ℝ)] ![(11770072291021/100000000000000 : ℝ), (47030237143621/100000000000000 : ℝ), (41199690544983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-242817171/1250000000 : ℝ)|^4373 ≤ (11770072291021/100000000000000 : ℝ)^3349
        have hw : |(-242817171/1250000000 : ℝ)|=(242817171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5611703329/10000000000 : ℝ)|^4373 ≤ (47030237143621/100000000000000 : ℝ)^3349
        have hw : |(5611703329/10000000000 : ℝ)|=(5611703329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2535373831/5000000000 : ℝ)|^4373 ≤ (41199690544983/100000000000000 : ℝ)^3349
        have hw : |(2535373831/5000000000 : ℝ)|=(2535373831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s1_1 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2699211241/5000000000 : ℝ)*x 0 + (-2229539599/10000000000 : ℝ)*x 1 + (1267686201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2699211241/5000000000 : ℝ)^4373 ≤ (11177482948259/25000000000000 : ℝ)^3349 := by
    have hnat : (2699211241 : ℕ)^4373*25000000000000^3349 ≤ 11177482948259^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699211241 5000000000 11177482948259 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2229539599/10000000000 : ℝ)^4373 ≤ (14090407958007/100000000000000 : ℝ)^3349 := by
    have hnat : (2229539599 : ℕ)^4373*100000000000000^3349 ≤ 14090407958007^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229539599 10000000000 14090407958007 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1267686201/2500000000 : ℝ)^4373 ≤ (20599830111819/50000000000000 : ℝ)^3349 := by
    have hnat : (1267686201 : ℕ)^4373*50000000000000^3349 ≤ 20599830111819^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267686201 2500000000 20599830111819 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2699211241/5000000000 : ℝ), (-2229539599/10000000000 : ℝ), (1267686201/2500000000 : ℝ)] ![(11177482948259/25000000000000 : ℝ), (14090407958007/100000000000000 : ℝ), (20599830111819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2699211241/5000000000 : ℝ)|^4373 ≤ (11177482948259/25000000000000 : ℝ)^3349
        have hw : |(2699211241/5000000000 : ℝ)|=(2699211241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2229539599/10000000000 : ℝ)|^4373 ≤ (14090407958007/100000000000000 : ℝ)^3349
        have hw : |(-2229539599/10000000000 : ℝ)|=(2229539599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1267686201/2500000000 : ℝ)|^4373 ≤ (20599830111819/50000000000000 : ℝ)^3349
        have hw : |(1267686201/2500000000 : ℝ)|=(1267686201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s1_2 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269921037/500000000 : ℝ)*x 0 + (1267686921/2500000000 : ℝ)*x 1 + (-2229538181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269921037/500000000 : ℝ)^4373 ≤ (22354956477197/50000000000000 : ℝ)^3349 := by
    have hnat : (269921037 : ℕ)^4373*50000000000000^3349 ≤ 22354956477197^3349*500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269921037 500000000 22354956477197 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267686921/2500000000 : ℝ)^4373 ≤ (10299922694597/25000000000000 : ℝ)^3349 := by
    have hnat : (1267686921 : ℕ)^4373*25000000000000^3349 ≤ 10299922694597^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267686921 2500000000 10299922694597 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2229538181/10000000000 : ℝ)^4373 ≤ (14090396256309/100000000000000 : ℝ)^3349 := by
    have hnat : (2229538181 : ℕ)^4373*100000000000000^3349 ≤ 14090396256309^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2229538181 10000000000 14090396256309 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269921037/500000000 : ℝ), (1267686921/2500000000 : ℝ), (-2229538181/10000000000 : ℝ)] ![(22354956477197/50000000000000 : ℝ), (10299922694597/25000000000000 : ℝ), (14090396256309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269921037/500000000 : ℝ)|^4373 ≤ (22354956477197/50000000000000 : ℝ)^3349
        have hw : |(269921037/500000000 : ℝ)|=(269921037/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1267686921/2500000000 : ℝ)|^4373 ≤ (10299922694597/25000000000000 : ℝ)^3349
        have hw : |(1267686921/2500000000 : ℝ)|=(1267686921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2229538181/10000000000 : ℝ)|^4373 ≤ (14090396256309/100000000000000 : ℝ)^3349
        have hw : |(-2229538181/10000000000 : ℝ)|=(2229538181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s1_3 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21397723/50000000 : ℝ)*x 0 + (3733364571/10000000000 : ℝ)*x 1 + (1224196059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21397723/50000000 : ℝ)^4373 ≤ (33013578303789/100000000000000 : ℝ)^3349 := by
    have hnat : (21397723 : ℕ)^4373*100000000000000^3349 ≤ 33013578303789^3349*50000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21397723 50000000 33013578303789 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3733364571/10000000000 : ℝ)^4373 ≤ (27622601215077/100000000000000 : ℝ)^3349 := by
    have hnat : (3733364571 : ℕ)^4373*100000000000000^3349 ≤ 27622601215077^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733364571 10000000000 27622601215077 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1224196059/2500000000 : ℝ)^4373 ≤ (39363820467717/100000000000000 : ℝ)^3349 := by
    have hnat : (1224196059 : ℕ)^4373*100000000000000^3349 ≤ 39363820467717^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224196059 2500000000 39363820467717 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21397723/50000000 : ℝ), (3733364571/10000000000 : ℝ), (1224196059/2500000000 : ℝ)] ![(33013578303789/100000000000000 : ℝ), (27622601215077/100000000000000 : ℝ), (39363820467717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21397723/50000000 : ℝ)|^4373 ≤ (33013578303789/100000000000000 : ℝ)^3349
        have hw : |(21397723/50000000 : ℝ)|=(21397723/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3733364571/10000000000 : ℝ)|^4373 ≤ (27622601215077/100000000000000 : ℝ)^3349
        have hw : |(3733364571/10000000000 : ℝ)|=(3733364571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1224196059/2500000000 : ℝ)|^4373 ≤ (39363820467717/100000000000000 : ℝ)^3349
        have hw : |(1224196059/2500000000 : ℝ)|=(1224196059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s1_4 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1942957199/10000000000 : ℝ)*x 0 + (5077169027/10000000000 : ℝ)*x 1 + (1401293007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1942957199/10000000000 : ℝ)^4373 ≤ (470935760413/4000000000000 : ℝ)^3349 := by
    have hnat : (1942957199 : ℕ)^4373*4000000000000^3349 ≤ 470935760413^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942957199 10000000000 470935760413 4000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077169027/10000000000 : ℝ)^4373 ≤ (8253565969661/20000000000000 : ℝ)^3349 := by
    have hnat : (5077169027 : ℕ)^4373*20000000000000^3349 ≤ 8253565969661^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077169027 10000000000 8253565969661 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1401293007/2500000000 : ℝ)^4373 ≤ (46958776126967/100000000000000 : ℝ)^3349 := by
    have hnat : (1401293007 : ℕ)^4373*100000000000000^3349 ≤ 46958776126967^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1401293007 2500000000 46958776126967 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1942957199/10000000000 : ℝ), (5077169027/10000000000 : ℝ), (1401293007/2500000000 : ℝ)] ![(470935760413/4000000000000 : ℝ), (8253565969661/20000000000000 : ℝ), (46958776126967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1942957199/10000000000 : ℝ)|^4373 ≤ (470935760413/4000000000000 : ℝ)^3349
        have hw : |(-1942957199/10000000000 : ℝ)|=(1942957199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077169027/10000000000 : ℝ)|^4373 ≤ (8253565969661/20000000000000 : ℝ)^3349
        have hw : |(5077169027/10000000000 : ℝ)|=(5077169027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1401293007/2500000000 : ℝ)|^4373 ≤ (46958776126967/100000000000000 : ℝ)^3349
        have hw : |(1401293007/2500000000 : ℝ)|=(1401293007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s1_5 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628626593/5000000000 : ℝ)*x 0 + (-211889089/1250000000 : ℝ)*x 1 + (280258591/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628626593/5000000000 : ℝ)^4373 ≤ (21594707330279/50000000000000 : ℝ)^3349 := by
    have hnat : (2628626593 : ℕ)^4373*50000000000000^3349 ≤ 21594707330279^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628626593 5000000000 21594707330279 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211889089/1250000000 : ℝ)^4373 ≤ (4925905736367/50000000000000 : ℝ)^3349 := by
    have hnat : (211889089 : ℕ)^4373*50000000000000^3349 ≤ 4925905736367^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211889089 1250000000 4925905736367 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280258591/500000000 : ℝ)^4373 ≤ (46958773851579/100000000000000 : ℝ)^3349 := by
    have hnat : (280258591 : ℕ)^4373*100000000000000^3349 ≤ 46958773851579^3349*500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280258591 500000000 46958773851579 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628626593/5000000000 : ℝ), (-211889089/1250000000 : ℝ), (280258591/500000000 : ℝ)] ![(21594707330279/50000000000000 : ℝ), (4925905736367/50000000000000 : ℝ), (46958773851579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628626593/5000000000 : ℝ)|^4373 ≤ (21594707330279/50000000000000 : ℝ)^3349
        have hw : |(2628626593/5000000000 : ℝ)|=(2628626593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211889089/1250000000 : ℝ)|^4373 ≤ (4925905736367/50000000000000 : ℝ)^3349
        have hw : |(-211889089/1250000000 : ℝ)|=(211889089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280258591/500000000 : ℝ)|^4373 ≤ (46958773851579/100000000000000 : ℝ)^3349
        have hw : |(280258591/500000000 : ℝ)|=(280258591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s1_6 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257253861/10000000000 : ℝ)*x 0 + (1121034469/2000000000 : ℝ)*x 1 + (-847555501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257253861/10000000000 : ℝ)^4373 ≤ (21594710950679/50000000000000 : ℝ)^3349 := by
    have hnat : (5257253861 : ℕ)^4373*50000000000000^3349 ≤ 21594710950679^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257253861 10000000000 21594710950679 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121034469/2000000000 : ℝ)^4373 ≤ (23479389797373/50000000000000 : ℝ)^3349 := by
    have hnat : (1121034469 : ℕ)^4373*50000000000000^3349 ≤ 23479389797373^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121034469 2000000000 23479389797373 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (847555501/5000000000 : ℝ)^4373 ≤ (9851798495627/100000000000000 : ℝ)^3349 := by
    have hnat : (847555501 : ℕ)^4373*100000000000000^3349 ≤ 9851798495627^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847555501 5000000000 9851798495627 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257253861/10000000000 : ℝ), (1121034469/2000000000 : ℝ), (-847555501/5000000000 : ℝ)] ![(21594710950679/50000000000000 : ℝ), (23479389797373/50000000000000 : ℝ), (9851798495627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257253861/10000000000 : ℝ)|^4373 ≤ (21594710950679/50000000000000 : ℝ)^3349
        have hw : |(5257253861/10000000000 : ℝ)|=(5257253861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121034469/2000000000 : ℝ)|^4373 ≤ (23479389797373/50000000000000 : ℝ)^3349
        have hw : |(1121034469/2000000000 : ℝ)|=(1121034469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-847555501/5000000000 : ℝ)|^4373 ≤ (9851798495627/100000000000000 : ℝ)^3349
        have hw : |(-847555501/5000000000 : ℝ)|=(847555501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s1_7 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2140224189/5000000000 : ℝ)*x 0 + (2441484691/5000000000 : ℝ)*x 1 + (14989669/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2140224189/5000000000 : ℝ)^4373 ≤ (16511341182393/50000000000000 : ℝ)^3349 := by
    have hnat : (2140224189 : ℕ)^4373*50000000000000^3349 ≤ 16511341182393^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140224189 5000000000 16511341182393 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2441484691/5000000000 : ℝ)^4373 ≤ (7843774680627/20000000000000 : ℝ)^3349 := by
    have hnat : (2441484691 : ℕ)^4373*20000000000000^3349 ≤ 7843774680627^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441484691 5000000000 7843774680627 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14989669/40000000 : ℝ)^4373 ≤ (13879222106373/50000000000000 : ℝ)^3349 := by
    have hnat : (14989669 : ℕ)^4373*50000000000000^3349 ≤ 13879222106373^3349*40000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14989669 40000000 13879222106373 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2140224189/5000000000 : ℝ), (2441484691/5000000000 : ℝ), (14989669/40000000 : ℝ)] ![(16511341182393/50000000000000 : ℝ), (7843774680627/20000000000000 : ℝ), (13879222106373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2140224189/5000000000 : ℝ)|^4373 ≤ (16511341182393/50000000000000 : ℝ)^3349
        have hw : |(2140224189/5000000000 : ℝ)|=(2140224189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2441484691/5000000000 : ℝ)|^4373 ≤ (7843774680627/20000000000000 : ℝ)^3349
        have hw : |(2441484691/5000000000 : ℝ)|=(2441484691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(14989669/40000000 : ℝ)|^4373 ≤ (13879222106373/50000000000000 : ℝ)^3349
        have hw : |(14989669/40000000 : ℝ)|=(14989669/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1413_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (967/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3759/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9477/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (967/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26369/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (967/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (967/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26369/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (967/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (967/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26369/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (967/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (967/50000 : ℝ) ^ (1093/256 : ℝ) ≤ (4830280476427/100000000000000000000 : ℝ) := by
    have hpowers : (967/50000 : ℝ)^1093 ≤ (4830280476427/100000000000000000000 : ℝ)^256 := by
      have hnat : (967 : ℕ)^1093*100000000000000000000^256 ≤ 4830280476427^256*50000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        967 50000 4830280476427 100000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (967/50000 : ℝ)) (X := (4830280476427/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hpowhi : (26369/100000 : ℝ) ^ (1093/256 : ℝ) ≤ (84388117741136883/25000000000000000000 : ℝ) := by
    have hpowers : (26369/100000 : ℝ)^1093 ≤ (84388117741136883/25000000000000000000 : ℝ)^256 := by
      have hnat : (26369 : ℕ)^1093*25000000000000000000^256 ≤ 84388117741136883^256*100000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26369 100000 84388117741136883 25000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26369/100000 : ℝ)) (X := (84388117741136883/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000004830280476427/50000000000000000000 : ℝ) ≤ (2500000056566869/2500000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (50000004830280476427/50000000000000000000 : ℝ)^256 ≤ (2500000056566869/2500000000000000 : ℝ)^1093 := by
      have hnat : (50000004830280476427 : ℕ)^256*2500000000000000^1093 ≤ 2500000056566869^1093*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000004830280476427 50000000000000000000 2500000056566869 2500000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000056566869/2500000000000000 : ℝ)) (X := (50000004830280476427/50000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100337557301245023959/100000000000000000000 : ℝ) ≤ (400315839712873/400000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (100337557301245023959/100000000000000000000 : ℝ)^256 ≤ (400315839712873/400000000000000 : ℝ)^1093 := by
      have hnat : (100337557301245023959 : ℕ)^256*400000000000000^1093 ≤ 400315839712873^1093*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100337557301245023959 100000000000000000000 400315839712873 400000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400315839712873/400000000000000 : ℝ)) (X := (100337557301245023959/100000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12584388117741136883/12500000000000000000 : ℝ) ≤ (5007895879688087/5000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (12584388117741136883/12500000000000000000 : ℝ)^256 ≤ (5007895879688087/5000000000000000 : ℝ)^1093 := by
      have hnat : (12584388117741136883 : ℕ)^256*5000000000000000^1093 ≤ 5007895879688087^1093*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12584388117741136883 12500000000000000000 5007895879688087 5000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007895879688087/5000000000000000 : ℝ)) (X := (12584388117741136883/12500000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4830280476427/100000000000000000000 : ℝ) ≤ ((5089988847996115711/5090625000000000000 : ℝ)+2*(2631922184783/814500000000000 : ℝ)*(967/50000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (5089988847996115711/5090625000000000000 : ℝ)+2*(2631922184783/814500000000000 : ℝ)*(967/50000 : ℝ)=(2500000056566869/2500000000000000 : ℝ) by norm_num, show 1+2*(4830280476427/100000000000000000000 : ℝ)=(50000004830280476427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(84388117741136883/25000000000000000000 : ℝ)+(4830280476427/100000000000000000000 : ℝ) ≤ ((5089988847996115711/5090625000000000000 : ℝ)+(2631922184783/814500000000000 : ℝ)*((26369/100000 : ℝ)+(967/50000 : ℝ)))^(1093/256 : ℝ) := by
    rw [show (5089988847996115711/5090625000000000000 : ℝ)+(2631922184783/814500000000000 : ℝ)*((26369/100000 : ℝ)+(967/50000 : ℝ))=(400315839712873/400000000000000 : ℝ) by norm_num, show 1+(84388117741136883/25000000000000000000 : ℝ)+(4830280476427/100000000000000000000 : ℝ)=(100337557301245023959/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(84388117741136883/25000000000000000000 : ℝ) ≤ ((5089988847996115711/5090625000000000000 : ℝ)+2*(2631922184783/814500000000000 : ℝ)*(26369/100000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (5089988847996115711/5090625000000000000 : ℝ)+2*(2631922184783/814500000000000 : ℝ)*(26369/100000 : ℝ)=(5007895879688087/5000000000000000 : ℝ) by norm_num, show 1+2*(84388117741136883/25000000000000000000 : ℝ)=(12584388117741136883/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5089988847996115711/5090625000000000000 : ℝ)*(X 1 0+X 2 0)+(2631922184783/814500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (967/50000 : ℝ)) (hi := (26369/100000 : ℝ)) (c := (5089988847996115711/5090625000000000000 : ℝ)) (alpha := (2631922184783/814500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5089988847996115711/5090625000000000000 : ℝ)*(X 0 1+X 2 1)+(2631922184783/814500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (967/50000 : ℝ)) (hi := (26369/100000 : ℝ)) (c := (5089988847996115711/5090625000000000000 : ℝ)) (alpha := (2631922184783/814500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5089988847996115711/5090625000000000000 : ℝ)*(X 0 2+X 1 2)+(2631922184783/814500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (967/50000 : ℝ)) (hi := (26369/100000 : ℝ)) (c := (5089988847996115711/5090625000000000000 : ℝ)) (alpha := (2631922184783/814500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-242817171/1250000000 : ℝ)*X 0 0+(5611703329/10000000000 : ℝ)*X 0 1+(2535373831/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2699211241/5000000000 : ℝ)*X 1 0+(-2229539599/10000000000 : ℝ)*X 1 1+(1267686201/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((269921037/500000000 : ℝ)*X 2 0+(1267686921/2500000000 : ℝ)*X 2 1+(-2229538181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((21397723/50000000 : ℝ)*X 0 0+(3733364571/10000000000 : ℝ)*X 0 1+(1224196059/2500000000 : ℝ)*X 0 2+(21397723/50000000 : ℝ)*X 1 0+(3733364571/10000000000 : ℝ)*X 1 1+(1224196059/2500000000 : ℝ)*X 1 2+(21397723/50000000 : ℝ)*X 2 0+(3733364571/10000000000 : ℝ)*X 2 1+(1224196059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1942957199/10000000000 : ℝ)*X 0 0+(5077169027/10000000000 : ℝ)*X 0 1+(1401293007/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2628626593/5000000000 : ℝ)*X 1 0+(-211889089/1250000000 : ℝ)*X 1 1+(280258591/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257253861/10000000000 : ℝ)*X 2 0+(1121034469/2000000000 : ℝ)*X 2 1+(-847555501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2140224189/5000000000 : ℝ)*X 0 0+(2441484691/5000000000 : ℝ)*X 0 1+(14989669/40000000 : ℝ)*X 0 2+(2140224189/5000000000 : ℝ)*X 1 0+(2441484691/5000000000 : ℝ)*X 1 1+(14989669/40000000 : ℝ)*X 1 2+(2140224189/5000000000 : ℝ)*X 2 0+(2441484691/5000000000 : ℝ)*X 2 1+(14989669/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (85207313660639198629368151/10605468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (33002193/20000000000000 : ℝ)*(base1) + (1988685363/100000000000000 : ℝ)*(base19) + (1392171511/100000000000000 : ℝ)*(base23) + (89155721/100000000000000 : ℝ)*(upper3) + (588251877/100000000000000 : ℝ)*(upper5) + (84629057167271/6250000000000 : ℝ)*(major0) + (84629057167271/6250000000000 : ℝ)*(major1) + (84629057167271/6250000000000 : ℝ)*(major2) + (462145149432487/25000000000000 : ℝ)*(sp0) + (924291833418777/50000000000000 : ℝ)*(sp1) + (924292131675703/50000000000000 : ℝ)*(sp2) + (214885240202757/25000000000000 : ℝ)*(sp3) + (2611401967/50000000000000 : ℝ)*(sp4) + (1390099197/50000000000000 : ℝ)*(sp7) + (171908781204077/20000000000000 : ℝ)*(f.failure) + (924292827761459/50000000000000 : ℝ)*(f.sum) + (38701945893181/20362500000000000000000000000 : ℝ)*base66 + (92477442942580829/21210937500000000000000000000000 : ℝ)*base67 + (3173612554296199/5302734375000000000000000000000 : ℝ)*base70 + (38902577728673227/10605468750000000000000000000000 : ℝ)*base71 + (57292485961919/20362500000000000000000000000 : ℝ)*base73 + (341342660781419/1325683593750000000000000000000 : ℝ)*base75 + (2558809584922213/2651367187500000000000000000000 : ℝ)*base77 + (33305409663829477/10605468750000000000000000000000 : ℝ)*base79 + (23070088007069/20362500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2428493/400000000000000000000 : ℝ)*base90 + (2428493/400000000000000000000 : ℝ)*base92 + (2428493/400000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (447884257002463207470872689/84843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130306121/50000000000000 : ℝ)*(base1) + (1335118097/100000000000000 : ℝ)*(base19) + (1706455757/100000000000000 : ℝ)*(base23) + (85186881/100000000000000 : ℝ)*(upper3) + (2194393/800000000000 : ℝ)*(upper5) + (1387280308454351/100000000000000 : ℝ)*(major0) + (1387280308454351/100000000000000 : ℝ)*(major1) + (1387280308454351/100000000000000 : ℝ)*(major2) + (2957402471/50000000000000 : ℝ)*(sp1) + (10688074569/100000000000000 : ℝ)*(sp2) + (1893932068357683/100000000000000 : ℝ)*(sp4) + (946962278911201/50000000000000 : ℝ)*(sp5) + (946959706607557/50000000000000 : ℝ)*(sp6) + (440314186293333/50000000000000 : ℝ)*(sp7) + (220157158299727/25000000000000 : ℝ)*(f.failure) + (1893931807745441/100000000000000 : ℝ)*(f.sum) + (6752950663321/20362500000000000000000000000 : ℝ)*base66 + (217866322064232563/169687500000000000000000000000000 : ℝ)*base68 + (14480871481704937/169687500000000000000000000000000 : ℝ)*base69 + (253413268850454937/169687500000000000000000000000000 : ℝ)*base71 + (141735491108417/40725000000000000000000000000 : ℝ)*base74 + (990856798209545063/169687500000000000000000000000000 : ℝ)*base76 + (799461297877329937/169687500000000000000000000000000 : ℝ)*base77 + (321776226637329937/169687500000000000000000000000000 : ℝ)*base79 + (22948454595329/20362500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (999343/500000000000000000000 : ℝ)*base90 + (999343/500000000000000000000 : ℝ)*base92 + (999343/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1413_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26369/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (967/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3759/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9477/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1413_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1413_s2_0 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-988439627/5000000000 : ℝ)*x 0 + (170682103/312500000 : ℝ)*x 1 + (5198537923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (988439627/5000000000 : ℝ)^4373 ≤ (2408501807183/20000000000000 : ℝ)^3349 := by
    have hnat : (988439627 : ℕ)^4373*20000000000000^3349 ≤ 2408501807183^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988439627 5000000000 2408501807183 20000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (170682103/312500000 : ℝ)^4373 ≤ (45396843180573/100000000000000 : ℝ)^3349 := by
    have hnat : (170682103 : ℕ)^4373*100000000000000^3349 ≤ 45396843180573^3349*312500000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170682103 312500000 45396843180573 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5198537923/10000000000 : ℝ)^4373 ≤ (10640161941069/25000000000000 : ℝ)^3349 := by
    have hnat : (5198537923 : ℕ)^4373*25000000000000^3349 ≤ 10640161941069^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5198537923 10000000000 10640161941069 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-988439627/5000000000 : ℝ), (170682103/312500000 : ℝ), (5198537923/10000000000 : ℝ)] ![(2408501807183/20000000000000 : ℝ), (45396843180573/100000000000000 : ℝ), (10640161941069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-988439627/5000000000 : ℝ)|^4373 ≤ (2408501807183/20000000000000 : ℝ)^3349
        have hw : |(-988439627/5000000000 : ℝ)|=(988439627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(170682103/312500000 : ℝ)|^4373 ≤ (45396843180573/100000000000000 : ℝ)^3349
        have hw : |(170682103/312500000 : ℝ)|=(170682103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5198537923/10000000000 : ℝ)|^4373 ≤ (10640161941069/25000000000000 : ℝ)^3349
        have hw : |(5198537923/10000000000 : ℝ)|=(5198537923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s2_1 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361164949/10000000000 : ℝ)*x 0 + (-1056219023/5000000000 : ℝ)*x 1 + (162454309/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361164949/10000000000 : ℝ)^4373 ≤ (11076860156777/25000000000000 : ℝ)^3349 := by
    have hnat : (5361164949 : ℕ)^4373*25000000000000^3349 ≤ 11076860156777^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361164949 10000000000 11076860156777 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056219023/5000000000 : ℝ)^4373 ≤ (6565955987013/50000000000000 : ℝ)^3349 := by
    have hnat : (1056219023 : ℕ)^4373*50000000000000^3349 ≤ 6565955987013^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056219023 5000000000 6565955987013 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162454309/312500000 : ℝ)^4373 ≤ (21280323695057/50000000000000 : ℝ)^3349 := by
    have hnat : (162454309 : ℕ)^4373*50000000000000^3349 ≤ 21280323695057^3349*312500000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162454309 312500000 21280323695057 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361164949/10000000000 : ℝ), (-1056219023/5000000000 : ℝ), (162454309/312500000 : ℝ)] ![(11076860156777/25000000000000 : ℝ), (6565955987013/50000000000000 : ℝ), (21280323695057/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361164949/10000000000 : ℝ)|^4373 ≤ (11076860156777/25000000000000 : ℝ)^3349
        have hw : |(5361164949/10000000000 : ℝ)|=(5361164949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056219023/5000000000 : ℝ)|^4373 ≤ (6565955987013/50000000000000 : ℝ)^3349
        have hw : |(-1056219023/5000000000 : ℝ)|=(1056219023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162454309/312500000 : ℝ)|^4373 ≤ (21280323695057/50000000000000 : ℝ)^3349
        have hw : |(162454309/312500000 : ℝ)|=(162454309/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s2_2 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (41884099/78125000 : ℝ)*x 0 + (25992691/50000000 : ℝ)*x 1 + (-1056219001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41884099/78125000 : ℝ)^4373 ≤ (22153718818931/50000000000000 : ℝ)^3349 := by
    have hnat : (41884099 : ℕ)^4373*50000000000000^3349 ≤ 22153718818931^3349*78125000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41884099 78125000 22153718818931 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25992691/50000000 : ℝ)^4373 ≤ (42560650725499/100000000000000 : ℝ)^3349 := by
    have hnat : (25992691 : ℕ)^4373*100000000000000^3349 ≤ 42560650725499^3349*50000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25992691 50000000 42560650725499 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056219001/5000000000 : ℝ)^4373 ≤ (13131911616867/100000000000000 : ℝ)^3349 := by
    have hnat : (1056219001 : ℕ)^4373*100000000000000^3349 ≤ 13131911616867^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056219001 5000000000 13131911616867 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41884099/78125000 : ℝ), (25992691/50000000 : ℝ), (-1056219001/5000000000 : ℝ)] ![(22153718818931/50000000000000 : ℝ), (42560650725499/100000000000000 : ℝ), (13131911616867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41884099/78125000 : ℝ)|^4373 ≤ (22153718818931/50000000000000 : ℝ)^3349
        have hw : |(41884099/78125000 : ℝ)|=(41884099/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25992691/50000000 : ℝ)|^4373 ≤ (42560650725499/100000000000000 : ℝ)^3349
        have hw : |(25992691/50000000 : ℝ)|=(25992691/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1056219001/5000000000 : ℝ)|^4373 ≤ (13131911616867/100000000000000 : ℝ)^3349
        have hw : |(-1056219001/5000000000 : ℝ)|=(1056219001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s2_3 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4303744763/10000000000 : ℝ)*x 0 + (4029039219/10000000000 : ℝ)*x 1 + (919056963/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4303744763/10000000000 : ℝ)^4373 ≤ (33257557315911/100000000000000 : ℝ)^3349 := by
    have hnat : (4303744763 : ℕ)^4373*100000000000000^3349 ≤ 33257557315911^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303744763 10000000000 33257557315911 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4029039219/10000000000 : ℝ)^4373 ≤ (30513129581601/100000000000000 : ℝ)^3349 := by
    have hnat : (4029039219 : ℕ)^4373*100000000000000^3349 ≤ 30513129581601^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4029039219 10000000000 30513129581601 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919056963/2000000000 : ℝ)^4373 ≤ (1132166033823/3125000000000 : ℝ)^3349 := by
    have hnat : (919056963 : ℕ)^4373*3125000000000^3349 ≤ 1132166033823^3349*2000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919056963 2000000000 1132166033823 3125000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4303744763/10000000000 : ℝ), (4029039219/10000000000 : ℝ), (919056963/2000000000 : ℝ)] ![(33257557315911/100000000000000 : ℝ), (30513129581601/100000000000000 : ℝ), (1132166033823/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4303744763/10000000000 : ℝ)|^4373 ≤ (33257557315911/100000000000000 : ℝ)^3349
        have hw : |(4303744763/10000000000 : ℝ)|=(4303744763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4029039219/10000000000 : ℝ)|^4373 ≤ (30513129581601/100000000000000 : ℝ)^3349
        have hw : |(4029039219/10000000000 : ℝ)|=(4029039219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(919056963/2000000000 : ℝ)|^4373 ≤ (1132166033823/3125000000000 : ℝ)^3349
        have hw : |(919056963/2000000000 : ℝ)|=(919056963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s2_4 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1976927597/10000000000 : ℝ)*x 0 + (5200068937/10000000000 : ℝ)*x 1 + (5460283671/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1976927597/10000000000 : ℝ)^4373 ≤ (12042893571369/100000000000000 : ℝ)^3349 := by
    have hnat : (1976927597 : ℕ)^4373*100000000000000^3349 ≤ 12042893571369^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1976927597 10000000000 12042893571369 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5200068937/10000000000 : ℝ)^4373 ≤ (42577015554747/100000000000000 : ℝ)^3349 := by
    have hnat : (5200068937 : ℕ)^4373*100000000000000^3349 ≤ 42577015554747^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5200068937 10000000000 42577015554747 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460283671/10000000000 : ℝ)^4373 ≤ (45380090856829/100000000000000 : ℝ)^3349 := by
    have hnat : (5460283671 : ℕ)^4373*100000000000000^3349 ≤ 45380090856829^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460283671 10000000000 45380090856829 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1976927597/10000000000 : ℝ), (5200068937/10000000000 : ℝ), (5460283671/10000000000 : ℝ)] ![(12042893571369/100000000000000 : ℝ), (42577015554747/100000000000000 : ℝ), (45380090856829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1976927597/10000000000 : ℝ)|^4373 ≤ (12042893571369/100000000000000 : ℝ)^3349
        have hw : |(-1976927597/10000000000 : ℝ)|=(1976927597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5200068937/10000000000 : ℝ)|^4373 ≤ (42577015554747/100000000000000 : ℝ)^3349
        have hw : |(5200068937/10000000000 : ℝ)|=(5200068937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460283671/10000000000 : ℝ)|^4373 ≤ (45380090856829/100000000000000 : ℝ)^3349
        have hw : |(5460283671/10000000000 : ℝ)|=(5460283671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s2_5 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323201367/2500000000 : ℝ)*x 0 + (-1850692903/10000000000 : ℝ)*x 1 + (5460283403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323201367/2500000000 : ℝ)^4373 ≤ (21785590795793/50000000000000 : ℝ)^3349 := by
    have hnat : (1323201367 : ℕ)^4373*50000000000000^3349 ≤ 21785590795793^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323201367 2500000000 21785590795793 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1850692903/10000000000 : ℝ)^4373 ≤ (5524365220613/50000000000000 : ℝ)^3349 := by
    have hnat : (1850692903 : ℕ)^4373*50000000000000^3349 ≤ 5524365220613^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1850692903 10000000000 5524365220613 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460283403/10000000000 : ℝ)^4373 ≤ (45380087948461/100000000000000 : ℝ)^3349 := by
    have hnat : (5460283403 : ℕ)^4373*100000000000000^3349 ≤ 45380087948461^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460283403 10000000000 45380087948461 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323201367/2500000000 : ℝ), (-1850692903/10000000000 : ℝ), (5460283403/10000000000 : ℝ)] ![(21785590795793/50000000000000 : ℝ), (5524365220613/50000000000000 : ℝ), (45380087948461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323201367/2500000000 : ℝ)|^4373 ≤ (21785590795793/50000000000000 : ℝ)^3349
        have hw : |(1323201367/2500000000 : ℝ)|=(1323201367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1850692903/10000000000 : ℝ)|^4373 ≤ (5524365220613/50000000000000 : ℝ)^3349
        have hw : |(-1850692903/10000000000 : ℝ)|=(1850692903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460283403/10000000000 : ℝ)|^4373 ≤ (45380087948461/100000000000000 : ℝ)^3349
        have hw : |(5460283403/10000000000 : ℝ)|=(5460283403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s2_6 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132320173/250000000 : ℝ)*x 0 + (1365070847/2500000000 : ℝ)*x 1 + (-925345461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132320173/250000000 : ℝ)^4373 ≤ (21785598599741/50000000000000 : ℝ)^3349 := by
    have hnat : (132320173 : ℕ)^4373*50000000000000^3349 ≤ 21785598599741^3349*250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132320173 250000000 21785598599741 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365070847/2500000000 : ℝ)^4373 ≤ (567251097321/1250000000000 : ℝ)^3349 := by
    have hnat : (1365070847 : ℕ)^4373*1250000000000^3349 ≤ 567251097321^3349*2500000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365070847 2500000000 567251097321 1250000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (925345461/5000000000 : ℝ)^4373 ≤ (11048714998401/100000000000000 : ℝ)^3349 := by
    have hnat : (925345461 : ℕ)^4373*100000000000000^3349 ≤ 11048714998401^3349*5000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925345461 5000000000 11048714998401 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132320173/250000000 : ℝ), (1365070847/2500000000 : ℝ), (-925345461/5000000000 : ℝ)] ![(21785598599741/50000000000000 : ℝ), (567251097321/1250000000000 : ℝ), (11048714998401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132320173/250000000 : ℝ)|^4373 ≤ (21785598599741/50000000000000 : ℝ)^3349
        have hw : |(132320173/250000000 : ℝ)|=(132320173/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1365070847/2500000000 : ℝ)|^4373 ≤ (567251097321/1250000000000 : ℝ)^3349
        have hw : |(1365070847/2500000000 : ℝ)|=(1365070847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-925345461/5000000000 : ℝ)|^4373 ≤ (11048714998401/100000000000000 : ℝ)^3349
        have hw : |(-925345461/5000000000 : ℝ)|=(925345461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1413_s2_7 (p : ℝ) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537981231/1250000000 : ℝ)*x 0 + (4591992501/10000000000 : ℝ)*x 1 + (4032358591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537981231/1250000000 : ℝ)^4373 ≤ (8314654417259/25000000000000 : ℝ)^3349 := by
    have hnat : (537981231 : ℕ)^4373*25000000000000^3349 ≤ 8314654417259^3349*1250000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537981231 1250000000 8314654417259 25000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4591992501/10000000000 : ℝ)^4373 ≤ (36195423543087/100000000000000 : ℝ)^3349 := by
    have hnat : (4591992501 : ℕ)^4373*100000000000000^3349 ≤ 36195423543087^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4591992501 10000000000 36195423543087 100000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4032358591/10000000000 : ℝ)^4373 ≤ (15272979387087/50000000000000 : ℝ)^3349 := by
    have hnat : (4032358591 : ℕ)^4373*50000000000000^3349 ≤ 15272979387087^3349*10000000000^4373 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032358591 10000000000 15272979387087 50000000000000 4373 3349 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4373/1024 : ℝ)) 4373 3349 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537981231/1250000000 : ℝ), (4591992501/10000000000 : ℝ), (4032358591/10000000000 : ℝ)] ![(8314654417259/25000000000000 : ℝ), (36195423543087/100000000000000 : ℝ), (15272979387087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537981231/1250000000 : ℝ)|^4373 ≤ (8314654417259/25000000000000 : ℝ)^3349
        have hw : |(537981231/1250000000 : ℝ)|=(537981231/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4591992501/10000000000 : ℝ)|^4373 ≤ (36195423543087/100000000000000 : ℝ)^3349
        have hw : |(4591992501/10000000000 : ℝ)|=(4591992501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4032358591/10000000000 : ℝ)|^4373 ≤ (15272979387087/50000000000000 : ℝ)^3349
        have hw : |(4032358591/10000000000 : ℝ)|=(4032358591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1413_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9477/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (257/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (317/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9477/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3759/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9477/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3759/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9477/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3759/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9477/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3759/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9477/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3759/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9477/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3759/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3759/50000 : ℝ) ^ (1093/256 : ℝ) ≤ (397579284672671/25000000000000000000 : ℝ) := by
    have hpowers : (3759/50000 : ℝ)^1093 ≤ (397579284672671/25000000000000000000 : ℝ)^256 := by
      have hnat : (3759 : ℕ)^1093*25000000000000000000^256 ≤ 397579284672671^256*50000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3759 50000 397579284672671 25000000000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3759/50000 : ℝ)) (X := (397579284672671/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9477/50000 : ℝ) ^ (1093/256 : ℝ) ≤ (322018894075559/390625000000000000 : ℝ) := by
    have hpowers : (9477/50000 : ℝ)^1093 ≤ (322018894075559/390625000000000000 : ℝ)^256 := by
      have hnat : (9477 : ℕ)^1093*390625000000000000^256 ≤ 322018894075559^256*50000^1093 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9477 50000 322018894075559 390625000000000000 1093 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9477/50000 : ℝ)) (X := (322018894075559/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500397579284672671/12500000000000000000 : ℝ) ≤ (10000074495192961/10000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (12500397579284672671/12500000000000000000 : ℝ)^256 ≤ (10000074495192961/10000000000000000 : ℝ)^1093 := by
      have hnat : (12500397579284672671 : ℕ)^256*10000000000000000^1093 ≤ 10000074495192961^1093*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500397579284672671 12500000000000000000 10000074495192961 10000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000074495192961/10000000000000000 : ℝ)) (X := (12500397579284672671/12500000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25021006788505508447/25000000000000000000 : ℝ) ≤ (5000983716106039/5000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (25021006788505508447/25000000000000000000 : ℝ)^256 ≤ (5000983716106039/5000000000000000 : ℝ)^1093 := by
      have hnat : (25021006788505508447 : ℕ)^256*5000000000000000^1093 ≤ 5000983716106039^1093*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25021006788505508447 25000000000000000000 5000983716106039 5000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000983716106039/5000000000000000 : ℝ)) (X := (25021006788505508447/25000000000000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (195634518894075559/195312500000000000 : ℝ) ≤ (2000772073846239/2000000000000000 : ℝ) ^ (1093/256 : ℝ) := by
    have hpowers : (195634518894075559/195312500000000000 : ℝ)^256 ≤ (2000772073846239/2000000000000000 : ℝ)^1093 := by
      have hnat : (195634518894075559 : ℕ)^256*2000000000000000^1093 ≤ 2000772073846239^1093*195312500000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        195634518894075559 195312500000000000 2000772073846239 2000000000000000 256 1093 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000772073846239/2000000000000000 : ℝ)) (X := (195634518894075559/195312500000000000 : ℝ)) (by norm_num) 1093 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(397579284672671/25000000000000000000 : ℝ) ≤ ((1190962392979242279/1191250000000000000 : ℝ)+2*(1892937019117/1143600000000000 : ℝ)*(3759/50000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (1190962392979242279/1191250000000000000 : ℝ)+2*(1892937019117/1143600000000000 : ℝ)*(3759/50000 : ℝ)=(10000074495192961/10000000000000000 : ℝ) by norm_num, show 1+2*(397579284672671/25000000000000000000 : ℝ)=(12500397579284672671/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(322018894075559/390625000000000000 : ℝ)+(397579284672671/25000000000000000000 : ℝ) ≤ ((1190962392979242279/1191250000000000000 : ℝ)+(1892937019117/1143600000000000 : ℝ)*((9477/50000 : ℝ)+(3759/50000 : ℝ)))^(1093/256 : ℝ) := by
    rw [show (1190962392979242279/1191250000000000000 : ℝ)+(1892937019117/1143600000000000 : ℝ)*((9477/50000 : ℝ)+(3759/50000 : ℝ))=(5000983716106039/5000000000000000 : ℝ) by norm_num, show 1+(322018894075559/390625000000000000 : ℝ)+(397579284672671/25000000000000000000 : ℝ)=(25021006788505508447/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(322018894075559/390625000000000000 : ℝ) ≤ ((1190962392979242279/1191250000000000000 : ℝ)+2*(1892937019117/1143600000000000 : ℝ)*(9477/50000 : ℝ))^(1093/256 : ℝ) := by
    rw [show (1190962392979242279/1191250000000000000 : ℝ)+2*(1892937019117/1143600000000000 : ℝ)*(9477/50000 : ℝ)=(2000772073846239/2000000000000000 : ℝ) by norm_num, show 1+2*(322018894075559/390625000000000000 : ℝ)=(195634518894075559/195312500000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1190962392979242279/1191250000000000000 : ℝ)*(X 1 0+X 2 0)+(1892937019117/1143600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (3759/50000 : ℝ)) (hi := (9477/50000 : ℝ)) (c := (1190962392979242279/1191250000000000000 : ℝ)) (alpha := (1892937019117/1143600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1190962392979242279/1191250000000000000 : ℝ)*(X 0 1+X 2 1)+(1892937019117/1143600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (3759/50000 : ℝ)) (hi := (9477/50000 : ℝ)) (c := (1190962392979242279/1191250000000000000 : ℝ)) (alpha := (1892937019117/1143600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1190962392979242279/1191250000000000000 : ℝ)*(X 0 2+X 1 2)+(1892937019117/1143600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1093/256 : ℝ)) (lo := (3759/50000 : ℝ)) (hi := (9477/50000 : ℝ)) (c := (1190962392979242279/1191250000000000000 : ℝ)) (alpha := (1892937019117/1143600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-988439627/5000000000 : ℝ)*X 0 0+(170682103/312500000 : ℝ)*X 0 1+(5198537923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361164949/10000000000 : ℝ)*X 1 0+(-1056219023/5000000000 : ℝ)*X 1 1+(162454309/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((41884099/78125000 : ℝ)*X 2 0+(25992691/50000000 : ℝ)*X 2 1+(-1056219001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4303744763/10000000000 : ℝ)*X 0 0+(4029039219/10000000000 : ℝ)*X 0 1+(919056963/2000000000 : ℝ)*X 0 2+(4303744763/10000000000 : ℝ)*X 1 0+(4029039219/10000000000 : ℝ)*X 1 1+(919056963/2000000000 : ℝ)*X 1 2+(4303744763/10000000000 : ℝ)*X 2 0+(4029039219/10000000000 : ℝ)*X 2 1+(919056963/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1976927597/10000000000 : ℝ)*X 0 0+(5200068937/10000000000 : ℝ)*X 0 1+(5460283671/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323201367/2500000000 : ℝ)*X 1 0+(-1850692903/10000000000 : ℝ)*X 1 1+(5460283403/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132320173/250000000 : ℝ)*X 2 0+(1365070847/2500000000 : ℝ)*X 2 1+(-925345461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537981231/1250000000 : ℝ)*X 0 0+(4591992501/10000000000 : ℝ)*X 0 1+(4032358591/10000000000 : ℝ)*X 0 2+(537981231/1250000000 : ℝ)*X 1 0+(4591992501/10000000000 : ℝ)*X 1 1+(4032358591/10000000000 : ℝ)*X 1 2+(537981231/1250000000 : ℝ)*X 2 0+(4591992501/10000000000 : ℝ)*X 2 1+(4032358591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1413_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1194515572123164438811223/119125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1575645327/100000000000000 : ℝ)*(base19) + (1153800389/100000000000000 : ℝ)*(base23) + (120949569/100000000000000 : ℝ)*(lower2) + (290291403/100000000000000 : ℝ)*(upper3) + (13559729/12500000000000 : ℝ)*(upper5) + (5564176608293/200000000000 : ℝ)*(major0) + (5564176608293/200000000000 : ℝ)*(major1) + (5564176608293/200000000000 : ℝ)*(major2) + (949530804591807/25000000000000 : ℝ)*(sp0) + (1899069473941579/50000000000000 : ℝ)*(sp1) + (759627873945619/20000000000000 : ℝ)*(sp2) + (176602592687151/10000000000000 : ℝ)*(sp3) + (2163145157/12500000000000 : ℝ)*(sp4) + (4911822949/50000000000000 : ℝ)*(sp7) + (55188617203669/3125000000000 : ℝ)*(f.failure) + (949535130882121/25000000000000 : ℝ)*(f.sum) + (3332758568503/571800000000000000000000000 : ℝ)*base65 + (2339694025235317/357375000000000000000000000000 : ℝ)*base68 + (1001198368205317/357375000000000000000000000000 : ℝ)*base70 + (3531765735666817/357375000000000000000000000000 : ℝ)*base72 + (667597934171/571800000000000000000000000 : ℝ)*base74 + (7863889106724817/357375000000000000000000000000 : ℝ)*base76 + (1652984927839567/357375000000000000000000000000 : ℝ)*base78 + (3743094442955317/357375000000000000000000000000 : ℝ)*base80 + (13590344147123/2859000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (382379/62500000000000000000 : ℝ)*base89 + (382379/62500000000000000000 : ℝ)*base91 + (382379/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96396567682377462562682227/14890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (335379857/50000000000000 : ℝ)*(base19) + (2826903247/100000000000000 : ℝ)*(base23) + (41882727/25000000000000 : ℝ)*(upper3) + (297521199/100000000000000 : ℝ)*(lower4) + (36400977/50000000000000 : ℝ)*(upper5) + (703733306975423/25000000000000 : ℝ)*(major0) + (703733306975423/25000000000000 : ℝ)*(major1) + (703733306975423/25000000000000 : ℝ)*(major2) + (649163051/50000000000000 : ℝ)*(sp1) + (344725787/800000000000 : ℝ)*(sp2) + (1921490466087507/50000000000000 : ℝ)*(sp4) + (1921489481544599/50000000000000 : ℝ)*(sp5) + (480366876818549/12500000000000 : ℝ)*(sp6) + (893442653920157/50000000000000 : ℝ)*(sp7) + (893442653920157/50000000000000 : ℝ)*(f.failure) + (1921490466087507/50000000000000 : ℝ)*(f.sum) + (10601867645861/14295000000000000000000000000 : ℝ)*base65 + (409312694619531787/44671875000000000000000000000000 : ℝ)*base68 + (478545547813656787/44671875000000000000000000000000 : ℝ)*base70 + (268966184985438037/44671875000000000000000000000000 : ℝ)*base72 + (31865166755231/14295000000000000000000000000 : ℝ)*base73 + (577535607413406787/44671875000000000000000000000000 : ℝ)*base76 + (316619781577656787/44671875000000000000000000000000 : ℝ)*base78 + (56114771628874463/44671875000000000000000000000000 : ℝ)*base79 + (40624729241509/14295000000000000000000000000 : ℝ)*base82 + (13254787/1000000000000000000000 : ℝ)*base89 + (13254787/1000000000000000000000 : ℝ)*base91 + (13254787/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1413_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9477/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3759/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (317/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1413_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1413_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (317/2000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1413_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1413_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1413_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1093/256 : ℝ) ≤ p) (hpb : p ≤ (4373/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31506591/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (257/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (317/2000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1413_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
