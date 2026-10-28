-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:47.118011+00:00
-- url     : https://prove2.me/submissions/c8704908-7046-478b-aa9f-159f3998ffe1

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
theorem support_rectangle_w1277_s3_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098920123/10000000000 : ℝ)*x 0 + (543635899/1000000000 : ℝ)*x 1 + (5223763781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098920123/10000000000 : ℝ)^4237 ≤ (12761814922129/100000000000000 : ℝ)^3213 := by
    have hnat : (2098920123 : ℕ)^4237*100000000000000^3213 ≤ 12761814922129^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098920123 10000000000 12761814922129 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543635899/1000000000 : ℝ)^4237 ≤ (44766118055453/100000000000000 : ℝ)^3213 := by
    have hnat : (543635899 : ℕ)^4237*100000000000000^3213 ≤ 44766118055453^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543635899 1000000000 44766118055453 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223763781/10000000000 : ℝ)^4237 ≤ (42472067004363/100000000000000 : ℝ)^3213 := by
    have hnat : (5223763781 : ℕ)^4237*100000000000000^3213 ≤ 42472067004363^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223763781 10000000000 42472067004363 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098920123/10000000000 : ℝ), (543635899/1000000000 : ℝ), (5223763781/10000000000 : ℝ)] ![(12761814922129/100000000000000 : ℝ), (44766118055453/100000000000000 : ℝ), (42472067004363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098920123/10000000000 : ℝ)|^4237 ≤ (12761814922129/100000000000000 : ℝ)^3213
        have hw : |(-2098920123/10000000000 : ℝ)|=(2098920123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543635899/1000000000 : ℝ)|^4237 ≤ (44766118055453/100000000000000 : ℝ)^3213
        have hw : |(543635899/1000000000 : ℝ)|=(543635899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223763781/10000000000 : ℝ)|^4237 ≤ (42472067004363/100000000000000 : ℝ)^3213
        have hw : |(5223763781/10000000000 : ℝ)|=(5223763781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s3_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267756653/500000000 : ℝ)*x 0 + (-551943661/2500000000 : ℝ)*x 1 + (163242623/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267756653/500000000 : ℝ)^4237 ≤ (43886194499611/100000000000000 : ℝ)^3213 := by
    have hnat : (267756653 : ℕ)^4237*100000000000000^3213 ≤ 43886194499611^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267756653 500000000 43886194499611 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (551943661/2500000000 : ℝ)^4237 ≤ (13641736812963/100000000000000 : ℝ)^3213 := by
    have hnat : (551943661 : ℕ)^4237*100000000000000^3213 ≤ 13641736812963^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551943661 2500000000 13641736812963 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163242623/312500000 : ℝ)^4237 ≤ (21236034333121/50000000000000 : ℝ)^3213 := by
    have hnat : (163242623 : ℕ)^4237*50000000000000^3213 ≤ 21236034333121^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163242623 312500000 21236034333121 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267756653/500000000 : ℝ), (-551943661/2500000000 : ℝ), (163242623/312500000 : ℝ)] ![(43886194499611/100000000000000 : ℝ), (13641736812963/100000000000000 : ℝ), (21236034333121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267756653/500000000 : ℝ)|^4237 ≤ (43886194499611/100000000000000 : ℝ)^3213
        have hw : |(267756653/500000000 : ℝ)|=(267756653/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-551943661/2500000000 : ℝ)|^4237 ≤ (13641736812963/100000000000000 : ℝ)^3213
        have hw : |(-551943661/2500000000 : ℝ)|=(551943661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163242623/312500000 : ℝ)|^4237 ≤ (21236034333121/50000000000000 : ℝ)^3213
        have hw : |(163242623/312500000 : ℝ)|=(163242623/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s3_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677566543/5000000000 : ℝ)*x 0 + (1305940917/2500000000 : ℝ)*x 1 + (-2207774963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677566543/5000000000 : ℝ)^4237 ≤ (43886194780593/100000000000000 : ℝ)^3213 := by
    have hnat : (2677566543 : ℕ)^4237*100000000000000^3213 ≤ 43886194780593^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677566543 5000000000 43886194780593 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305940917/2500000000 : ℝ)^4237 ≤ (53090082241/125000000000 : ℝ)^3213 := by
    have hnat : (1305940917 : ℕ)^4237*125000000000^3213 ≤ 53090082241^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305940917 2500000000 53090082241 125000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207774963/10000000000 : ℝ)^4237 ≤ (2728347882449/20000000000000 : ℝ)^3213 := by
    have hnat : (2207774963 : ℕ)^4237*20000000000000^3213 ≤ 2728347882449^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207774963 10000000000 2728347882449 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677566543/5000000000 : ℝ), (1305940917/2500000000 : ℝ), (-2207774963/10000000000 : ℝ)] ![(43886194780593/100000000000000 : ℝ), (53090082241/125000000000 : ℝ), (2728347882449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677566543/5000000000 : ℝ)|^4237 ≤ (43886194780593/100000000000000 : ℝ)^3213
        have hw : |(2677566543/5000000000 : ℝ)|=(2677566543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305940917/2500000000 : ℝ)|^4237 ≤ (53090082241/125000000000 : ℝ)^3213
        have hw : |(1305940917/2500000000 : ℝ)|=(1305940917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207774963/10000000000 : ℝ)|^4237 ≤ (2728347882449/20000000000000 : ℝ)^3213
        have hw : |(-2207774963/10000000000 : ℝ)|=(2207774963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s3_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342363353/10000000000 : ℝ)*x 0 + (1032593049/2500000000 : ℝ)*x 1 + (4564803199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342363353/10000000000 : ℝ)^4237 ≤ (4160807233131/12500000000000 : ℝ)^3213 := by
    have hnat : (4342363353 : ℕ)^4237*12500000000000^3213 ≤ 4160807233131^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342363353 10000000000 4160807233131 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1032593049/2500000000 : ℝ)^4237 ≤ (1246415710431/4000000000000 : ℝ)^3213 := by
    have hnat : (1032593049 : ℕ)^4237*4000000000000^3213 ≤ 1246415710431^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032593049 2500000000 1246415710431 4000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4564803199/10000000000 : ℝ)^4237 ≤ (35553149362423/100000000000000 : ℝ)^3213 := by
    have hnat : (4564803199 : ℕ)^4237*100000000000000^3213 ≤ 35553149362423^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4564803199 10000000000 35553149362423 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342363353/10000000000 : ℝ), (1032593049/2500000000 : ℝ), (4564803199/10000000000 : ℝ)] ![(4160807233131/12500000000000 : ℝ), (1246415710431/4000000000000 : ℝ), (35553149362423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342363353/10000000000 : ℝ)|^4237 ≤ (4160807233131/12500000000000 : ℝ)^3213
        have hw : |(4342363353/10000000000 : ℝ)|=(4342363353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1032593049/2500000000 : ℝ)|^4237 ≤ (1246415710431/4000000000000 : ℝ)^3213
        have hw : |(1032593049/2500000000 : ℝ)|=(1032593049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4564803199/10000000000 : ℝ)|^4237 ≤ (35553149362423/100000000000000 : ℝ)^3213
        have hw : |(4564803199/10000000000 : ℝ)|=(4564803199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s3_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-262367979/1250000000 : ℝ)*x 0 + (1044937891/2000000000 : ℝ)*x 1 + (2717713727/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262367979/1250000000 : ℝ)^4237 ≤ (12762005020453/100000000000000 : ℝ)^3213 := by
    have hnat : (262367979 : ℕ)^4237*100000000000000^3213 ≤ 12762005020453^3213*1250000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262367979 1250000000 12762005020453 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044937891/2000000000 : ℝ)^4237 ≤ (8496398434783/20000000000000 : ℝ)^3213 := by
    have hnat : (1044937891 : ℕ)^4237*20000000000000^3213 ≤ 8496398434783^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044937891 2000000000 8496398434783 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717713727/5000000000 : ℝ)^4237 ≤ (11189000700143/25000000000000 : ℝ)^3213 := by
    have hnat : (2717713727 : ℕ)^4237*25000000000000^3213 ≤ 11189000700143^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717713727 5000000000 11189000700143 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262367979/1250000000 : ℝ), (1044937891/2000000000 : ℝ), (2717713727/5000000000 : ℝ)] ![(12762005020453/100000000000000 : ℝ), (8496398434783/20000000000000 : ℝ), (11189000700143/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262367979/1250000000 : ℝ)|^4237 ≤ (12762005020453/100000000000000 : ℝ)^3213
        have hw : |(-262367979/1250000000 : ℝ)|=(262367979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044937891/2000000000 : ℝ)|^4237 ≤ (8496398434783/20000000000000 : ℝ)^3213
        have hw : |(1044937891/2000000000 : ℝ)|=(1044937891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717713727/5000000000 : ℝ)|^4237 ≤ (11189000700143/25000000000000 : ℝ)^3213
        have hw : |(2717713727/5000000000 : ℝ)|=(2717713727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s3_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530080267/1000000000 : ℝ)*x 0 + (-99805543/500000000 : ℝ)*x 1 + (2717713691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530080267/1000000000 : ℝ)^4237 ≤ (10824999272469/25000000000000 : ℝ)^3213 := by
    have hnat : (530080267 : ℕ)^4237*25000000000000^3213 ≤ 10824999272469^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530080267 1000000000 10824999272469 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99805543/500000000 : ℝ)^4237 ≤ (5972000441943/50000000000000 : ℝ)^3213 := by
    have hnat : (99805543 : ℕ)^4237*50000000000000^3213 ≤ 5972000441943^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99805543 500000000 5972000441943 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717713691/5000000000 : ℝ)^4237 ≤ (2797250126173/6250000000000 : ℝ)^3213 := by
    have hnat : (2717713691 : ℕ)^4237*6250000000000^3213 ≤ 2797250126173^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717713691 5000000000 2797250126173 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530080267/1000000000 : ℝ), (-99805543/500000000 : ℝ), (2717713691/5000000000 : ℝ)] ![(10824999272469/25000000000000 : ℝ), (5972000441943/50000000000000 : ℝ), (2797250126173/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530080267/1000000000 : ℝ)|^4237 ≤ (10824999272469/25000000000000 : ℝ)^3213
        have hw : |(530080267/1000000000 : ℝ)|=(530080267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99805543/500000000 : ℝ)|^4237 ≤ (5972000441943/50000000000000 : ℝ)^3213
        have hw : |(-99805543/500000000 : ℝ)|=(99805543/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717713691/5000000000 : ℝ)|^4237 ≤ (2797250126173/6250000000000 : ℝ)^3213
        have hw : |(2717713691/5000000000 : ℝ)|=(2717713691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s3_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212032107/400000000 : ℝ)*x 0 + (5435427367/10000000000 : ℝ)*x 1 + (-1996110873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212032107/400000000 : ℝ)^4237 ≤ (5412499642967/12500000000000 : ℝ)^3213 := by
    have hnat : (212032107 : ℕ)^4237*12500000000000^3213 ≤ 5412499642967^3213*400000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212032107 400000000 5412499642967 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435427367/10000000000 : ℝ)^4237 ≤ (11189000463973/25000000000000 : ℝ)^3213 := by
    have hnat : (5435427367 : ℕ)^4237*25000000000000^3213 ≤ 11189000463973^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435427367 10000000000 11189000463973 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1996110873/10000000000 : ℝ)^4237 ≤ (373250030827/3125000000000 : ℝ)^3213 := by
    have hnat : (1996110873 : ℕ)^4237*3125000000000^3213 ≤ 373250030827^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996110873 10000000000 373250030827 3125000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212032107/400000000 : ℝ), (5435427367/10000000000 : ℝ), (-1996110873/10000000000 : ℝ)] ![(5412499642967/12500000000000 : ℝ), (11189000463973/25000000000000 : ℝ), (373250030827/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212032107/400000000 : ℝ)|^4237 ≤ (5412499642967/12500000000000 : ℝ)^3213
        have hw : |(212032107/400000000 : ℝ)|=(212032107/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435427367/10000000000 : ℝ)|^4237 ≤ (11189000463973/25000000000000 : ℝ)^3213
        have hw : |(5435427367/10000000000 : ℝ)|=(5435427367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1996110873/10000000000 : ℝ)|^4237 ≤ (373250030827/3125000000000 : ℝ)^3213
        have hw : |(-1996110873/10000000000 : ℝ)|=(1996110873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s3_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4342411397/10000000000 : ℝ)*x 0 + (4562911427/10000000000 : ℝ)*x 1 + (4132276149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342411397/10000000000 : ℝ)^4237 ≤ (8321735880353/25000000000000 : ℝ)^3213 := by
    have hnat : (4342411397 : ℕ)^4237*25000000000000^3213 ≤ 8321735880353^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342411397 10000000000 8321735880353 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4562911427/10000000000 : ℝ)^4237 ≤ (35533720656893/100000000000000 : ℝ)^3213 := by
    have hnat : (4562911427 : ℕ)^4237*100000000000000^3213 ≤ 35533720656893^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562911427 10000000000 35533720656893 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132276149/10000000000 : ℝ)^4237 ≤ (7794833949289/25000000000000 : ℝ)^3213 := by
    have hnat : (4132276149 : ℕ)^4237*25000000000000^3213 ≤ 7794833949289^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132276149 10000000000 7794833949289 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342411397/10000000000 : ℝ), (4562911427/10000000000 : ℝ), (4132276149/10000000000 : ℝ)] ![(8321735880353/25000000000000 : ℝ), (35533720656893/100000000000000 : ℝ), (7794833949289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342411397/10000000000 : ℝ)|^4237 ≤ (8321735880353/25000000000000 : ℝ)^3213
        have hw : |(4342411397/10000000000 : ℝ)|=(4342411397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4562911427/10000000000 : ℝ)|^4237 ≤ (35533720656893/100000000000000 : ℝ)^3213
        have hw : |(4562911427/10000000000 : ℝ)|=(4562911427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132276149/10000000000 : ℝ)|^4237 ≤ (7794833949289/25000000000000 : ℝ)^3213
        have hw : |(4132276149/10000000000 : ℝ)|=(4132276149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1059/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16387/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9393/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16387/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9393/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16387/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9393/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9393/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (225341080090521/4000000000000000000 : ℝ) := by
    have hpowers : (9393/100000 : ℝ)^1059 ≤ (225341080090521/4000000000000000000 : ℝ)^256 := by
      have hnat : (9393 : ℕ)^1059*4000000000000000000^256 ≤ 225341080090521^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9393 100000 225341080090521 4000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9393/100000 : ℝ)) (X := (225341080090521/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16387/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (28156272931625993/50000000000000000000 : ℝ) := by
    have hpowers : (16387/100000 : ℝ)^1059 ≤ (28156272931625993/50000000000000000000 : ℝ)^256 := by
      have hnat : (16387 : ℕ)^1059*50000000000000000000^256 ≤ 28156272931625993^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16387 100000 28156272931625993 50000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16387/100000 : ℝ)) (X := (28156272931625993/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000225341080090521/2000000000000000000 : ℝ) ≤ (5000136177649767/5000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (2000225341080090521/2000000000000000000 : ℝ)^256 ≤ (5000136177649767/5000000000000000 : ℝ)^1059 := by
      have hnat : (2000225341080090521 : ℕ)^256*5000000000000000^1059 ≤ 5000136177649767^1059*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000225341080090521 2000000000000000000 5000136177649767 5000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000136177649767/5000000000000000 : ℝ)) (X := (2000225341080090521/2000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100061946072865515011/100000000000000000000 : ℝ) ≤ (10001497117242527/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (100061946072865515011/100000000000000000000 : ℝ)^256 ≤ (10001497117242527/10000000000000000 : ℝ)^1059 := by
      have hnat : (100061946072865515011 : ℕ)^256*10000000000000000^1059 ≤ 10001497117242527^1059*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100061946072865515011 100000000000000000000 10001497117242527 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001497117242527/10000000000000000 : ℝ)) (X := (100061946072865515011/100000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25028156272931625993/25000000000000000000 : ℝ) ≤ (125034023489819/125000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (25028156272931625993/25000000000000000000 : ℝ)^256 ≤ (125034023489819/125000000000000 : ℝ)^1059 := by
      have hnat : (25028156272931625993 : ℕ)^256*125000000000000^1059 ≤ 125034023489819^1059*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028156272931625993 25000000000000000000 125034023489819 125000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125034023489819/125000000000000 : ℝ)) (X := (25028156272931625993/25000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(225341080090521/4000000000000000000 : ℝ) ≤ ((34959448237551937149/34970000000000000000 : ℝ)+2*(1224761942993/699400000000000 : ℝ)*(9393/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (34959448237551937149/34970000000000000000 : ℝ)+2*(1224761942993/699400000000000 : ℝ)*(9393/100000 : ℝ)=(5000136177649767/5000000000000000 : ℝ) by norm_num, show 1+2*(225341080090521/4000000000000000000 : ℝ)=(2000225341080090521/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28156272931625993/50000000000000000000 : ℝ)+(225341080090521/4000000000000000000 : ℝ) ≤ ((34959448237551937149/34970000000000000000 : ℝ)+(1224761942993/699400000000000 : ℝ)*((16387/100000 : ℝ)+(9393/100000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (34959448237551937149/34970000000000000000 : ℝ)+(1224761942993/699400000000000 : ℝ)*((16387/100000 : ℝ)+(9393/100000 : ℝ))=(10001497117242527/10000000000000000 : ℝ) by norm_num, show 1+(28156272931625993/50000000000000000000 : ℝ)+(225341080090521/4000000000000000000 : ℝ)=(100061946072865515011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28156272931625993/50000000000000000000 : ℝ) ≤ ((34959448237551937149/34970000000000000000 : ℝ)+2*(1224761942993/699400000000000 : ℝ)*(16387/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (34959448237551937149/34970000000000000000 : ℝ)+2*(1224761942993/699400000000000 : ℝ)*(16387/100000 : ℝ)=(125034023489819/125000000000000 : ℝ) by norm_num, show 1+2*(28156272931625993/50000000000000000000 : ℝ)=(25028156272931625993/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34959448237551937149/34970000000000000000 : ℝ)*(X 1 0+X 2 0)+(1224761942993/699400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (9393/100000 : ℝ)) (hi := (16387/100000 : ℝ)) (c := (34959448237551937149/34970000000000000000 : ℝ)) (alpha := (1224761942993/699400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34959448237551937149/34970000000000000000 : ℝ)*(X 0 1+X 2 1)+(1224761942993/699400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (9393/100000 : ℝ)) (hi := (16387/100000 : ℝ)) (c := (34959448237551937149/34970000000000000000 : ℝ)) (alpha := (1224761942993/699400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34959448237551937149/34970000000000000000 : ℝ)*(X 0 2+X 1 2)+(1224761942993/699400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (9393/100000 : ℝ)) (hi := (16387/100000 : ℝ)) (c := (34959448237551937149/34970000000000000000 : ℝ)) (alpha := (1224761942993/699400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2098920123/10000000000 : ℝ)*X 0 0+(543635899/1000000000 : ℝ)*X 0 1+(5223763781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267756653/500000000 : ℝ)*X 1 0+(-551943661/2500000000 : ℝ)*X 1 1+(163242623/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677566543/5000000000 : ℝ)*X 2 0+(1305940917/2500000000 : ℝ)*X 2 1+(-2207774963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4342363353/10000000000 : ℝ)*X 0 0+(1032593049/2500000000 : ℝ)*X 0 1+(4564803199/10000000000 : ℝ)*X 0 2+(4342363353/10000000000 : ℝ)*X 1 0+(1032593049/2500000000 : ℝ)*X 1 1+(4564803199/10000000000 : ℝ)*X 1 2+(4342363353/10000000000 : ℝ)*X 2 0+(1032593049/2500000000 : ℝ)*X 2 1+(4564803199/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-262367979/1250000000 : ℝ)*X 0 0+(1044937891/2000000000 : ℝ)*X 0 1+(2717713727/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530080267/1000000000 : ℝ)*X 1 0+(-99805543/500000000 : ℝ)*X 1 1+(2717713691/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212032107/400000000 : ℝ)*X 2 0+(5435427367/10000000000 : ℝ)*X 2 1+(-1996110873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342411397/10000000000 : ℝ)*X 0 0+(4562911427/10000000000 : ℝ)*X 0 1+(4132276149/10000000000 : ℝ)*X 0 2+(4342411397/10000000000 : ℝ)*X 1 0+(4562911427/10000000000 : ℝ)*X 1 1+(4132276149/10000000000 : ℝ)*X 1 2+(4342411397/10000000000 : ℝ)*X 2 0+(4562911427/10000000000 : ℝ)*X 2 1+(4132276149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (977708788207880852866669521/174850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50810697/6250000000000 : ℝ)*(base19) + (20496273/2500000000000 : ℝ)*(base23) + (7666823/12500000000000 : ℝ)*(lower2) + (323520647/100000000000000 : ℝ)*(upper3) + (52788921/100000000000000 : ℝ)*(lower4) + (350283608508019/10000000000000 : ℝ)*(major0) + (350283608508019/10000000000000 : ℝ)*(major1) + (350283608508019/10000000000000 : ℝ)*(major2) + (4703790753117909/100000000000000 : ℝ)*(sp0) + (1175949111230037/25000000000000 : ℝ)*(sp1) + (235189821902019/5000000000000 : ℝ)*(sp2) + (2301866060845479/100000000000000 : ℝ)*(sp3) + (6504773391/100000000000000 : ℝ)*(sp4) + (541564599/6250000000000 : ℝ)*(sp7) + (287734340734883/12500000000000 : ℝ)*(f.failure) + (47037972578913/1000000000000 : ℝ)*(f.sum) + (2781779860537/699400000000000000000000000 : ℝ)*base66 + (1350466298763947831/349700000000000000000000000000000 : ℝ)*base67 + (6165801827927847831/349700000000000000000000000000000 : ℝ)*base69 + (3054704508188347831/349700000000000000000000000000000 : ℝ)*base71 + (485343512313/3497000000000000000000000000 : ℝ)*base74 + (1908046233803347831/349700000000000000000000000000000 : ℝ)*base75 + (1541510714128347831/349700000000000000000000000000000 : ℝ)*base77 + (4177276731021447831/349700000000000000000000000000000 : ℝ)*base79 + (3679335339779/1748500000000000000000000000 : ℝ)*base81 + (2342471/250000000000000000000 : ℝ)*base89 + (2342471/250000000000000000000 : ℝ)*base91 + (2342471/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72318117719184465836601/8742500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1869260309/100000000000000 : ℝ)*(base19) + (487645561/25000000000000 : ℝ)*(base23) + (17888329/10000000000000 : ℝ)*(upper3) + (39584399/100000000000000 : ℝ)*(lower4) + (10581779/5000000000000 : ℝ)*(upper5) + (1766844838648493/50000000000000 : ℝ)*(major0) + (1766844838648493/50000000000000 : ℝ)*(major1) + (1766844838648493/50000000000000 : ℝ)*(major2) + (30245586341/100000000000000 : ℝ)*(sp1) + (30457268309/100000000000000 : ℝ)*(sp2) + (949045807647121/20000000000000 : ℝ)*(sp4) + (2372598461694477/50000000000000 : ℝ)*(sp5) + (4745196630385051/100000000000000 : ℝ)*(sp6) + (580537510156107/25000000000000 : ℝ)*(sp7) + (580537510156107/25000000000000 : ℝ)*(f.failure) + (949045807647121/20000000000000 : ℝ)*(f.sum) + (1434856857111/17485000000000000000000000000 : ℝ)*base66 + (2951660754986483543/1748500000000000000000000000000000 : ℝ)*base68 + (7149080849119983543/1748500000000000000000000000000000 : ℝ)*base70 + (1319370479948983543/1748500000000000000000000000000000 : ℝ)*base72 + (47273227310229/17485000000000000000000000000 : ℝ)*base73 + (1662245471781016457/1748500000000000000000000000000000 : ℝ)*base75 + (882441505339516457/1748500000000000000000000000000000 : ℝ)*base77 + (11410443314794516457/1748500000000000000000000000000000 : ℝ)*base79 + (81229282665221/17485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (121841/500000000000000000000 : ℝ)*base90 + (121841/500000000000000000000 : ℝ)*base92 + (121841/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1277_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1059/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1277_s4_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2101002331/10000000000 : ℝ)*x 0 + (5420109999/10000000000 : ℝ)*x 1 + (1047729743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101002331/10000000000 : ℝ)^4237 ≤ (199664259937/1562500000000 : ℝ)^3213 := by
    have hnat : (2101002331 : ℕ)^4237*1562500000000^3213 ≤ 199664259937^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101002331 10000000000 199664259937 1562500000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420109999/10000000000 : ℝ)^4237 ≤ (44589754680241/100000000000000 : ℝ)^3213 := by
    have hnat : (5420109999 : ℕ)^4237*100000000000000^3213 ≤ 44589754680241^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420109999 10000000000 44589754680241 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047729743/2000000000 : ℝ)^4237 ≤ (4263173267417/10000000000000 : ℝ)^3213 := by
    have hnat : (1047729743 : ℕ)^4237*10000000000000^3213 ≤ 4263173267417^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047729743 2000000000 4263173267417 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2101002331/10000000000 : ℝ), (5420109999/10000000000 : ℝ), (1047729743/2000000000 : ℝ)] ![(199664259937/1562500000000 : ℝ), (44589754680241/100000000000000 : ℝ), (4263173267417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2101002331/10000000000 : ℝ)|^4237 ≤ (199664259937/1562500000000 : ℝ)^3213
        have hw : |(-2101002331/10000000000 : ℝ)|=(2101002331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420109999/10000000000 : ℝ)|^4237 ≤ (44589754680241/100000000000000 : ℝ)^3213
        have hw : |(5420109999/10000000000 : ℝ)|=(5420109999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047729743/2000000000 : ℝ)|^4237 ≤ (4263173267417/10000000000000 : ℝ)^3213
        have hw : |(1047729743/2000000000 : ℝ)|=(1047729743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s4_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351037307/10000000000 : ℝ)*x 0 + (-2193596783/10000000000 : ℝ)*x 1 + (2619324327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351037307/10000000000 : ℝ)^4237 ≤ (2192096853381/5000000000000 : ℝ)^3213 := by
    have hnat : (5351037307 : ℕ)^4237*5000000000000^3213 ≤ 2192096853381^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351037307 10000000000 2192096853381 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193596783/10000000000 : ℝ)^4237 ≤ (6763165448301/50000000000000 : ℝ)^3213 := by
    have hnat : (2193596783 : ℕ)^4237*50000000000000^3213 ≤ 6763165448301^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193596783 10000000000 6763165448301 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619324327/5000000000 : ℝ)^4237 ≤ (42631732019547/100000000000000 : ℝ)^3213 := by
    have hnat : (2619324327 : ℕ)^4237*100000000000000^3213 ≤ 42631732019547^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619324327 5000000000 42631732019547 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351037307/10000000000 : ℝ), (-2193596783/10000000000 : ℝ), (2619324327/5000000000 : ℝ)] ![(2192096853381/5000000000000 : ℝ), (6763165448301/50000000000000 : ℝ), (42631732019547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351037307/10000000000 : ℝ)|^4237 ≤ (2192096853381/5000000000000 : ℝ)^3213
        have hw : |(5351037307/10000000000 : ℝ)|=(5351037307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193596783/10000000000 : ℝ)|^4237 ≤ (6763165448301/50000000000000 : ℝ)^3213
        have hw : |(-2193596783/10000000000 : ℝ)|=(2193596783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619324327/5000000000 : ℝ)|^4237 ≤ (42631732019547/100000000000000 : ℝ)^3213
        have hw : |(2619324327/5000000000 : ℝ)|=(2619324327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s4_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337759257/2500000000 : ℝ)*x 0 + (2619324443/5000000000 : ℝ)*x 1 + (-137099803/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337759257/2500000000 : ℝ)^4237 ≤ (43841934053201/100000000000000 : ℝ)^3213 := by
    have hnat : (1337759257 : ℕ)^4237*100000000000000^3213 ≤ 43841934053201^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337759257 2500000000 43841934053201 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619324443/5000000000 : ℝ)^4237 ≤ (2131586725463/5000000000000 : ℝ)^3213 := by
    have hnat : (2619324443 : ℕ)^4237*5000000000000^3213 ≤ 2131586725463^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619324443 5000000000 2131586725463 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137099803/625000000 : ℝ)^4237 ≤ (270526628503/2000000000000 : ℝ)^3213 := by
    have hnat : (137099803 : ℕ)^4237*2000000000000^3213 ≤ 270526628503^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137099803 625000000 270526628503 2000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337759257/2500000000 : ℝ), (2619324443/5000000000 : ℝ), (-137099803/625000000 : ℝ)] ![(43841934053201/100000000000000 : ℝ), (2131586725463/5000000000000 : ℝ), (270526628503/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337759257/2500000000 : ℝ)|^4237 ≤ (43841934053201/100000000000000 : ℝ)^3213
        have hw : |(1337759257/2500000000 : ℝ)|=(1337759257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619324443/5000000000 : ℝ)|^4237 ≤ (2131586725463/5000000000000 : ℝ)^3213
        have hw : |(2619324443/5000000000 : ℝ)|=(2619324443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137099803/625000000 : ℝ)|^4237 ≤ (270526628503/2000000000000 : ℝ)^3213
        have hw : |(-137099803/625000000 : ℝ)|=(137099803/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s4_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171810383/5000000000 : ℝ)*x 0 + (832404841/2000000000 : ℝ)*x 1 + (35412761/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171810383/5000000000 : ℝ)^4237 ≤ (33299169082391/100000000000000 : ℝ)^3213 := by
    have hnat : (2171810383 : ℕ)^4237*100000000000000^3213 ≤ 33299169082391^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171810383 5000000000 33299169082391 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832404841/2000000000 : ℝ)^4237 ≤ (15737834721863/50000000000000 : ℝ)^3213 := by
    have hnat : (832404841 : ℕ)^4237*50000000000000^3213 ≤ 15737834721863^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832404841 2000000000 15737834721863 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35412761/78125000 : ℝ)^4237 ≤ (17612580731033/50000000000000 : ℝ)^3213 := by
    have hnat : (35412761 : ℕ)^4237*50000000000000^3213 ≤ 17612580731033^3213*78125000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35412761 78125000 17612580731033 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171810383/5000000000 : ℝ), (832404841/2000000000 : ℝ), (35412761/78125000 : ℝ)] ![(33299169082391/100000000000000 : ℝ), (15737834721863/50000000000000 : ℝ), (17612580731033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171810383/5000000000 : ℝ)|^4237 ≤ (33299169082391/100000000000000 : ℝ)^3213
        have hw : |(2171810383/5000000000 : ℝ)|=(2171810383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(832404841/2000000000 : ℝ)|^4237 ≤ (15737834721863/50000000000000 : ℝ)^3213
        have hw : |(832404841/2000000000 : ℝ)|=(832404841/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35412761/78125000 : ℝ)|^4237 ≤ (17612580731033/50000000000000 : ℝ)^3213
        have hw : |(35412761/78125000 : ℝ)|=(35412761/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s4_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-84040697/400000000 : ℝ)*x 0 + (523932379/1000000000 : ℝ)*x 1 + (338714439/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84040697/400000000 : ℝ)^4237 ≤ (798664606097/6250000000000 : ℝ)^3213 := by
    have hnat : (84040697 : ℕ)^4237*6250000000000^3213 ≤ 798664606097^3213*400000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84040697 400000000 798664606097 6250000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523932379/1000000000 : ℝ)^4237 ≤ (42638977407231/100000000000000 : ℝ)^3213 := by
    have hnat : (523932379 : ℕ)^4237*100000000000000^3213 ≤ 42638977407231^3213*1000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523932379 1000000000 42638977407231 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338714439/625000000 : ℝ)^4237 ≤ (1783295555269/4000000000000 : ℝ)^3213 := by
    have hnat : (338714439 : ℕ)^4237*4000000000000^3213 ≤ 1783295555269^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338714439 625000000 1783295555269 4000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-84040697/400000000 : ℝ), (523932379/1000000000 : ℝ), (338714439/625000000 : ℝ)] ![(798664606097/6250000000000 : ℝ), (42638977407231/100000000000000 : ℝ), (1783295555269/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-84040697/400000000 : ℝ)|^4237 ≤ (798664606097/6250000000000 : ℝ)^3213
        have hw : |(-84040697/400000000 : ℝ)|=(84040697/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523932379/1000000000 : ℝ)|^4237 ≤ (42638977407231/100000000000000 : ℝ)^3213
        have hw : |(523932379/1000000000 : ℝ)|=(523932379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338714439/625000000 : ℝ)|^4237 ≤ (1783295555269/4000000000000 : ℝ)^3213
        have hw : |(338714439/625000000 : ℝ)|=(338714439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s4_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304667387/10000000000 : ℝ)*x 0 + (-100640717/500000000 : ℝ)*x 1 + (2709715559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304667387/10000000000 : ℝ)^4237 ≤ (43341632429477/100000000000000 : ℝ)^3213 := by
    have hnat : (5304667387 : ℕ)^4237*100000000000000^3213 ≤ 43341632429477^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304667387 10000000000 43341632429477 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100640717/500000000 : ℝ)^4237 ≤ (2415195531349/20000000000000 : ℝ)^3213 := by
    have hnat : (100640717 : ℕ)^4237*20000000000000^3213 ≤ 2415195531349^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100640717 500000000 2415195531349 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709715559/5000000000 : ℝ)^4237 ≤ (8916477980291/20000000000000 : ℝ)^3213 := by
    have hnat : (2709715559 : ℕ)^4237*20000000000000^3213 ≤ 8916477980291^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709715559 5000000000 8916477980291 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304667387/10000000000 : ℝ), (-100640717/500000000 : ℝ), (2709715559/5000000000 : ℝ)] ![(43341632429477/100000000000000 : ℝ), (2415195531349/20000000000000 : ℝ), (8916477980291/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304667387/10000000000 : ℝ)|^4237 ≤ (43341632429477/100000000000000 : ℝ)^3213
        have hw : |(5304667387/10000000000 : ℝ)|=(5304667387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100640717/500000000 : ℝ)|^4237 ≤ (2415195531349/20000000000000 : ℝ)^3213
        have hw : |(-100640717/500000000 : ℝ)|=(100640717/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709715559/5000000000 : ℝ)|^4237 ≤ (8916477980291/20000000000000 : ℝ)^3213
        have hw : |(2709715559/5000000000 : ℝ)|=(2709715559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s4_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652333647/5000000000 : ℝ)*x 0 + (5419430979/10000000000 : ℝ)*x 1 + (-2012814657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652333647/5000000000 : ℝ)^4237 ≤ (43341631427453/100000000000000 : ℝ)^3213 := by
    have hnat : (2652333647 : ℕ)^4237*100000000000000^3213 ≤ 43341631427453^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652333647 5000000000 43341631427453 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419430979/10000000000 : ℝ)^4237 ≤ (11145597098389/25000000000000 : ℝ)^3213 := by
    have hnat : (5419430979 : ℕ)^4237*25000000000000^3213 ≤ 11145597098389^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419430979 10000000000 11145597098389 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2012814657/10000000000 : ℝ)^4237 ≤ (12075980164733/100000000000000 : ℝ)^3213 := by
    have hnat : (2012814657 : ℕ)^4237*100000000000000^3213 ≤ 12075980164733^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2012814657 10000000000 12075980164733 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652333647/5000000000 : ℝ), (5419430979/10000000000 : ℝ), (-2012814657/10000000000 : ℝ)] ![(43341631427453/100000000000000 : ℝ), (11145597098389/25000000000000 : ℝ), (12075980164733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652333647/5000000000 : ℝ)|^4237 ≤ (43341631427453/100000000000000 : ℝ)^3213
        have hw : |(2652333647/5000000000 : ℝ)|=(2652333647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419430979/10000000000 : ℝ)|^4237 ≤ (11145597098389/25000000000000 : ℝ)^3213
        have hw : |(5419430979/10000000000 : ℝ)|=(5419430979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2012814657/10000000000 : ℝ)|^4237 ≤ (12075980164733/100000000000000 : ℝ)^3213
        have hw : |(-2012814657/10000000000 : ℝ)|=(2012814657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s4_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343651053/10000000000 : ℝ)*x 0 + (141607919/312500000 : ℝ)*x 1 + (4163411411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343651053/10000000000 : ℝ)^4237 ≤ (6659895053769/20000000000000 : ℝ)^3213 := by
    have hnat : (4343651053 : ℕ)^4237*20000000000000^3213 ≤ 6659895053769^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343651053 10000000000 6659895053769 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141607919/312500000 : ℝ)^4237 ≤ (35211020173391/100000000000000 : ℝ)^3213 := by
    have hnat : (141607919 : ℕ)^4237*100000000000000^3213 ≤ 35211020173391^3213*312500000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141607919 312500000 35211020173391 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163411411/10000000000 : ℝ)^4237 ≤ (15744752269197/50000000000000 : ℝ)^3213 := by
    have hnat : (4163411411 : ℕ)^4237*50000000000000^3213 ≤ 15744752269197^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163411411 10000000000 15744752269197 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343651053/10000000000 : ℝ), (141607919/312500000 : ℝ), (4163411411/10000000000 : ℝ)] ![(6659895053769/20000000000000 : ℝ), (35211020173391/100000000000000 : ℝ), (15744752269197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343651053/10000000000 : ℝ)|^4237 ≤ (6659895053769/20000000000000 : ℝ)^3213
        have hw : |(4343651053/10000000000 : ℝ)|=(4343651053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(141607919/312500000 : ℝ)|^4237 ≤ (35211020173391/100000000000000 : ℝ)^3213
        have hw : |(141607919/312500000 : ℝ)|=(141607919/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163411411/10000000000 : ℝ)|^4237 ≤ (15744752269197/50000000000000 : ℝ)^3213
        have hw : |(4163411411/10000000000 : ℝ)|=(4163411411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2727/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1059/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15087/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1059/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1059/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15087/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1059/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1059/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15087/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1059/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1059/10000 : ℝ) ^ (1059/256 : ℝ) ≤ (2313176883887779/25000000000000000000 : ℝ) := by
    have hpowers : (1059/10000 : ℝ)^1059 ≤ (2313176883887779/25000000000000000000 : ℝ)^256 := by
      have hnat : (1059 : ℕ)^1059*25000000000000000000^256 ≤ 2313176883887779^256*10000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1059 10000 2313176883887779 25000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1059/10000 : ℝ)) (X := (2313176883887779/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (15087/100000 : ℝ) ^ (1059/256 : ℝ) ≤ (2500294655853067/6250000000000000000 : ℝ) := by
    have hpowers : (15087/100000 : ℝ)^1059 ≤ (2500294655853067/6250000000000000000 : ℝ)^256 := by
      have hnat : (15087 : ℕ)^1059*6250000000000000000^256 ≤ 2500294655853067^256*100000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15087 100000 2500294655853067 6250000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15087/100000 : ℝ)) (X := (2500294655853067/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502313176883887779/12500000000000000000 : ℝ) ≤ (10000447313873477/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (12502313176883887779/12500000000000000000 : ℝ)^256 ≤ (10000447313873477/10000000000000000 : ℝ)^1059 := by
      have hnat : (12502313176883887779 : ℕ)^256*10000000000000000^1059 ≤ 10000447313873477^1059*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502313176883887779 12500000000000000000 10000447313873477 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000447313873477/10000000000000000 : ℝ)) (X := (12502313176883887779/12500000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012314355507300047/25000000000000000000 : ℝ) ≤ (400047620569657/400000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (25012314355507300047/25000000000000000000 : ℝ)^256 ≤ (400047620569657/400000000000000 : ℝ)^1059 := by
      have hnat : (25012314355507300047 : ℕ)^256*400000000000000^1059 ≤ 400047620569657^1059*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012314355507300047 25000000000000000000 400047620569657 400000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400047620569657/400000000000000 : ℝ)) (X := (25012314355507300047/25000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127500294655853067/3125000000000000000 : ℝ) ≤ (10001933714609373/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (3127500294655853067/3125000000000000000 : ℝ)^256 ≤ (10001933714609373/10000000000000000 : ℝ)^1059 := by
      have hnat : (3127500294655853067 : ℕ)^256*10000000000000000^1059 ≤ 10001933714609373^1059*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127500294655853067 3125000000000000000 10001933714609373 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001933714609373/10000000000000000 : ℝ)) (X := (3127500294655853067/3125000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2313176883887779/25000000000000000000 : ℝ) ≤ ((14985423528898629143/14990000000000000000 : ℝ)+2*(185800091987/112425000000000 : ℝ)*(1059/10000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (14985423528898629143/14990000000000000000 : ℝ)+2*(185800091987/112425000000000 : ℝ)*(1059/10000 : ℝ)=(10000447313873477/10000000000000000 : ℝ) by norm_num, show 1+2*(2313176883887779/25000000000000000000 : ℝ)=(12502313176883887779/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2500294655853067/6250000000000000000 : ℝ)+(2313176883887779/25000000000000000000 : ℝ) ≤ ((14985423528898629143/14990000000000000000 : ℝ)+(185800091987/112425000000000 : ℝ)*((15087/100000 : ℝ)+(1059/10000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (14985423528898629143/14990000000000000000 : ℝ)+(185800091987/112425000000000 : ℝ)*((15087/100000 : ℝ)+(1059/10000 : ℝ))=(400047620569657/400000000000000 : ℝ) by norm_num, show 1+(2500294655853067/6250000000000000000 : ℝ)+(2313176883887779/25000000000000000000 : ℝ)=(25012314355507300047/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2500294655853067/6250000000000000000 : ℝ) ≤ ((14985423528898629143/14990000000000000000 : ℝ)+2*(185800091987/112425000000000 : ℝ)*(15087/100000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (14985423528898629143/14990000000000000000 : ℝ)+2*(185800091987/112425000000000 : ℝ)*(15087/100000 : ℝ)=(10001933714609373/10000000000000000 : ℝ) by norm_num, show 1+2*(2500294655853067/6250000000000000000 : ℝ)=(3127500294655853067/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14985423528898629143/14990000000000000000 : ℝ)*(X 1 0+X 2 0)+(185800091987/112425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (1059/10000 : ℝ)) (hi := (15087/100000 : ℝ)) (c := (14985423528898629143/14990000000000000000 : ℝ)) (alpha := (185800091987/112425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14985423528898629143/14990000000000000000 : ℝ)*(X 0 1+X 2 1)+(185800091987/112425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (1059/10000 : ℝ)) (hi := (15087/100000 : ℝ)) (c := (14985423528898629143/14990000000000000000 : ℝ)) (alpha := (185800091987/112425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14985423528898629143/14990000000000000000 : ℝ)*(X 0 2+X 1 2)+(185800091987/112425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (1059/10000 : ℝ)) (hi := (15087/100000 : ℝ)) (c := (14985423528898629143/14990000000000000000 : ℝ)) (alpha := (185800091987/112425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2101002331/10000000000 : ℝ)*X 0 0+(5420109999/10000000000 : ℝ)*X 0 1+(1047729743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351037307/10000000000 : ℝ)*X 1 0+(-2193596783/10000000000 : ℝ)*X 1 1+(2619324327/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337759257/2500000000 : ℝ)*X 2 0+(2619324443/5000000000 : ℝ)*X 2 1+(-137099803/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171810383/5000000000 : ℝ)*X 0 0+(832404841/2000000000 : ℝ)*X 0 1+(35412761/78125000 : ℝ)*X 0 2+(2171810383/5000000000 : ℝ)*X 1 0+(832404841/2000000000 : ℝ)*X 1 1+(35412761/78125000 : ℝ)*X 1 2+(2171810383/5000000000 : ℝ)*X 2 0+(832404841/2000000000 : ℝ)*X 2 1+(35412761/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-84040697/400000000 : ℝ)*X 0 0+(523932379/1000000000 : ℝ)*X 0 1+(338714439/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304667387/10000000000 : ℝ)*X 1 0+(-100640717/500000000 : ℝ)*X 1 1+(2709715559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652333647/5000000000 : ℝ)*X 2 0+(5419430979/10000000000 : ℝ)*X 2 1+(-2012814657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343651053/10000000000 : ℝ)*X 0 0+(141607919/312500000 : ℝ)*X 0 1+(4163411411/10000000000 : ℝ)*X 0 2+(4343651053/10000000000 : ℝ)*X 1 0+(141607919/312500000 : ℝ)*X 1 1+(4163411411/10000000000 : ℝ)*X 1 2+(4343651053/10000000000 : ℝ)*X 2 0+(141607919/312500000 : ℝ)*X 2 1+(4163411411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58182125074655928407691/7495000000000000000000000000 : ℝ) := by norm_num
    linear_combination (182946417/50000000000000 : ℝ)*(base19) + (4099423/2000000000000 : ℝ)*(base23) + (2819047/3125000000000 : ℝ)*(lower2) + (31859209/100000000000000 : ℝ)*(upper3) + (39462993/25000000000000 : ℝ)*(lower4) + (2051911160899971/50000000000000 : ℝ)*(major0) + (2051911160899971/50000000000000 : ℝ)*(major1) + (2051911160899971/50000000000000 : ℝ)*(major2) + (551082794185287/10000000000000 : ℝ)*(sp0) + (5510833590881457/100000000000000 : ℝ)*(sp1) + (2755416875901571/50000000000000 : ℝ)*(sp2) + (2696808082717027/100000000000000 : ℝ)*(sp3) + (3007460711/50000000000000 : ℝ)*(sp4) + (1172674413/50000000000000 : ℝ)*(sp7) + (674202607016463/25000000000000 : ℝ)*(f.failure) + (1377708489193573/25000000000000 : ℝ)*(f.sum) + (6510331465093/1873750000000000000000000000 : ℝ)*base65 + (470226032308554853/749500000000000000000000000000000 : ℝ)*base67 + (4340466420127945147/749500000000000000000000000000000 : ℝ)*base70 + (3715580597838445147/749500000000000000000000000000000 : ℝ)*base72 + (340252731149/234218750000000000000000000 : ℝ)*base74 + (4703712080222054853/749500000000000000000000000000000 : ℝ)*base75 + (6104406242749945147/749500000000000000000000000000000 : ℝ)*base78 + (2126228817459554853/749500000000000000000000000000000 : ℝ)*base79 + (1230393574949/3747500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (5571069/500000000000000000000 : ℝ)*base90 + (5571069/500000000000000000000 : ℝ)*base92 + (5571069/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2026962387774185827365051021/187375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1531685349/100000000000000 : ℝ)*(base19) + (1571781167/100000000000000 : ℝ)*(base23) + (135779051/100000000000000 : ℝ)*(upper3) + (119561703/100000000000000 : ℝ)*(lower4) + (35283563/12500000000000 : ℝ)*(upper5) + (2067331779651951/50000000000000 : ℝ)*(major0) + (2067331779651951/50000000000000 : ℝ)*(major1) + (2067331779651951/50000000000000 : ℝ)*(major2) + (4273168307/12500000000000 : ℝ)*(sp1) + (24123682737/100000000000000 : ℝ)*(sp2) + (1110449826811491/20000000000000 : ℝ)*(sp4) + (111044268340513/2000000000000 : ℝ)*(sp5) + (5552223438593551/100000000000000 : ℝ)*(sp6) + (1358538811980541/50000000000000 : ℝ)*(sp7) + (1358538811980541/50000000000000 : ℝ)*(f.failure) + (1110449826811491/20000000000000 : ℝ)*(f.sum) + (18621423241613/7495000000000000000000000000 : ℝ)*base66 + (2015235992570007993/749500000000000000000000000000000 : ℝ)*base67 + (3593623810071992007/749500000000000000000000000000000 : ℝ)*base70 + (1804545560061007993/749500000000000000000000000000000 : ℝ)*base71 + (1806990358991/936875000000000000000000000 : ℝ)*base74 + (3723922318430007993/749500000000000000000000000000000 : ℝ)*base75 + (1889466842105007993/749500000000000000000000000000000 : ℝ)*base77 + (3759215343300507993/749500000000000000000000000000000 : ℝ)*base79 + (55428249597873/7495000000000000000000000000 : ℝ)*base82 + (3601383/1000000000000000000000 : ℝ)*base90 + (3601383/1000000000000000000000 : ℝ)*base92 + (3601383/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1277_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15087/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1059/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1277_s5_0 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-525350239/2500000000 : ℝ)*x 0 + (5416750493/10000000000 : ℝ)*x 1 + (5241746319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525350239/2500000000 : ℝ)^4237 ≤ (12781709904939/100000000000000 : ℝ)^3213 := by
    have hnat : (525350239 : ℕ)^4237*100000000000000^3213 ≤ 12781709904939^3213*2500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525350239 2500000000 12781709904939 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416750493/10000000000 : ℝ)^4237 ≤ (22276656128887/50000000000000 : ℝ)^3213 := by
    have hnat : (5416750493 : ℕ)^4237*50000000000000^3213 ≤ 22276656128887^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416750493 10000000000 22276656128887 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241746319/10000000000 : ℝ)^4237 ≤ (5333122227627/12500000000000 : ℝ)^3213 := by
    have hnat : (5241746319 : ℕ)^4237*12500000000000^3213 ≤ 5333122227627^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241746319 10000000000 5333122227627 12500000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525350239/2500000000 : ℝ), (5416750493/10000000000 : ℝ), (5241746319/10000000000 : ℝ)] ![(12781709904939/100000000000000 : ℝ), (22276656128887/50000000000000 : ℝ), (5333122227627/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525350239/2500000000 : ℝ)|^4237 ≤ (12781709904939/100000000000000 : ℝ)^3213
        have hw : |(-525350239/2500000000 : ℝ)|=(525350239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416750493/10000000000 : ℝ)|^4237 ≤ (22276656128887/50000000000000 : ℝ)^3213
        have hw : |(5416750493/10000000000 : ℝ)|=(5416750493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241746319/10000000000 : ℝ)|^4237 ≤ (5333122227627/12500000000000 : ℝ)^3213
        have hw : |(5241746319/10000000000 : ℝ)|=(5241746319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s5_1 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350187779/10000000000 : ℝ)*x 0 + (-2190636343/10000000000 : ℝ)*x 1 + (5241746341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350187779/10000000000 : ℝ)^4237 ≤ (8766551736807/20000000000000 : ℝ)^3213 := by
    have hnat : (5350187779 : ℕ)^4237*20000000000000^3213 ≤ 8766551736807^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350187779 10000000000 8766551736807 20000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2190636343/10000000000 : ℝ)^4237 ≤ (13502263241957/100000000000000 : ℝ)^3213 := by
    have hnat : (2190636343 : ℕ)^4237*100000000000000^3213 ≤ 13502263241957^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2190636343 10000000000 13502263241957 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241746341/10000000000 : ℝ)^4237 ≤ (21332489028577/50000000000000 : ℝ)^3213 := by
    have hnat : (5241746341 : ℕ)^4237*50000000000000^3213 ≤ 21332489028577^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241746341 10000000000 21332489028577 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350187779/10000000000 : ℝ), (-2190636343/10000000000 : ℝ), (5241746341/10000000000 : ℝ)] ![(8766551736807/20000000000000 : ℝ), (13502263241957/100000000000000 : ℝ), (21332489028577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350187779/10000000000 : ℝ)|^4237 ≤ (8766551736807/20000000000000 : ℝ)^3213
        have hw : |(5350187779/10000000000 : ℝ)|=(5350187779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2190636343/10000000000 : ℝ)|^4237 ≤ (13502263241957/100000000000000 : ℝ)^3213
        have hw : |(-2190636343/10000000000 : ℝ)|=(2190636343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241746341/10000000000 : ℝ)|^4237 ≤ (21332489028577/50000000000000 : ℝ)^3213
        have hw : |(5241746341/10000000000 : ℝ)|=(5241746341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s5_2 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350187837/10000000000 : ℝ)*x 0 + (2620873179/5000000000 : ℝ)*x 1 + (-438127249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350187837/10000000000 : ℝ)^4237 ≤ (43832759310657/100000000000000 : ℝ)^3213 := by
    have hnat : (5350187837 : ℕ)^4237*100000000000000^3213 ≤ 43832759310657^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350187837 10000000000 43832759310657 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620873179/5000000000 : ℝ)^4237 ≤ (341319825917/800000000000 : ℝ)^3213 := by
    have hnat : (2620873179 : ℕ)^4237*800000000000^3213 ≤ 341319825917^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620873179 5000000000 341319825917 800000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438127249/2000000000 : ℝ)^4237 ≤ (13502262445413/100000000000000 : ℝ)^3213 := by
    have hnat : (438127249 : ℕ)^4237*100000000000000^3213 ≤ 13502262445413^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438127249 2000000000 13502262445413 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350187837/10000000000 : ℝ), (2620873179/5000000000 : ℝ), (-438127249/2000000000 : ℝ)] ![(43832759310657/100000000000000 : ℝ), (341319825917/800000000000 : ℝ), (13502262445413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350187837/10000000000 : ℝ)|^4237 ≤ (43832759310657/100000000000000 : ℝ)^3213
        have hw : |(5350187837/10000000000 : ℝ)|=(5350187837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620873179/5000000000 : ℝ)|^4237 ≤ (341319825917/800000000000 : ℝ)^3213
        have hw : |(2620873179/5000000000 : ℝ)|=(2620873179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438127249/2000000000 : ℝ)|^4237 ≤ (13502262445413/100000000000000 : ℝ)^3213
        have hw : |(-438127249/2000000000 : ℝ)|=(438127249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s5_3 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4343857363/10000000000 : ℝ)*x 0 + (2084295517/5000000000 : ℝ)*x 1 + (4526206233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343857363/10000000000 : ℝ)^4237 ≤ (33301560978087/100000000000000 : ℝ)^3213 := by
    have hnat : (4343857363 : ℕ)^4237*100000000000000^3213 ≤ 33301560978087^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343857363 10000000000 33301560978087 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084295517/5000000000 : ℝ)^4237 ≤ (31541175727183/100000000000000 : ℝ)^3213 := by
    have hnat : (2084295517 : ℕ)^4237*100000000000000^3213 ≤ 31541175727183^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084295517 5000000000 31541175727183 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526206233/10000000000 : ℝ)^4237 ≤ (17578631637017/50000000000000 : ℝ)^3213 := by
    have hnat : (4526206233 : ℕ)^4237*50000000000000^3213 ≤ 17578631637017^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526206233 10000000000 17578631637017 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343857363/10000000000 : ℝ), (2084295517/5000000000 : ℝ), (4526206233/10000000000 : ℝ)] ![(33301560978087/100000000000000 : ℝ), (31541175727183/100000000000000 : ℝ), (17578631637017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343857363/10000000000 : ℝ)|^4237 ≤ (33301560978087/100000000000000 : ℝ)^3213
        have hw : |(4343857363/10000000000 : ℝ)|=(4343857363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084295517/5000000000 : ℝ)|^4237 ≤ (31541175727183/100000000000000 : ℝ)^3213
        have hw : |(2084295517/5000000000 : ℝ)|=(2084295517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526206233/10000000000 : ℝ)|^4237 ≤ (17578631637017/50000000000000 : ℝ)^3213
        have hw : |(4526206233/10000000000 : ℝ)|=(4526206233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s5_4 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2101413987/10000000000 : ℝ)*x 0 + (5242374513/10000000000 : ℝ)*x 1 + (270805959/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2101413987/10000000000 : ℝ)^4237 ≤ (12781814426513/100000000000000 : ℝ)^3213 := by
    have hnat : (2101413987 : ℕ)^4237*100000000000000^3213 ≤ 12781814426513^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101413987 10000000000 12781814426513 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242374513/10000000000 : ℝ)^4237 ≤ (42671720699629/100000000000000 : ℝ)^3213 := by
    have hnat : (5242374513 : ℕ)^4237*100000000000000^3213 ≤ 42671720699629^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242374513 10000000000 42671720699629 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270805959/500000000 : ℝ)^4237 ≤ (22273232429901/50000000000000 : ℝ)^3213 := by
    have hnat : (270805959 : ℕ)^4237*50000000000000^3213 ≤ 22273232429901^3213*500000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270805959 500000000 22273232429901 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2101413987/10000000000 : ℝ), (5242374513/10000000000 : ℝ), (270805959/500000000 : ℝ)] ![(12781814426513/100000000000000 : ℝ), (42671720699629/100000000000000 : ℝ), (22273232429901/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2101413987/10000000000 : ℝ)|^4237 ≤ (12781814426513/100000000000000 : ℝ)^3213
        have hw : |(-2101413987/10000000000 : ℝ)|=(2101413987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242374513/10000000000 : ℝ)|^4237 ≤ (42671720699629/100000000000000 : ℝ)^3213
        have hw : |(5242374513/10000000000 : ℝ)|=(5242374513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270805959/500000000 : ℝ)|^4237 ≤ (22273232429901/50000000000000 : ℝ)^3213
        have hw : |(270805959/500000000 : ℝ)|=(270805959/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s5_5 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061093559/2000000000 : ℝ)*x 0 + (-1008131719/5000000000 : ℝ)*x 1 + (8462687/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061093559/2000000000 : ℝ)^4237 ≤ (43350256587541/100000000000000 : ℝ)^3213 := by
    have hnat : (1061093559 : ℕ)^4237*100000000000000^3213 ≤ 43350256587541^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061093559 2000000000 43350256587541 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1008131719/5000000000 : ℝ)^4237 ≤ (12103273114541/100000000000000 : ℝ)^3213 := by
    have hnat : (1008131719 : ℕ)^4237*100000000000000^3213 ≤ 12103273114541^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008131719 5000000000 12103273114541 100000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8462687/15625000 : ℝ)^4237 ≤ (22273235141421/50000000000000 : ℝ)^3213 := by
    have hnat : (8462687 : ℕ)^4237*50000000000000^3213 ≤ 22273235141421^3213*15625000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8462687 15625000 22273235141421 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061093559/2000000000 : ℝ), (-1008131719/5000000000 : ℝ), (8462687/15625000 : ℝ)] ![(43350256587541/100000000000000 : ℝ), (12103273114541/100000000000000 : ℝ), (22273235141421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061093559/2000000000 : ℝ)|^4237 ≤ (43350256587541/100000000000000 : ℝ)^3213
        have hw : |(1061093559/2000000000 : ℝ)|=(1061093559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1008131719/5000000000 : ℝ)|^4237 ≤ (12103273114541/100000000000000 : ℝ)^3213
        have hw : |(-1008131719/5000000000 : ℝ)|=(1008131719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8462687/15625000 : ℝ)|^4237 ≤ (22273235141421/50000000000000 : ℝ)^3213
        have hw : |(8462687/15625000 : ℝ)|=(8462687/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s5_6 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305468241/10000000000 : ℝ)*x 0 + (5416119329/10000000000 : ℝ)*x 1 + (-126016457/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305468241/10000000000 : ℝ)^4237 ≤ (21675130696587/50000000000000 : ℝ)^3213 := by
    have hnat : (5305468241 : ℕ)^4237*50000000000000^3213 ≤ 21675130696587^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305468241 10000000000 21675130696587 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416119329/10000000000 : ℝ)^4237 ≤ (11136616618967/25000000000000 : ℝ)^3213 := by
    have hnat : (5416119329 : ℕ)^4237*25000000000000^3213 ≤ 11136616618967^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416119329 10000000000 11136616618967 25000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126016457/625000000 : ℝ)^4237 ≤ (1210327211713/10000000000000 : ℝ)^3213 := by
    have hnat : (126016457 : ℕ)^4237*10000000000000^3213 ≤ 1210327211713^3213*625000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126016457 625000000 1210327211713 10000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305468241/10000000000 : ℝ), (5416119329/10000000000 : ℝ), (-126016457/625000000 : ℝ)] ![(21675130696587/50000000000000 : ℝ), (11136616618967/25000000000000 : ℝ), (1210327211713/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305468241/10000000000 : ℝ)|^4237 ≤ (21675130696587/50000000000000 : ℝ)^3213
        have hw : |(5305468241/10000000000 : ℝ)|=(5305468241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416119329/10000000000 : ℝ)|^4237 ≤ (11136616618967/25000000000000 : ℝ)^3213
        have hw : |(5416119329/10000000000 : ℝ)|=(5416119329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126016457/625000000 : ℝ)|^4237 ≤ (1210327211713/10000000000000 : ℝ)^3213
        have hw : |(-126016457/625000000 : ℝ)|=(126016457/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1277_s5_7 (p : ℝ) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171941973/5000000000 : ℝ)*x 0 + (904984529/2000000000 : ℝ)*x 1 + (4169881681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171941973/5000000000 : ℝ)^4237 ≤ (1665091486179/5000000000000 : ℝ)^3213 := by
    have hnat : (2171941973 : ℕ)^4237*5000000000000^3213 ≤ 1665091486179^3213*5000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171941973 5000000000 1665091486179 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (904984529/2000000000 : ℝ)^4237 ≤ (1757205801867/5000000000000 : ℝ)^3213 := by
    have hnat : (904984529 : ℕ)^4237*5000000000000^3213 ≤ 1757205801867^3213*2000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904984529 2000000000 1757205801867 5000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4169881681/10000000000 : ℝ)^4237 ≤ (15777027112781/50000000000000 : ℝ)^3213 := by
    have hnat : (4169881681 : ℕ)^4237*50000000000000^3213 ≤ 15777027112781^3213*10000000000^4237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169881681 10000000000 15777027112781 50000000000000 4237 3213 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4237/1024 : ℝ)) 4237 3213 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171941973/5000000000 : ℝ), (904984529/2000000000 : ℝ), (4169881681/10000000000 : ℝ)] ![(1665091486179/5000000000000 : ℝ), (1757205801867/5000000000000 : ℝ), (15777027112781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171941973/5000000000 : ℝ)|^4237 ≤ (1665091486179/5000000000000 : ℝ)^3213
        have hw : |(2171941973/5000000000 : ℝ)|=(2171941973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(904984529/2000000000 : ℝ)|^4237 ≤ (1757205801867/5000000000000 : ℝ)^3213
        have hw : |(904984529/2000000000 : ℝ)|=(904984529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4169881681/10000000000 : ℝ)|^4237 ≤ (15777027112781/50000000000000 : ℝ)^3213
        have hw : |(4169881681/10000000000 : ℝ)|=(4169881681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1277_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5487/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7339/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2727/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2727/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2727/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2727/25000 : ℝ) ^ (1059/256 : ℝ) ≤ (2091472842202331/20000000000000000000 : ℝ) := by
    have hpowers : (2727/25000 : ℝ)^1059 ≤ (2091472842202331/20000000000000000000 : ℝ)^256 := by
      have hnat : (2727 : ℕ)^1059*20000000000000000000^256 ≤ 2091472842202331^256*25000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2727 25000 2091472842202331 20000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2727/25000 : ℝ)) (X := (2091472842202331/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (1059/256 : ℝ) ≤ (18207602040616653/50000000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^1059 ≤ (18207602040616653/50000000000000000000 : ℝ)^256 := by
      have hnat : (3687 : ℕ)^1059*50000000000000000000^256 ≤ 18207602040616653^256*25000^1059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 18207602040616653 50000000000000000000 1059 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (18207602040616653/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002091472842202331/10000000000000000000 : ℝ) ≤ (2000101109461247/2000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (10002091472842202331/10000000000000000000 : ℝ)^256 ≤ (2000101109461247/2000000000000000 : ℝ)^1059 := by
      have hnat : (10002091472842202331 : ℕ)^256*2000000000000000^1059 ≤ 2000101109461247^1059*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002091472842202331 10000000000000000000 2000101109461247 2000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000101109461247/2000000000000000 : ℝ)) (X := (10002091472842202331/10000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046872568292244961/100000000000000000000 : ℝ) ≤ (312535402637147/312500000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (100046872568292244961/100000000000000000000 : ℝ)^256 ≤ (312535402637147/312500000000000 : ℝ)^1059 := by
      have hnat : (100046872568292244961 : ℕ)^256*312500000000000^1059 ≤ 312535402637147^1059*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046872568292244961 100000000000000000000 312535402637147 312500000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312535402637147/312500000000000 : ℝ)) (X := (100046872568292244961/100000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018207602040616653/25000000000000000000 : ℝ) ≤ (10001760221471173/10000000000000000 : ℝ) ^ (1059/256 : ℝ) := by
    have hpowers : (25018207602040616653/25000000000000000000 : ℝ)^256 ≤ (10001760221471173/10000000000000000 : ℝ)^1059 := by
      have hnat : (25018207602040616653 : ℕ)^256*10000000000000000^1059 ≤ 10001760221471173^1059*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018207602040616653 25000000000000000000 10001760221471173 10000000000000000 256 1059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001760221471173/10000000000000000 : ℝ)) (X := (25018207602040616653/25000000000000000000 : ℝ)) (by norm_num) 1059 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2091472842202331/20000000000000000000 : ℝ) ≤ ((1599510638161033279/1600000000000000000 : ℝ)+2*(209112360823/128000000000000 : ℝ)*(2727/25000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (1599510638161033279/1600000000000000000 : ℝ)+2*(209112360823/128000000000000 : ℝ)*(2727/25000 : ℝ)=(2000101109461247/2000000000000000 : ℝ) by norm_num, show 1+2*(2091472842202331/20000000000000000000 : ℝ)=(10002091472842202331/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18207602040616653/50000000000000000000 : ℝ)+(2091472842202331/20000000000000000000 : ℝ) ≤ ((1599510638161033279/1600000000000000000 : ℝ)+(209112360823/128000000000000 : ℝ)*((3687/25000 : ℝ)+(2727/25000 : ℝ)))^(1059/256 : ℝ) := by
    rw [show (1599510638161033279/1600000000000000000 : ℝ)+(209112360823/128000000000000 : ℝ)*((3687/25000 : ℝ)+(2727/25000 : ℝ))=(312535402637147/312500000000000 : ℝ) by norm_num, show 1+(18207602040616653/50000000000000000000 : ℝ)+(2091472842202331/20000000000000000000 : ℝ)=(100046872568292244961/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18207602040616653/50000000000000000000 : ℝ) ≤ ((1599510638161033279/1600000000000000000 : ℝ)+2*(209112360823/128000000000000 : ℝ)*(3687/25000 : ℝ))^(1059/256 : ℝ) := by
    rw [show (1599510638161033279/1600000000000000000 : ℝ)+2*(209112360823/128000000000000 : ℝ)*(3687/25000 : ℝ)=(10001760221471173/10000000000000000 : ℝ) by norm_num, show 1+2*(18207602040616653/50000000000000000000 : ℝ)=(25018207602040616653/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1599510638161033279/1600000000000000000 : ℝ)*(X 1 0+X 2 0)+(209112360823/128000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (1599510638161033279/1600000000000000000 : ℝ)) (alpha := (209112360823/128000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1599510638161033279/1600000000000000000 : ℝ)*(X 0 1+X 2 1)+(209112360823/128000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (1599510638161033279/1600000000000000000 : ℝ)) (alpha := (209112360823/128000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1599510638161033279/1600000000000000000 : ℝ)*(X 0 2+X 1 2)+(209112360823/128000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1059/256 : ℝ)) (lo := (2727/25000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (1599510638161033279/1600000000000000000 : ℝ)) (alpha := (209112360823/128000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-525350239/2500000000 : ℝ)*X 0 0+(5416750493/10000000000 : ℝ)*X 0 1+(5241746319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350187779/10000000000 : ℝ)*X 1 0+(-2190636343/10000000000 : ℝ)*X 1 1+(5241746341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350187837/10000000000 : ℝ)*X 2 0+(2620873179/5000000000 : ℝ)*X 2 1+(-438127249/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4343857363/10000000000 : ℝ)*X 0 0+(2084295517/5000000000 : ℝ)*X 0 1+(4526206233/10000000000 : ℝ)*X 0 2+(4343857363/10000000000 : ℝ)*X 1 0+(2084295517/5000000000 : ℝ)*X 1 1+(4526206233/10000000000 : ℝ)*X 1 2+(4343857363/10000000000 : ℝ)*X 2 0+(2084295517/5000000000 : ℝ)*X 2 1+(4526206233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2101413987/10000000000 : ℝ)*X 0 0+(5242374513/10000000000 : ℝ)*X 0 1+(270805959/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061093559/2000000000 : ℝ)*X 1 0+(-1008131719/5000000000 : ℝ)*X 1 1+(8462687/15625000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305468241/10000000000 : ℝ)*X 2 0+(5416119329/10000000000 : ℝ)*X 2 1+(-126016457/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171941973/5000000000 : ℝ)*X 0 0+(904984529/2000000000 : ℝ)*X 0 1+(4169881681/10000000000 : ℝ)*X 0 2+(2171941973/5000000000 : ℝ)*X 1 0+(904984529/2000000000 : ℝ)*X 1 1+(4169881681/10000000000 : ℝ)*X 1 2+(2171941973/5000000000 : ℝ)*X 2 0+(904984529/2000000000 : ℝ)*X 2 1+(4169881681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1277_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18630240992721775337289/3200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1329490109/100000000000000 : ℝ)*(base19) + (1305569421/100000000000000 : ℝ)*(base23) + (45940349/100000000000000 : ℝ)*(lower2) + (202139439/100000000000000 : ℝ)*(upper3) + (66400233/25000000000000 : ℝ)*(upper5) + (2127631348202873/50000000000000 : ℝ)*(major0) + (2127631348202873/50000000000000 : ℝ)*(major1) + (2127631348202873/50000000000000 : ℝ)*(major2) + (2857085463327217/50000000000000 : ℝ)*(sp0) + (5714195004610637/100000000000000 : ℝ)*(sp1) + (228567801141253/4000000000000 : ℝ)*(sp2) + (699078856766367/25000000000000 : ℝ)*(sp3) + (3175930789/12500000000000 : ℝ)*(sp4) + (13437580261/100000000000000 : ℝ)*(sp7) + (279632886464573/10000000000000 : ℝ)*(f.failure) + (2857098167050373/50000000000000 : ℝ)*(f.sum) + (262178230079/3200000000000000000000000000 : ℝ)*base65 + (401410963047601933/80000000000000000000000000000000 : ℝ)*base68 + (393817267672398067/80000000000000000000000000000000 : ℝ)*base69 + (56093342087601933/80000000000000000000000000000000 : ℝ)*base72 + (769321193279/3200000000000000000000000000 : ℝ)*base73 + (315702338792398067/80000000000000000000000000000000 : ℝ)*base75 + (403291553752398067/80000000000000000000000000000000 : ℝ)*base77 + (1221641549607601933/80000000000000000000000000000000 : ℝ)*base80 + (26542945532479/3200000000000000000000000000 : ℝ)*base81 + (615001/200000000000000000000 : ℝ)*base89 + (615001/200000000000000000000 : ℝ)*base91 + (615001/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (528379495945042924852066623/40000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (325314753/25000000000000 : ℝ)*(base19) + (2029809827/100000000000000 : ℝ)*(base23) + (277605909/100000000000000 : ℝ)*(upper3) + (21235639/25000000000000 : ℝ)*(lower4) + (53646767/20000000000000 : ℝ)*(upper5) + (2143038159246421/50000000000000 : ℝ)*(major0) + (2143038159246421/50000000000000 : ℝ)*(major1) + (2143038159246421/50000000000000 : ℝ)*(major2) + (17395272931/50000000000000 : ℝ)*(sp1) + (22414387989/50000000000000 : ℝ)*(sp2) + (5755574283489231/100000000000000 : ℝ)*(sp4) + (1438884547921089/25000000000000 : ℝ)*(sp5) + (230221096996137/4000000000000 : ℝ)*(sp6) + (1408288956590099/50000000000000 : ℝ)*(sp7) + (1408288956590099/50000000000000 : ℝ)*(f.failure) + (5755574283489231/100000000000000 : ℝ)*(f.sum) + (1049835969283/3200000000000000000000000000 : ℝ)*base65 + (667699958358681959/80000000000000000000000000000000 : ℝ)*base67 + (56664058041318041/80000000000000000000000000000000 : ℝ)*base70 + (9506730681318041/80000000000000000000000000000000 : ℝ)*base72 + (361101006717/3200000000000000000000000000 : ℝ)*base74 + (1937866626598681959/80000000000000000000000000000000 : ℝ)*base75 + (330631709878681959/80000000000000000000000000000000 : ℝ)*base77 + (1381634322678681959/80000000000000000000000000000000 : ℝ)*base79 + (24612113845117/3200000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (859063/1000000000000000000000 : ℝ)*base89 + (859063/1000000000000000000000 : ℝ)*base91 + (859063/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1277_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2727/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1277_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1277_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1277_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1277_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1277_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1059/256 : ℝ) ≤ p) (hpb : p ≤ (4237/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (30434637/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16387/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9393/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5487/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1277_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
