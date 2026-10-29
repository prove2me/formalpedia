-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1492_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:49:22.977728+00:00
-- url     : https://prove2.me/submissions/f3b58d61-98b0-41f3-bcab-7935f860bb8b

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
theorem support_rectangle_w1492_s6_0 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-189797233/1000000000 : ℝ)*x 0 + (2717924653/5000000000 : ℝ)*x 1 + (1304139851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (189797233/1000000000 : ℝ)^4481 ≤ (2320286925887/20000000000000 : ℝ)^3457 := by
    have hnat : (189797233 : ℕ)^4481*20000000000000^3457 ≤ 2320286925887^3457*1000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189797233 1000000000 2320286925887 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717924653/5000000000 : ℝ)^4481 ≤ (45378570654953/100000000000000 : ℝ)^3457 := by
    have hnat : (2717924653 : ℕ)^4481*100000000000000^3457 ≤ 45378570654953^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717924653 5000000000 45378570654953 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304139851/2500000000 : ℝ)^4481 ≤ (43019994704387/100000000000000 : ℝ)^3457 := by
    have hnat : (1304139851 : ℕ)^4481*100000000000000^3457 ≤ 43019994704387^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304139851 2500000000 43019994704387 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-189797233/1000000000 : ℝ), (2717924653/5000000000 : ℝ), (1304139851/2500000000 : ℝ)] ![(2320286925887/20000000000000 : ℝ), (45378570654953/100000000000000 : ℝ), (43019994704387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-189797233/1000000000 : ℝ)|^4481 ≤ (2320286925887/20000000000000 : ℝ)^3457
        have hw : |(-189797233/1000000000 : ℝ)|=(189797233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717924653/5000000000 : ℝ)|^4481 ≤ (45378570654953/100000000000000 : ℝ)^3457
        have hw : |(2717924653/5000000000 : ℝ)|=(2717924653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304139851/2500000000 : ℝ)|^4481 ≤ (43019994704387/100000000000000 : ℝ)^3457
        have hw : |(1304139851/2500000000 : ℝ)|=(1304139851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s6_1 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676339917/5000000000 : ℝ)*x 0 + (-1005164247/5000000000 : ℝ)*x 1 + (5216559377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676339917/5000000000 : ℝ)^4481 ≤ (11120164493849/25000000000000 : ℝ)^3457 := by
    have hnat : (2676339917 : ℕ)^4481*25000000000000^3457 ≤ 11120164493849^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676339917 5000000000 11120164493849 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005164247/5000000000 : ℝ)^4481 ≤ (12499347597321/100000000000000 : ℝ)^3457 := by
    have hnat : (1005164247 : ℕ)^4481*100000000000000^3457 ≤ 12499347597321^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005164247 5000000000 12499347597321 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216559377/10000000000 : ℝ)^4481 ≤ (5377499301971/12500000000000 : ℝ)^3457 := by
    have hnat : (5216559377 : ℕ)^4481*12500000000000^3457 ≤ 5377499301971^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216559377 10000000000 5377499301971 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676339917/5000000000 : ℝ), (-1005164247/5000000000 : ℝ), (5216559377/10000000000 : ℝ)] ![(11120164493849/25000000000000 : ℝ), (12499347597321/100000000000000 : ℝ), (5377499301971/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676339917/5000000000 : ℝ)|^4481 ≤ (11120164493849/25000000000000 : ℝ)^3457
        have hw : |(2676339917/5000000000 : ℝ)|=(2676339917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005164247/5000000000 : ℝ)|^4481 ≤ (12499347597321/100000000000000 : ℝ)^3457
        have hw : |(-1005164247/5000000000 : ℝ)|=(1005164247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216559377/10000000000 : ℝ)|^4481 ≤ (5377499301971/12500000000000 : ℝ)^3457
        have hw : |(5216559377/10000000000 : ℝ)|=(5216559377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s6_2 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338169959/2500000000 : ℝ)*x 0 + (2608279711/5000000000 : ℝ)*x 1 + (-201032843/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338169959/2500000000 : ℝ)^4481 ≤ (44480657996939/100000000000000 : ℝ)^3457 := by
    have hnat : (1338169959 : ℕ)^4481*100000000000000^3457 ≤ 44480657996939^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338169959 2500000000 44480657996939 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608279711/5000000000 : ℝ)^4481 ≤ (53774993621/125000000000 : ℝ)^3457 := by
    have hnat : (2608279711 : ℕ)^4481*125000000000^3457 ≤ 53774993621^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608279711 5000000000 53774993621 125000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (201032843/1000000000 : ℝ)^4481 ≤ (1562418385191/12500000000000 : ℝ)^3457 := by
    have hnat : (201032843 : ℕ)^4481*12500000000000^3457 ≤ 1562418385191^3457*1000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201032843 1000000000 1562418385191 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338169959/2500000000 : ℝ), (2608279711/5000000000 : ℝ), (-201032843/1000000000 : ℝ)] ![(44480657996939/100000000000000 : ℝ), (53774993621/125000000000 : ℝ), (1562418385191/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338169959/2500000000 : ℝ)|^4481 ≤ (44480657996939/100000000000000 : ℝ)^3457
        have hw : |(1338169959/2500000000 : ℝ)|=(1338169959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608279711/5000000000 : ℝ)|^4481 ≤ (53774993621/125000000000 : ℝ)^3457
        have hw : |(2608279711/5000000000 : ℝ)|=(2608279711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-201032843/1000000000 : ℝ)|^4481 ≤ (1562418385191/12500000000000 : ℝ)^3457
        have hw : |(-201032843/1000000000 : ℝ)|=(201032843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s6_3 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855835543/2000000000 : ℝ)*x 0 + (404010979/1000000000 : ℝ)*x 1 + (906073711/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855835543/2000000000 : ℝ)^4481 ≤ (3327862301943/10000000000000 : ℝ)^3457 := by
    have hnat : (855835543 : ℕ)^4481*10000000000000^3457 ≤ 3327862301943^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855835543 2000000000 3327862301943 10000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404010979/1000000000 : ℝ)^4481 ≤ (30888915182041/100000000000000 : ℝ)^3457 := by
    have hnat : (404010979 : ℕ)^4481*100000000000000^3457 ≤ 30888915182041^3457*1000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404010979 1000000000 30888915182041 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906073711/2000000000 : ℝ)^4481 ≤ (35832461792773/100000000000000 : ℝ)^3457 := by
    have hnat : (906073711 : ℕ)^4481*100000000000000^3457 ≤ 35832461792773^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906073711 2000000000 35832461792773 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855835543/2000000000 : ℝ), (404010979/1000000000 : ℝ), (906073711/2000000000 : ℝ)] ![(3327862301943/10000000000000 : ℝ), (30888915182041/100000000000000 : ℝ), (35832461792773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855835543/2000000000 : ℝ)|^4481 ≤ (3327862301943/10000000000000 : ℝ)^3457
        have hw : |(855835543/2000000000 : ℝ)|=(855835543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404010979/1000000000 : ℝ)|^4481 ≤ (30888915182041/100000000000000 : ℝ)^3457
        have hw : |(404010979/1000000000 : ℝ)|=(404010979/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(906073711/2000000000 : ℝ)|^4481 ≤ (35832461792773/100000000000000 : ℝ)^3457
        have hw : |(906073711/2000000000 : ℝ)|=(906073711/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s6_4 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-949001059/5000000000 : ℝ)*x 0 + (2608841907/5000000000 : ℝ)*x 1 + (2717358323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (949001059/5000000000 : ℝ)^4481 ≤ (11601670644507/100000000000000 : ℝ)^3457 := by
    have hnat : (949001059 : ℕ)^4481*100000000000000^3457 ≤ 11601670644507^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      949001059 5000000000 11601670644507 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608841907/5000000000 : ℝ)^4481 ≤ (5379001823707/12500000000000 : ℝ)^3457 := by
    have hnat : (2608841907 : ℕ)^4481*12500000000000^3457 ≤ 5379001823707^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608841907 5000000000 5379001823707 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717358323/5000000000 : ℝ)^4481 ≤ (1814652590289/4000000000000 : ℝ)^3457 := by
    have hnat : (2717358323 : ℕ)^4481*4000000000000^3457 ≤ 1814652590289^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717358323 5000000000 1814652590289 4000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-949001059/5000000000 : ℝ), (2608841907/5000000000 : ℝ), (2717358323/5000000000 : ℝ)] ![(11601670644507/100000000000000 : ℝ), (5379001823707/12500000000000 : ℝ), (1814652590289/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-949001059/5000000000 : ℝ)|^4481 ≤ (11601670644507/100000000000000 : ℝ)^3457
        have hw : |(-949001059/5000000000 : ℝ)|=(949001059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608841907/5000000000 : ℝ)|^4481 ≤ (5379001823707/12500000000000 : ℝ)^3457
        have hw : |(2608841907/5000000000 : ℝ)|=(2608841907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717358323/5000000000 : ℝ)|^4481 ≤ (1814652590289/4000000000000 : ℝ)^3457
        have hw : |(2717358323/5000000000 : ℝ)|=(2717358323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s6_5 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295294223/10000000000 : ℝ)*x 0 + (-1792171279/10000000000 : ℝ)*x 1 + (1358679159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295294223/10000000000 : ℝ)^4481 ≤ (21931756900481/50000000000000 : ℝ)^3457 := by
    have hnat : (5295294223 : ℕ)^4481*50000000000000^3457 ≤ 21931756900481^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295294223 10000000000 21931756900481 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1792171279/10000000000 : ℝ)^4481 ≤ (5385085767221/50000000000000 : ℝ)^3457 := by
    have hnat : (1792171279 : ℕ)^4481*50000000000000^3457 ≤ 5385085767221^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792171279 10000000000 5385085767221 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358679159/2500000000 : ℝ)^4481 ≤ (708848666391/1562500000000 : ℝ)^3457 := by
    have hnat : (1358679159 : ℕ)^4481*1562500000000^3457 ≤ 708848666391^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358679159 2500000000 708848666391 1562500000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295294223/10000000000 : ℝ), (-1792171279/10000000000 : ℝ), (1358679159/2500000000 : ℝ)] ![(21931756900481/50000000000000 : ℝ), (5385085767221/50000000000000 : ℝ), (708848666391/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295294223/10000000000 : ℝ)|^4481 ≤ (21931756900481/50000000000000 : ℝ)^3457
        have hw : |(5295294223/10000000000 : ℝ)|=(5295294223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1792171279/10000000000 : ℝ)|^4481 ≤ (5385085767221/50000000000000 : ℝ)^3457
        have hw : |(-1792171279/10000000000 : ℝ)|=(1792171279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358679159/2500000000 : ℝ)|^4481 ≤ (708848666391/1562500000000 : ℝ)^3457
        have hw : |(1358679159/2500000000 : ℝ)|=(1358679159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s6_6 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647647111/5000000000 : ℝ)*x 0 + (5434716641/10000000000 : ℝ)*x 1 + (-1792171273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647647111/5000000000 : ℝ)^4481 ≤ (1754540551609/4000000000000 : ℝ)^3457 := by
    have hnat : (2647647111 : ℕ)^4481*4000000000000^3457 ≤ 1754540551609^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647647111 5000000000 1754540551609 4000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434716641/10000000000 : ℝ)^4481 ≤ (2903444141/6400000000 : ℝ)^3457 := by
    have hnat : (5434716641 : ℕ)^4481*6400000000^3457 ≤ 2903444141^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434716641 10000000000 2903444141 6400000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1792171273/10000000000 : ℝ)^4481 ≤ (1346271435963/12500000000000 : ℝ)^3457 := by
    have hnat : (1792171273 : ℕ)^4481*12500000000000^3457 ≤ 1346271435963^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792171273 10000000000 1346271435963 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647647111/5000000000 : ℝ), (5434716641/10000000000 : ℝ), (-1792171273/10000000000 : ℝ)] ![(1754540551609/4000000000000 : ℝ), (2903444141/6400000000 : ℝ), (1346271435963/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647647111/5000000000 : ℝ)|^4481 ≤ (1754540551609/4000000000000 : ℝ)^3457
        have hw : |(2647647111/5000000000 : ℝ)|=(2647647111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434716641/10000000000 : ℝ)|^4481 ≤ (2903444141/6400000000 : ℝ)^3457
        have hw : |(5434716641/10000000000 : ℝ)|=(5434716641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1792171273/10000000000 : ℝ)|^4481 ≤ (1346271435963/12500000000000 : ℝ)^3457
        have hw : |(-1792171273/10000000000 : ℝ)|=(1792171273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_s6_7 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2139622197/5000000000 : ℝ)*x 0 + (2263927379/5000000000 : ℝ)*x 1 + (2021321029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2139622197/5000000000 : ℝ)^4481 ≤ (33279295176343/100000000000000 : ℝ)^3457 := by
    have hnat : (2139622197 : ℕ)^4481*100000000000000^3457 ≤ 33279295176343^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139622197 5000000000 33279295176343 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263927379/5000000000 : ℝ)^4481 ≤ (17903345933023/50000000000000 : ℝ)^3457 := by
    have hnat : (2263927379 : ℕ)^4481*50000000000000^3457 ≤ 17903345933023^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263927379 5000000000 17903345933023 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021321029/5000000000 : ℝ)^4481 ≤ (15457006472923/50000000000000 : ℝ)^3457 := by
    have hnat : (2021321029 : ℕ)^4481*50000000000000^3457 ≤ 15457006472923^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021321029 5000000000 15457006472923 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2139622197/5000000000 : ℝ), (2263927379/5000000000 : ℝ), (2021321029/5000000000 : ℝ)] ![(33279295176343/100000000000000 : ℝ), (17903345933023/50000000000000 : ℝ), (15457006472923/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2139622197/5000000000 : ℝ)|^4481 ≤ (33279295176343/100000000000000 : ℝ)^3457
        have hw : |(2139622197/5000000000 : ℝ)|=(2139622197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263927379/5000000000 : ℝ)|^4481 ≤ (17903345933023/50000000000000 : ℝ)^3457
        have hw : |(2263927379/5000000000 : ℝ)|=(2263927379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2021321029/5000000000 : ℝ)|^4481 ≤ (15457006472923/50000000000000 : ℝ)^3457
        have hw : |(2021321029/5000000000 : ℝ)|=(2021321029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1492_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2167/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2709/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2167/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2167/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2167/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2167/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2167/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2167/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2167/20000 : ℝ) ^ (4479/1024 : ℝ) ≤ (6002318766566247/100000000000000000000 : ℝ) := by
    have hpowers : (2167/20000 : ℝ)^4479 ≤ (6002318766566247/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2167 : ℕ)^4479*100000000000000000000^1024 ≤ 6002318766566247^1024*20000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2167 20000 6002318766566247 100000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2167/20000 : ℝ)) (X := (6002318766566247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4479/1024 : ℝ) ≤ (14289241546879223/50000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4479 ≤ (14289241546879223/50000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4479*50000000000000000000^1024 ≤ 14289241546879223^1024*2500^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 14289241546879223 50000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (14289241546879223/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006002318766566247/50000000000000000000 : ℝ) ≤ (10000274440270449/10000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (50006002318766566247/50000000000000000000 : ℝ)^1024 ≤ (10000274440270449/10000000000000000 : ℝ)^4479 := by
      have hnat : (50006002318766566247 : ℕ)^1024*10000000000000000^4479 ≤ 10000274440270449^4479*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006002318766566247 50000000000000000000 10000274440270449 10000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000274440270449/10000000000000000 : ℝ)) (X := (50006002318766566247/50000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034580801860324693/100000000000000000000 : ℝ) ≤ (2500197622344203/2500000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (100034580801860324693/100000000000000000000 : ℝ)^1024 ≤ (2500197622344203/2500000000000000 : ℝ)^4479 := by
      have hnat : (100034580801860324693 : ℕ)^1024*2500000000000000^4479 ≤ 2500197622344203^4479*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034580801860324693 100000000000000000000 2500197622344203 2500000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500197622344203/2500000000000000 : ℝ)) (X := (100034580801860324693/100000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014289241546879223/25000000000000000000 : ℝ) ≤ (400052261539327/400000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (25014289241546879223/25000000000000000000 : ℝ)^1024 ≤ (400052261539327/400000000000000 : ℝ)^4479 := by
      have hnat : (25014289241546879223 : ℕ)^1024*400000000000000^4479 ≤ 400052261539327^4479*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014289241546879223 25000000000000000000 400052261539327 400000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400052261539327/400000000000000 : ℝ)) (X := (25014289241546879223/25000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6002318766566247/100000000000000000000 : ℝ) ≤ ((9288018398184269879/9290000000000000000 : ℝ)+2*(516049106363/464500000000000 : ℝ)*(2167/20000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (9288018398184269879/9290000000000000000 : ℝ)+2*(516049106363/464500000000000 : ℝ)*(2167/20000 : ℝ)=(10000274440270449/10000000000000000 : ℝ) by norm_num, show 1+2*(6002318766566247/100000000000000000000 : ℝ)=(50006002318766566247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14289241546879223/50000000000000000000 : ℝ)+(6002318766566247/100000000000000000000 : ℝ) ≤ ((9288018398184269879/9290000000000000000 : ℝ)+(516049106363/464500000000000 : ℝ)*((387/2500 : ℝ)+(2167/20000 : ℝ)))^(4479/1024 : ℝ) := by
    rw [show (9288018398184269879/9290000000000000000 : ℝ)+(516049106363/464500000000000 : ℝ)*((387/2500 : ℝ)+(2167/20000 : ℝ))=(2500197622344203/2500000000000000 : ℝ) by norm_num, show 1+(14289241546879223/50000000000000000000 : ℝ)+(6002318766566247/100000000000000000000 : ℝ)=(100034580801860324693/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14289241546879223/50000000000000000000 : ℝ) ≤ ((9288018398184269879/9290000000000000000 : ℝ)+2*(516049106363/464500000000000 : ℝ)*(387/2500 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (9288018398184269879/9290000000000000000 : ℝ)+2*(516049106363/464500000000000 : ℝ)*(387/2500 : ℝ)=(400052261539327/400000000000000 : ℝ) by norm_num, show 1+2*(14289241546879223/50000000000000000000 : ℝ)=(25014289241546879223/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9288018398184269879/9290000000000000000 : ℝ)*(X 1 0+X 2 0)+(516049106363/464500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (2167/20000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (9288018398184269879/9290000000000000000 : ℝ)) (alpha := (516049106363/464500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9288018398184269879/9290000000000000000 : ℝ)*(X 0 1+X 2 1)+(516049106363/464500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (2167/20000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (9288018398184269879/9290000000000000000 : ℝ)) (alpha := (516049106363/464500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9288018398184269879/9290000000000000000 : ℝ)*(X 0 2+X 1 2)+(516049106363/464500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (2167/20000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (9288018398184269879/9290000000000000000 : ℝ)) (alpha := (516049106363/464500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-189797233/1000000000 : ℝ)*X 0 0+(2717924653/5000000000 : ℝ)*X 0 1+(1304139851/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676339917/5000000000 : ℝ)*X 1 0+(-1005164247/5000000000 : ℝ)*X 1 1+(5216559377/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338169959/2500000000 : ℝ)*X 2 0+(2608279711/5000000000 : ℝ)*X 2 1+(-201032843/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((855835543/2000000000 : ℝ)*X 0 0+(404010979/1000000000 : ℝ)*X 0 1+(906073711/2000000000 : ℝ)*X 0 2+(855835543/2000000000 : ℝ)*X 1 0+(404010979/1000000000 : ℝ)*X 1 1+(906073711/2000000000 : ℝ)*X 1 2+(855835543/2000000000 : ℝ)*X 2 0+(404010979/1000000000 : ℝ)*X 2 1+(906073711/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-949001059/5000000000 : ℝ)*X 0 0+(2608841907/5000000000 : ℝ)*X 0 1+(2717358323/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295294223/10000000000 : ℝ)*X 1 0+(-1792171279/10000000000 : ℝ)*X 1 1+(1358679159/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647647111/5000000000 : ℝ)*X 2 0+(5434716641/10000000000 : ℝ)*X 2 1+(-1792171273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2139622197/5000000000 : ℝ)*X 0 0+(2263927379/5000000000 : ℝ)*X 0 1+(2021321029/5000000000 : ℝ)*X 0 2+(2139622197/5000000000 : ℝ)*X 1 0+(2263927379/5000000000 : ℝ)*X 1 1+(2021321029/5000000000 : ℝ)*X 1 2+(2139622197/5000000000 : ℝ)*X 2 0+(2263927379/5000000000 : ℝ)*X 2 1+(2021321029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (996008729597014654886489697/116125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64801747/4000000000000 : ℝ)*(base19) + (77354371/5000000000000 : ℝ)*(base23) + (4995399/12500000000000 : ℝ)*(lower2) + (89520949/50000000000000 : ℝ)*(upper3) + (36866511/20000000000000 : ℝ)*(upper5) + (824998606344381/25000000000000 : ℝ)*(major0) + (824998606344381/25000000000000 : ℝ)*(major1) + (824998606344381/25000000000000 : ℝ)*(major2) + (912039815750953/20000000000000 : ℝ)*(sp0) + (2280112104656767/50000000000000 : ℝ)*(sp1) + (1140056070567447/25000000000000 : ℝ)*(sp2) + (7967776525887/390625000000 : ℝ)*(sp3) + (6687650611/25000000000000 : ℝ)*(sp4) + (5972434717/50000000000000 : ℝ)*(sp7) + (2039762735496507/100000000000000 : ℝ)*(f.failure) + (570028228669651/12500000000000 : ℝ)*(f.sum) + (70694690480281/11612500000000000000000000000 : ℝ)*base65 + (48573331999759899/232250000000000000000000000000000 : ℝ)*base67 + (2398466702820740101/232250000000000000000000000000000 : ℝ)*base70 + (1844877418086740101/232250000000000000000000000000000 : ℝ)*base72 + (46373765721153/5806250000000000000000000000 : ℝ)*base73 + (1844565649867240101/232250000000000000000000000000000 : ℝ)*base76 + (1406975016023740101/232250000000000000000000000000000 : ℝ)*base78 + (3611228404532259899/232250000000000000000000000000000 : ℝ)*base79 + (5427124425891/725781250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (130611243/10000000000000000000000 : ℝ)*base89 + (130611243/10000000000000000000000 : ℝ)*base91 + (130611243/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (211406806031770716513646503/58062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (600493579/100000000000000 : ℝ)*(base19) + (328817931/50000000000000 : ℝ)*(base23) + (194082763/100000000000000 : ℝ)*(lower1) + (75451981/100000000000000 : ℝ)*(upper3) + (6423809/25000000000000 : ℝ)*(lower4) + (37970533/50000000000000 : ℝ)*(upper5) + (416783516683219/12500000000000 : ℝ)*(major0) + (416783516683219/12500000000000 : ℝ)*(major1) + (416783516683219/12500000000000 : ℝ)*(major2) + (875488989/100000000000000 : ℝ)*(sp2) + (2303794227660501/50000000000000 : ℝ)*(sp4) + (4607587854827423/100000000000000 : ℝ)*(sp5) + (4607586922196151/100000000000000 : ℝ)*(sp6) + (1030473845121553/50000000000000 : ℝ)*(sp7) + (1030473845121553/50000000000000 : ℝ)*(f.failure) + (2303794227660501/50000000000000 : ℝ)*(f.sum) + (3345333662989/1451562500000000000000000000 : ℝ)*base66 + (1979257322983400501/116125000000000000000000000000000 : ℝ)*base67 + (2205944748273599499/116125000000000000000000000000000 : ℝ)*base70 + (3856816823771775501/116125000000000000000000000000000 : ℝ)*base71 + (30180702057499/23225000000000000000000000000 : ℝ)*base74 + (4742615216366599499/116125000000000000000000000000000 : ℝ)*base76 + (1290701107379849499/116125000000000000000000000000000 : ℝ)*base78 + (1994701767392724499/116125000000000000000000000000000 : ℝ)*base80 + (80102970667601/23225000000000000000000000000 : ℝ)*base81 + (44265697/5000000000000000000000 : ℝ)*base89 + (44265697/5000000000000000000000 : ℝ)*base91 + (44265697/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1492_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2167/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1492_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1492_box_0 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1680699857/10000000000 : ℝ)*x 0 + (1351249629/2500000000 : ℝ)*x 1 + (2702498837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1680699857/10000000000 : ℝ)^4481 ≤ (9909965659161/100000000000000 : ℝ)^3457 := by
    have hnat : (1680699857 : ℕ)^4481*100000000000000^3457 ≤ 9909965659161^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1680699857 10000000000 9909965659161 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351249629/2500000000 : ℝ)^4481 ≤ (22522510857323/50000000000000 : ℝ)^3457 := by
    have hnat : (1351249629 : ℕ)^4481*50000000000000^3457 ≤ 22522510857323^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351249629 2500000000 22522510857323 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702498837/5000000000 : ℝ)^4481 ≤ (5630626577361/12500000000000 : ℝ)^3457 := by
    have hnat : (2702498837 : ℕ)^4481*12500000000000^3457 ≤ 5630626577361^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702498837 5000000000 5630626577361 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1680699857/10000000000 : ℝ), (1351249629/2500000000 : ℝ), (2702498837/5000000000 : ℝ)] ![(9909965659161/100000000000000 : ℝ), (22522510857323/50000000000000 : ℝ), (5630626577361/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1680699857/10000000000 : ℝ)|^4481 ≤ (9909965659161/100000000000000 : ℝ)^3457
        have hw : |(-1680699857/10000000000 : ℝ)|=(1680699857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351249629/2500000000 : ℝ)|^4481 ≤ (22522510857323/50000000000000 : ℝ)^3457
        have hw : |(1351249629/2500000000 : ℝ)|=(1351249629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702498837/5000000000 : ℝ)|^4481 ≤ (5630626577361/12500000000000 : ℝ)^3457
        have hw : |(2702498837/5000000000 : ℝ)|=(2702498837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_1 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270467971/10000000000 : ℝ)*x 0 + (-1867154371/10000000000 : ℝ)*x 1 + (540499789/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270467971/10000000000 : ℝ)^4481 ≤ (43597135988519/100000000000000 : ℝ)^3457 := by
    have hnat : (5270467971 : ℕ)^4481*100000000000000^3457 ≤ 43597135988519^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270467971 10000000000 43597135988519 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867154371/10000000000 : ℝ)^4481 ≤ (11357849046893/100000000000000 : ℝ)^3457 := by
    have hnat : (1867154371 : ℕ)^4481*100000000000000^3457 ≤ 11357849046893^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867154371 10000000000 11357849046893 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540499789/1000000000 : ℝ)^4481 ≤ (22522507476121/50000000000000 : ℝ)^3457 := by
    have hnat : (540499789 : ℕ)^4481*50000000000000^3457 ≤ 22522507476121^3457*1000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540499789 1000000000 22522507476121 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270467971/10000000000 : ℝ), (-1867154371/10000000000 : ℝ), (540499789/1000000000 : ℝ)] ![(43597135988519/100000000000000 : ℝ), (11357849046893/100000000000000 : ℝ), (22522507476121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270467971/10000000000 : ℝ)|^4481 ≤ (43597135988519/100000000000000 : ℝ)^3457
        have hw : |(5270467971/10000000000 : ℝ)|=(5270467971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1867154371/10000000000 : ℝ)|^4481 ≤ (11357849046893/100000000000000 : ℝ)^3457
        have hw : |(-1867154371/10000000000 : ℝ)|=(1867154371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540499789/1000000000 : ℝ)|^4481 ≤ (22522507476121/50000000000000 : ℝ)^3457
        have hw : |(540499789/1000000000 : ℝ)|=(540499789/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_2 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270467827/10000000000 : ℝ)*x 0 + (540499833/1000000000 : ℝ)*x 1 + (-1867153963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270467827/10000000000 : ℝ)^4481 ≤ (43597134444521/100000000000000 : ℝ)^3457 := by
    have hnat : (5270467827 : ℕ)^4481*100000000000000^3457 ≤ 43597134444521^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270467827 10000000000 43597134444521 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540499833/1000000000 : ℝ)^4481 ≤ (45045019705369/100000000000000 : ℝ)^3457 := by
    have hnat : (540499833 : ℕ)^4481*100000000000000^3457 ≤ 45045019705369^3457*1000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540499833 1000000000 45045019705369 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1867153963/10000000000 : ℝ)^4481 ≤ (11357845829889/100000000000000 : ℝ)^3457 := by
    have hnat : (1867153963 : ℕ)^4481*100000000000000^3457 ≤ 11357845829889^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867153963 10000000000 11357845829889 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270467827/10000000000 : ℝ), (540499833/1000000000 : ℝ), (-1867153963/10000000000 : ℝ)] ![(43597134444521/100000000000000 : ℝ), (45045019705369/100000000000000 : ℝ), (11357845829889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270467827/10000000000 : ℝ)|^4481 ≤ (43597134444521/100000000000000 : ℝ)^3457
        have hw : |(5270467827/10000000000 : ℝ)|=(5270467827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540499833/1000000000 : ℝ)|^4481 ≤ (45045019705369/100000000000000 : ℝ)^3457
        have hw : |(540499833/1000000000 : ℝ)|=(540499833/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1867153963/10000000000 : ℝ)|^4481 ≤ (11357845829889/100000000000000 : ℝ)^3457
        have hw : |(-1867153963/10000000000 : ℝ)|=(1867153963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_3 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (35024867/78125000 : ℝ)*x 0 + (836858119/2000000000 : ℝ)*x 1 + (2092145249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35024867/78125000 : ℝ)^4481 ≤ (35349452074179/100000000000000 : ℝ)^3457 := by
    have hnat : (35024867 : ℕ)^4481*100000000000000^3457 ≤ 35349452074179^3457*78125000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35024867 78125000 35349452074179 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (836858119/2000000000 : ℝ)^4481 ≤ (32325274444137/100000000000000 : ℝ)^3457 := by
    have hnat : (836858119 : ℕ)^4481*100000000000000^3457 ≤ 32325274444137^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836858119 2000000000 32325274444137 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2092145249/5000000000 : ℝ)^4481 ≤ (6465054694561/20000000000000 : ℝ)^3457 := by
    have hnat : (2092145249 : ℕ)^4481*20000000000000^3457 ≤ 6465054694561^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092145249 5000000000 6465054694561 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(35024867/78125000 : ℝ), (836858119/2000000000 : ℝ), (2092145249/5000000000 : ℝ)] ![(35349452074179/100000000000000 : ℝ), (32325274444137/100000000000000 : ℝ), (6465054694561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(35024867/78125000 : ℝ)|^4481 ≤ (35349452074179/100000000000000 : ℝ)^3457
        have hw : |(35024867/78125000 : ℝ)|=(35024867/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(836858119/2000000000 : ℝ)|^4481 ≤ (32325274444137/100000000000000 : ℝ)^3457
        have hw : |(836858119/2000000000 : ℝ)|=(836858119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2092145249/5000000000 : ℝ)|^4481 ≤ (6465054694561/20000000000000 : ℝ)^3457
        have hw : |(2092145249/5000000000 : ℝ)|=(2092145249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_4 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1060352911/5000000000 : ℝ)*x 0 + (5242918239/10000000000 : ℝ)*x 1 + (2621459441/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060352911/5000000000 : ℝ)^4481 ≤ (13396051267079/100000000000000 : ℝ)^3457 := by
    have hnat : (1060352911 : ℕ)^4481*100000000000000^3457 ≤ 13396051267079^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060352911 5000000000 13396051267079 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242918239/10000000000 : ℝ)^4481 ≤ (4330197091873/10000000000000 : ℝ)^3457 := by
    have hnat : (5242918239 : ℕ)^4481*10000000000000^3457 ≤ 4330197091873^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242918239 10000000000 4330197091873 10000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621459441/5000000000 : ℝ)^4481 ≤ (43301977802417/100000000000000 : ℝ)^3457 := by
    have hnat : (2621459441 : ℕ)^4481*100000000000000^3457 ≤ 43301977802417^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621459441 5000000000 43301977802417 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1060352911/5000000000 : ℝ), (5242918239/10000000000 : ℝ), (2621459441/5000000000 : ℝ)] ![(13396051267079/100000000000000 : ℝ), (4330197091873/10000000000000 : ℝ), (43301977802417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1060352911/5000000000 : ℝ)|^4481 ≤ (13396051267079/100000000000000 : ℝ)^3457
        have hw : |(-1060352911/5000000000 : ℝ)|=(1060352911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242918239/10000000000 : ℝ)|^4481 ≤ (4330197091873/10000000000000 : ℝ)^3457
        have hw : |(5242918239/10000000000 : ℝ)|=(5242918239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621459441/5000000000 : ℝ)|^4481 ≤ (43301977802417/100000000000000 : ℝ)^3457
        have hw : |(2621459441/5000000000 : ℝ)|=(2621459441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_5 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1345871811/2500000000 : ℝ)*x 0 + (-1933693559/10000000000 : ℝ)*x 1 + (5242918489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345871811/2500000000 : ℝ)^4481 ≤ (44812781956131/100000000000000 : ℝ)^3457 := by
    have hnat : (1345871811 : ℕ)^4481*100000000000000^3457 ≤ 44812781956131^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345871811 2500000000 44812781956131 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933693559/10000000000 : ℝ)^4481 ≤ (5942622212111/50000000000000 : ℝ)^3457 := by
    have hnat : (1933693559 : ℕ)^4481*50000000000000^3457 ≤ 5942622212111^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933693559 10000000000 5942622212111 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242918489/10000000000 : ℝ)^4481 ≤ (346415788761/800000000000 : ℝ)^3457 := by
    have hnat : (5242918489 : ℕ)^4481*800000000000^3457 ≤ 346415788761^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242918489 10000000000 346415788761 800000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345871811/2500000000 : ℝ), (-1933693559/10000000000 : ℝ), (5242918489/10000000000 : ℝ)] ![(44812781956131/100000000000000 : ℝ), (5942622212111/50000000000000 : ℝ), (346415788761/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345871811/2500000000 : ℝ)|^4481 ≤ (44812781956131/100000000000000 : ℝ)^3457
        have hw : |(1345871811/2500000000 : ℝ)|=(1345871811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933693559/10000000000 : ℝ)|^4481 ≤ (5942622212111/50000000000000 : ℝ)^3457
        have hw : |(-1933693559/10000000000 : ℝ)|=(1933693559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242918489/10000000000 : ℝ)|^4481 ≤ (346415788761/800000000000 : ℝ)^3457
        have hw : |(5242918489/10000000000 : ℝ)|=(5242918489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_6 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691743313/5000000000 : ℝ)*x 0 + (1048583809/2000000000 : ℝ)*x 1 + (-38673873/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691743313/5000000000 : ℝ)^4481 ≤ (44812775288029/100000000000000 : ℝ)^3457 := by
    have hnat : (2691743313 : ℕ)^4481*100000000000000^3457 ≤ 44812775288029^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691743313 5000000000 44812775288029 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048583809/2000000000 : ℝ)^4481 ≤ (43301979547427/100000000000000 : ℝ)^3457 := by
    have hnat : (1048583809 : ℕ)^4481*100000000000000^3457 ≤ 43301979547427^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048583809 2000000000 43301979547427 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38673873/200000000 : ℝ)^4481 ≤ (11885245149221/100000000000000 : ℝ)^3457 := by
    have hnat : (38673873 : ℕ)^4481*100000000000000^3457 ≤ 11885245149221^3457*200000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38673873 200000000 11885245149221 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691743313/5000000000 : ℝ), (1048583809/2000000000 : ℝ), (-38673873/200000000 : ℝ)] ![(44812775288029/100000000000000 : ℝ), (43301979547427/100000000000000 : ℝ), (11885245149221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691743313/5000000000 : ℝ)|^4481 ≤ (44812775288029/100000000000000 : ℝ)^3457
        have hw : |(2691743313/5000000000 : ℝ)|=(2691743313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048583809/2000000000 : ℝ)|^4481 ≤ (43301979547427/100000000000000 : ℝ)^3457
        have hw : |(1048583809/2000000000 : ℝ)|=(1048583809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38673873/200000000 : ℝ)|^4481 ≤ (11885245149221/100000000000000 : ℝ)^3457
        have hw : |(-38673873/200000000 : ℝ)|=(38673873/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_7 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4072853203/10000000000 : ℝ)*x 0 + (2194659303/5000000000 : ℝ)*x 1 + (2194659159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4072853203/10000000000 : ℝ)^4481 ≤ (31213799686297/100000000000000 : ℝ)^3457 := by
    have hnat : (4072853203 : ℕ)^4481*100000000000000^3457 ≤ 31213799686297^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4072853203 10000000000 31213799686297 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2194659303/5000000000 : ℝ)^4481 ≤ (6878620321659/20000000000000 : ℝ)^3457 := by
    have hnat : (2194659303 : ℕ)^4481*20000000000000^3457 ≤ 6878620321659^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194659303 5000000000 6878620321659 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194659159/5000000000 : ℝ)^4481 ≤ (6878619736637/20000000000000 : ℝ)^3457 := by
    have hnat : (2194659159 : ℕ)^4481*20000000000000^3457 ≤ 6878619736637^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194659159 5000000000 6878619736637 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4072853203/10000000000 : ℝ), (2194659303/5000000000 : ℝ), (2194659159/5000000000 : ℝ)] ![(31213799686297/100000000000000 : ℝ), (6878620321659/20000000000000 : ℝ), (6878619736637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4072853203/10000000000 : ℝ)|^4481 ≤ (31213799686297/100000000000000 : ℝ)^3457
        have hw : |(4072853203/10000000000 : ℝ)|=(4072853203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2194659303/5000000000 : ℝ)|^4481 ≤ (6878620321659/20000000000000 : ℝ)^3457
        have hw : |(2194659303/5000000000 : ℝ)|=(2194659303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2194659159/5000000000 : ℝ)|^4481 ≤ (6878619736637/20000000000000 : ℝ)^3457
        have hw : |(2194659159/5000000000 : ℝ)|=(2194659159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_8 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-253479177/1250000000 : ℝ)*x 0 + (5129594121/10000000000 : ℝ)*x 1 + (5425509709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (253479177/1250000000 : ℝ)^4481 ≤ (3160151528359/25000000000000 : ℝ)^3457 := by
    have hnat : (253479177 : ℕ)^4481*25000000000000^3457 ≤ 3160151528359^3457*1250000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253479177 1250000000 3160151528359 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5129594121/10000000000 : ℝ)^4481 ≤ (10523168576487/25000000000000 : ℝ)^3457 := by
    have hnat : (5129594121 : ℕ)^4481*25000000000000^3457 ≤ 10523168576487^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129594121 10000000000 10523168576487 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425509709/10000000000 : ℝ)^4481 ≤ (5658339947521/12500000000000 : ℝ)^3457 := by
    have hnat : (5425509709 : ℕ)^4481*12500000000000^3457 ≤ 5658339947521^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425509709 10000000000 5658339947521 12500000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-253479177/1250000000 : ℝ), (5129594121/10000000000 : ℝ), (5425509709/10000000000 : ℝ)] ![(3160151528359/25000000000000 : ℝ), (10523168576487/25000000000000 : ℝ), (5658339947521/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-253479177/1250000000 : ℝ)|^4481 ≤ (3160151528359/25000000000000 : ℝ)^3457
        have hw : |(-253479177/1250000000 : ℝ)|=(253479177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5129594121/10000000000 : ℝ)|^4481 ≤ (10523168576487/25000000000000 : ℝ)^3457
        have hw : |(5129594121/10000000000 : ℝ)|=(5129594121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425509709/10000000000 : ℝ)|^4481 ≤ (5658339947521/12500000000000 : ℝ)^3457
        have hw : |(5425509709/10000000000 : ℝ)|=(5425509709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_9 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210246331/400000000 : ℝ)*x 0 + (-58077563/312500000 : ℝ)*x 1 + (5425509527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210246331/400000000 : ℝ)^4481 ≤ (10860941536621/25000000000000 : ℝ)^3457 := by
    have hnat : (210246331 : ℕ)^4481*25000000000000^3457 ≤ 10860941536621^3457*400000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210246331 400000000 10860941536621 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58077563/312500000 : ℝ)^4481 ≤ (11289516234341/100000000000000 : ℝ)^3457 := by
    have hnat : (58077563 : ℕ)^4481*100000000000000^3457 ≤ 11289516234341^3457*312500000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58077563 312500000 11289516234341 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425509527/10000000000 : ℝ)^4481 ≤ (9053343522379/20000000000000 : ℝ)^3457 := by
    have hnat : (5425509527 : ℕ)^4481*20000000000000^3457 ≤ 9053343522379^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425509527 10000000000 9053343522379 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210246331/400000000 : ℝ), (-58077563/312500000 : ℝ), (5425509527/10000000000 : ℝ)] ![(10860941536621/25000000000000 : ℝ), (11289516234341/100000000000000 : ℝ), (9053343522379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210246331/400000000 : ℝ)|^4481 ≤ (10860941536621/25000000000000 : ℝ)^3457
        have hw : |(210246331/400000000 : ℝ)|=(210246331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58077563/312500000 : ℝ)|^4481 ≤ (11289516234341/100000000000000 : ℝ)^3457
        have hw : |(-58077563/312500000 : ℝ)|=(58077563/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425509527/10000000000 : ℝ)|^4481 ≤ (9053343522379/20000000000000 : ℝ)^3457
        have hw : |(5425509527/10000000000 : ℝ)|=(5425509527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_10 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256157833/10000000000 : ℝ)*x 0 + (2712755021/5000000000 : ℝ)*x 1 + (-464620477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256157833/10000000000 : ℝ)^4481 ≤ (21721880705541/50000000000000 : ℝ)^3457 := by
    have hnat : (5256157833 : ℕ)^4481*50000000000000^3457 ≤ 21721880705541^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256157833 10000000000 21721880705541 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712755021/5000000000 : ℝ)^4481 ≤ (2263336159073/5000000000000 : ℝ)^3457 := by
    have hnat : (2712755021 : ℕ)^4481*5000000000000^3457 ≤ 2263336159073^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712755021 5000000000 2263336159073 5000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464620477/2500000000 : ℝ)^4481 ≤ (2257903076791/20000000000000 : ℝ)^3457 := by
    have hnat : (464620477 : ℕ)^4481*20000000000000^3457 ≤ 2257903076791^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464620477 2500000000 2257903076791 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256157833/10000000000 : ℝ), (2712755021/5000000000 : ℝ), (-464620477/2500000000 : ℝ)] ![(21721880705541/50000000000000 : ℝ), (2263336159073/5000000000000 : ℝ), (2257903076791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256157833/10000000000 : ℝ)|^4481 ≤ (21721880705541/50000000000000 : ℝ)^3457
        have hw : |(5256157833/10000000000 : ℝ)|=(5256157833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712755021/5000000000 : ℝ)|^4481 ≤ (2263336159073/5000000000000 : ℝ)^3457
        have hw : |(2712755021/5000000000 : ℝ)|=(2712755021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464620477/2500000000 : ℝ)|^4481 ≤ (2257903076791/20000000000000 : ℝ)^3457
        have hw : |(-464620477/2500000000 : ℝ)|=(464620477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_11 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2266978597/5000000000 : ℝ)*x 0 + (4158312129/10000000000 : ℝ)*x 1 + (831662367/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2266978597/5000000000 : ℝ)^4481 ≤ (1120914302787/3125000000000 : ℝ)^3457 := by
    have hnat : (2266978597 : ℕ)^4481*3125000000000^3457 ≤ 1120914302787^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266978597 5000000000 1120914302787 3125000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158312129/10000000000 : ℝ)^4481 ≤ (32065372613269/100000000000000 : ℝ)^3457 := by
    have hnat : (4158312129 : ℕ)^4481*100000000000000^3457 ≤ 32065372613269^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158312129 10000000000 32065372613269 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (831662367/2000000000 : ℝ)^4481 ≤ (16032684837329/50000000000000 : ℝ)^3457 := by
    have hnat : (831662367 : ℕ)^4481*50000000000000^3457 ≤ 16032684837329^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831662367 2000000000 16032684837329 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2266978597/5000000000 : ℝ), (4158312129/10000000000 : ℝ), (831662367/2000000000 : ℝ)] ![(1120914302787/3125000000000 : ℝ), (32065372613269/100000000000000 : ℝ), (16032684837329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2266978597/5000000000 : ℝ)|^4481 ≤ (1120914302787/3125000000000 : ℝ)^3457
        have hw : |(2266978597/5000000000 : ℝ)|=(2266978597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158312129/10000000000 : ℝ)|^4481 ≤ (32065372613269/100000000000000 : ℝ)^3457
        have hw : |(4158312129/10000000000 : ℝ)|=(4158312129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(831662367/2000000000 : ℝ)|^4481 ≤ (16032684837329/50000000000000 : ℝ)^3457
        have hw : |(831662367/2000000000 : ℝ)|=(831662367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_12 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-88681659/500000000 : ℝ)*x 0 + (2757304267/5000000000 : ℝ)*x 1 + (2613955687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88681659/500000000 : ℝ)^4481 ≤ (10625987757117/100000000000000 : ℝ)^3457 := by
    have hnat : (88681659 : ℕ)^4481*100000000000000^3457 ≤ 10625987757117^3457*500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88681659 500000000 10625987757117 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757304267/5000000000 : ℝ)^4481 ≤ (9246526067461/20000000000000 : ℝ)^3457 := by
    have hnat : (2757304267 : ℕ)^4481*20000000000000^3457 ≤ 9246526067461^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757304267 5000000000 9246526067461 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613955687/5000000000 : ℝ)^4481 ≤ (8628276379699/20000000000000 : ℝ)^3457 := by
    have hnat : (2613955687 : ℕ)^4481*20000000000000^3457 ≤ 8628276379699^3457*5000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613955687 5000000000 8628276379699 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88681659/500000000 : ℝ), (2757304267/5000000000 : ℝ), (2613955687/5000000000 : ℝ)] ![(10625987757117/100000000000000 : ℝ), (9246526067461/20000000000000 : ℝ), (8628276379699/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88681659/500000000 : ℝ)|^4481 ≤ (10625987757117/100000000000000 : ℝ)^3457
        have hw : |(-88681659/500000000 : ℝ)|=(88681659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757304267/5000000000 : ℝ)|^4481 ≤ (9246526067461/20000000000000 : ℝ)^3457
        have hw : |(2757304267/5000000000 : ℝ)|=(2757304267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613955687/5000000000 : ℝ)|^4481 ≤ (8628276379699/20000000000000 : ℝ)^3457
        have hw : |(2613955687/5000000000 : ℝ)|=(2613955687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_13 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539395119/1000000000 : ℝ)*x 0 + (-1939673351/10000000000 : ℝ)*x 1 + (5227910653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539395119/1000000000 : ℝ)^4481 ≤ (1403928700893/3125000000000 : ℝ)^3457 := by
    have hnat : (539395119 : ℕ)^4481*3125000000000^3457 ≤ 1403928700893^3457*1000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539395119 1000000000 1403928700893 3125000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1939673351/10000000000 : ℝ)^4481 ≤ (2386581472857/20000000000000 : ℝ)^3457 := by
    have hnat : (1939673351 : ℕ)^4481*20000000000000^3457 ≤ 2386581472857^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939673351 10000000000 2386581472857 20000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227910653/10000000000 : ℝ)^4481 ≤ (10785343546581/25000000000000 : ℝ)^3457 := by
    have hnat : (5227910653 : ℕ)^4481*25000000000000^3457 ≤ 10785343546581^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227910653 10000000000 10785343546581 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539395119/1000000000 : ℝ), (-1939673351/10000000000 : ℝ), (5227910653/10000000000 : ℝ)] ![(1403928700893/3125000000000 : ℝ), (2386581472857/20000000000000 : ℝ), (10785343546581/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539395119/1000000000 : ℝ)|^4481 ≤ (1403928700893/3125000000000 : ℝ)^3457
        have hw : |(539395119/1000000000 : ℝ)|=(539395119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1939673351/10000000000 : ℝ)|^4481 ≤ (2386581472857/20000000000000 : ℝ)^3457
        have hw : |(-1939673351/10000000000 : ℝ)|=(1939673351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227910653/10000000000 : ℝ)|^4481 ≤ (10785343546581/25000000000000 : ℝ)^3457
        have hw : |(5227910653/10000000000 : ℝ)|=(5227910653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_14 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348487693/2500000000 : ℝ)*x 0 + (653488921/1250000000 : ℝ)*x 1 + (-1939672959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348487693/2500000000 : ℝ)^4481 ≤ (44925713915841/100000000000000 : ℝ)^3457 := by
    have hnat : (1348487693 : ℕ)^4481*100000000000000^3457 ≤ 44925713915841^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348487693 2500000000 44925713915841 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653488921/1250000000 : ℝ)^4481 ≤ (10785345458579/25000000000000 : ℝ)^3457 := by
    have hnat : (653488921 : ℕ)^4481*25000000000000^3457 ≤ 10785345458579^3457*1250000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653488921 1250000000 10785345458579 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939672959/10000000000 : ℝ)^4481 ≤ (5966452119177/50000000000000 : ℝ)^3457 := by
    have hnat : (1939672959 : ℕ)^4481*50000000000000^3457 ≤ 5966452119177^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939672959 10000000000 5966452119177 50000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348487693/2500000000 : ℝ), (653488921/1250000000 : ℝ), (-1939672959/10000000000 : ℝ)] ![(44925713915841/100000000000000 : ℝ), (10785345458579/25000000000000 : ℝ), (5966452119177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348487693/2500000000 : ℝ)|^4481 ≤ (44925713915841/100000000000000 : ℝ)^3457
        have hw : |(1348487693/2500000000 : ℝ)|=(1348487693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653488921/1250000000 : ℝ)|^4481 ≤ (10785345458579/25000000000000 : ℝ)^3457
        have hw : |(653488921/1250000000 : ℝ)|=(653488921/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1939672959/10000000000 : ℝ)|^4481 ≤ (5966452119177/50000000000000 : ℝ)^3457
        have hw : |(-1939672959/10000000000 : ℝ)|=(1939672959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1492_box_15 (p : ℝ) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4033999999/10000000000 : ℝ)*x 0 + (1102070267/2500000000 : ℝ)*x 1 + (881655857/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4033999999/10000000000 : ℝ)^4481 ≤ (30828379130569/100000000000000 : ℝ)^3457 := by
    have hnat : (4033999999 : ℕ)^4481*100000000000000^3457 ≤ 30828379130569^3457*10000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4033999999 10000000000 30828379130569 100000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1102070267/2500000000 : ℝ)^4481 ≤ (8646454874541/25000000000000 : ℝ)^3457 := by
    have hnat : (1102070267 : ℕ)^4481*25000000000000^3457 ≤ 8646454874541^3457*2500000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102070267 2500000000 8646454874541 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (881655857/2000000000 : ℝ)^4481 ≤ (8646450341437/25000000000000 : ℝ)^3457 := by
    have hnat : (881655857 : ℕ)^4481*25000000000000^3457 ≤ 8646450341437^3457*2000000000^4481 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881655857 2000000000 8646450341437 25000000000000 4481 3457 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4481/1024 : ℝ)) 4481 3457 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4033999999/10000000000 : ℝ), (1102070267/2500000000 : ℝ), (881655857/2000000000 : ℝ)] ![(30828379130569/100000000000000 : ℝ), (8646454874541/25000000000000 : ℝ), (8646450341437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4033999999/10000000000 : ℝ)|^4481 ≤ (30828379130569/100000000000000 : ℝ)^3457
        have hw : |(4033999999/10000000000 : ℝ)|=(4033999999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1102070267/2500000000 : ℝ)|^4481 ≤ (8646454874541/25000000000000 : ℝ)^3457
        have hw : |(1102070267/2500000000 : ℝ)|=(1102070267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(881655857/2000000000 : ℝ)|^4481 ≤ (8646450341437/25000000000000 : ℝ)^3457
        have hw : |(881655857/2000000000 : ℝ)|=(881655857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1492_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(12743/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29267/50000 : ℝ) ∧ (80101/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5367/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2709/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2709/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2709/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2709/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2709/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2709/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2709/25000 : ℝ) ^ (4479/1024 : ℝ) ≤ (6004742243359981/100000000000000000000 : ℝ) := by
    have hpowers : (2709/25000 : ℝ)^4479 ≤ (6004742243359981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2709 : ℕ)^4479*100000000000000000000^1024 ≤ 6004742243359981^1024*25000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2709 25000 6004742243359981 100000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2709/25000 : ℝ)) (X := (6004742243359981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7739/50000 : ℝ) ^ (4479/1024 : ℝ) ≤ (5712467272188887/20000000000000000000 : ℝ) := by
    have hpowers : (7739/50000 : ℝ)^4479 ≤ (5712467272188887/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7739 : ℕ)^4479*20000000000000000000^1024 ≤ 5712467272188887^1024*50000^4479 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7739 50000 5712467272188887 20000000000000000000 4479 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7739/50000 : ℝ)) (X := (5712467272188887/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006004742243359981/50000000000000000000 : ℝ) ≤ (625017159442027/625000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (50006004742243359981/50000000000000000000 : ℝ)^1024 ≤ (625017159442027/625000000000000 : ℝ)^4479 := by
      have hnat : (50006004742243359981 : ℕ)^1024*625000000000000^4479 ≤ 625017159442027^4479*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006004742243359981 50000000000000000000 625017159442027 625000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017159442027/625000000000000 : ℝ)) (X := (50006004742243359981/50000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126080221206384513/3125000000000000000 : ℝ) ≤ (2000158035143201/2000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (3126080221206384513/3125000000000000000 : ℝ)^1024 ≤ (2000158035143201/2000000000000000 : ℝ)^4479 := by
      have hnat : (3126080221206384513 : ℕ)^1024*2000000000000000^4479 ≤ 2000158035143201^4479*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126080221206384513 3125000000000000000 2000158035143201 2000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000158035143201/2000000000000000 : ℝ)) (X := (3126080221206384513/3125000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005712467272188887/10000000000000000000 : ℝ) ≤ (5000652900179789/5000000000000000 : ℝ) ^ (4479/1024 : ℝ) := by
    have hpowers : (10005712467272188887/10000000000000000000 : ℝ)^1024 ≤ (5000652900179789/5000000000000000 : ℝ)^4479 := by
      have hnat : (10005712467272188887 : ℕ)^1024*5000000000000000^4479 ≤ 5000652900179789^4479*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005712467272188887 10000000000000000000 5000652900179789 5000000000000000 1024 4479 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000652900179789/5000000000000000 : ℝ)) (X := (10005712467272188887/10000000000000000000 : ℝ)) (by norm_num) 4479 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6004742243359981/100000000000000000000 : ℝ) ≤ ((5801262481100339411/5802500000000000000 : ℝ)+2*(515624643573/464200000000000 : ℝ)*(2709/25000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (5801262481100339411/5802500000000000000 : ℝ)+2*(515624643573/464200000000000 : ℝ)*(2709/25000 : ℝ)=(625017159442027/625000000000000 : ℝ) by norm_num, show 1+2*(6004742243359981/100000000000000000000 : ℝ)=(50006004742243359981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5712467272188887/20000000000000000000 : ℝ)+(6004742243359981/100000000000000000000 : ℝ) ≤ ((5801262481100339411/5802500000000000000 : ℝ)+(515624643573/464200000000000 : ℝ)*((7739/50000 : ℝ)+(2709/25000 : ℝ)))^(4479/1024 : ℝ) := by
    rw [show (5801262481100339411/5802500000000000000 : ℝ)+(515624643573/464200000000000 : ℝ)*((7739/50000 : ℝ)+(2709/25000 : ℝ))=(2000158035143201/2000000000000000 : ℝ) by norm_num, show 1+(5712467272188887/20000000000000000000 : ℝ)+(6004742243359981/100000000000000000000 : ℝ)=(3126080221206384513/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5712467272188887/20000000000000000000 : ℝ) ≤ ((5801262481100339411/5802500000000000000 : ℝ)+2*(515624643573/464200000000000 : ℝ)*(7739/50000 : ℝ))^(4479/1024 : ℝ) := by
    rw [show (5801262481100339411/5802500000000000000 : ℝ)+2*(515624643573/464200000000000 : ℝ)*(7739/50000 : ℝ)=(5000652900179789/5000000000000000 : ℝ) by norm_num, show 1+2*(5712467272188887/20000000000000000000 : ℝ)=(10005712467272188887/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5801262481100339411/5802500000000000000 : ℝ)*(X 1 0+X 2 0)+(515624643573/464200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (2709/25000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (5801262481100339411/5802500000000000000 : ℝ)) (alpha := (515624643573/464200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5801262481100339411/5802500000000000000 : ℝ)*(X 0 1+X 2 1)+(515624643573/464200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (2709/25000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (5801262481100339411/5802500000000000000 : ℝ)) (alpha := (515624643573/464200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5801262481100339411/5802500000000000000 : ℝ)*(X 0 2+X 1 2)+(515624643573/464200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4479/1024 : ℝ)) (lo := (2709/25000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (5801262481100339411/5802500000000000000 : ℝ)) (alpha := (515624643573/464200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1680699857/10000000000 : ℝ)*X 0 0+(1351249629/2500000000 : ℝ)*X 0 1+(2702498837/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270467971/10000000000 : ℝ)*X 1 0+(-1867154371/10000000000 : ℝ)*X 1 1+(540499789/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270467827/10000000000 : ℝ)*X 2 0+(540499833/1000000000 : ℝ)*X 2 1+(-1867153963/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((35024867/78125000 : ℝ)*X 0 0+(836858119/2000000000 : ℝ)*X 0 1+(2092145249/5000000000 : ℝ)*X 0 2+(35024867/78125000 : ℝ)*X 1 0+(836858119/2000000000 : ℝ)*X 1 1+(2092145249/5000000000 : ℝ)*X 1 2+(35024867/78125000 : ℝ)*X 2 0+(836858119/2000000000 : ℝ)*X 2 1+(2092145249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1060352911/5000000000 : ℝ)*X 0 0+(5242918239/10000000000 : ℝ)*X 0 1+(2621459441/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1345871811/2500000000 : ℝ)*X 1 0+(-1933693559/10000000000 : ℝ)*X 1 1+(5242918489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691743313/5000000000 : ℝ)*X 2 0+(1048583809/2000000000 : ℝ)*X 2 1+(-38673873/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4072853203/10000000000 : ℝ)*X 0 0+(2194659303/5000000000 : ℝ)*X 0 1+(2194659159/5000000000 : ℝ)*X 0 2+(4072853203/10000000000 : ℝ)*X 1 0+(2194659303/5000000000 : ℝ)*X 1 1+(2194659159/5000000000 : ℝ)*X 1 2+(4072853203/10000000000 : ℝ)*X 2 0+(2194659303/5000000000 : ℝ)*X 2 1+(2194659159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-253479177/1250000000 : ℝ)*X 0 0+(5129594121/10000000000 : ℝ)*X 0 1+(5425509709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((210246331/400000000 : ℝ)*X 1 0+(-58077563/312500000 : ℝ)*X 1 1+(5425509527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5256157833/10000000000 : ℝ)*X 2 0+(2712755021/5000000000 : ℝ)*X 2 1+(-464620477/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2266978597/5000000000 : ℝ)*X 0 0+(4158312129/10000000000 : ℝ)*X 0 1+(831662367/2000000000 : ℝ)*X 0 2+(2266978597/5000000000 : ℝ)*X 1 0+(4158312129/10000000000 : ℝ)*X 1 1+(831662367/2000000000 : ℝ)*X 1 2+(2266978597/5000000000 : ℝ)*X 2 0+(4158312129/10000000000 : ℝ)*X 2 1+(831662367/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-88681659/500000000 : ℝ)*X 0 0+(2757304267/5000000000 : ℝ)*X 0 1+(2613955687/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((539395119/1000000000 : ℝ)*X 1 0+(-1939673351/10000000000 : ℝ)*X 1 1+(5227910653/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1348487693/2500000000 : ℝ)*X 2 0+(653488921/1250000000 : ℝ)*X 2 1+(-1939672959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4033999999/10000000000 : ℝ)*X 0 0+(1102070267/2500000000 : ℝ)*X 0 1+(881655857/2000000000 : ℝ)*X 0 2+(4033999999/10000000000 : ℝ)*X 1 0+(1102070267/2500000000 : ℝ)*X 1 1+(881655857/2000000000 : ℝ)*X 1 2+(4033999999/10000000000 : ℝ)*X 2 0+(1102070267/2500000000 : ℝ)*X 2 1+(881655857/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1492_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-12743/20000 : ℝ) ≤ (-92422850078276343297536019231423/145062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60286853/50000000000000 : ℝ)*(upper1) + (67429993/50000000000000 : ℝ)*(lower4) + (4600731/20000000000000 : ℝ)*(upper5) + (2193700154525181/100000000000000 : ℝ)*(major0) + (2193700154525181/100000000000000 : ℝ)*(major1) + (2193700154525181/100000000000000 : ℝ)*(major2) + (1814893651/100000000000000 : ℝ)*(sp3) + (1526341301173933/50000000000000 : ℝ)*(sp4) + (3052682200614479/100000000000000 : ℝ)*(sp5) + (1526315395389321/50000000000000 : ℝ)*(sp6) + (677974151183991/50000000000000 : ℝ)*(sp7) + (2533778681/50000000000000 : ℝ)*(sp12) + (1367322687/25000000000000 : ℝ)*(sp13) + (11375825317/20000000000000 : ℝ)*(sp14) + (677975058630817/50000000000000 : ℝ)*(f.failure) + (763171917476307/25000000000000 : ℝ)*(f.sum) + (109047262192613/23210000000000000000000000000 : ℝ)*base65 + (1297877071657129109/580250000000000000000000000000000 : ℝ)*base68 + (1034076333704120891/580250000000000000000000000000000 : ℝ)*base69 + (3007933622173120891/580250000000000000000000000000000 : ℝ)*base71 + (55971275139167/23210000000000000000000000000 : ℝ)*base74 + (7096122463335370891/580250000000000000000000000000000 : ℝ)*base75 + (1910611523014120891/580250000000000000000000000000000 : ℝ)*base77 + (3193432068330870891/580250000000000000000000000000000 : ℝ)*base79 + (118783869981323/23210000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (15784433/5000000000000000000000 : ℝ)*base89 + (15784433/5000000000000000000000 : ℝ)*base91 + (15784433/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29267/50000 : ℝ) ≤ (849141983657180648074618743/1450625000000000000000000000 : ℝ) := by norm_num
    linear_combination (25521359/50000000000000 : ℝ)*(upper0) + (25367247/100000000000000 : ℝ)*(upper3) + (26080537/25000000000000 : ℝ)*(upper4) + (1134295416924801/50000000000000 : ℝ)*(major0) + (1134295416924801/50000000000000 : ℝ)*(major1) + (1134295416924801/50000000000000 : ℝ)*(major2) + (124616793017683/4000000000000 : ℝ)*(sp0) + (1557713621258233/50000000000000 : ℝ)*(sp1) + (623082808510793/20000000000000 : ℝ)*(sp2) + (1402236960075969/100000000000000 : ℝ)*(sp3) + (1462942879/100000000000000 : ℝ)*(sp5) + (733145269/5000000000000 : ℝ)*(sp6) + (3907178219/100000000000000 : ℝ)*(sp7) + (888001727/10000000000000 : ℝ)*(sp8) + (1402240867254187/100000000000000 : ℝ)*(f.failure) + (194714294091209/6250000000000 : ℝ)*(f.sum) + (7113193766343/11605000000000000000000000000 : ℝ)*base65 + (240700370998419711/290125000000000000000000000000000 : ℝ)*base67 + (547708962244705289/290125000000000000000000000000000 : ℝ)*base70 + (550075012722919711/290125000000000000000000000000000 : ℝ)*base71 + (198204246626337/11605000000000000000000000000 : ℝ)*base74 + (492828508458580289/290125000000000000000000000000000 : ℝ)*base76 + (60638207306294711/290125000000000000000000000000000 : ℝ)*base77 + (1095444257474080289/290125000000000000000000000000000 : ℝ)*base80 + (15304540957493/2901250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (118286437/10000000000000000000000 : ℝ)*base90 + (118286437/10000000000000000000000 : ℝ)*base92 + (118286437/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (80101/100000 : ℝ) ≤ (116200805996223780698280171068151/145062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24301949/50000000000000 : ℝ)*(upper1) + (18343557/50000000000000 : ℝ)*(upper2) + (349691/1250000000000 : ℝ)*(lower5) + (1232387328342851/50000000000000 : ℝ)*(major0) + (1232387328342851/50000000000000 : ℝ)*(major1) + (1232387328342851/50000000000000 : ℝ)*(major2) + (1534500491/25000000000000 : ℝ)*(sp1) + (21219990413/25000000000000 : ℝ)*(sp2) + (10725713921/100000000000000 : ℝ)*(sp3) + (279205761/20000000000000 : ℝ)*(sp4) + (3379342358456997/100000000000000 : ℝ)*(sp8) + (1689668808241919/50000000000000 : ℝ)*(sp9) + (67585177490483/2000000000000 : ℝ)*(sp10) + (761746756698291/50000000000000 : ℝ)*(sp11) + (190438029888813/12500000000000 : ℝ)*(f.failure) + (1689671877242901/50000000000000 : ℝ)*(f.sum) + (48778713152713/11605000000000000000000000000 : ℝ)*base65 + (2686970380770063261/290125000000000000000000000000000 : ℝ)*base67 + (2161598857354313261/290125000000000000000000000000000 : ℝ)*base69 + (2898277356150938261/290125000000000000000000000000000 : ℝ)*base71 + (26691390066459/5802500000000000000000000000 : ℝ)*base73 + (1432369465896438261/290125000000000000000000000000000 : ℝ)*base75 + (2803875711918438261/290125000000000000000000000000000 : ℝ)*base77 + (1824090345846563261/290125000000000000000000000000000 : ℝ)*base79 + (43287932084337/11605000000000000000000000000 : ℝ)*base82 + (893437/1250000000000000000000 : ℝ)*base89 + (893437/1250000000000000000000 : ℝ)*base91 + (893437/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-5367/6250 : ℝ) ≤ (-249129799291800262118188531458867/290125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37962671/20000000000000 : ℝ)*(lower0) + (48600113/50000000000000 : ℝ)*(upper1) + (13840237/50000000000000 : ℝ)*(lower2) + (18832461/20000000000000 : ℝ)*(upper3) + (142874691/100000000000000 : ℝ)*(upper5) + (2503360442233699/100000000000000 : ℝ)*(major0) + (2503360442233699/100000000000000 : ℝ)*(major1) + (2503360442233699/100000000000000 : ℝ)*(major2) + (242558121/100000000000000 : ℝ)*(sp4) + (165786826279/100000000000000 : ℝ)*(sp5) + (1089996680373/31250000000 : ℝ)*(sp12) + (3487823832925443/100000000000000 : ℝ)*(sp13) + (1743994809875861/50000000000000 : ℝ)*(sp14) + (309470907242529/20000000000000 : ℝ)*(sp15) + (309470907242529/20000000000000 : ℝ)*(f.failure) + (1743994809875861/50000000000000 : ℝ)*(f.sum) + (77673357459997/23210000000000000000000000000 : ℝ)*base65 + (1426056820401151211/580250000000000000000000000000000 : ℝ)*base68 + (3604507726716848789/580250000000000000000000000000000 : ℝ)*base69 + (1599460716016651211/580250000000000000000000000000000 : ℝ)*base72 + (293701836363267/23210000000000000000000000000 : ℝ)*base73 + (6221048279848789/580250000000000000000000000000000 : ℝ)*base75 + (350981689658848789/580250000000000000000000000000000 : ℝ)*base77 + (522002359844598789/580250000000000000000000000000000 : ℝ)*base79 + (168670146125857/23210000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (7403279/2000000000000000000000 : ℝ)*base90 + (7403279/2000000000000000000000 : ℝ)*base92 + (7403279/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1492_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2709/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12743/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29267/50000 : ℝ) else (80101/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5367/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1492_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1492_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2167/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12743/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29267/50000 : ℝ) else (80101/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5367/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1492_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1492_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4479/1024 : ℝ) ≤ p) (hpb : p ≤ (4481/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161783249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2167/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(12743/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(29267/50000 : ℝ) else (80101/100000 : ℝ) ≤ X j i ∧ X j i ≤ (5367/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1492_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
