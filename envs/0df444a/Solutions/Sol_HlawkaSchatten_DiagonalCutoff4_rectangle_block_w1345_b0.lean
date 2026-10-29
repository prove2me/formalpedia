-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1345_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:05:27.851331+00:00
-- url     : https://prove2.me/submissions/107b50da-f081-418c-935f-422d8b748345

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
theorem support_rectangle_w1345_s0_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1807374059/10000000000 : ℝ)*x 0 + (1199124419/2000000000 : ℝ)*x 1 + (75181629/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1807374059/10000000000 : ℝ)^4305 ≤ (10596751792597/100000000000000 : ℝ)^3281 := by
    have hnat : (1807374059 : ℕ)^4305*100000000000000^3281 ≤ 10596751792597^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807374059 10000000000 10596751792597 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199124419/2000000000 : ℝ)^4305 ≤ (25554437886977/50000000000000 : ℝ)^3281 := by
    have hnat : (1199124419 : ℕ)^4305*50000000000000^3281 ≤ 25554437886977^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199124419 2000000000 25554437886977 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (75181629/156250000 : ℝ)^4305 ≤ (19147186208713/50000000000000 : ℝ)^3281 := by
    have hnat : (75181629 : ℕ)^4305*50000000000000^3281 ≤ 19147186208713^3281*156250000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75181629 156250000 19147186208713 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1807374059/10000000000 : ℝ), (1199124419/2000000000 : ℝ), (75181629/156250000 : ℝ)] ![(10596751792597/100000000000000 : ℝ), (25554437886977/50000000000000 : ℝ), (19147186208713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1807374059/10000000000 : ℝ)|^4305 ≤ (10596751792597/100000000000000 : ℝ)^3281
        have hw : |(-1807374059/10000000000 : ℝ)|=(1807374059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199124419/2000000000 : ℝ)|^4305 ≤ (25554437886977/50000000000000 : ℝ)^3281
        have hw : |(1199124419/2000000000 : ℝ)|=(1199124419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(75181629/156250000 : ℝ)|^4305 ≤ (19147186208713/50000000000000 : ℝ)^3281
        have hw : |(75181629/156250000 : ℝ)|=(75181629/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s0_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343842291/625000000 : ℝ)*x 0 + (-620051603/2500000000 : ℝ)*x 1 + (4811624677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343842291/625000000 : ℝ)^4305 ≤ (9130884718061/20000000000000 : ℝ)^3281 := by
    have hnat : (343842291 : ℕ)^4305*20000000000000^3281 ≤ 9130884718061^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343842291 625000000 9130884718061 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (620051603/2500000000 : ℝ)^4305 ≤ (8025599791511/50000000000000 : ℝ)^3281 := by
    have hnat : (620051603 : ℕ)^4305*50000000000000^3281 ≤ 8025599791511^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      620051603 2500000000 8025599791511 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4811624677/10000000000 : ℝ)^4305 ≤ (2393398550861/6250000000000 : ℝ)^3281 := by
    have hnat : (4811624677 : ℕ)^4305*6250000000000^3281 ≤ 2393398550861^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4811624677 10000000000 2393398550861 6250000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343842291/625000000 : ℝ), (-620051603/2500000000 : ℝ), (4811624677/10000000000 : ℝ)] ![(9130884718061/20000000000000 : ℝ), (8025599791511/50000000000000 : ℝ), (2393398550861/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343842291/625000000 : ℝ)|^4305 ≤ (9130884718061/20000000000000 : ℝ)^3281
        have hw : |(343842291/625000000 : ℝ)|=(343842291/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-620051603/2500000000 : ℝ)|^4305 ≤ (8025599791511/50000000000000 : ℝ)^3281
        have hw : |(-620051603/2500000000 : ℝ)|=(620051603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4811624677/10000000000 : ℝ)|^4305 ≤ (2393398550861/6250000000000 : ℝ)^3281
        have hw : |(4811624677/10000000000 : ℝ)|=(4811624677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s0_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5501476393/10000000000 : ℝ)*x 0 + (192464977/400000000 : ℝ)*x 1 + (-2480207059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501476393/10000000000 : ℝ)^4305 ≤ (45654420726613/100000000000000 : ℝ)^3281 := by
    have hnat : (5501476393 : ℕ)^4305*100000000000000^3281 ≤ 45654420726613^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501476393 10000000000 45654420726613 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192464977/400000000 : ℝ)^4305 ≤ (38294374182231/100000000000000 : ℝ)^3281 := by
    have hnat : (192464977 : ℕ)^4305*100000000000000^3281 ≤ 38294374182231^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192464977 400000000 38294374182231 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2480207059/10000000000 : ℝ)^4305 ≤ (321024101541/2000000000000 : ℝ)^3281 := by
    have hnat : (2480207059 : ℕ)^4305*2000000000000^3281 ≤ 321024101541^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480207059 10000000000 321024101541 2000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501476393/10000000000 : ℝ), (192464977/400000000 : ℝ), (-2480207059/10000000000 : ℝ)] ![(45654420726613/100000000000000 : ℝ), (38294374182231/100000000000000 : ℝ), (321024101541/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501476393/10000000000 : ℝ)|^4305 ≤ (45654420726613/100000000000000 : ℝ)^3281
        have hw : |(5501476393/10000000000 : ℝ)|=(5501476393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192464977/400000000 : ℝ)|^4305 ≤ (38294374182231/100000000000000 : ℝ)^3281
        have hw : |(192464977/400000000 : ℝ)|=(192464977/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2480207059/10000000000 : ℝ)|^4305 ≤ (321024101541/2000000000000 : ℝ)^3281
        have hw : |(-2480207059/10000000000 : ℝ)|=(2480207059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s0_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4178297907/10000000000 : ℝ)*x 0 + (776604459/2500000000 : ℝ)*x 1 + (2794592803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4178297907/10000000000 : ℝ)^4305 ≤ (31820963548099/100000000000000 : ℝ)^3281 := by
    have hnat : (4178297907 : ℕ)^4305*100000000000000^3281 ≤ 31820963548099^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4178297907 10000000000 31820963548099 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776604459/2500000000 : ℝ)^4305 ≤ (10783610593971/50000000000000 : ℝ)^3281 := by
    have hnat : (776604459 : ℕ)^4305*50000000000000^3281 ≤ 10783610593971^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776604459 2500000000 10783610593971 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2794592803/5000000000 : ℝ)^4305 ≤ (23305907626439/50000000000000 : ℝ)^3281 := by
    have hnat : (2794592803 : ℕ)^4305*50000000000000^3281 ≤ 23305907626439^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794592803 5000000000 23305907626439 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4178297907/10000000000 : ℝ), (776604459/2500000000 : ℝ), (2794592803/5000000000 : ℝ)] ![(31820963548099/100000000000000 : ℝ), (10783610593971/50000000000000 : ℝ), (23305907626439/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4178297907/10000000000 : ℝ)|^4305 ≤ (31820963548099/100000000000000 : ℝ)^3281
        have hw : |(4178297907/10000000000 : ℝ)|=(4178297907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(776604459/2500000000 : ℝ)|^4305 ≤ (10783610593971/50000000000000 : ℝ)^3281
        have hw : |(776604459/2500000000 : ℝ)|=(776604459/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2794592803/5000000000 : ℝ)|^4305 ≤ (23305907626439/50000000000000 : ℝ)^3281
        have hw : |(2794592803/5000000000 : ℝ)|=(2794592803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s0_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-905907473/5000000000 : ℝ)*x 0 + (605261521/1250000000 : ℝ)*x 1 + (5964066289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (905907473/5000000000 : ℝ)^4305 ≤ (332216509577/3125000000000 : ℝ)^3281 := by
    have hnat : (905907473 : ℕ)^4305*3125000000000^3281 ≤ 332216509577^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905907473 5000000000 332216509577 3125000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605261521/1250000000 : ℝ)^4305 ≤ (9653212923169/25000000000000 : ℝ)^3281 := by
    have hnat : (605261521 : ℕ)^4305*25000000000000^3281 ≤ 9653212923169^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605261521 1250000000 9653212923169 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5964066289/10000000000 : ℝ)^4305 ≤ (50756219991459/100000000000000 : ℝ)^3281 := by
    have hnat : (5964066289 : ℕ)^4305*100000000000000^3281 ≤ 50756219991459^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964066289 10000000000 50756219991459 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-905907473/5000000000 : ℝ), (605261521/1250000000 : ℝ), (5964066289/10000000000 : ℝ)] ![(332216509577/3125000000000 : ℝ), (9653212923169/25000000000000 : ℝ), (50756219991459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-905907473/5000000000 : ℝ)|^4305 ≤ (332216509577/3125000000000 : ℝ)^3281
        have hw : |(-905907473/5000000000 : ℝ)|=(905907473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605261521/1250000000 : ℝ)|^4305 ≤ (9653212923169/25000000000000 : ℝ)^3281
        have hw : |(605261521/1250000000 : ℝ)|=(605261521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5964066289/10000000000 : ℝ)|^4305 ≤ (50756219991459/100000000000000 : ℝ)^3281
        have hw : |(5964066289/10000000000 : ℝ)|=(5964066289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s0_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035755909/2000000000 : ℝ)*x 0 + (-66388291/500000000 : ℝ)*x 1 + (5964066027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035755909/2000000000 : ℝ)^4305 ≤ (42173321988751/100000000000000 : ℝ)^3281 := by
    have hnat : (1035755909 : ℕ)^4305*100000000000000^3281 ≤ 42173321988751^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035755909 2000000000 42173321988751 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66388291/500000000 : ℝ)^4305 ≤ (3535230464407/50000000000000 : ℝ)^3281 := by
    have hnat : (66388291 : ℕ)^4305*50000000000000^3281 ≤ 3535230464407^3281*500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66388291 500000000 3535230464407 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5964066027/10000000000 : ℝ)^4305 ≤ (25378108532929/50000000000000 : ℝ)^3281 := by
    have hnat : (5964066027 : ℕ)^4305*50000000000000^3281 ≤ 25378108532929^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964066027 10000000000 25378108532929 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035755909/2000000000 : ℝ), (-66388291/500000000 : ℝ), (5964066027/10000000000 : ℝ)] ![(42173321988751/100000000000000 : ℝ), (3535230464407/50000000000000 : ℝ), (25378108532929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035755909/2000000000 : ℝ)|^4305 ≤ (42173321988751/100000000000000 : ℝ)^3281
        have hw : |(1035755909/2000000000 : ℝ)|=(1035755909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66388291/500000000 : ℝ)|^4305 ≤ (3535230464407/50000000000000 : ℝ)^3281
        have hw : |(-66388291/500000000 : ℝ)|=(66388291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5964066027/10000000000 : ℝ)|^4305 ≤ (25378108532929/50000000000000 : ℝ)^3281
        have hw : |(5964066027/10000000000 : ℝ)|=(5964066027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s0_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2589389761/5000000000 : ℝ)*x 0 + (2982033151/5000000000 : ℝ)*x 1 + (-1327765417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589389761/5000000000 : ℝ)^4305 ≤ (8434664348599/20000000000000 : ℝ)^3281 := by
    have hnat : (2589389761 : ℕ)^4305*20000000000000^3281 ≤ 8434664348599^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589389761 5000000000 8434664348599 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2982033151/5000000000 : ℝ)^4305 ≤ (25378110068311/50000000000000 : ℝ)^3281 := by
    have hnat : (2982033151 : ℕ)^4305*50000000000000^3281 ≤ 25378110068311^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982033151 5000000000 25378110068311 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1327765417/10000000000 : ℝ)^4305 ≤ (3535229056519/50000000000000 : ℝ)^3281 := by
    have hnat : (1327765417 : ℕ)^4305*50000000000000^3281 ≤ 3535229056519^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327765417 10000000000 3535229056519 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589389761/5000000000 : ℝ), (2982033151/5000000000 : ℝ), (-1327765417/10000000000 : ℝ)] ![(8434664348599/20000000000000 : ℝ), (25378110068311/50000000000000 : ℝ), (3535229056519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589389761/5000000000 : ℝ)|^4305 ≤ (8434664348599/20000000000000 : ℝ)^3281
        have hw : |(2589389761/5000000000 : ℝ)|=(2589389761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2982033151/5000000000 : ℝ)|^4305 ≤ (25378110068311/50000000000000 : ℝ)^3281
        have hw : |(2982033151/5000000000 : ℝ)|=(2982033151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1327765417/10000000000 : ℝ)|^4305 ≤ (3535229056519/50000000000000 : ℝ)^3281
        have hw : |(-1327765417/10000000000 : ℝ)|=(1327765417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s0_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2093804039/5000000000 : ℝ)*x 0 + (5525297277/10000000000 : ℝ)*x 1 + (3172587807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093804039/5000000000 : ℝ)^4305 ≤ (31914029198061/100000000000000 : ℝ)^3281 := by
    have hnat : (2093804039 : ℕ)^4305*100000000000000^3281 ≤ 31914029198061^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093804039 5000000000 31914029198061 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5525297277/10000000000 : ℝ)^4305 ≤ (22956985484233/50000000000000 : ℝ)^3281 := by
    have hnat : (5525297277 : ℕ)^4305*50000000000000^3281 ≤ 22956985484233^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5525297277 10000000000 22956985484233 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3172587807/10000000000 : ℝ)^4305 ≤ (22171999821087/100000000000000 : ℝ)^3281 := by
    have hnat : (3172587807 : ℕ)^4305*100000000000000^3281 ≤ 22171999821087^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3172587807 10000000000 22171999821087 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093804039/5000000000 : ℝ), (5525297277/10000000000 : ℝ), (3172587807/10000000000 : ℝ)] ![(31914029198061/100000000000000 : ℝ), (22956985484233/50000000000000 : ℝ), (22171999821087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093804039/5000000000 : ℝ)|^4305 ≤ (31914029198061/100000000000000 : ℝ)^3281
        have hw : |(2093804039/5000000000 : ℝ)|=(2093804039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5525297277/10000000000 : ℝ)|^4305 ≤ (22956985484233/50000000000000 : ℝ)^3281
        have hw : |(5525297277/10000000000 : ℝ)|=(5525297277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3172587807/10000000000 : ℝ)|^4305 ≤ (22171999821087/100000000000000 : ℝ)^3281
        have hw : |(3172587807/10000000000 : ℝ)|=(3172587807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1437/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (537/2000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (0 : ℝ) ^ (269/64 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^269 ≤ (0 : ℝ)^64 := by
      have hnat : (0 : ℕ)^269*1^64 ≤ 0^64*1^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (269/64 : ℝ) ≤ (2125242053841550767/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^269 ≤ (2125242053841550767/100000000000000000000 : ℝ)^64 := by
      have hnat : (2 : ℕ)^269*100000000000000000000^64 ≤ 2125242053841550767^64*5^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2125242053841550767 100000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2125242053841550767/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (1 : ℝ)^64 ≤ (1 : ℝ)^269 := by
      have hnat : (1 : ℕ)^64*1^269 ≤ 1^269*1^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (102125242053841550767/100000000000000000000 : ℝ) ≤ (10050158952829167/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (102125242053841550767/100000000000000000000 : ℝ)^64 ≤ (10050158952829167/10000000000000000 : ℝ)^269 := by
      have hnat : (102125242053841550767 : ℕ)^64*10000000000000000^269 ≤ 10050158952829167^269*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102125242053841550767 100000000000000000000 10050158952829167 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050158952829167/10000000000000000 : ℝ)) (X := (102125242053841550767/100000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (52125242053841550767/50000000000000000000 : ℝ) ≤ (5050158952829167/5000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (52125242053841550767/50000000000000000000 : ℝ)^64 ≤ (5050158952829167/5000000000000000 : ℝ)^269 := by
      have hnat : (52125242053841550767 : ℕ)^64*5000000000000000^269 ≤ 5050158952829167^269*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52125242053841550767 50000000000000000000 5050158952829167 5000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050158952829167/5000000000000000 : ℝ)) (X := (52125242053841550767/50000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(50158952829167/4000000000000000 : ℝ)*(0 : ℝ))^(269/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(50158952829167/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2125242053841550767/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(50158952829167/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(269/64 : ℝ) := by
    rw [show (1 : ℝ)+(50158952829167/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10050158952829167/10000000000000000 : ℝ) by norm_num, show 1+(2125242053841550767/100000000000000000000 : ℝ)+(0 : ℝ)=(102125242053841550767/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2125242053841550767/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(50158952829167/4000000000000000 : ℝ)*(2/5 : ℝ))^(269/64 : ℝ) := by
    rw [show (1 : ℝ)+2*(50158952829167/4000000000000000 : ℝ)*(2/5 : ℝ)=(5050158952829167/5000000000000000 : ℝ) by norm_num, show 1+2*(2125242053841550767/100000000000000000000 : ℝ)=(52125242053841550767/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(50158952829167/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50158952829167/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(50158952829167/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50158952829167/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(50158952829167/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50158952829167/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1807374059/10000000000 : ℝ)*X 0 0+(1199124419/2000000000 : ℝ)*X 0 1+(75181629/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((343842291/625000000 : ℝ)*X 1 0+(-620051603/2500000000 : ℝ)*X 1 1+(4811624677/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5501476393/10000000000 : ℝ)*X 2 0+(192464977/400000000 : ℝ)*X 2 1+(-2480207059/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4178297907/10000000000 : ℝ)*X 0 0+(776604459/2500000000 : ℝ)*X 0 1+(2794592803/5000000000 : ℝ)*X 0 2+(4178297907/10000000000 : ℝ)*X 1 0+(776604459/2500000000 : ℝ)*X 1 1+(2794592803/5000000000 : ℝ)*X 1 2+(4178297907/10000000000 : ℝ)*X 2 0+(776604459/2500000000 : ℝ)*X 2 1+(2794592803/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-905907473/5000000000 : ℝ)*X 0 0+(605261521/1250000000 : ℝ)*X 0 1+(5964066289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1035755909/2000000000 : ℝ)*X 1 0+(-66388291/500000000 : ℝ)*X 1 1+(5964066027/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2589389761/5000000000 : ℝ)*X 2 0+(2982033151/5000000000 : ℝ)*X 2 1+(-1327765417/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2093804039/5000000000 : ℝ)*X 0 0+(5525297277/10000000000 : ℝ)*X 0 1+(3172587807/10000000000 : ℝ)*X 0 2+(2093804039/5000000000 : ℝ)*X 1 0+(5525297277/10000000000 : ℝ)*X 1 1+(3172587807/10000000000 : ℝ)*X 1 2+(2093804039/5000000000 : ℝ)*X 2 0+(5525297277/10000000000 : ℝ)*X 2 1+(3172587807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (291966400872816426024447/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21708901/25000000000000 : ℝ)*(base1) + (8005189/50000000000000 : ℝ)*(base16) + (679650841/100000000000000 : ℝ)*(base19) + (655284829/100000000000000 : ℝ)*(base23) + (7799139/6250000000000 : ℝ)*(upper3) + (623689430538053/100000000000000 : ℝ)*(major0) + (623689430538053/100000000000000 : ℝ)*(major1) + (623689430538053/100000000000000 : ℝ)*(major2) + (21114968188447/2500000000000 : ℝ)*(sp0) + (422299900611457/50000000000000 : ℝ)*(sp1) + (844599841599303/100000000000000 : ℝ)*(sp2) + (100694263484309/25000000000000 : ℝ)*(sp3) + (1856181857/100000000000000 : ℝ)*(sp4) + (1126096993/100000000000000 : ℝ)*(sp7) + (201389133434917/50000000000000 : ℝ)*(f.failure) + (211150124221033/25000000000000 : ℝ)*(f.sum) + (323054428991851/200000000000000000000000000000 : ℝ)*base65 + (1254017828591851/400000000000000000000000000000 : ℝ)*base67 + (860838726208149/400000000000000000000000000000 : ℝ)*base70 + (2064743365791851/400000000000000000000000000000 : ℝ)*base71 + (978330443991851/200000000000000000000000000000 : ℝ)*base73 + (711363856208149/400000000000000000000000000000 : ℝ)*base76 + (786159967791851/400000000000000000000000000000 : ℝ)*base77 + (2479249348991851/400000000000000000000000000000 : ℝ)*base79 + (55290496208149/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (6582969/5000000000000000000000 : ℝ)*base90 + (6582969/5000000000000000000000 : ℝ)*base92 + (6582969/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (471496400987206970284551/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2097804089/100000000000000 : ℝ)*(base19) + (530361323/25000000000000 : ℝ)*(base23) + (5046301/50000000000000 : ℝ)*(base32) + (281576997/100000000000000 : ℝ)*(upper3) + (116636609/50000000000000 : ℝ)*(upper5) + (658164083822051/100000000000000 : ℝ)*(major0) + (658164083822051/100000000000000 : ℝ)*(major1) + (658164083822051/100000000000000 : ℝ)*(major2) + (2350363393/50000000000000 : ℝ)*(sp1) + (2571830107/50000000000000 : ℝ)*(sp2) + (891285875659121/100000000000000 : ℝ)*(sp4) + (445639538564123/50000000000000 : ℝ)*(sp5) + (178255722110723/20000000000000 : ℝ)*(sp6) + (425041967561441/100000000000000 : ℝ)*(sp7) + (425041977654043/100000000000000 : ℝ)*(f.failure) + (891285875659121/100000000000000 : ℝ)*(f.sum) + (81238555838483/200000000000000000000000000000 : ℝ)*base66 + (196203163438483/400000000000000000000000000000 : ℝ)*base68 + (3609027711838483/400000000000000000000000000000 : ℝ)*base70 + (2401401403038483/400000000000000000000000000000 : ℝ)*base72 + (612582509561517/200000000000000000000000000000 : ℝ)*base73 + (3141717629838483/400000000000000000000000000000 : ℝ)*base76 + (1697387181438483/400000000000000000000000000000 : ℝ)*base78 + (2091020904238483/400000000000000000000000000000 : ℝ)*base80 + (660132330638483/200000000000000000000000000000 : ℝ)*base82 + (4736249/10000000000000000000000 : ℝ)*base89 + (4736249/10000000000000000000000 : ℝ)*base91 + (4736249/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1345_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1437/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (537/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1345_s1_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1991752223/10000000000 : ℝ)*x 0 + (2820399217/5000000000 : ℝ)*x 1 + (504836757/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1991752223/10000000000 : ℝ)^4305 ≤ (6018616572911/50000000000000 : ℝ)^3281 := by
    have hnat : (1991752223 : ℕ)^4305*50000000000000^3281 ≤ 6018616572911^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991752223 10000000000 6018616572911 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2820399217/5000000000 : ℝ)^4305 ≤ (47177397967787/100000000000000 : ℝ)^3281 := by
    have hnat : (2820399217 : ℕ)^4305*100000000000000^3281 ≤ 47177397967787^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820399217 5000000000 47177397967787 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (504836757/1000000000 : ℝ)^4305 ≤ (20392684433231/50000000000000 : ℝ)^3281 := by
    have hnat : (504836757 : ℕ)^4305*50000000000000^3281 ≤ 20392684433231^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504836757 1000000000 20392684433231 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1991752223/10000000000 : ℝ), (2820399217/5000000000 : ℝ), (504836757/1000000000 : ℝ)] ![(6018616572911/50000000000000 : ℝ), (47177397967787/100000000000000 : ℝ), (20392684433231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1991752223/10000000000 : ℝ)|^4305 ≤ (6018616572911/50000000000000 : ℝ)^3281
        have hw : |(-1991752223/10000000000 : ℝ)|=(1991752223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2820399217/5000000000 : ℝ)|^4305 ≤ (47177397967787/100000000000000 : ℝ)^3281
        have hw : |(2820399217/5000000000 : ℝ)|=(2820399217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(504836757/1000000000 : ℝ)|^4305 ≤ (20392684433231/50000000000000 : ℝ)^3281
        have hw : |(504836757/1000000000 : ℝ)|=(504836757/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s1_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5405407433/10000000000 : ℝ)*x 0 + (-2307806579/10000000000 : ℝ)*x 1 + (5048367743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5405407433/10000000000 : ℝ)^4305 ≤ (44611229946897/100000000000000 : ℝ)^3281 := by
    have hnat : (5405407433 : ℕ)^4305*100000000000000^3281 ≤ 44611229946897^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405407433 10000000000 44611229946897 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2307806579/10000000000 : ℝ)^4305 ≤ (7301699669891/50000000000000 : ℝ)^3281 := by
    have hnat : (2307806579 : ℕ)^4305*50000000000000^3281 ≤ 7301699669891^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2307806579 10000000000 7301699669891 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5048367743/10000000000 : ℝ)^4305 ≤ (40785370700323/100000000000000 : ℝ)^3281 := by
    have hnat : (5048367743 : ℕ)^4305*100000000000000^3281 ≤ 40785370700323^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5048367743 10000000000 40785370700323 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5405407433/10000000000 : ℝ), (-2307806579/10000000000 : ℝ), (5048367743/10000000000 : ℝ)] ![(44611229946897/100000000000000 : ℝ), (7301699669891/50000000000000 : ℝ), (40785370700323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5405407433/10000000000 : ℝ)|^4305 ≤ (44611229946897/100000000000000 : ℝ)^3281
        have hw : |(5405407433/10000000000 : ℝ)|=(5405407433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2307806579/10000000000 : ℝ)|^4305 ≤ (7301699669891/50000000000000 : ℝ)^3281
        have hw : |(-2307806579/10000000000 : ℝ)|=(2307806579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5048367743/10000000000 : ℝ)|^4305 ≤ (40785370700323/100000000000000 : ℝ)^3281
        have hw : |(5048367743/10000000000 : ℝ)|=(5048367743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s1_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540540741/1000000000 : ℝ)*x 0 + (5048367469/10000000000 : ℝ)*x 1 + (-1153903479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540540741/1000000000 : ℝ)^4305 ≤ (44611229697833/100000000000000 : ℝ)^3281 := by
    have hnat : (540540741 : ℕ)^4305*100000000000000^3281 ≤ 44611229697833^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540540741 1000000000 44611229697833 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5048367469/10000000000 : ℝ)^4305 ≤ (20392683897913/50000000000000 : ℝ)^3281 := by
    have hnat : (5048367469 : ℕ)^4305*50000000000000^3281 ≤ 20392683897913^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5048367469 10000000000 20392683897913 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1153903479/5000000000 : ℝ)^4305 ≤ (14603402486521/100000000000000 : ℝ)^3281 := by
    have hnat : (1153903479 : ℕ)^4305*100000000000000^3281 ≤ 14603402486521^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1153903479 5000000000 14603402486521 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540540741/1000000000 : ℝ), (5048367469/10000000000 : ℝ), (-1153903479/5000000000 : ℝ)] ![(44611229697833/100000000000000 : ℝ), (20392683897913/50000000000000 : ℝ), (14603402486521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540540741/1000000000 : ℝ)|^4305 ≤ (44611229697833/100000000000000 : ℝ)^3281
        have hw : |(540540741/1000000000 : ℝ)|=(540540741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5048367469/10000000000 : ℝ)|^4305 ≤ (20392683897913/50000000000000 : ℝ)^3281
        have hw : |(5048367469/10000000000 : ℝ)|=(5048367469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1153903479/5000000000 : ℝ)|^4305 ≤ (14603402486521/100000000000000 : ℝ)^3281
        have hw : |(-1153903479/5000000000 : ℝ)|=(1153903479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s1_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4291771489/10000000000 : ℝ)*x 0 + (1856114197/5000000000 : ℝ)*x 1 + (990903461/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4291771489/10000000000 : ℝ)^4305 ≤ (32959641661539/100000000000000 : ℝ)^3281 := by
    have hnat : (4291771489 : ℕ)^4305*100000000000000^3281 ≤ 32959641661539^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4291771489 10000000000 32959641661539 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1856114197/5000000000 : ℝ)^4305 ≤ (6811734249647/25000000000000 : ℝ)^3281 := by
    have hnat : (1856114197 : ℕ)^4305*25000000000000^3281 ≤ 6811734249647^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1856114197 5000000000 6811734249647 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (990903461/2000000000 : ℝ)^4305 ≤ (3979342132559/10000000000000 : ℝ)^3281 := by
    have hnat : (990903461 : ℕ)^4305*10000000000000^3281 ≤ 3979342132559^3281*2000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      990903461 2000000000 3979342132559 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4291771489/10000000000 : ℝ), (1856114197/5000000000 : ℝ), (990903461/2000000000 : ℝ)] ![(32959641661539/100000000000000 : ℝ), (6811734249647/25000000000000 : ℝ), (3979342132559/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4291771489/10000000000 : ℝ)|^4305 ≤ (32959641661539/100000000000000 : ℝ)^3281
        have hw : |(4291771489/10000000000 : ℝ)|=(4291771489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1856114197/5000000000 : ℝ)|^4305 ≤ (6811734249647/25000000000000 : ℝ)^3281
        have hw : |(1856114197/5000000000 : ℝ)|=(1856114197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(990903461/2000000000 : ℝ)|^4305 ≤ (3979342132559/10000000000000 : ℝ)^3281
        have hw : |(990903461/2000000000 : ℝ)|=(990903461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s1_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-996141693/5000000000 : ℝ)*x 0 + (5055784291/10000000000 : ℝ)*x 1 + (563324711/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (996141693/5000000000 : ℝ)^4305 ≤ (481657811967/4000000000000 : ℝ)^3281 := by
    have hnat : (996141693 : ℕ)^4305*4000000000000^3281 ≤ 481657811967^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      996141693 5000000000 481657811967 4000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5055784291/10000000000 : ℝ)^4305 ≤ (40864006749643/100000000000000 : ℝ)^3281 := by
    have hnat : (5055784291 : ℕ)^4305*100000000000000^3281 ≤ 40864006749643^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5055784291 10000000000 40864006749643 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563324711/1000000000 : ℝ)^4305 ≤ (9418909587561/20000000000000 : ℝ)^3281 := by
    have hnat : (563324711 : ℕ)^4305*20000000000000^3281 ≤ 9418909587561^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563324711 1000000000 9418909587561 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-996141693/5000000000 : ℝ), (5055784291/10000000000 : ℝ), (563324711/1000000000 : ℝ)] ![(481657811967/4000000000000 : ℝ), (40864006749643/100000000000000 : ℝ), (9418909587561/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-996141693/5000000000 : ℝ)|^4305 ≤ (481657811967/4000000000000 : ℝ)^3281
        have hw : |(-996141693/5000000000 : ℝ)|=(996141693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5055784291/10000000000 : ℝ)|^4305 ≤ (40864006749643/100000000000000 : ℝ)^3281
        have hw : |(5055784291/10000000000 : ℝ)|=(5055784291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563324711/1000000000 : ℝ)|^4305 ≤ (9418909587561/20000000000000 : ℝ)^3281
        have hw : |(563324711/1000000000 : ℝ)|=(563324711/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s1_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525164119/1000000000 : ℝ)*x 0 + (-107682929/625000000 : ℝ)*x 1 + (352077947/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525164119/1000000000 : ℝ)^4305 ≤ (4295355745273/10000000000000 : ℝ)^3281 := by
    have hnat : (525164119 : ℕ)^4305*10000000000000^3281 ≤ 4295355745273^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525164119 1000000000 4295355745273 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107682929/625000000 : ℝ)^4305 ≤ (4975947067161/50000000000000 : ℝ)^3281 := by
    have hnat : (107682929 : ℕ)^4305*50000000000000^3281 ≤ 4975947067161^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107682929 625000000 4975947067161 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (352077947/625000000 : ℝ)^4305 ≤ (9418909679703/20000000000000 : ℝ)^3281 := by
    have hnat : (352077947 : ℕ)^4305*20000000000000^3281 ≤ 9418909679703^3281*625000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352077947 625000000 9418909679703 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525164119/1000000000 : ℝ), (-107682929/625000000 : ℝ), (352077947/625000000 : ℝ)] ![(4295355745273/10000000000000 : ℝ), (4975947067161/50000000000000 : ℝ), (9418909679703/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525164119/1000000000 : ℝ)|^4305 ≤ (4295355745273/10000000000000 : ℝ)^3281
        have hw : |(525164119/1000000000 : ℝ)|=(525164119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-107682929/625000000 : ℝ)|^4305 ≤ (4975947067161/50000000000000 : ℝ)^3281
        have hw : |(-107682929/625000000 : ℝ)|=(107682929/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(352077947/625000000 : ℝ)|^4305 ≤ (9418909679703/20000000000000 : ℝ)^3281
        have hw : |(352077947/625000000 : ℝ)|=(352077947/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s1_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251641091/10000000000 : ℝ)*x 0 + (2816623609/5000000000 : ℝ)*x 1 + (-1722926909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251641091/10000000000 : ℝ)^4305 ≤ (8590711278057/20000000000000 : ℝ)^3281 := by
    have hnat : (5251641091 : ℕ)^4305*20000000000000^3281 ≤ 8590711278057^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251641091 10000000000 8590711278057 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2816623609/5000000000 : ℝ)^4305 ≤ (47094549122489/100000000000000 : ℝ)^3281 := by
    have hnat : (2816623609 : ℕ)^4305*100000000000000^3281 ≤ 47094549122489^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2816623609 5000000000 47094549122489 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1722926909/10000000000 : ℝ)^4305 ≤ (9951894475373/100000000000000 : ℝ)^3281 := by
    have hnat : (1722926909 : ℕ)^4305*100000000000000^3281 ≤ 9951894475373^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1722926909 10000000000 9951894475373 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251641091/10000000000 : ℝ), (2816623609/5000000000 : ℝ), (-1722926909/10000000000 : ℝ)] ![(8590711278057/20000000000000 : ℝ), (47094549122489/100000000000000 : ℝ), (9951894475373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251641091/10000000000 : ℝ)|^4305 ≤ (8590711278057/20000000000000 : ℝ)^3281
        have hw : |(5251641091/10000000000 : ℝ)|=(5251641091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2816623609/5000000000 : ℝ)|^4305 ≤ (47094549122489/100000000000000 : ℝ)^3281
        have hw : |(2816623609/5000000000 : ℝ)|=(2816623609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1722926909/10000000000 : ℝ)|^4305 ≤ (9951894475373/100000000000000 : ℝ)^3281
        have hw : |(-1722926909/10000000000 : ℝ)|=(1722926909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s1_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4292885517/10000000000 : ℝ)*x 0 + (493896527/1000000000 : ℝ)*x 1 + (466007759/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4292885517/10000000000 : ℝ)^4305 ≤ (8242716924919/25000000000000 : ℝ)^3281 := by
    have hnat : (4292885517 : ℕ)^4305*25000000000000^3281 ≤ 8242716924919^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4292885517 10000000000 8242716924919 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493896527/1000000000 : ℝ)^4305 ≤ (39629607277379/100000000000000 : ℝ)^3281 := by
    have hnat : (493896527 : ℕ)^4305*100000000000000^3281 ≤ 39629607277379^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493896527 1000000000 39629607277379 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466007759/1250000000 : ℝ)^4305 ≤ (2739952501241/10000000000000 : ℝ)^3281 := by
    have hnat : (466007759 : ℕ)^4305*10000000000000^3281 ≤ 2739952501241^3281*1250000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466007759 1250000000 2739952501241 10000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4292885517/10000000000 : ℝ), (493896527/1000000000 : ℝ), (466007759/1250000000 : ℝ)] ![(8242716924919/25000000000000 : ℝ), (39629607277379/100000000000000 : ℝ), (2739952501241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4292885517/10000000000 : ℝ)|^4305 ≤ (8242716924919/25000000000000 : ℝ)^3281
        have hw : |(4292885517/10000000000 : ℝ)|=(4292885517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(493896527/1000000000 : ℝ)|^4305 ≤ (39629607277379/100000000000000 : ℝ)^3281
        have hw : |(493896527/1000000000 : ℝ)|=(493896527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466007759/1250000000 : ℝ)|^4305 ≤ (2739952501241/10000000000000 : ℝ)^3281
        have hw : |(466007759/1250000000 : ℝ)|=(466007759/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (537/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3459/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19439/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (537/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (537/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1437/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (537/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (537/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1437/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (537/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (537/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1437/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1437/100000 : ℝ) ^ (269/64 : ℝ) ≤ (450298486479/25000000000000000000 : ℝ) := by
    have hpowers : (1437/100000 : ℝ)^269 ≤ (450298486479/25000000000000000000 : ℝ)^64 := by
      have hnat : (1437 : ℕ)^269*25000000000000000000^64 ≤ 450298486479^64*100000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1437 100000 450298486479 25000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1437/100000 : ℝ)) (X := (450298486479/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (537/2000 : ℝ) ^ (269/64 : ℝ) ≤ (397906898952308789/100000000000000000000 : ℝ) := by
    have hpowers : (537/2000 : ℝ)^269 ≤ (397906898952308789/100000000000000000000 : ℝ)^64 := by
      have hnat : (537 : ℕ)^269*100000000000000000000^64 ≤ 397906898952308789^64*2000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        537 2000 397906898952308789 100000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (537/2000 : ℝ)) (X := (397906898952308789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000450298486479/12500000000000000000 : ℝ) ≤ (10000000085707369/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (12500000450298486479/12500000000000000000 : ℝ)^64 ≤ (10000000085707369/10000000000000000 : ℝ)^269 := by
      have hnat : (12500000450298486479 : ℕ)^64*10000000000000000^269 ≤ 10000000085707369^269*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000450298486479 12500000000000000000 10000000085707369 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000085707369/10000000000000000 : ℝ)) (X := (12500000450298486479/12500000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (20079581740029250941/20000000000000000000 : ℝ) ≤ (10009452652471241/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (20079581740029250941/20000000000000000000 : ℝ)^64 ≤ (10009452652471241/10000000000000000 : ℝ)^269 := by
      have hnat : (20079581740029250941 : ℕ)^64*10000000000000000^269 ≤ 10009452652471241^269*20000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20079581740029250941 20000000000000000000 10009452652471241 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009452652471241/10000000000000000 : ℝ)) (X := (20079581740029250941/20000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50397906898952308789/50000000000000000000 : ℝ) ≤ (10018905219235113/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (50397906898952308789/50000000000000000000 : ℝ)^64 ≤ (10018905219235113/10000000000000000 : ℝ)^269 := by
      have hnat : (50397906898952308789 : ℕ)^64*10000000000000000^269 ≤ 10018905219235113^269*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50397906898952308789 50000000000000000000 10018905219235113 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10018905219235113/10000000000000000 : ℝ)) (X := (50397906898952308789/50000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(450298486479/25000000000000000000 : ℝ) ≤ ((84700945167067333423/84710000000000000000 : ℝ)+2*(295392711371/79415625000000 : ℝ)*(1437/100000 : ℝ))^(269/64 : ℝ) := by
    rw [show (84700945167067333423/84710000000000000000 : ℝ)+2*(295392711371/79415625000000 : ℝ)*(1437/100000 : ℝ)=(10000000085707369/10000000000000000 : ℝ) by norm_num, show 1+2*(450298486479/25000000000000000000 : ℝ)=(12500000450298486479/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(397906898952308789/100000000000000000000 : ℝ)+(450298486479/25000000000000000000 : ℝ) ≤ ((84700945167067333423/84710000000000000000 : ℝ)+(295392711371/79415625000000 : ℝ)*((537/2000 : ℝ)+(1437/100000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (84700945167067333423/84710000000000000000 : ℝ)+(295392711371/79415625000000 : ℝ)*((537/2000 : ℝ)+(1437/100000 : ℝ))=(10009452652471241/10000000000000000 : ℝ) by norm_num, show 1+(397906898952308789/100000000000000000000 : ℝ)+(450298486479/25000000000000000000 : ℝ)=(20079581740029250941/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(397906898952308789/100000000000000000000 : ℝ) ≤ ((84700945167067333423/84710000000000000000 : ℝ)+2*(295392711371/79415625000000 : ℝ)*(537/2000 : ℝ))^(269/64 : ℝ) := by
    rw [show (84700945167067333423/84710000000000000000 : ℝ)+2*(295392711371/79415625000000 : ℝ)*(537/2000 : ℝ)=(10018905219235113/10000000000000000 : ℝ) by norm_num, show 1+2*(397906898952308789/100000000000000000000 : ℝ)=(50397906898952308789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84700945167067333423/84710000000000000000 : ℝ)*(X 1 0+X 2 0)+(295392711371/79415625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (1437/100000 : ℝ)) (hi := (537/2000 : ℝ)) (c := (84700945167067333423/84710000000000000000 : ℝ)) (alpha := (295392711371/79415625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84700945167067333423/84710000000000000000 : ℝ)*(X 0 1+X 2 1)+(295392711371/79415625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (1437/100000 : ℝ)) (hi := (537/2000 : ℝ)) (c := (84700945167067333423/84710000000000000000 : ℝ)) (alpha := (295392711371/79415625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84700945167067333423/84710000000000000000 : ℝ)*(X 0 2+X 1 2)+(295392711371/79415625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (1437/100000 : ℝ)) (hi := (537/2000 : ℝ)) (c := (84700945167067333423/84710000000000000000 : ℝ)) (alpha := (295392711371/79415625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1991752223/10000000000 : ℝ)*X 0 0+(2820399217/5000000000 : ℝ)*X 0 1+(504836757/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5405407433/10000000000 : ℝ)*X 1 0+(-2307806579/10000000000 : ℝ)*X 1 1+(5048367743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((540540741/1000000000 : ℝ)*X 2 0+(5048367469/10000000000 : ℝ)*X 2 1+(-1153903479/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4291771489/10000000000 : ℝ)*X 0 0+(1856114197/5000000000 : ℝ)*X 0 1+(990903461/2000000000 : ℝ)*X 0 2+(4291771489/10000000000 : ℝ)*X 1 0+(1856114197/5000000000 : ℝ)*X 1 1+(990903461/2000000000 : ℝ)*X 1 2+(4291771489/10000000000 : ℝ)*X 2 0+(1856114197/5000000000 : ℝ)*X 2 1+(990903461/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-996141693/5000000000 : ℝ)*X 0 0+(5055784291/10000000000 : ℝ)*X 0 1+(563324711/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((525164119/1000000000 : ℝ)*X 1 0+(-107682929/625000000 : ℝ)*X 1 1+(352077947/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5251641091/10000000000 : ℝ)*X 2 0+(2816623609/5000000000 : ℝ)*X 2 1+(-1722926909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4292885517/10000000000 : ℝ)*X 0 0+(493896527/1000000000 : ℝ)*X 0 1+(466007759/1250000000 : ℝ)*X 0 2+(4292885517/10000000000 : ℝ)*X 1 0+(493896527/1000000000 : ℝ)*X 1 1+(466007759/1250000000 : ℝ)*X 1 2+(4292885517/10000000000 : ℝ)*X 2 0+(493896527/1000000000 : ℝ)*X 2 1+(466007759/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6261032763328356718554867489/2117750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (760949/10000000000000 : ℝ)*(base1) + (32237801/100000000000000 : ℝ)*(base16) + (115613943/50000000000000 : ℝ)*(base19) + (256283407/100000000000000 : ℝ)*(base23) + (13933649/20000000000000 : ℝ)*(upper3) + (1246464871935381/100000000000000 : ℝ)*(major0) + (1246464871935381/100000000000000 : ℝ)*(major1) + (1246464871935381/100000000000000 : ℝ)*(major2) + (337592490213309/20000000000000 : ℝ)*(sp0) + (210995387720701/12500000000000 : ℝ)*(sp1) + (1687963108947889/100000000000000 : ℝ)*(sp2) + (201241462464163/25000000000000 : ℝ)*(sp3) + (921774241/100000000000000 : ℝ)*(sp4) + (211312407/50000000000000 : ℝ)*(sp7) + (160993256018191/20000000000000 : ℝ)*(f.failure) + (26374427581739/1562500000000 : ℝ)*(f.sum) + (105006573265531/42355000000000000000000000000 : ℝ)*base66 + (96110714023947060837/8471000000000000000000000000000000 : ℝ)*base68 + (91290980157776060837/8471000000000000000000000000000000 : ℝ)*base70 + (1004619892981939163/8471000000000000000000000000000000 : ℝ)*base71 + (80124847647759/10588750000000000000000000000 : ℝ)*base74 + (48074848657840060837/8471000000000000000000000000000000 : ℝ)*base76 + (29469745224464060837/8471000000000000000000000000000000 : ℝ)*base78 + (91720908659827060837/8471000000000000000000000000000000 : ℝ)*base80 + (102163077730693/21177500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6921013/2000000000000000000000 : ℝ)*base89 + (6921013/2000000000000000000000 : ℝ)*base91 + (6921013/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225122254133351922224007/42355000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5987939/10000000000000 : ℝ)*(base1) + (546095911/50000000000000 : ℝ)*(base19) + (264115649/25000000000000 : ℝ)*(base23) + (61284651/50000000000000 : ℝ)*(upper3) + (114641377/100000000000000 : ℝ)*(upper5) + (639385768824411/50000000000000 : ℝ)*(major0) + (639385768824411/50000000000000 : ℝ)*(major1) + (639385768824411/50000000000000 : ℝ)*(major2) + (5606378389/100000000000000 : ℝ)*(sp1) + (5501036583/100000000000000 : ℝ)*(sp2) + (216464131528373/12500000000000 : ℝ)*(sp4) + (865853146888691/50000000000000 : ℝ)*(sp5) + (865853217424207/50000000000000 : ℝ)*(sp6) + (825829845899717/100000000000000 : ℝ)*(sp7) + (825829905779107/100000000000000 : ℝ)*(f.failure) + (1731712992347593/100000000000000 : ℝ)*(f.sum) + (20941240534147/42355000000000000000000000000 : ℝ)*base66 + (3261853630032011147/4235500000000000000000000000000000 : ℝ)*base68 + (13981535345047011147/4235500000000000000000000000000000 : ℝ)*base70 + (11617069169661988853/4235500000000000000000000000000000 : ℝ)*base71 + (10996559554477/42355000000000000000000000000 : ℝ)*base74 + (28918125173042488853/4235500000000000000000000000000000 : ℝ)*base75 + (21633477380373488853/4235500000000000000000000000000000 : ℝ)*base77 + (1312771129924511147/4235500000000000000000000000000000 : ℝ)*base80 + (9163313233337/2647187500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (25690799/10000000000000000000000 : ℝ)*base90 + (25690799/10000000000000000000000 : ℝ)*base92 + (25690799/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1345_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (537/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1437/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3459/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19439/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1345_s2_0 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-203164983/1000000000 : ℝ)*x 0 + (5478929433/10000000000 : ℝ)*x 1 + (2592337723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (203164983/1000000000 : ℝ)^4305 ≤ (6177297386957/50000000000000 : ℝ)^3281 := by
    have hnat : (203164983 : ℕ)^4305*50000000000000^3281 ≤ 6177297386957^3281*1000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203164983 1000000000 6177297386957 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478929433/10000000000 : ℝ)^4305 ≤ (22704536962577/50000000000000 : ℝ)^3281 := by
    have hnat : (5478929433 : ℕ)^4305*50000000000000^3281 ≤ 22704536962577^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478929433 10000000000 22704536962577 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592337723/5000000000 : ℝ)^4305 ≤ (21118165642201/50000000000000 : ℝ)^3281 := by
    have hnat : (2592337723 : ℕ)^4305*50000000000000^3281 ≤ 21118165642201^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592337723 5000000000 21118165642201 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-203164983/1000000000 : ℝ), (5478929433/10000000000 : ℝ), (2592337723/5000000000 : ℝ)] ![(6177297386957/50000000000000 : ℝ), (22704536962577/50000000000000 : ℝ), (21118165642201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-203164983/1000000000 : ℝ)|^4305 ≤ (6177297386957/50000000000000 : ℝ)^3281
        have hw : |(-203164983/1000000000 : ℝ)|=(203164983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478929433/10000000000 : ℝ)|^4305 ≤ (22704536962577/50000000000000 : ℝ)^3281
        have hw : |(5478929433/10000000000 : ℝ)|=(5478929433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592337723/5000000000 : ℝ)|^4305 ≤ (21118165642201/50000000000000 : ℝ)^3281
        have hw : |(2592337723/5000000000 : ℝ)|=(2592337723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s2_1 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5365742443/10000000000 : ℝ)*x 0 + (-3411981/15625000 : ℝ)*x 1 + (2592337919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5365742443/10000000000 : ℝ)^4305 ≤ (44182196053951/100000000000000 : ℝ)^3281 := by
    have hnat : (5365742443 : ℕ)^4305*100000000000000^3281 ≤ 44182196053951^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5365742443 10000000000 44182196053951 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3411981/15625000 : ℝ)^4305 ≤ (848841778379/6250000000000 : ℝ)^3281 := by
    have hnat : (3411981 : ℕ)^4305*6250000000000^3281 ≤ 848841778379^3281*15625000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3411981 15625000 848841778379 6250000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592337919/5000000000 : ℝ)^4305 ≤ (10559083868609/25000000000000 : ℝ)^3281 := by
    have hnat : (2592337919 : ℕ)^4305*25000000000000^3281 ≤ 10559083868609^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592337919 5000000000 10559083868609 25000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5365742443/10000000000 : ℝ), (-3411981/15625000 : ℝ), (2592337919/5000000000 : ℝ)] ![(44182196053951/100000000000000 : ℝ), (848841778379/6250000000000 : ℝ), (10559083868609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5365742443/10000000000 : ℝ)|^4305 ≤ (44182196053951/100000000000000 : ℝ)^3281
        have hw : |(5365742443/10000000000 : ℝ)|=(5365742443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3411981/15625000 : ℝ)|^4305 ≤ (848841778379/6250000000000 : ℝ)^3281
        have hw : |(-3411981/15625000 : ℝ)|=(3411981/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592337919/5000000000 : ℝ)|^4305 ≤ (10559083868609/25000000000000 : ℝ)^3281
        have hw : |(2592337919/5000000000 : ℝ)|=(2592337919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s2_2 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214629701/400000000 : ℝ)*x 0 + (162021117/312500000 : ℝ)*x 1 + (-1091833927/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214629701/400000000 : ℝ)^4305 ≤ (44182196939879/100000000000000 : ℝ)^3281 := by
    have hnat : (214629701 : ℕ)^4305*100000000000000^3281 ≤ 44182196939879^3281*400000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214629701 400000000 44182196939879 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162021117/312500000 : ℝ)^4305 ≤ (42236334469683/100000000000000 : ℝ)^3281 := by
    have hnat : (162021117 : ℕ)^4305*100000000000000^3281 ≤ 42236334469683^3281*312500000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162021117 312500000 42236334469683 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091833927/5000000000 : ℝ)^4305 ≤ (6790734284157/50000000000000 : ℝ)^3281 := by
    have hnat : (1091833927 : ℕ)^4305*50000000000000^3281 ≤ 6790734284157^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091833927 5000000000 6790734284157 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214629701/400000000 : ℝ), (162021117/312500000 : ℝ), (-1091833927/5000000000 : ℝ)] ![(44182196939879/100000000000000 : ℝ), (42236334469683/100000000000000 : ℝ), (6790734284157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214629701/400000000 : ℝ)|^4305 ≤ (44182196939879/100000000000000 : ℝ)^3281
        have hw : |(214629701/400000000 : ℝ)|=(214629701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162021117/312500000 : ℝ)|^4305 ≤ (42236334469683/100000000000000 : ℝ)^3281
        have hw : |(162021117/312500000 : ℝ)|=(162021117/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1091833927/5000000000 : ℝ)|^4305 ≤ (6790734284157/50000000000000 : ℝ)^3281
        have hw : |(-1091833927/5000000000 : ℝ)|=(1091833927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s2_3 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159839863/5000000000 : ℝ)*x 0 + (201071051/500000000 : ℝ)*x 1 + (4638452289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159839863/5000000000 : ℝ)^4305 ≤ (33241145967007/100000000000000 : ℝ)^3281 := by
    have hnat : (2159839863 : ℕ)^4305*100000000000000^3281 ≤ 33241145967007^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159839863 5000000000 33241145967007 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201071051/500000000 : ℝ)^4305 ≤ (756565302681/2500000000000 : ℝ)^3281 := by
    have hnat : (201071051 : ℕ)^4305*2500000000000^3281 ≤ 756565302681^3281*500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201071051 500000000 756565302681 2500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4638452289/10000000000 : ℝ)^4305 ≤ (4562030238363/12500000000000 : ℝ)^3281 := by
    have hnat : (4638452289 : ℕ)^4305*12500000000000^3281 ≤ 4562030238363^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4638452289 10000000000 4562030238363 12500000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159839863/5000000000 : ℝ), (201071051/500000000 : ℝ), (4638452289/10000000000 : ℝ)] ![(33241145967007/100000000000000 : ℝ), (756565302681/2500000000000 : ℝ), (4562030238363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159839863/5000000000 : ℝ)|^4305 ≤ (33241145967007/100000000000000 : ℝ)^3281
        have hw : |(2159839863/5000000000 : ℝ)|=(2159839863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201071051/500000000 : ℝ)|^4305 ≤ (756565302681/2500000000000 : ℝ)^3281
        have hw : |(201071051/500000000 : ℝ)|=(201071051/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4638452289/10000000000 : ℝ)|^4305 ≤ (4562030238363/12500000000000 : ℝ)^3281
        have hw : |(4638452289/10000000000 : ℝ)|=(4638452289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s2_4 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031714917/10000000000 : ℝ)*x 0 + (2593257637/5000000000 : ℝ)*x 1 + (5477073077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031714917/10000000000 : ℝ)^4305 ≤ (12355114103423/100000000000000 : ℝ)^3281 := by
    have hnat : (2031714917 : ℕ)^4305*100000000000000^3281 ≤ 12355114103423^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031714917 10000000000 12355114103423 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593257637/5000000000 : ℝ)^4305 ≤ (42255998043973/100000000000000 : ℝ)^3281 := by
    have hnat : (2593257637 : ℕ)^4305*100000000000000^3281 ≤ 42255998043973^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593257637 5000000000 42255998043973 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477073077/10000000000 : ℝ)^4305 ≤ (22694443918513/50000000000000 : ℝ)^3281 := by
    have hnat : (5477073077 : ℕ)^4305*50000000000000^3281 ≤ 22694443918513^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477073077 10000000000 22694443918513 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031714917/10000000000 : ℝ), (2593257637/5000000000 : ℝ), (5477073077/10000000000 : ℝ)] ![(12355114103423/100000000000000 : ℝ), (42255998043973/100000000000000 : ℝ), (22694443918513/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031714917/10000000000 : ℝ)|^4305 ≤ (12355114103423/100000000000000 : ℝ)^3281
        have hw : |(-2031714917/10000000000 : ℝ)|=(2031714917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593257637/5000000000 : ℝ)|^4305 ≤ (42255998043973/100000000000000 : ℝ)^3281
        have hw : |(2593257637/5000000000 : ℝ)|=(2593257637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477073077/10000000000 : ℝ)|^4305 ≤ (22694443918513/50000000000000 : ℝ)^3281
        have hw : |(5477073077/10000000000 : ℝ)|=(5477073077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s2_5 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644936917/5000000000 : ℝ)*x 0 + (-945635151/5000000000 : ℝ)*x 1 + (1369268267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644936917/5000000000 : ℝ)^4305 ≤ (338783800237/781250000000 : ℝ)^3281 := by
    have hnat : (2644936917 : ℕ)^4305*781250000000^3281 ≤ 338783800237^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644936917 5000000000 338783800237 781250000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945635151/5000000000 : ℝ)^4305 ≤ (702924113609/6250000000000 : ℝ)^3281 := by
    have hnat : (945635151 : ℕ)^4305*6250000000000^3281 ≤ 702924113609^3281*5000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945635151 5000000000 702924113609 6250000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369268267/2500000000 : ℝ)^4305 ≤ (9077777547833/20000000000000 : ℝ)^3281 := by
    have hnat : (1369268267 : ℕ)^4305*20000000000000^3281 ≤ 9077777547833^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369268267 2500000000 9077777547833 20000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644936917/5000000000 : ℝ), (-945635151/5000000000 : ℝ), (1369268267/2500000000 : ℝ)] ![(338783800237/781250000000 : ℝ), (702924113609/6250000000000 : ℝ), (9077777547833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644936917/5000000000 : ℝ)|^4305 ≤ (338783800237/781250000000 : ℝ)^3281
        have hw : |(2644936917/5000000000 : ℝ)|=(2644936917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945635151/5000000000 : ℝ)|^4305 ≤ (702924113609/6250000000000 : ℝ)^3281
        have hw : |(-945635151/5000000000 : ℝ)|=(945635151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369268267/2500000000 : ℝ)|^4305 ≤ (9077777547833/20000000000000 : ℝ)^3281
        have hw : |(1369268267/2500000000 : ℝ)|=(1369268267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s2_6 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289873841/10000000000 : ℝ)*x 0 + (1369268271/2500000000 : ℝ)*x 1 + (-1891270271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289873841/10000000000 : ℝ)^4305 ≤ (43364326505629/100000000000000 : ℝ)^3281 := by
    have hnat : (5289873841 : ℕ)^4305*100000000000000^3281 ≤ 43364326505629^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289873841 10000000000 43364326505629 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369268271/2500000000 : ℝ)^4305 ≤ (2269444395657/5000000000000 : ℝ)^3281 := by
    have hnat : (1369268271 : ℕ)^4305*5000000000000^3281 ≤ 2269444395657^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369268271 2500000000 2269444395657 5000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1891270271/10000000000 : ℝ)^4305 ≤ (5623392787931/50000000000000 : ℝ)^3281 := by
    have hnat : (1891270271 : ℕ)^4305*50000000000000^3281 ≤ 5623392787931^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891270271 10000000000 5623392787931 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289873841/10000000000 : ℝ), (1369268271/2500000000 : ℝ), (-1891270271/10000000000 : ℝ)] ![(43364326505629/100000000000000 : ℝ), (2269444395657/5000000000000 : ℝ), (5623392787931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289873841/10000000000 : ℝ)|^4305 ≤ (43364326505629/100000000000000 : ℝ)^3281
        have hw : |(5289873841/10000000000 : ℝ)|=(5289873841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369268271/2500000000 : ℝ)|^4305 ≤ (2269444395657/5000000000000 : ℝ)^3281
        have hw : |(1369268271/2500000000 : ℝ)|=(1369268271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1891270271/10000000000 : ℝ)|^4305 ≤ (5623392787931/50000000000000 : ℝ)^3281
        have hw : |(-1891270271/10000000000 : ℝ)|=(1891270271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1345_s2_7 (p : ℝ) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319816561/10000000000 : ℝ)*x 0 + (4634594931/10000000000 : ℝ)*x 1 + (1006328269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319816561/10000000000 : ℝ)^4305 ≤ (33242527593677/100000000000000 : ℝ)^3281 := by
    have hnat : (4319816561 : ℕ)^4305*100000000000000^3281 ≤ 33242527593677^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319816561 10000000000 33242527593677 100000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4634594931/10000000000 : ℝ)^4305 ≤ (1822821213179/5000000000000 : ℝ)^3281 := by
    have hnat : (4634594931 : ℕ)^4305*5000000000000^3281 ≤ 1822821213179^3281*10000000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634594931 10000000000 1822821213179 5000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006328269/2500000000 : ℝ)^4305 ≤ (15150524065157/50000000000000 : ℝ)^3281 := by
    have hnat : (1006328269 : ℕ)^4305*50000000000000^3281 ≤ 15150524065157^3281*2500000000^4305 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006328269 2500000000 15150524065157 50000000000000 4305 3281 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4305/1024 : ℝ)) 4305 3281 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319816561/10000000000 : ℝ), (4634594931/10000000000 : ℝ), (1006328269/2500000000 : ℝ)] ![(33242527593677/100000000000000 : ℝ), (1822821213179/5000000000000 : ℝ), (15150524065157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319816561/10000000000 : ℝ)|^4305 ≤ (33242527593677/100000000000000 : ℝ)^3281
        have hw : |(4319816561/10000000000 : ℝ)|=(4319816561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4634594931/10000000000 : ℝ)|^4305 ≤ (1822821213179/5000000000000 : ℝ)^3281
        have hw : |(4634594931/10000000000 : ℝ)|=(4634594931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006328269/2500000000 : ℝ)|^4305 ≤ (15150524065157/50000000000000 : ℝ)^3281
        have hw : |(1006328269/2500000000 : ℝ)|=(1006328269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1345_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19439/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9871/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4023/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19439/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3459/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19439/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3459/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19439/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3459/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19439/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3459/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19439/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3459/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19439/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3459/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3459/50000 : ℝ) ^ (269/64 : ℝ) ≤ (665676592361057/50000000000000000000 : ℝ) := by
    have hpowers : (3459/50000 : ℝ)^269 ≤ (665676592361057/50000000000000000000 : ℝ)^64 := by
      have hnat : (3459 : ℕ)^269*50000000000000000000^64 ≤ 665676592361057^64*50000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3459 50000 665676592361057 50000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3459/50000 : ℝ)) (X := (665676592361057/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hpowhi : (19439/100000 : ℝ) ^ (269/64 : ℝ) ≤ (51189109363038099/50000000000000000000 : ℝ) := by
    have hpowers : (19439/100000 : ℝ)^269 ≤ (51189109363038099/50000000000000000000 : ℝ)^64 := by
      have hnat : (19439 : ℕ)^269*50000000000000000000^64 ≤ 51189109363038099^64*100000^269 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19439 100000 51189109363038099 50000000000000000000 269 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19439/100000 : ℝ)) (X := (51189109363038099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000665676592361057/25000000000000000000 : ℝ) ≤ (10000063349992067/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (25000665676592361057/25000000000000000000 : ℝ)^64 ≤ (10000063349992067/10000000000000000 : ℝ)^269 := by
      have hnat : (25000665676592361057 : ℕ)^64*10000000000000000^269 ≤ 10000063349992067^269*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000665676592361057 25000000000000000000 10000063349992067 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063349992067/10000000000000000 : ℝ)) (X := (25000665676592361057/25000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (12512963696488849789/12500000000000000000 : ℝ) ≤ (10002466465150023/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (12512963696488849789/12500000000000000000 : ℝ)^64 ≤ (10002466465150023/10000000000000000 : ℝ)^269 := by
      have hnat : (12512963696488849789 : ℕ)^64*10000000000000000^269 ≤ 10002466465150023^269*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12512963696488849789 12500000000000000000 10002466465150023 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002466465150023/10000000000000000 : ℝ)) (X := (12512963696488849789/12500000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (25051189109363038099/25000000000000000000 : ℝ) ≤ (10004869580307979/10000000000000000 : ℝ) ^ (269/64 : ℝ) := by
    have hpowers : (25051189109363038099/25000000000000000000 : ℝ)^64 ≤ (10004869580307979/10000000000000000 : ℝ)^269 := by
      have hnat : (25051189109363038099 : ℕ)^64*10000000000000000^269 ≤ 10004869580307979^269*25000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25051189109363038099 25000000000000000000 10004869580307979 10000000000000000 64 269 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004869580307979/10000000000000000 : ℝ)) (X := (25051189109363038099/25000000000000000000 : ℝ)) (by norm_num) 269 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(665676592361057/50000000000000000000 : ℝ) ≤ ((125177543703925191691/125210000000000000000 : ℝ)+2*(600778789489/313025000000000 : ℝ)*(3459/50000 : ℝ))^(269/64 : ℝ) := by
    rw [show (125177543703925191691/125210000000000000000 : ℝ)+2*(600778789489/313025000000000 : ℝ)*(3459/50000 : ℝ)=(10000063349992067/10000000000000000 : ℝ) by norm_num, show 1+2*(665676592361057/50000000000000000000 : ℝ)=(25000665676592361057/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51189109363038099/50000000000000000000 : ℝ)+(665676592361057/50000000000000000000 : ℝ) ≤ ((125177543703925191691/125210000000000000000 : ℝ)+(600778789489/313025000000000 : ℝ)*((19439/100000 : ℝ)+(3459/50000 : ℝ)))^(269/64 : ℝ) := by
    rw [show (125177543703925191691/125210000000000000000 : ℝ)+(600778789489/313025000000000 : ℝ)*((19439/100000 : ℝ)+(3459/50000 : ℝ))=(10002466465150023/10000000000000000 : ℝ) by norm_num, show 1+(51189109363038099/50000000000000000000 : ℝ)+(665676592361057/50000000000000000000 : ℝ)=(12512963696488849789/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51189109363038099/50000000000000000000 : ℝ) ≤ ((125177543703925191691/125210000000000000000 : ℝ)+2*(600778789489/313025000000000 : ℝ)*(19439/100000 : ℝ))^(269/64 : ℝ) := by
    rw [show (125177543703925191691/125210000000000000000 : ℝ)+2*(600778789489/313025000000000 : ℝ)*(19439/100000 : ℝ)=(10004869580307979/10000000000000000 : ℝ) by norm_num, show 1+2*(51189109363038099/50000000000000000000 : ℝ)=(25051189109363038099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125177543703925191691/125210000000000000000 : ℝ)*(X 1 0+X 2 0)+(600778789489/313025000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (3459/50000 : ℝ)) (hi := (19439/100000 : ℝ)) (c := (125177543703925191691/125210000000000000000 : ℝ)) (alpha := (600778789489/313025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125177543703925191691/125210000000000000000 : ℝ)*(X 0 1+X 2 1)+(600778789489/313025000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (3459/50000 : ℝ)) (hi := (19439/100000 : ℝ)) (c := (125177543703925191691/125210000000000000000 : ℝ)) (alpha := (600778789489/313025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125177543703925191691/125210000000000000000 : ℝ)*(X 0 2+X 1 2)+(600778789489/313025000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (269/64 : ℝ)) (lo := (3459/50000 : ℝ)) (hi := (19439/100000 : ℝ)) (c := (125177543703925191691/125210000000000000000 : ℝ)) (alpha := (600778789489/313025000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-203164983/1000000000 : ℝ)*X 0 0+(5478929433/10000000000 : ℝ)*X 0 1+(2592337723/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5365742443/10000000000 : ℝ)*X 1 0+(-3411981/15625000 : ℝ)*X 1 1+(2592337919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214629701/400000000 : ℝ)*X 2 0+(162021117/312500000 : ℝ)*X 2 1+(-1091833927/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159839863/5000000000 : ℝ)*X 0 0+(201071051/500000000 : ℝ)*X 0 1+(4638452289/10000000000 : ℝ)*X 0 2+(2159839863/5000000000 : ℝ)*X 1 0+(201071051/500000000 : ℝ)*X 1 1+(4638452289/10000000000 : ℝ)*X 1 2+(2159839863/5000000000 : ℝ)*X 2 0+(201071051/500000000 : ℝ)*X 2 1+(4638452289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2031714917/10000000000 : ℝ)*X 0 0+(2593257637/5000000000 : ℝ)*X 0 1+(5477073077/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644936917/5000000000 : ℝ)*X 1 0+(-945635151/5000000000 : ℝ)*X 1 1+(1369268267/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289873841/10000000000 : ℝ)*X 2 0+(1369268271/2500000000 : ℝ)*X 2 1+(-1891270271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319816561/10000000000 : ℝ)*X 0 0+(4634594931/10000000000 : ℝ)*X 0 1+(1006328269/2500000000 : ℝ)*X 0 2+(4319816561/10000000000 : ℝ)*X 1 0+(4634594931/10000000000 : ℝ)*X 1 1+(1006328269/2500000000 : ℝ)*X 1 2+(4319816561/10000000000 : ℝ)*X 2 0+(4634594931/10000000000 : ℝ)*X 2 1+(1006328269/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1345_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32034991263332112289659/3295000000000000000000000000 : ℝ) := by norm_num
    linear_combination (347249759/20000000000000 : ℝ)*(base19) + (431454303/25000000000000 : ℝ)*(base23) + (33464801/100000000000000 : ℝ)*(lower2) + (116893977/50000000000000 : ℝ)*(upper3) + (182038999/100000000000000 : ℝ)*(upper5) + (313697568713821/12500000000000 : ℝ)*(major0) + (313697568713821/12500000000000 : ℝ)*(major1) + (313697568713821/12500000000000 : ℝ)*(major2) + (169922499035899/5000000000000 : ℝ)*(sp0) + (1699236699155053/50000000000000 : ℝ)*(sp1) + (3398473408741689/100000000000000 : ℝ)*(sp2) + (405168522533443/25000000000000 : ℝ)*(sp3) + (25153840921/100000000000000 : ℝ)*(sp4) + (721915729/6250000000000 : ℝ)*(sp7) + (405171410196359/25000000000000 : ℝ)*(f.failure) + (3398475134558901/100000000000000 : ℝ)*(f.sum) + (17229266008973/3295000000000000000000000000 : ℝ)*base66 + (122164912928890069/82375000000000000000000000000000 : ℝ)*base67 + (123109733502765069/82375000000000000000000000000000 : ℝ)*base69 + (539611751939109931/82375000000000000000000000000000 : ℝ)*base72 + (18176882011/102968750000000000000000000 : ℝ)*base73 + (888973516924140069/82375000000000000000000000000000 : ℝ)*base75 + (306292453245734931/82375000000000000000000000000000 : ℝ)*base78 + (116134340770859931/82375000000000000000000000000000 : ℝ)*base80 + (1318234865831/1647500000000000000000000000 : ℝ)*base81 + (1244637/2500000000000000000000 : ℝ)*base89 + (1244637/2500000000000000000000 : ℝ)*base91 + (1244637/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16188319921310160759618346299/3130250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (551242343/50000000000000 : ℝ)*(base19) + (1261789193/100000000000000 : ℝ)*(base23) + (136142931/100000000000000 : ℝ)*(upper3) + (59960897/100000000000000 : ℝ)*(lower4) + (68373343/100000000000000 : ℝ)*(upper5) + (1270732741737963/50000000000000 : ℝ)*(major0) + (1270732741737963/50000000000000 : ℝ)*(major1) + (1270732741737963/50000000000000 : ℝ)*(major2) + (2458336201/20000000000000 : ℝ)*(sp1) + (948639881/6250000000000 : ℝ)*(sp2) + (215103367646007/6250000000000 : ℝ)*(sp4) + (1720820244085211/50000000000000 : ℝ)*(sp5) + (3441637442308823/100000000000000 : ℝ)*(sp6) + (1641276912229929/100000000000000 : ℝ)*(sp7) + (1641276912229929/100000000000000 : ℝ)*(f.failure) + (215103367646007/6250000000000 : ℝ)*(f.sum) + (37511980300931/62605000000000000000000000000 : ℝ)*base65 + (23388245427283834567/6260500000000000000000000000000000 : ℝ)*base68 + (76855692841764334567/6260500000000000000000000000000000 : ℝ)*base70 + (1771309577643665433/6260500000000000000000000000000000 : ℝ)*base71 + (32927304087981/62605000000000000000000000000 : ℝ)*base73 + (146080515879515334567/6260500000000000000000000000000000 : ℝ)*base76 + (4917220969653665433/6260500000000000000000000000000000 : ℝ)*base77 + (64502131335397834567/6260500000000000000000000000000000 : ℝ)*base80 + (163582361701879/62605000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4235853/10000000000000000000000 : ℝ)*base90 + (4235853/10000000000000000000000 : ℝ)*base92 + (4235853/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1345_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19439/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4023/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1345_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1345_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4023/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1345_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1345_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1345_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (269/64 : ℝ) ≤ p) (hpb : p ≤ (4305/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154846843/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9871/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4023/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1345_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
