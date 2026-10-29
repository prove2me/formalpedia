-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1500_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:52:20.103611+00:00
-- url     : https://prove2.me/submissions/50ced8bd-e3dd-4472-af7f-5656b6a7c8fc

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
theorem support_rectangle_w1500_s3_0 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-942659107/5000000000 : ℝ)*x 0 + (5438556091/10000000000 : ℝ)*x 1 + (325851771/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (942659107/5000000000 : ℝ)^4497 ≤ (1152749022549/10000000000000 : ℝ)^3473 := by
    have hnat : (942659107 : ℕ)^4497*10000000000000^3473 ≤ 1152749022549^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942659107 5000000000 1152749022549 10000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438556091/10000000000 : ℝ)^4497 ≤ (45445619203581/100000000000000 : ℝ)^3473 := by
    have hnat : (5438556091 : ℕ)^4497*100000000000000^3473 ≤ 45445619203581^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438556091 10000000000 45445619203581 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325851771/625000000 : ℝ)^4497 ≤ (10756722638747/25000000000000 : ℝ)^3473 := by
    have hnat : (325851771 : ℕ)^4497*25000000000000^3473 ≤ 10756722638747^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325851771 625000000 10756722638747 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-942659107/5000000000 : ℝ), (5438556091/10000000000 : ℝ), (325851771/625000000 : ℝ)] ![(1152749022549/10000000000000 : ℝ), (45445619203581/100000000000000 : ℝ), (10756722638747/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-942659107/5000000000 : ℝ)|^4497 ≤ (1152749022549/10000000000000 : ℝ)^3473
        have hw : |(-942659107/5000000000 : ℝ)|=(942659107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438556091/10000000000 : ℝ)|^4497 ≤ (45445619203581/100000000000000 : ℝ)^3473
        have hw : |(5438556091/10000000000 : ℝ)|=(5438556091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325851771/625000000 : ℝ)|^4497 ≤ (10756722638747/25000000000000 : ℝ)^3473
        have hw : |(325851771/625000000 : ℝ)|=(325851771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s3_1 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267661499/500000000 : ℝ)*x 0 + (-250079179/1250000000 : ℝ)*x 1 + (2606814179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267661499/500000000 : ℝ)^4497 ≤ (44524535555051/100000000000000 : ℝ)^3473 := by
    have hnat : (267661499 : ℕ)^4497*100000000000000^3473 ≤ 44524535555051^3473*500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267661499 500000000 44524535555051 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (250079179/1250000000 : ℝ)^4497 ≤ (1244857364333/10000000000000 : ℝ)^3473 := by
    have hnat : (250079179 : ℕ)^4497*10000000000000^3473 ≤ 1244857364333^3473*1250000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250079179 1250000000 1244857364333 10000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606814179/5000000000 : ℝ)^4497 ≤ (43026890790081/100000000000000 : ℝ)^3473 := by
    have hnat : (2606814179 : ℕ)^4497*100000000000000^3473 ≤ 43026890790081^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606814179 5000000000 43026890790081 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267661499/500000000 : ℝ), (-250079179/1250000000 : ℝ), (2606814179/5000000000 : ℝ)] ![(44524535555051/100000000000000 : ℝ), (1244857364333/10000000000000 : ℝ), (43026890790081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267661499/500000000 : ℝ)|^4497 ≤ (44524535555051/100000000000000 : ℝ)^3473
        have hw : |(267661499/500000000 : ℝ)|=(267661499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-250079179/1250000000 : ℝ)|^4497 ≤ (1244857364333/10000000000000 : ℝ)^3473
        have hw : |(-250079179/1250000000 : ℝ)|=(250079179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606814179/5000000000 : ℝ)|^4497 ≤ (43026890790081/100000000000000 : ℝ)^3473
        have hw : |(2606814179/5000000000 : ℝ)|=(2606814179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s3_2 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676615059/5000000000 : ℝ)*x 0 + (104272567/200000000 : ℝ)*x 1 + (-1000316629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676615059/5000000000 : ℝ)^4497 ≤ (44524537041263/100000000000000 : ℝ)^3473 := by
    have hnat : (2676615059 : ℕ)^4497*100000000000000^3473 ≤ 44524537041263^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676615059 5000000000 44524537041263 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104272567/200000000 : ℝ)^4497 ≤ (43026890704593/100000000000000 : ℝ)^3473 := by
    have hnat : (104272567 : ℕ)^4497*100000000000000^3473 ≤ 43026890704593^3473*200000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104272567 200000000 43026890704593 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000316629/5000000000 : ℝ)^4497 ≤ (6224286120711/50000000000000 : ℝ)^3473 := by
    have hnat : (1000316629 : ℕ)^4497*50000000000000^3473 ≤ 6224286120711^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000316629 5000000000 6224286120711 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676615059/5000000000 : ℝ), (104272567/200000000 : ℝ), (-1000316629/5000000000 : ℝ)] ![(44524537041263/100000000000000 : ℝ), (43026890704593/100000000000000 : ℝ), (6224286120711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676615059/5000000000 : ℝ)|^4497 ≤ (44524537041263/100000000000000 : ℝ)^3473
        have hw : |(2676615059/5000000000 : ℝ)|=(2676615059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104272567/200000000 : ℝ)|^4497 ≤ (43026890704593/100000000000000 : ℝ)^3473
        have hw : |(104272567/200000000 : ℝ)|=(104272567/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1000316629/5000000000 : ℝ)|^4497 ≤ (6224286120711/50000000000000 : ℝ)^3473
        have hw : |(-1000316629/5000000000 : ℝ)|=(1000316629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s3_3 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068758739/2500000000 : ℝ)*x 0 + (4028580597/10000000000 : ℝ)*x 1 + (283394621/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068758739/2500000000 : ℝ)^4497 ≤ (33275433728939/100000000000000 : ℝ)^3473 := by
    have hnat : (1068758739 : ℕ)^4497*100000000000000^3473 ≤ 33275433728939^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068758739 2500000000 33275433728939 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028580597/10000000000 : ℝ)^4497 ≤ (7703227899697/25000000000000 : ℝ)^3473 := by
    have hnat : (4028580597 : ℕ)^4497*25000000000000^3473 ≤ 7703227899697^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028580597 10000000000 7703227899697 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283394621/625000000 : ℝ)^4497 ≤ (17955827328309/50000000000000 : ℝ)^3473 := by
    have hnat : (283394621 : ℕ)^4497*50000000000000^3473 ≤ 17955827328309^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283394621 625000000 17955827328309 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068758739/2500000000 : ℝ), (4028580597/10000000000 : ℝ), (283394621/625000000 : ℝ)] ![(33275433728939/100000000000000 : ℝ), (7703227899697/25000000000000 : ℝ), (17955827328309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068758739/2500000000 : ℝ)|^4497 ≤ (33275433728939/100000000000000 : ℝ)^3473
        have hw : |(1068758739/2500000000 : ℝ)|=(1068758739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028580597/10000000000 : ℝ)|^4497 ≤ (7703227899697/25000000000000 : ℝ)^3473
        have hw : |(4028580597/10000000000 : ℝ)|=(4028580597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283394621/625000000 : ℝ)|^4497 ≤ (17955827328309/50000000000000 : ℝ)^3473
        have hw : |(283394621/625000000 : ℝ)|=(283394621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s3_4 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885349887/10000000000 : ℝ)*x 0 + (1303705319/2500000000 : ℝ)*x 1 + (5437354661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885349887/10000000000 : ℝ)^4497 ≤ (720483811601/6250000000000 : ℝ)^3473 := by
    have hnat : (1885349887 : ℕ)^4497*6250000000000^3473 ≤ 720483811601^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885349887 10000000000 720483811601 6250000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303705319/2500000000 : ℝ)^4497 ≤ (43039638824823/100000000000000 : ℝ)^3473 := by
    have hnat : (1303705319 : ℕ)^4497*100000000000000^3473 ≤ 43039638824823^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303705319 2500000000 43039638824823 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437354661/10000000000 : ℝ)^4497 ≤ (45432620176611/100000000000000 : ℝ)^3473 := by
    have hnat : (5437354661 : ℕ)^4497*100000000000000^3473 ≤ 45432620176611^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437354661 10000000000 45432620176611 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885349887/10000000000 : ℝ), (1303705319/2500000000 : ℝ), (5437354661/10000000000 : ℝ)] ![(720483811601/6250000000000 : ℝ), (43039638824823/100000000000000 : ℝ), (45432620176611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885349887/10000000000 : ℝ)|^4497 ≤ (720483811601/6250000000000 : ℝ)^3473
        have hw : |(-1885349887/10000000000 : ℝ)|=(1885349887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303705319/2500000000 : ℝ)|^4497 ≤ (43039638824823/100000000000000 : ℝ)^3473
        have hw : |(1303705319/2500000000 : ℝ)|=(1303705319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437354661/10000000000 : ℝ)|^4497 ≤ (45432620176611/100000000000000 : ℝ)^3473
        have hw : |(5437354661/10000000000 : ℝ)|=(5437354661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s3_5 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294291203/10000000000 : ℝ)*x 0 + (-444226729/2500000000 : ℝ)*x 1 + (2718677393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294291203/10000000000 : ℝ)^4497 ≤ (4389081849271/10000000000000 : ℝ)^3473 := by
    have hnat : (5294291203 : ℕ)^4497*10000000000000^3473 ≤ 4389081849271^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294291203 10000000000 4389081849271 10000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (444226729/2500000000 : ℝ)^4497 ≤ (10676559959663/100000000000000 : ℝ)^3473 := by
    have hnat : (444226729 : ℕ)^4497*100000000000000^3473 ≤ 10676559959663^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444226729 2500000000 10676559959663 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718677393/5000000000 : ℝ)^4497 ≤ (2271631076451/5000000000000 : ℝ)^3473 := by
    have hnat : (2718677393 : ℕ)^4497*5000000000000^3473 ≤ 2271631076451^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718677393 5000000000 2271631076451 5000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294291203/10000000000 : ℝ), (-444226729/2500000000 : ℝ), (2718677393/5000000000 : ℝ)] ![(4389081849271/10000000000000 : ℝ), (10676559959663/100000000000000 : ℝ), (2271631076451/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294291203/10000000000 : ℝ)|^4497 ≤ (4389081849271/10000000000000 : ℝ)^3473
        have hw : |(5294291203/10000000000 : ℝ)|=(5294291203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-444226729/2500000000 : ℝ)|^4497 ≤ (10676559959663/100000000000000 : ℝ)^3473
        have hw : |(-444226729/2500000000 : ℝ)|=(444226729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718677393/5000000000 : ℝ)|^4497 ≤ (2271631076451/5000000000000 : ℝ)^3473
        have hw : |(2718677393/5000000000 : ℝ)|=(2718677393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s3_6 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (33089319/62500000 : ℝ)*x 0 + (2718677509/5000000000 : ℝ)*x 1 + (-888453409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33089319/62500000 : ℝ)^4497 ≤ (21945408371489/50000000000000 : ℝ)^3473 := by
    have hnat : (33089319 : ℕ)^4497*50000000000000^3473 ≤ 21945408371489^3473*62500000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33089319 62500000 21945408371489 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718677509/5000000000 : ℝ)^4497 ≤ (11358156009773/25000000000000 : ℝ)^3473 := by
    have hnat : (2718677509 : ℕ)^4497*25000000000000^3473 ≤ 11358156009773^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718677509 5000000000 11358156009773 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (888453409/5000000000 : ℝ)^4497 ≤ (5338279598607/50000000000000 : ℝ)^3473 := by
    have hnat : (888453409 : ℕ)^4497*50000000000000^3473 ≤ 5338279598607^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      888453409 5000000000 5338279598607 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33089319/62500000 : ℝ), (2718677509/5000000000 : ℝ), (-888453409/5000000000 : ℝ)] ![(21945408371489/50000000000000 : ℝ), (11358156009773/25000000000000 : ℝ), (5338279598607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33089319/62500000 : ℝ)|^4497 ≤ (21945408371489/50000000000000 : ℝ)^3473
        have hw : |(33089319/62500000 : ℝ)|=(33089319/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718677509/5000000000 : ℝ)|^4497 ≤ (11358156009773/25000000000000 : ℝ)^3473
        have hw : |(2718677509/5000000000 : ℝ)|=(2718677509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-888453409/5000000000 : ℝ)|^4497 ≤ (5338279598607/50000000000000 : ℝ)^3473
        have hw : |(-888453409/5000000000 : ℝ)|=(888453409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s3_7 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855021543/2000000000 : ℝ)*x 0 + (4531632781/10000000000 : ℝ)*x 1 + (806256467/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855021543/2000000000 : ℝ)^4497 ≤ (33276167042929/100000000000000 : ℝ)^3473 := by
    have hnat : (855021543 : ℕ)^4497*100000000000000^3473 ≤ 33276167042929^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855021543 2000000000 33276167042929 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531632781/10000000000 : ℝ)^4497 ≤ (35884161412303/100000000000000 : ℝ)^3473 := by
    have hnat : (4531632781 : ℕ)^4497*100000000000000^3473 ≤ 35884161412303^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531632781 10000000000 35884161412303 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806256467/2000000000 : ℝ)^4497 ≤ (481869867611/1562500000000 : ℝ)^3473 := by
    have hnat : (806256467 : ℕ)^4497*1562500000000^3473 ≤ 481869867611^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806256467 2000000000 481869867611 1562500000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855021543/2000000000 : ℝ), (4531632781/10000000000 : ℝ), (806256467/2000000000 : ℝ)] ![(33276167042929/100000000000000 : ℝ), (35884161412303/100000000000000 : ℝ), (481869867611/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855021543/2000000000 : ℝ)|^4497 ≤ (33276167042929/100000000000000 : ℝ)^3473
        have hw : |(855021543/2000000000 : ℝ)|=(855021543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531632781/10000000000 : ℝ)|^4497 ≤ (35884161412303/100000000000000 : ℝ)^3473
        have hw : |(4531632781/10000000000 : ℝ)|=(4531632781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806256467/2000000000 : ℝ)|^4497 ≤ (481869867611/1562500000000 : ℝ)^3473
        have hw : |(806256467/2000000000 : ℝ)|=(806256467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1500_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4011/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (2699/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7779/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4011/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (207/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4011/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (207/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4011/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (207/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4011/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (207/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4011/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (207/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4011/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (207/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (207/2000 : ℝ) ^ (4495/1024 : ℝ) ≤ (4741704064298117/100000000000000000000 : ℝ) := by
    have hpowers : (207/2000 : ℝ)^4495 ≤ (4741704064298117/100000000000000000000 : ℝ)^1024 := by
      have hnat : (207 : ℕ)^4495*100000000000000000000^1024 ≤ 4741704064298117^1024*2000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        207 2000 4741704064298117 100000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (207/2000 : ℝ)) (X := (4741704064298117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4011/25000 : ℝ) ^ (4495/1024 : ℝ) ≤ (6495789246903761/20000000000000000000 : ℝ) := by
    have hpowers : (4011/25000 : ℝ)^4495 ≤ (6495789246903761/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4011 : ℕ)^4495*20000000000000000000^1024 ≤ 6495789246903761^1024*25000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4011 25000 6495789246903761 20000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4011/25000 : ℝ)) (X := (6495789246903761/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004741704064298117/50000000000000000000 : ℝ) ≤ (10000216032355389/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (50004741704064298117/50000000000000000000 : ℝ)^1024 ≤ (10000216032355389/10000000000000000 : ℝ)^4495 := by
      have hnat : (50004741704064298117 : ℕ)^1024*10000000000000000^4495 ≤ 10000216032355389^4495*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004741704064298117 50000000000000000000 10000216032355389 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000216032355389/10000000000000000 : ℝ)) (X := (50004741704064298117/50000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50018610325149408461/50000000000000000000 : ℝ) ≤ (40003391187529/40000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (50018610325149408461/50000000000000000000 : ℝ)^1024 ≤ (40003391187529/40000000000000 : ℝ)^4495 := by
      have hnat : (50018610325149408461 : ℕ)^1024*40000000000000^4495 ≤ 40003391187529^4495*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018610325149408461 50000000000000000000 40003391187529 40000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (40003391187529/40000000000000 : ℝ)) (X := (50018610325149408461/50000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006495789246903761/10000000000000000000 : ℝ) ≤ (10001479561409111/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (10006495789246903761/10000000000000000000 : ℝ)^1024 ≤ (10001479561409111/10000000000000000 : ℝ)^4495 := by
      have hnat : (10006495789246903761 : ℕ)^1024*10000000000000000^4495 ≤ 10001479561409111^4495*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006495789246903761 10000000000000000000 10001479561409111 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001479561409111/10000000000000000 : ℝ)) (X := (10006495789246903761/10000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4741704064298117/100000000000000000000 : ℝ) ≤ ((729848109775968747/730000000000000000 : ℝ)+2*(48597271297/43800000000000 : ℝ)*(207/2000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (729848109775968747/730000000000000000 : ℝ)+2*(48597271297/43800000000000 : ℝ)*(207/2000 : ℝ)=(10000216032355389/10000000000000000 : ℝ) by norm_num, show 1+2*(4741704064298117/100000000000000000000 : ℝ)=(50004741704064298117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6495789246903761/20000000000000000000 : ℝ)+(4741704064298117/100000000000000000000 : ℝ) ≤ ((729848109775968747/730000000000000000 : ℝ)+(48597271297/43800000000000 : ℝ)*((4011/25000 : ℝ)+(207/2000 : ℝ)))^(4495/1024 : ℝ) := by
    rw [show (729848109775968747/730000000000000000 : ℝ)+(48597271297/43800000000000 : ℝ)*((4011/25000 : ℝ)+(207/2000 : ℝ))=(40003391187529/40000000000000 : ℝ) by norm_num, show 1+(6495789246903761/20000000000000000000 : ℝ)+(4741704064298117/100000000000000000000 : ℝ)=(50018610325149408461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6495789246903761/20000000000000000000 : ℝ) ≤ ((729848109775968747/730000000000000000 : ℝ)+2*(48597271297/43800000000000 : ℝ)*(4011/25000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (729848109775968747/730000000000000000 : ℝ)+2*(48597271297/43800000000000 : ℝ)*(4011/25000 : ℝ)=(10001479561409111/10000000000000000 : ℝ) by norm_num, show 1+2*(6495789246903761/20000000000000000000 : ℝ)=(10006495789246903761/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (729848109775968747/730000000000000000 : ℝ)*(X 1 0+X 2 0)+(48597271297/43800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (207/2000 : ℝ)) (hi := (4011/25000 : ℝ)) (c := (729848109775968747/730000000000000000 : ℝ)) (alpha := (48597271297/43800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (729848109775968747/730000000000000000 : ℝ)*(X 0 1+X 2 1)+(48597271297/43800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (207/2000 : ℝ)) (hi := (4011/25000 : ℝ)) (c := (729848109775968747/730000000000000000 : ℝ)) (alpha := (48597271297/43800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (729848109775968747/730000000000000000 : ℝ)*(X 0 2+X 1 2)+(48597271297/43800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (207/2000 : ℝ)) (hi := (4011/25000 : ℝ)) (c := (729848109775968747/730000000000000000 : ℝ)) (alpha := (48597271297/43800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-942659107/5000000000 : ℝ)*X 0 0+(5438556091/10000000000 : ℝ)*X 0 1+(325851771/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267661499/500000000 : ℝ)*X 1 0+(-250079179/1250000000 : ℝ)*X 1 1+(2606814179/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676615059/5000000000 : ℝ)*X 2 0+(104272567/200000000 : ℝ)*X 2 1+(-1000316629/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1068758739/2500000000 : ℝ)*X 0 0+(4028580597/10000000000 : ℝ)*X 0 1+(283394621/625000000 : ℝ)*X 0 2+(1068758739/2500000000 : ℝ)*X 1 0+(4028580597/10000000000 : ℝ)*X 1 1+(283394621/625000000 : ℝ)*X 1 2+(1068758739/2500000000 : ℝ)*X 2 0+(4028580597/10000000000 : ℝ)*X 2 1+(283394621/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1885349887/10000000000 : ℝ)*X 0 0+(1303705319/2500000000 : ℝ)*X 0 1+(5437354661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294291203/10000000000 : ℝ)*X 1 0+(-444226729/2500000000 : ℝ)*X 1 1+(2718677393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33089319/62500000 : ℝ)*X 2 0+(2718677509/5000000000 : ℝ)*X 2 1+(-888453409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((855021543/2000000000 : ℝ)*X 0 0+(4531632781/10000000000 : ℝ)*X 0 1+(806256467/2000000000 : ℝ)*X 0 2+(855021543/2000000000 : ℝ)*X 1 0+(4531632781/10000000000 : ℝ)*X 1 1+(806256467/2000000000 : ℝ)*X 1 2+(855021543/2000000000 : ℝ)*X 2 0+(4531632781/10000000000 : ℝ)*X 2 1+(806256467/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71083558994439157169453397/9125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2668496291/100000000000000 : ℝ)*(base19) + (2103866589/100000000000000 : ℝ)*(base23) + (20840459/4000000000000 : ℝ)*(upper3) + (363613223/100000000000000 : ℝ)*(upper4) + (44391497/20000000000000 : ℝ)*(upper5) + (802912547974683/25000000000000 : ℝ)*(major0) + (802912547974683/25000000000000 : ℝ)*(major1) + (802912547974683/25000000000000 : ℝ)*(major2) + (69467296268011/1562500000000 : ℝ)*(sp0) + (2222969265705883/50000000000000 : ℝ)*(sp1) + (1111484774010367/25000000000000 : ℝ)*(sp2) + (247167509155441/12500000000000 : ℝ)*(sp3) + (4279844419/12500000000000 : ℝ)*(sp4) + (9425489951/50000000000000 : ℝ)*(sp7) + (197735892422343/10000000000000 : ℝ)*(f.failure) + (555742649988507/12500000000000 : ℝ)*(f.sum) + (48834766167/45625000000000000000000000 : ℝ)*base66 + (49059127570582201/18250000000000000000000000000000 : ℝ)*base67 + (125852012295582201/18250000000000000000000000000000 : ℝ)*base69 + (65555841237582201/18250000000000000000000000000000 : ℝ)*base71 + (562641022411/91250000000000000000000000 : ℝ)*base73 + (388052365923417799/18250000000000000000000000000000 : ℝ)*base76 + (182618399690417799/18250000000000000000000000000000 : ℝ)*base78 + (80966905912582201/18250000000000000000000000000000 : ℝ)*base79 + (216793281739/22812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (203337/200000000000000000000 : ℝ)*base90 + (203337/200000000000000000000 : ℝ)*base92 + (203337/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (40843610801197069566324249/9125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (719975097/100000000000000 : ℝ)*(base19) + (817065453/100000000000000 : ℝ)*(base23) + (40091747/50000000000000 : ℝ)*(upper2) + (18209989/10000000000000 : ℝ)*(upper3) + (14633173/100000000000000 : ℝ)*(upper5) + (811537711721037/25000000000000 : ℝ)*(major0) + (811537711721037/25000000000000 : ℝ)*(major1) + (811537711721037/25000000000000 : ℝ)*(major2) + (1810876521/20000000000000 : ℝ)*(sp1) + (16598784697/100000000000000 : ℝ)*(sp2) + (449370114821929/10000000000000 : ℝ)*(sp4) + (1123422843465397/25000000000000 : ℝ)*(sp5) + (224684186618457/5000000000000 : ℝ)*(sp6) + (249825049543573/12500000000000 : ℝ)*(sp7) + (249825049543573/12500000000000 : ℝ)*(f.failure) + (449370114821929/10000000000000 : ℝ)*(f.sum) + (335700959469/91250000000000000000000000 : ℝ)*base65 + (238102405749580639/18250000000000000000000000000000 : ℝ)*base67 + (181919266355080639/18250000000000000000000000000000 : ℝ)*base69 + (191037705589580639/18250000000000000000000000000000 : ℝ)*base71 + (252357499343/182500000000000000000000000 : ℝ)*base73 + (253246433614080639/18250000000000000000000000000000 : ℝ)*base75 + (244183501718080639/18250000000000000000000000000000 : ℝ)*base77 + (215708005402080639/18250000000000000000000000000000 : ℝ)*base79 + (1075819207/712890625000000000000000 : ℝ)*base82 + (4666907/250000000000000000000 : ℝ)*base90 + (4666907/250000000000000000000 : ℝ)*base92 + (4666907/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1500_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4011/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2699/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7779/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1500_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1500_s4_0 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-471455229/2500000000 : ℝ)*x 0 + (5435271957/10000000000 : ℝ)*x 1 + (8346529/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (471455229/2500000000 : ℝ)^4497 ≤ (11531470342931/100000000000000 : ℝ)^3473 := by
    have hnat : (471455229 : ℕ)^4497*100000000000000^3473 ≤ 11531470342931^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471455229 2500000000 11531470342931 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435271957/10000000000 : ℝ)^4497 ≤ (9082017619669/20000000000000 : ℝ)^3473 := by
    have hnat : (5435271957 : ℕ)^4497*20000000000000^3473 ≤ 9082017619669^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435271957 10000000000 9082017619669 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8346529/16000000 : ℝ)^4497 ≤ (21529220776991/50000000000000 : ℝ)^3473 := by
    have hnat : (8346529 : ℕ)^4497*50000000000000^3473 ≤ 21529220776991^3473*16000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8346529 16000000 21529220776991 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-471455229/2500000000 : ℝ), (5435271957/10000000000 : ℝ), (8346529/16000000 : ℝ)] ![(11531470342931/100000000000000 : ℝ), (9082017619669/20000000000000 : ℝ), (21529220776991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-471455229/2500000000 : ℝ)|^4497 ≤ (11531470342931/100000000000000 : ℝ)^3473
        have hw : |(-471455229/2500000000 : ℝ)|=(471455229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435271957/10000000000 : ℝ)|^4497 ≤ (9082017619669/20000000000000 : ℝ)^3473
        have hw : |(5435271957/10000000000 : ℝ)|=(5435271957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8346529/16000000 : ℝ)|^4497 ≤ (21529220776991/50000000000000 : ℝ)^3473
        have hw : |(8346529/16000000 : ℝ)|=(8346529/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s4_1 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214094911/400000000 : ℝ)*x 0 + (-1997862539/10000000000 : ℝ)*x 1 + (1043316147/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214094911/400000000 : ℝ)^4497 ≤ (1780612158997/4000000000000 : ℝ)^3473 := by
    have hnat : (214094911 : ℕ)^4497*4000000000000^3473 ≤ 1780612158997^3473*400000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214094911 400000000 1780612158997 4000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997862539/10000000000 : ℝ)^4497 ≤ (6213126641081/50000000000000 : ℝ)^3473 := by
    have hnat : (1997862539 : ℕ)^4497*50000000000000^3473 ≤ 6213126641081^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997862539 10000000000 6213126641081 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043316147/2000000000 : ℝ)^4497 ≤ (21529221364823/50000000000000 : ℝ)^3473 := by
    have hnat : (1043316147 : ℕ)^4497*50000000000000^3473 ≤ 21529221364823^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043316147 2000000000 21529221364823 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214094911/400000000 : ℝ), (-1997862539/10000000000 : ℝ), (1043316147/2000000000 : ℝ)] ![(1780612158997/4000000000000 : ℝ), (6213126641081/50000000000000 : ℝ), (21529221364823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214094911/400000000 : ℝ)|^4497 ≤ (1780612158997/4000000000000 : ℝ)^3473
        have hw : |(214094911/400000000 : ℝ)|=(214094911/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997862539/10000000000 : ℝ)|^4497 ≤ (6213126641081/50000000000000 : ℝ)^3473
        have hw : |(-1997862539/10000000000 : ℝ)|=(1997862539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043316147/2000000000 : ℝ)|^4497 ≤ (21529221364823/50000000000000 : ℝ)^3473
        have hw : |(1043316147/2000000000 : ℝ)|=(1043316147/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s4_2 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352372801/10000000000 : ℝ)*x 0 + (5216580607/10000000000 : ℝ)*x 1 + (-998931337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352372801/10000000000 : ℝ)^4497 ≤ (44515304254923/100000000000000 : ℝ)^3473 := by
    have hnat : (5352372801 : ℕ)^4497*100000000000000^3473 ≤ 44515304254923^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352372801 10000000000 44515304254923 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216580607/10000000000 : ℝ)^4497 ≤ (43058441361601/100000000000000 : ℝ)^3473 := by
    have hnat : (5216580607 : ℕ)^4497*100000000000000^3473 ≤ 43058441361601^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216580607 10000000000 43058441361601 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998931337/5000000000 : ℝ)^4497 ≤ (2485250873881/20000000000000 : ℝ)^3473 := by
    have hnat : (998931337 : ℕ)^4497*20000000000000^3473 ≤ 2485250873881^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998931337 5000000000 2485250873881 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352372801/10000000000 : ℝ), (5216580607/10000000000 : ℝ), (-998931337/5000000000 : ℝ)] ![(44515304254923/100000000000000 : ℝ), (43058441361601/100000000000000 : ℝ), (2485250873881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352372801/10000000000 : ℝ)|^4497 ≤ (44515304254923/100000000000000 : ℝ)^3473
        have hw : |(5352372801/10000000000 : ℝ)|=(5352372801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216580607/10000000000 : ℝ)|^4497 ≤ (43058441361601/100000000000000 : ℝ)^3473
        have hw : |(5216580607/10000000000 : ℝ)|=(5216580607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998931337/5000000000 : ℝ)|^4497 ≤ (2485250873881/20000000000000 : ℝ)^3473
        have hw : |(-998931337/5000000000 : ℝ)|=(998931337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s4_3 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068837191/2500000000 : ℝ)*x 0 + (4035555801/10000000000 : ℝ)*x 1 + (452726601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068837191/2500000000 : ℝ)^4497 ≤ (33278596522673/100000000000000 : ℝ)^3473 := by
    have hnat : (1068837191 : ℕ)^4497*100000000000000^3473 ≤ 33278596522673^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068837191 2500000000 33278596522673 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4035555801/10000000000 : ℝ)^4497 ≤ (6176401952139/20000000000000 : ℝ)^3473 := by
    have hnat : (4035555801 : ℕ)^4497*20000000000000^3473 ≤ 6176401952139^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035555801 10000000000 6176401952139 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452726601/1000000000 : ℝ)^4497 ≤ (35839393700253/100000000000000 : ℝ)^3473 := by
    have hnat : (452726601 : ℕ)^4497*100000000000000^3473 ≤ 35839393700253^3473*1000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452726601 1000000000 35839393700253 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068837191/2500000000 : ℝ), (4035555801/10000000000 : ℝ), (452726601/1000000000 : ℝ)] ![(33278596522673/100000000000000 : ℝ), (6176401952139/20000000000000 : ℝ), (35839393700253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068837191/2500000000 : ℝ)|^4497 ≤ (33278596522673/100000000000000 : ℝ)^3473
        have hw : |(1068837191/2500000000 : ℝ)|=(1068837191/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4035555801/10000000000 : ℝ)|^4497 ≤ (6176401952139/20000000000000 : ℝ)^3473
        have hw : |(4035555801/10000000000 : ℝ)|=(4035555801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452726601/1000000000 : ℝ)|^4497 ≤ (35839393700253/100000000000000 : ℝ)^3473
        have hw : |(452726601/1000000000 : ℝ)|=(452726601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s4_4 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-29466419/156250000 : ℝ)*x 0 + (5217708361/10000000000 : ℝ)*x 1 + (5434135839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29466419/156250000 : ℝ)^4497 ≤ (11531707084513/100000000000000 : ℝ)^3473 := by
    have hnat : (29466419 : ℕ)^4497*100000000000000^3473 ≤ 11531707084513^3473*156250000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29466419 156250000 11531707084513 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217708361/10000000000 : ℝ)^4497 ≤ (8614099003023/20000000000000 : ℝ)^3473 := by
    have hnat : (5217708361 : ℕ)^4497*20000000000000^3473 ≤ 8614099003023^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217708361 10000000000 8614099003023 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434135839/10000000000 : ℝ)^4497 ≤ (11349449472633/25000000000000 : ℝ)^3473 := by
    have hnat : (5434135839 : ℕ)^4497*25000000000000^3473 ≤ 11349449472633^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434135839 10000000000 11349449472633 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29466419/156250000 : ℝ), (5217708361/10000000000 : ℝ), (5434135839/10000000000 : ℝ)] ![(11531707084513/100000000000000 : ℝ), (8614099003023/20000000000000 : ℝ), (11349449472633/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29466419/156250000 : ℝ)|^4497 ≤ (11531707084513/100000000000000 : ℝ)^3473
        have hw : |(-29466419/156250000 : ℝ)|=(29466419/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217708361/10000000000 : ℝ)|^4497 ≤ (8614099003023/20000000000000 : ℝ)^3473
        have hw : |(5217708361/10000000000 : ℝ)|=(5217708361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434135839/10000000000 : ℝ)|^4497 ≤ (11349449472633/25000000000000 : ℝ)^3473
        have hw : |(5434135839/10000000000 : ℝ)|=(5434135839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s4_5 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295069927/10000000000 : ℝ)*x 0 + (-55634609/312500000 : ℝ)*x 1 + (5434135837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295069927/10000000000 : ℝ)^4497 ≤ (21949588963953/50000000000000 : ℝ)^3473 := by
    have hnat : (5295069927 : ℕ)^4497*50000000000000^3473 ≤ 21949588963953^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295069927 10000000000 21949588963953 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (55634609/312500000 : ℝ)^4497 ≤ (10703024185901/100000000000000 : ℝ)^3473 := by
    have hnat : (55634609 : ℕ)^4497*100000000000000^3473 ≤ 10703024185901^3473*312500000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55634609 312500000 10703024185901 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434135837/10000000000 : ℝ)^4497 ≤ (45397797868897/100000000000000 : ℝ)^3473 := by
    have hnat : (5434135837 : ℕ)^4497*100000000000000^3473 ≤ 45397797868897^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434135837 10000000000 45397797868897 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295069927/10000000000 : ℝ), (-55634609/312500000 : ℝ), (5434135837/10000000000 : ℝ)] ![(21949588963953/50000000000000 : ℝ), (10703024185901/100000000000000 : ℝ), (45397797868897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295069927/10000000000 : ℝ)|^4497 ≤ (21949588963953/50000000000000 : ℝ)^3473
        have hw : |(5295069927/10000000000 : ℝ)|=(5295069927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-55634609/312500000 : ℝ)|^4497 ≤ (10703024185901/100000000000000 : ℝ)^3473
        have hw : |(-55634609/312500000 : ℝ)|=(55634609/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434135837/10000000000 : ℝ)|^4497 ≤ (45397797868897/100000000000000 : ℝ)^3473
        have hw : |(5434135837/10000000000 : ℝ)|=(5434135837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s4_6 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647534959/5000000000 : ℝ)*x 0 + (5434135843/10000000000 : ℝ)*x 1 + (-445076873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647534959/5000000000 : ℝ)^4497 ≤ (43899177831291/100000000000000 : ℝ)^3473 := by
    have hnat : (2647534959 : ℕ)^4497*100000000000000^3473 ≤ 43899177831291^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647534959 5000000000 43899177831291 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434135843/10000000000 : ℝ)^4497 ≤ (22698898966901/50000000000000 : ℝ)^3473 := by
    have hnat : (5434135843 : ℕ)^4497*50000000000000^3473 ≤ 22698898966901^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434135843 10000000000 22698898966901 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (445076873/2500000000 : ℝ)^4497 ≤ (10703024217039/100000000000000 : ℝ)^3473 := by
    have hnat : (445076873 : ℕ)^4497*100000000000000^3473 ≤ 10703024217039^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445076873 2500000000 10703024217039 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647534959/5000000000 : ℝ), (5434135843/10000000000 : ℝ), (-445076873/2500000000 : ℝ)] ![(43899177831291/100000000000000 : ℝ), (22698898966901/50000000000000 : ℝ), (10703024217039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647534959/5000000000 : ℝ)|^4497 ≤ (43899177831291/100000000000000 : ℝ)^3473
        have hw : |(2647534959/5000000000 : ℝ)|=(2647534959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434135843/10000000000 : ℝ)|^4497 ≤ (22698898966901/50000000000000 : ℝ)^3473
        have hw : |(5434135843/10000000000 : ℝ)|=(5434135843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-445076873/2500000000 : ℝ)|^4497 ≤ (10703024217039/100000000000000 : ℝ)^3473
        have hw : |(-445076873/2500000000 : ℝ)|=(445076873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s4_7 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213770799/500000000 : ℝ)*x 0 + (565591323/1250000000 : ℝ)*x 1 + (2019054913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213770799/500000000 : ℝ)^4497 ≤ (8319818496281/25000000000000 : ℝ)^3473 := by
    have hnat : (213770799 : ℕ)^4497*25000000000000^3473 ≤ 8319818496281^3473*500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213770799 500000000 8319818496281 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565591323/1250000000 : ℝ)^4497 ≤ (35813406599977/100000000000000 : ℝ)^3473 := by
    have hnat : (565591323 : ℕ)^4497*100000000000000^3473 ≤ 35813406599977^3473*1250000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565591323 1250000000 35813406599977 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019054913/5000000000 : ℝ)^4497 ≤ (15453659700107/50000000000000 : ℝ)^3473 := by
    have hnat : (2019054913 : ℕ)^4497*50000000000000^3473 ≤ 15453659700107^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019054913 5000000000 15453659700107 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213770799/500000000 : ℝ), (565591323/1250000000 : ℝ), (2019054913/5000000000 : ℝ)] ![(8319818496281/25000000000000 : ℝ), (35813406599977/100000000000000 : ℝ), (15453659700107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213770799/500000000 : ℝ)|^4497 ≤ (8319818496281/25000000000000 : ℝ)^3473
        have hw : |(213770799/500000000 : ℝ)|=(213770799/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565591323/1250000000 : ℝ)|^4497 ≤ (35813406599977/100000000000000 : ℝ)^3473
        have hw : |(565591323/1250000000 : ℝ)|=(565591323/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2019054913/5000000000 : ℝ)|^4497 ≤ (15453659700107/50000000000000 : ℝ)^3473
        have hw : |(2019054913/5000000000 : ℝ)|=(2019054913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1500_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7779/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2699/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (543/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7779/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2699/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7779/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2699/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7779/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2699/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7779/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2699/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7779/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2699/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7779/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2699/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2699/25000 : ℝ) ^ (4495/1024 : ℝ) ≤ (570642210904897/10000000000000000000 : ℝ) := by
    have hpowers : (2699/25000 : ℝ)^4495 ≤ (570642210904897/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2699 : ℕ)^4495*10000000000000000000^1024 ≤ 570642210904897^1024*25000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2699 25000 570642210904897 10000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2699/25000 : ℝ)) (X := (570642210904897/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7779/50000 : ℝ) ^ (4495/1024 : ℝ) ≤ (2837664954000717/10000000000000000000 : ℝ) := by
    have hpowers : (7779/50000 : ℝ)^4495 ≤ (2837664954000717/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7779 : ℕ)^4495*10000000000000000000^1024 ≤ 2837664954000717^1024*50000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7779 50000 2837664954000717 10000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7779/50000 : ℝ)) (X := (2837664954000717/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000570642210904897/5000000000000000000 : ℝ) ≤ (10000259983037669/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (5000570642210904897/5000000000000000000 : ℝ)^1024 ≤ (10000259983037669/10000000000000000 : ℝ)^4495 := by
      have hnat : (5000570642210904897 : ℕ)^1024*10000000000000000^4495 ≤ 10000259983037669^4495*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000570642210904897 5000000000000000000 10000259983037669 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000259983037669/10000000000000000 : ℝ)) (X := (5000570642210904897/5000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5001704153582452807/5000000000000000000 : ℝ) ≤ (400031053591589/400000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (5001704153582452807/5000000000000000000 : ℝ)^1024 ≤ (400031053591589/400000000000000 : ℝ)^4495 := by
      have hnat : (5001704153582452807 : ℕ)^1024*400000000000000^4495 ≤ 400031053591589^4495*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001704153582452807 5000000000000000000 400031053591589 400000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400031053591589/400000000000000 : ℝ)) (X := (5001704153582452807/5000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5002837664954000717/5000000000000000000 : ℝ) ≤ (10001292696541781/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (5002837664954000717/5000000000000000000 : ℝ)^1024 ≤ (10001292696541781/10000000000000000 : ℝ)^4495 := by
      have hnat : (5002837664954000717 : ℕ)^1024*10000000000000000^4495 ≤ 10001292696541781^4495*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5002837664954000717 5000000000000000000 10001292696541781 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001292696541781/10000000000000000 : ℝ)) (X := (5002837664954000717/5000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(570642210904897/10000000000000000000 : ℝ) ≤ ((23805044432117493313/23810000000000000000 : ℝ)+2*(64544594007/59525000000000 : ℝ)*(2699/25000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (23805044432117493313/23810000000000000000 : ℝ)+2*(64544594007/59525000000000 : ℝ)*(2699/25000 : ℝ)=(10000259983037669/10000000000000000 : ℝ) by norm_num, show 1+2*(570642210904897/10000000000000000000 : ℝ)=(5000570642210904897/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2837664954000717/10000000000000000000 : ℝ)+(570642210904897/10000000000000000000 : ℝ) ≤ ((23805044432117493313/23810000000000000000 : ℝ)+(64544594007/59525000000000 : ℝ)*((7779/50000 : ℝ)+(2699/25000 : ℝ)))^(4495/1024 : ℝ) := by
    rw [show (23805044432117493313/23810000000000000000 : ℝ)+(64544594007/59525000000000 : ℝ)*((7779/50000 : ℝ)+(2699/25000 : ℝ))=(400031053591589/400000000000000 : ℝ) by norm_num, show 1+(2837664954000717/10000000000000000000 : ℝ)+(570642210904897/10000000000000000000 : ℝ)=(5001704153582452807/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2837664954000717/10000000000000000000 : ℝ) ≤ ((23805044432117493313/23810000000000000000 : ℝ)+2*(64544594007/59525000000000 : ℝ)*(7779/50000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (23805044432117493313/23810000000000000000 : ℝ)+2*(64544594007/59525000000000 : ℝ)*(7779/50000 : ℝ)=(10001292696541781/10000000000000000 : ℝ) by norm_num, show 1+2*(2837664954000717/10000000000000000000 : ℝ)=(5002837664954000717/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23805044432117493313/23810000000000000000 : ℝ)*(X 1 0+X 2 0)+(64544594007/59525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (2699/25000 : ℝ)) (hi := (7779/50000 : ℝ)) (c := (23805044432117493313/23810000000000000000 : ℝ)) (alpha := (64544594007/59525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23805044432117493313/23810000000000000000 : ℝ)*(X 0 1+X 2 1)+(64544594007/59525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (2699/25000 : ℝ)) (hi := (7779/50000 : ℝ)) (c := (23805044432117493313/23810000000000000000 : ℝ)) (alpha := (64544594007/59525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23805044432117493313/23810000000000000000 : ℝ)*(X 0 2+X 1 2)+(64544594007/59525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (2699/25000 : ℝ)) (hi := (7779/50000 : ℝ)) (c := (23805044432117493313/23810000000000000000 : ℝ)) (alpha := (64544594007/59525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-471455229/2500000000 : ℝ)*X 0 0+(5435271957/10000000000 : ℝ)*X 0 1+(8346529/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((214094911/400000000 : ℝ)*X 1 0+(-1997862539/10000000000 : ℝ)*X 1 1+(1043316147/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352372801/10000000000 : ℝ)*X 2 0+(5216580607/10000000000 : ℝ)*X 2 1+(-998931337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1068837191/2500000000 : ℝ)*X 0 0+(4035555801/10000000000 : ℝ)*X 0 1+(452726601/1000000000 : ℝ)*X 0 2+(1068837191/2500000000 : ℝ)*X 1 0+(4035555801/10000000000 : ℝ)*X 1 1+(452726601/1000000000 : ℝ)*X 1 2+(1068837191/2500000000 : ℝ)*X 2 0+(4035555801/10000000000 : ℝ)*X 2 1+(452726601/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-29466419/156250000 : ℝ)*X 0 0+(5217708361/10000000000 : ℝ)*X 0 1+(5434135839/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295069927/10000000000 : ℝ)*X 1 0+(-55634609/312500000 : ℝ)*X 1 1+(5434135837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647534959/5000000000 : ℝ)*X 2 0+(5434135843/10000000000 : ℝ)*X 2 1+(-445076873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((213770799/500000000 : ℝ)*X 0 0+(565591323/1250000000 : ℝ)*X 0 1+(2019054913/5000000000 : ℝ)*X 0 2+(213770799/500000000 : ℝ)*X 1 0+(565591323/1250000000 : ℝ)*X 1 1+(2019054913/5000000000 : ℝ)*X 1 2+(213770799/500000000 : ℝ)*X 2 0+(565591323/1250000000 : ℝ)*X 2 1+(2019054913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (379726396576451214514883481/148812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (378608387/100000000000000 : ℝ)*(base19) + (16891369/4000000000000 : ℝ)*(base23) + (4582147/10000000000000 : ℝ)*(upper3) + (9297079/50000000000000 : ℝ)*(lower4) + (412899838012721/12500000000000 : ℝ)*(major0) + (412899838012721/12500000000000 : ℝ)*(major1) + (412899838012721/12500000000000 : ℝ)*(major2) + (4572664991707119/100000000000000 : ℝ)*(sp0) + (2286336571724193/50000000000000 : ℝ)*(sp1) + (4572671859665549/100000000000000 : ℝ)*(sp2) + (1016860391221307/50000000000000 : ℝ)*(sp3) + (8530349653/100000000000000 : ℝ)*(sp4) + (1240106999/100000000000000 : ℝ)*(sp6) + (754661783/25000000000000 : ℝ)*(sp7) + (1016861900544873/50000000000000 : ℝ)*(f.failure) + (4572673522056773/100000000000000 : ℝ)*(f.sum) + (9816772194221/2976250000000000000000000000 : ℝ)*base65 + (1736930551100484673/297625000000000000000000000000000 : ℝ)*base67 + (307183832928484673/297625000000000000000000000000000 : ℝ)*base69 + (499170651159484673/297625000000000000000000000000000 : ℝ)*base71 + (4223859871/744062500000000000000000000 : ℝ)*base74 + (111953598639984673/297625000000000000000000000000000 : ℝ)*base75 + (1907543458648140327/297625000000000000000000000000000 : ℝ)*base78 + (5010514747487515327/297625000000000000000000000000000 : ℝ)*base80 + (10446724073943/5952500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5846393/1000000000000000000000 : ℝ)*base89 + (5846393/1000000000000000000000 : ℝ)*base91 + (5846393/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (115624807936419089616423/11905000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1597819951/100000000000000 : ℝ)*(base19) + (1724163459/100000000000000 : ℝ)*(base23) + (200734761/100000000000000 : ℝ)*(upper3) + (3824847/6250000000000 : ℝ)*(lower4) + (200288743/100000000000000 : ℝ)*(upper5) + (417217041660643/12500000000000 : ℝ)*(major0) + (417217041660643/12500000000000 : ℝ)*(major1) + (417217041660643/12500000000000 : ℝ)*(major2) + (24264382823/100000000000000 : ℝ)*(sp1) + (6496290827/25000000000000 : ℝ)*(sp2) + (184819372208861/4000000000000 : ℝ)*(sp4) + (9024332896521/195312500000 : ℝ)*(sp5) + (2310228297947379/50000000000000 : ℝ)*(sp6) + (205498803760577/10000000000000 : ℝ)*(sp7) + (205498803760577/10000000000000 : ℝ)*(f.failure) + (184819372208861/4000000000000 : ℝ)*(f.sum) + (9384070775371/1488125000000000000000000000 : ℝ)*base66 + (1012845907944944741/297625000000000000000000000000000 : ℝ)*base68 + (20481219493805259/297625000000000000000000000000000 : ℝ)*base69 + (2612157454250444741/297625000000000000000000000000000 : ℝ)*base72 + (28653743880803/11905000000000000000000000000 : ℝ)*base74 + (21613428447055259/297625000000000000000000000000000 : ℝ)*base75 + (780859109670819741/297625000000000000000000000000000 : ℝ)*base78 + (3036428997064430259/297625000000000000000000000000000 : ℝ)*base79 + (13936536861057/2976250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1567057/200000000000000000000 : ℝ)*base89 + (1567057/200000000000000000000 : ℝ)*base91 + (1567057/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1500_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7779/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2699/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1500_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1500_s5_0 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885882663/10000000000 : ℝ)*x 0 + (2717425819/5000000000 : ℝ)*x 1 + (5216960311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885882663/10000000000 : ℝ)^4497 ≤ (11531959243227/100000000000000 : ℝ)^3473 := by
    have hnat : (1885882663 : ℕ)^4497*100000000000000^3473 ≤ 11531959243227^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885882663 10000000000 11531959243227 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717425819/5000000000 : ℝ)^4497 ≤ (354730789971/781250000000 : ℝ)^3473 := by
    have hnat : (2717425819 : ℕ)^4497*781250000000^3473 ≤ 354730789971^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717425819 5000000000 354730789971 781250000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216960311/10000000000 : ℝ)^4497 ≤ (21531249812911/50000000000000 : ℝ)^3473 := by
    have hnat : (5216960311 : ℕ)^4497*50000000000000^3473 ≤ 21531249812911^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216960311 10000000000 21531249812911 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885882663/10000000000 : ℝ), (2717425819/5000000000 : ℝ), (5216960311/10000000000 : ℝ)] ![(11531959243227/100000000000000 : ℝ), (354730789971/781250000000 : ℝ), (21531249812911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885882663/10000000000 : ℝ)|^4497 ≤ (11531959243227/100000000000000 : ℝ)^3473
        have hw : |(-1885882663/10000000000 : ℝ)|=(1885882663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717425819/5000000000 : ℝ)|^4497 ≤ (354730789971/781250000000 : ℝ)^3473
        have hw : |(2717425819/5000000000 : ℝ)|=(2717425819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216960311/10000000000 : ℝ)|^4497 ≤ (21531249812911/50000000000000 : ℝ)^3473
        have hw : |(5216960311/10000000000 : ℝ)|=(5216960311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s5_1 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676131813/5000000000 : ℝ)*x 0 + (-998752373/5000000000 : ℝ)*x 1 + (5216960311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676131813/5000000000 : ℝ)^4497 ≤ (44514128537403/100000000000000 : ℝ)^3473 := by
    have hnat : (2676131813 : ℕ)^4497*100000000000000^3473 ≤ 44514128537403^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676131813 5000000000 44514128537403 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (998752373/5000000000 : ℝ)^4497 ≤ (12423371818979/100000000000000 : ℝ)^3473 := by
    have hnat : (998752373 : ℕ)^4497*100000000000000^3473 ≤ 12423371818979^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998752373 5000000000 12423371818979 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216960311/10000000000 : ℝ)^4497 ≤ (21531249812911/50000000000000 : ℝ)^3473 := by
    have hnat : (5216960311 : ℕ)^4497*50000000000000^3473 ≤ 21531249812911^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216960311 10000000000 21531249812911 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676131813/5000000000 : ℝ), (-998752373/5000000000 : ℝ), (5216960311/10000000000 : ℝ)] ![(44514128537403/100000000000000 : ℝ), (12423371818979/100000000000000 : ℝ), (21531249812911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676131813/5000000000 : ℝ)|^4497 ≤ (44514128537403/100000000000000 : ℝ)^3473
        have hw : |(2676131813/5000000000 : ℝ)|=(2676131813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-998752373/5000000000 : ℝ)|^4497 ≤ (12423371818979/100000000000000 : ℝ)^3473
        have hw : |(-998752373/5000000000 : ℝ)|=(998752373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216960311/10000000000 : ℝ)|^4497 ≤ (21531249812911/50000000000000 : ℝ)^3473
        have hw : |(5216960311/10000000000 : ℝ)|=(5216960311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s5_2 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676131813/5000000000 : ℝ)*x 0 + (5216960311/10000000000 : ℝ)*x 1 + (-998752373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676131813/5000000000 : ℝ)^4497 ≤ (44514128537403/100000000000000 : ℝ)^3473 := by
    have hnat : (2676131813 : ℕ)^4497*100000000000000^3473 ≤ 44514128537403^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676131813 5000000000 44514128537403 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216960311/10000000000 : ℝ)^4497 ≤ (21531249812911/50000000000000 : ℝ)^3473 := by
    have hnat : (5216960311 : ℕ)^4497*50000000000000^3473 ≤ 21531249812911^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216960311 10000000000 21531249812911 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998752373/5000000000 : ℝ)^4497 ≤ (12423371818979/100000000000000 : ℝ)^3473 := by
    have hnat : (998752373 : ℕ)^4497*100000000000000^3473 ≤ 12423371818979^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998752373 5000000000 12423371818979 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676131813/5000000000 : ℝ), (5216960311/10000000000 : ℝ), (-998752373/5000000000 : ℝ)] ![(44514128537403/100000000000000 : ℝ), (21531249812911/50000000000000 : ℝ), (12423371818979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676131813/5000000000 : ℝ)|^4497 ≤ (44514128537403/100000000000000 : ℝ)^3473
        have hw : |(2676131813/5000000000 : ℝ)|=(2676131813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216960311/10000000000 : ℝ)|^4497 ≤ (21531249812911/50000000000000 : ℝ)^3473
        have hw : |(5216960311/10000000000 : ℝ)|=(5216960311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998752373/5000000000 : ℝ)|^4497 ≤ (12423371818979/100000000000000 : ℝ)^3473
        have hw : |(-998752373/5000000000 : ℝ)|=(998752373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s5_3 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (855077703/2000000000 : ℝ)*x 0 + (2018225093/5000000000 : ℝ)*x 1 + (565795287/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855077703/2000000000 : ℝ)^4497 ≤ (831974929203/2500000000000 : ℝ)^3473 := by
    have hnat : (855077703 : ℕ)^4497*2500000000000^3473 ≤ 831974929203^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855077703 2000000000 831974929203 2500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018225093/5000000000 : ℝ)^4497 ≤ (7722718079207/25000000000000 : ℝ)^3473 := by
    have hnat : (2018225093 : ℕ)^4497*25000000000000^3473 ≤ 7722718079207^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018225093 5000000000 7722718079207 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565795287/1250000000 : ℝ)^4497 ≤ (35830130501677/100000000000000 : ℝ)^3473 := by
    have hnat : (565795287 : ℕ)^4497*100000000000000^3473 ≤ 35830130501677^3473*1250000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565795287 1250000000 35830130501677 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(855077703/2000000000 : ℝ), (2018225093/5000000000 : ℝ), (565795287/1250000000 : ℝ)] ![(831974929203/2500000000000 : ℝ), (7722718079207/25000000000000 : ℝ), (35830130501677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(855077703/2000000000 : ℝ)|^4497 ≤ (831974929203/2500000000000 : ℝ)^3473
        have hw : |(855077703/2000000000 : ℝ)|=(855077703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2018225093/5000000000 : ℝ)|^4497 ≤ (7722718079207/25000000000000 : ℝ)^3473
        have hw : |(2018225093/5000000000 : ℝ)|=(2018225093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565795287/1250000000 : ℝ)|^4497 ≤ (35830130501677/100000000000000 : ℝ)^3473
        have hw : |(565795287/1250000000 : ℝ)|=(565795287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s5_4 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885912253/10000000000 : ℝ)*x 0 + (2609039883/5000000000 : ℝ)*x 1 + (135843097/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885912253/10000000000 : ℝ)^4497 ≤ (5766096766277/50000000000000 : ℝ)^3473 := by
    have hnat : (1885912253 : ℕ)^4497*50000000000000^3473 ≤ 5766096766277^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885912253 10000000000 5766096766277 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609039883/5000000000 : ℝ)^4497 ≤ (43074464831957/100000000000000 : ℝ)^3473 := by
    have hnat : (2609039883 : ℕ)^4497*100000000000000^3473 ≤ 43074464831957^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609039883 5000000000 43074464831957 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135843097/250000000 : ℝ)^4497 ≤ (2269667081003/5000000000000 : ℝ)^3473 := by
    have hnat : (135843097 : ℕ)^4497*5000000000000^3473 ≤ 2269667081003^3473*250000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135843097 250000000 2269667081003 5000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885912253/10000000000 : ℝ), (2609039883/5000000000 : ℝ), (135843097/250000000 : ℝ)] ![(5766096766277/50000000000000 : ℝ), (43074464831957/100000000000000 : ℝ), (2269667081003/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885912253/10000000000 : ℝ)|^4497 ≤ (5766096766277/50000000000000 : ℝ)^3473
        have hw : |(-1885912253/10000000000 : ℝ)|=(1885912253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609039883/5000000000 : ℝ)|^4497 ≤ (43074464831957/100000000000000 : ℝ)^3473
        have hw : |(2609039883/5000000000 : ℝ)|=(2609039883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135843097/250000000 : ℝ)|^4497 ≤ (2269667081003/5000000000000 : ℝ)^3473
        have hw : |(135843097/250000000 : ℝ)|=(135843097/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s5_5 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295170433/10000000000 : ℝ)*x 0 + (-445185287/2500000000 : ℝ)*x 1 + (5433724007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295170433/10000000000 : ℝ)^4497 ≤ (21950128432341/50000000000000 : ℝ)^3473 := by
    have hnat : (5295170433 : ℕ)^4497*50000000000000^3473 ≤ 21950128432341^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295170433 10000000000 21950128432341 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (445185287/2500000000 : ℝ)^4497 ≤ (2676600031151/25000000000000 : ℝ)^3473 := by
    have hnat : (445185287 : ℕ)^4497*25000000000000^3473 ≤ 2676600031151^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445185287 2500000000 2676600031151 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433724007/10000000000 : ℝ)^4497 ≤ (22696671496919/50000000000000 : ℝ)^3473 := by
    have hnat : (5433724007 : ℕ)^4497*50000000000000^3473 ≤ 22696671496919^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433724007 10000000000 22696671496919 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295170433/10000000000 : ℝ), (-445185287/2500000000 : ℝ), (5433724007/10000000000 : ℝ)] ![(21950128432341/50000000000000 : ℝ), (2676600031151/25000000000000 : ℝ), (22696671496919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295170433/10000000000 : ℝ)|^4497 ≤ (21950128432341/50000000000000 : ℝ)^3473
        have hw : |(5295170433/10000000000 : ℝ)|=(5295170433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-445185287/2500000000 : ℝ)|^4497 ≤ (2676600031151/25000000000000 : ℝ)^3473
        have hw : |(-445185287/2500000000 : ℝ)|=(445185287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433724007/10000000000 : ℝ)|^4497 ≤ (22696671496919/50000000000000 : ℝ)^3473
        have hw : |(5433724007/10000000000 : ℝ)|=(5433724007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s5_6 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323792623/2500000000 : ℝ)*x 0 + (5433723967/10000000000 : ℝ)*x 1 + (-890370561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323792623/2500000000 : ℝ)^4497 ≤ (10975064374513/25000000000000 : ℝ)^3473 := by
    have hnat : (1323792623 : ℕ)^4497*25000000000000^3473 ≤ 10975064374513^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323792623 2500000000 10975064374513 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433723967/10000000000 : ℝ)^4497 ≤ (354635488759/781250000000 : ℝ)^3473 := by
    have hnat : (5433723967 : ℕ)^4497*781250000000^3473 ≤ 354635488759^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433723967 10000000000 354635488759 781250000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890370561/5000000000 : ℝ)^4497 ≤ (10706399922193/100000000000000 : ℝ)^3473 := by
    have hnat : (890370561 : ℕ)^4497*100000000000000^3473 ≤ 10706399922193^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890370561 5000000000 10706399922193 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323792623/2500000000 : ℝ), (5433723967/10000000000 : ℝ), (-890370561/5000000000 : ℝ)] ![(10975064374513/25000000000000 : ℝ), (354635488759/781250000000 : ℝ), (10706399922193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323792623/2500000000 : ℝ)|^4497 ≤ (10975064374513/25000000000000 : ℝ)^3473
        have hw : |(1323792623/2500000000 : ℝ)|=(1323792623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433723967/10000000000 : ℝ)|^4497 ≤ (354635488759/781250000000 : ℝ)^3473
        have hw : |(5433723967/10000000000 : ℝ)|=(5433723967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890370561/5000000000 : ℝ)|^4497 ≤ (10706399922193/100000000000000 : ℝ)^3473
        have hw : |(-890370561/5000000000 : ℝ)|=(890370561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s5_7 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534431847/1250000000 : ℝ)*x 0 + (4523845357/10000000000 : ℝ)*x 1 + (807797149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534431847/1250000000 : ℝ)^4497 ≤ (33279665007043/100000000000000 : ℝ)^3473 := by
    have hnat : (534431847 : ℕ)^4497*100000000000000^3473 ≤ 33279665007043^3473*1250000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534431847 1250000000 33279665007043 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523845357/10000000000 : ℝ)^4497 ≤ (35804334389079/100000000000000 : ℝ)^3473 := by
    have hnat : (4523845357 : ℕ)^4497*100000000000000^3473 ≤ 35804334389079^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523845357 10000000000 35804334389079 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (807797149/2000000000 : ℝ)^4497 ≤ (3864500073503/12500000000000 : ℝ)^3473 := by
    have hnat : (807797149 : ℕ)^4497*12500000000000^3473 ≤ 3864500073503^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807797149 2000000000 3864500073503 12500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534431847/1250000000 : ℝ), (4523845357/10000000000 : ℝ), (807797149/2000000000 : ℝ)] ![(33279665007043/100000000000000 : ℝ), (35804334389079/100000000000000 : ℝ), (3864500073503/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534431847/1250000000 : ℝ)|^4497 ≤ (33279665007043/100000000000000 : ℝ)^3473
        have hw : |(534431847/1250000000 : ℝ)|=(534431847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523845357/10000000000 : ℝ)|^4497 ≤ (35804334389079/100000000000000 : ℝ)^3473
        have hw : |(4523845357/10000000000 : ℝ)|=(4523845357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(807797149/2000000000 : ℝ)|^4497 ≤ (3864500073503/12500000000000 : ℝ)^3473
        have hw : |(807797149/2000000000 : ℝ)|=(807797149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1500_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (2717/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (543/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (543/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (543/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (543/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (543/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (543/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (543/5000 : ℝ) ^ (4495/1024 : ℝ) ≤ (366025983533117/6250000000000000000 : ℝ) := by
    have hpowers : (543/5000 : ℝ)^4495 ≤ (366025983533117/6250000000000000000 : ℝ)^1024 := by
      have hnat : (543 : ℕ)^4495*6250000000000000000^1024 ≤ 366025983533117^1024*5000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        543 5000 366025983533117 6250000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (543/5000 : ℝ)) (X := (366025983533117/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4495/1024 : ℝ) ≤ (27836233542307071/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4495 ≤ (27836233542307071/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4495*100000000000000000000^1024 ≤ 27836233542307071^1024*10000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 27836233542307071 100000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (27836233542307071/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125366025983533117/3125000000000000000 : ℝ) ≤ (10000266816397491/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (3125366025983533117/3125000000000000000 : ℝ)^1024 ≤ (10000266816397491/10000000000000000 : ℝ)^4495 := by
      have hnat : (3125366025983533117 : ℕ)^1024*10000000000000000^4495 ≤ 10000266816397491^4495*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125366025983533117 3125000000000000000 10000266816397491 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000266816397491/10000000000000000 : ℝ)) (X := (3125366025983533117/3125000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033692649278836943/100000000000000000000 : ℝ) ≤ (5000383723978053/5000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (100033692649278836943/100000000000000000000 : ℝ)^1024 ≤ (5000383723978053/5000000000000000 : ℝ)^4495 := by
      have hnat : (100033692649278836943 : ℕ)^1024*5000000000000000^4495 ≤ 5000383723978053^4495*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033692649278836943 100000000000000000000 5000383723978053 5000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000383723978053/5000000000000000 : ℝ)) (X := (100033692649278836943/100000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027836233542307071/50000000000000000000 : ℝ) ≤ (10001268079514721/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (50027836233542307071/50000000000000000000 : ℝ)^1024 ≤ (10001268079514721/10000000000000000 : ℝ)^4495 := by
      have hnat : (50027836233542307071 : ℕ)^1024*10000000000000000^4495 ≤ 10001268079514721^4495*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027836233542307071 50000000000000000000 10001268079514721 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001268079514721/10000000000000000 : ℝ)) (X := (50027836233542307071/50000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(366025983533117/6250000000000000000 : ℝ) ≤ ((4629036164246726553/4630000000000000000 : ℝ)+2*(100126311723/92600000000000 : ℝ)*(543/5000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (4629036164246726553/4630000000000000000 : ℝ)+2*(100126311723/92600000000000 : ℝ)*(543/5000 : ℝ)=(10000266816397491/10000000000000000 : ℝ) by norm_num, show 1+2*(366025983533117/6250000000000000000 : ℝ)=(3125366025983533117/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27836233542307071/100000000000000000000 : ℝ)+(366025983533117/6250000000000000000 : ℝ) ≤ ((4629036164246726553/4630000000000000000 : ℝ)+(100126311723/92600000000000 : ℝ)*((1549/10000 : ℝ)+(543/5000 : ℝ)))^(4495/1024 : ℝ) := by
    rw [show (4629036164246726553/4630000000000000000 : ℝ)+(100126311723/92600000000000 : ℝ)*((1549/10000 : ℝ)+(543/5000 : ℝ))=(5000383723978053/5000000000000000 : ℝ) by norm_num, show 1+(27836233542307071/100000000000000000000 : ℝ)+(366025983533117/6250000000000000000 : ℝ)=(100033692649278836943/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27836233542307071/100000000000000000000 : ℝ) ≤ ((4629036164246726553/4630000000000000000 : ℝ)+2*(100126311723/92600000000000 : ℝ)*(1549/10000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (4629036164246726553/4630000000000000000 : ℝ)+2*(100126311723/92600000000000 : ℝ)*(1549/10000 : ℝ)=(10001268079514721/10000000000000000 : ℝ) by norm_num, show 1+2*(27836233542307071/100000000000000000000 : ℝ)=(50027836233542307071/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4629036164246726553/4630000000000000000 : ℝ)*(X 1 0+X 2 0)+(100126311723/92600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (543/5000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4629036164246726553/4630000000000000000 : ℝ)) (alpha := (100126311723/92600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4629036164246726553/4630000000000000000 : ℝ)*(X 0 1+X 2 1)+(100126311723/92600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (543/5000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4629036164246726553/4630000000000000000 : ℝ)) (alpha := (100126311723/92600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4629036164246726553/4630000000000000000 : ℝ)*(X 0 2+X 1 2)+(100126311723/92600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (543/5000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (4629036164246726553/4630000000000000000 : ℝ)) (alpha := (100126311723/92600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1885882663/10000000000 : ℝ)*X 0 0+(2717425819/5000000000 : ℝ)*X 0 1+(5216960311/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676131813/5000000000 : ℝ)*X 1 0+(-998752373/5000000000 : ℝ)*X 1 1+(5216960311/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676131813/5000000000 : ℝ)*X 2 0+(5216960311/10000000000 : ℝ)*X 2 1+(-998752373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((855077703/2000000000 : ℝ)*X 0 0+(2018225093/5000000000 : ℝ)*X 0 1+(565795287/1250000000 : ℝ)*X 0 2+(855077703/2000000000 : ℝ)*X 1 0+(2018225093/5000000000 : ℝ)*X 1 1+(565795287/1250000000 : ℝ)*X 1 2+(855077703/2000000000 : ℝ)*X 2 0+(2018225093/5000000000 : ℝ)*X 2 1+(565795287/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1885912253/10000000000 : ℝ)*X 0 0+(2609039883/5000000000 : ℝ)*X 0 1+(135843097/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295170433/10000000000 : ℝ)*X 1 0+(-445185287/2500000000 : ℝ)*X 1 1+(5433724007/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323792623/2500000000 : ℝ)*X 2 0+(5433723967/10000000000 : ℝ)*X 2 1+(-890370561/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((534431847/1250000000 : ℝ)*X 0 0+(4523845357/10000000000 : ℝ)*X 0 1+(807797149/2000000000 : ℝ)*X 0 2+(534431847/1250000000 : ℝ)*X 1 0+(4523845357/10000000000 : ℝ)*X 1 1+(807797149/2000000000 : ℝ)*X 1 2+(534431847/1250000000 : ℝ)*X 2 0+(4523845357/10000000000 : ℝ)*X 2 1+(807797149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (858183926014607306581633311/231500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131414317/20000000000000 : ℝ)*(base19) + (612955143/100000000000000 : ℝ)*(base23) + (23612283/100000000000000 : ℝ)*(lower2) + (2320317/2500000000000 : ℝ)*(upper3) + (60450763/100000000000000 : ℝ)*(upper5) + (3315328270385057/100000000000000 : ℝ)*(major0) + (3315328270385057/100000000000000 : ℝ)*(major1) + (3315328270385057/100000000000000 : ℝ)*(major2) + (2294727214735987/50000000000000 : ℝ)*(sp0) + (4589463989397121/100000000000000 : ℝ)*(sp1) + (4589464033513563/100000000000000 : ℝ)*(sp2) + (2041186843619507/100000000000000 : ℝ)*(sp3) + (2554249183/25000000000000 : ℝ)*(sp4) + (4927113297/100000000000000 : ℝ)*(sp7) + (510297942683201/25000000000000 : ℝ)*(f.failure) + (2294732323234353/50000000000000 : ℝ)*(f.sum) + (5555703362759/4630000000000000000000000000 : ℝ)*base66 + (2080505846591868521/463000000000000000000000000000000 : ℝ)*base67 + (676719961963868521/463000000000000000000000000000000 : ℝ)*base69 + (3333925154707868521/463000000000000000000000000000000 : ℝ)*base71 + (5809332197739/4630000000000000000000000000 : ℝ)*base74 + (3695720464072868521/463000000000000000000000000000000 : ℝ)*base75 + (4340885940311868521/463000000000000000000000000000000 : ℝ)*base77 + (1087426420944868521/463000000000000000000000000000000 : ℝ)*base79 + (1070227516359/4630000000000000000000000000 : ℝ)*base82 + (2935441/500000000000000000000 : ℝ)*base89 + (2935441/500000000000000000000 : ℝ)*base91 + (2935441/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1712674907098432697212195173/231500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (291060561/25000000000000 : ℝ)*(base19) + (250476507/20000000000000 : ℝ)*(base23) + (102371949/25000000000000 : ℝ)*(lower1) + (4420959/50000000000000 : ℝ)*(upper2) + (90515209/50000000000000 : ℝ)*(upper3) + (143849097/100000000000000 : ℝ)*(upper5) + (3349847600963153/100000000000000 : ℝ)*(major0) + (3349847600963153/100000000000000 : ℝ)*(major1) + (3349847600963153/100000000000000 : ℝ)*(major2) + (1833863117/100000000000000 : ℝ)*(sp2) + (2318625107107521/50000000000000 : ℝ)*(sp4) + (4637249049972797/100000000000000 : ℝ)*(sp5) + (4637247127969389/100000000000000 : ℝ)*(sp6) + (2062444741105789/100000000000000 : ℝ)*(sp7) + (2062444741105789/100000000000000 : ℝ)*(f.failure) + (2318625107107521/50000000000000 : ℝ)*(f.sum) + (12337509548679/4630000000000000000000000000 : ℝ)*base65 + (8482361186884348391/463000000000000000000000000000000 : ℝ)*base68 + (25389297903155651609/463000000000000000000000000000000 : ℝ)*base69 + (174119461355651609/463000000000000000000000000000000 : ℝ)*base71 + (15897767977091/4630000000000000000000000000 : ℝ)*base74 + (6598334274558651609/463000000000000000000000000000000 : ℝ)*base75 + (838320496428651609/463000000000000000000000000000000 : ℝ)*base77 + (2007007726898348391/463000000000000000000000000000000 : ℝ)*base80 + (180776810341669/4630000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3628851/2000000000000000000000 : ℝ)*base90 + (3628851/2000000000000000000000 : ℝ)*base92 + (3628851/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1500_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (543/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1500_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1500_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4011/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1500_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1500_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1500_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4011/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (207/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1500_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
