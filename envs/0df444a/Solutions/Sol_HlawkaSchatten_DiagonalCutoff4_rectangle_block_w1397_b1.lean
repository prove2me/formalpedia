-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1397_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:44:38.120984+00:00
-- url     : https://prove2.me/submissions/65ce2766-e485-435e-a719-f0933965dac8

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
theorem support_rectangle_w1397_s3_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-249514461/1250000000 : ℝ)*x 0 + (5420653111/10000000000 : ℝ)*x 1 + (5236202147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249514461/1250000000 : ℝ)^4357 ≤ (12166936933311/100000000000000 : ℝ)^3333 := by
    have hnat : (249514461 : ℕ)^4357*100000000000000^3333 ≤ 12166936933311^3333*1250000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249514461 1250000000 12166936933311 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5420653111/10000000000 : ℝ)^4357 ≤ (44910108223617/100000000000000 : ℝ)^3333 := by
    have hnat : (5420653111 : ℕ)^4357*100000000000000^3333 ≤ 44910108223617^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420653111 10000000000 44910108223617 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236202147/10000000000 : ℝ)^4357 ≤ (42922954819057/100000000000000 : ℝ)^3333 := by
    have hnat : (5236202147 : ℕ)^4357*100000000000000^3333 ≤ 42922954819057^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236202147 10000000000 42922954819057 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249514461/1250000000 : ℝ), (5420653111/10000000000 : ℝ), (5236202147/10000000000 : ℝ)] ![(12166936933311/100000000000000 : ℝ), (44910108223617/100000000000000 : ℝ), (42922954819057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249514461/1250000000 : ℝ)|^4357 ≤ (12166936933311/100000000000000 : ℝ)^3333
        have hw : |(-249514461/1250000000 : ℝ)|=(249514461/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5420653111/10000000000 : ℝ)|^4357 ≤ (44910108223617/100000000000000 : ℝ)^3333
        have hw : |(5420653111/10000000000 : ℝ)|=(5420653111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236202147/10000000000 : ℝ)|^4357 ≤ (42922954819057/100000000000000 : ℝ)^3333
        have hw : |(5236202147/10000000000 : ℝ)|=(5236202147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337688259/2500000000 : ℝ)*x 0 + (-41805279/200000000 : ℝ)*x 1 + (1636313/3125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337688259/2500000000 : ℝ)^4357 ≤ (44154566157761/100000000000000 : ℝ)^3333 := by
    have hnat : (1337688259 : ℕ)^4357*100000000000000^3333 ≤ 44154566157761^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337688259 2500000000 44154566157761 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41805279/200000000 : ℝ)^4357 ≤ (6461242434029/50000000000000 : ℝ)^3333 := by
    have hnat : (41805279 : ℕ)^4357*50000000000000^3333 ≤ 6461242434029^3333*200000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41805279 200000000 6461242434029 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1636313/3125000 : ℝ)^4357 ≤ (42922948957503/100000000000000 : ℝ)^3333 := by
    have hnat : (1636313 : ℕ)^4357*100000000000000^3333 ≤ 42922948957503^3333*3125000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636313 3125000 42922948957503 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337688259/2500000000 : ℝ), (-41805279/200000000 : ℝ), (1636313/3125000 : ℝ)] ![(44154566157761/100000000000000 : ℝ), (6461242434029/50000000000000 : ℝ), (42922948957503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337688259/2500000000 : ℝ)|^4357 ≤ (44154566157761/100000000000000 : ℝ)^3333
        have hw : |(1337688259/2500000000 : ℝ)|=(1337688259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41805279/200000000 : ℝ)|^4357 ≤ (6461242434029/50000000000000 : ℝ)^3333
        have hw : |(-41805279/200000000 : ℝ)|=(41805279/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1636313/3125000 : ℝ)|^4357 ≤ (42922948957503/100000000000000 : ℝ)^3333
        have hw : |(1636313/3125000 : ℝ)|=(1636313/3125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337688091/2500000000 : ℝ)*x 0 + (523620221/1000000000 : ℝ)*x 1 + (-2090264039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337688091/2500000000 : ℝ)^4357 ≤ (11038639727173/25000000000000 : ℝ)^3333 := by
    have hnat : (1337688091 : ℕ)^4357*25000000000000^3333 ≤ 11038639727173^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337688091 2500000000 11038639727173 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523620221/1000000000 : ℝ)^4357 ≤ (21461477747077/50000000000000 : ℝ)^3333 := by
    have hnat : (523620221 : ℕ)^4357*50000000000000^3333 ≤ 21461477747077^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523620221 1000000000 21461477747077 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090264039/10000000000 : ℝ)^4357 ≤ (323062139683/2500000000000 : ℝ)^3333 := by
    have hnat : (2090264039 : ℕ)^4357*2500000000000^3333 ≤ 323062139683^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090264039 10000000000 323062139683 2500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337688091/2500000000 : ℝ), (523620221/1000000000 : ℝ), (-2090264039/10000000000 : ℝ)] ![(11038639727173/25000000000000 : ℝ), (21461477747077/50000000000000 : ℝ), (323062139683/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337688091/2500000000 : ℝ)|^4357 ≤ (11038639727173/25000000000000 : ℝ)^3333
        have hw : |(1337688091/2500000000 : ℝ)|=(1337688091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523620221/1000000000 : ℝ)|^4357 ≤ (21461477747077/50000000000000 : ℝ)^3333
        have hw : |(523620221/1000000000 : ℝ)|=(523620221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090264039/10000000000 : ℝ)|^4357 ≤ (323062139683/2500000000000 : ℝ)^3333
        have hw : |(-2090264039/10000000000 : ℝ)|=(2090264039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4311663161/10000000000 : ℝ)*x 0 + (4118597467/10000000000 : ℝ)*x 1 + (902590469/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4311663161/10000000000 : ℝ)^4357 ≤ (2081021216853/6250000000000 : ℝ)^3333 := by
    have hnat : (4311663161 : ℕ)^4357*6250000000000^3333 ≤ 2081021216853^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4311663161 10000000000 2081021216853 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4118597467/10000000000 : ℝ)^4357 ≤ (15680449785543/50000000000000 : ℝ)^3333 := by
    have hnat : (4118597467 : ℕ)^4357*50000000000000^3333 ≤ 15680449785543^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118597467 10000000000 15680449785543 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902590469/2000000000 : ℝ)^4357 ≤ (35342760944701/100000000000000 : ℝ)^3333 := by
    have hnat : (902590469 : ℕ)^4357*100000000000000^3333 ≤ 35342760944701^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902590469 2000000000 35342760944701 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4311663161/10000000000 : ℝ), (4118597467/10000000000 : ℝ), (902590469/2000000000 : ℝ)] ![(2081021216853/6250000000000 : ℝ), (15680449785543/50000000000000 : ℝ), (35342760944701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4311663161/10000000000 : ℝ)|^4357 ≤ (2081021216853/6250000000000 : ℝ)^3333
        have hw : |(4311663161/10000000000 : ℝ)|=(4311663161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4118597467/10000000000 : ℝ)|^4357 ≤ (15680449785543/50000000000000 : ℝ)^3333
        have hw : |(4118597467/10000000000 : ℝ)|=(4118597467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902590469/2000000000 : ℝ)|^4357 ≤ (35342760944701/100000000000000 : ℝ)^3333
        have hw : |(902590469/2000000000 : ℝ)|=(902590469/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-399226539/2000000000 : ℝ)*x 0 + (2618474473/5000000000 : ℝ)*x 1 + (541990167/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399226539/2000000000 : ℝ)^4357 ≤ (12167072444787/100000000000000 : ℝ)^3333 := by
    have hnat : (399226539 : ℕ)^4357*100000000000000^3333 ≤ 12167072444787^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399226539 2000000000 12167072444787 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618474473/5000000000 : ℝ)^4357 ≤ (8586191511767/20000000000000 : ℝ)^3333 := by
    have hnat : (2618474473 : ℕ)^4357*20000000000000^3333 ≤ 8586191511767^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618474473 5000000000 8586191511767 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541990167/1000000000 : ℝ)^4357 ≤ (11225492496479/25000000000000 : ℝ)^3333 := by
    have hnat : (541990167 : ℕ)^4357*25000000000000^3333 ≤ 11225492496479^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541990167 1000000000 11225492496479 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399226539/2000000000 : ℝ), (2618474473/5000000000 : ℝ), (541990167/1000000000 : ℝ)] ![(12167072444787/100000000000000 : ℝ), (8586191511767/20000000000000 : ℝ), (11225492496479/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399226539/2000000000 : ℝ)|^4357 ≤ (12167072444787/100000000000000 : ℝ)^3333
        have hw : |(-399226539/2000000000 : ℝ)|=(399226539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618474473/5000000000 : ℝ)|^4357 ≤ (8586191511767/20000000000000 : ℝ)^3333
        have hw : |(2618474473/5000000000 : ℝ)|=(2618474473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541990167/1000000000 : ℝ)|^4357 ≤ (11225492496479/25000000000000 : ℝ)^3333
        have hw : |(541990167/1000000000 : ℝ)|=(541990167/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302955161/10000000000 : ℝ)*x 0 + (-1906563819/10000000000 : ℝ)*x 1 + (5419902177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302955161/10000000000 : ℝ)^4357 ≤ (21819832450433/50000000000000 : ℝ)^3333 := by
    have hnat : (5302955161 : ℕ)^4357*50000000000000^3333 ≤ 21819832450433^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302955161 10000000000 21819832450433 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906563819/10000000000 : ℝ)^4357 ≤ (179036868913/1562500000000 : ℝ)^3333 := by
    have hnat : (1906563819 : ℕ)^4357*1562500000000^3333 ≤ 179036868913^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906563819 10000000000 179036868913 1562500000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419902177/10000000000 : ℝ)^4357 ≤ (22450987738349/50000000000000 : ℝ)^3333 := by
    have hnat : (5419902177 : ℕ)^4357*50000000000000^3333 ≤ 22450987738349^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419902177 10000000000 22450987738349 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302955161/10000000000 : ℝ), (-1906563819/10000000000 : ℝ), (5419902177/10000000000 : ℝ)] ![(21819832450433/50000000000000 : ℝ), (179036868913/1562500000000 : ℝ), (22450987738349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302955161/10000000000 : ℝ)|^4357 ≤ (21819832450433/50000000000000 : ℝ)^3333
        have hw : |(5302955161/10000000000 : ℝ)|=(5302955161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906563819/10000000000 : ℝ)|^4357 ≤ (179036868913/1562500000000 : ℝ)^3333
        have hw : |(-1906563819/10000000000 : ℝ)|=(1906563819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419902177/10000000000 : ℝ)|^4357 ≤ (22450987738349/50000000000000 : ℝ)^3333
        have hw : |(5419902177/10000000000 : ℝ)|=(5419902177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325739053/2500000000 : ℝ)*x 0 + (2709950691/5000000000 : ℝ)*x 1 + (-76262539/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325739053/2500000000 : ℝ)^4357 ≤ (5454959525889/12500000000000 : ℝ)^3333 := by
    have hnat : (1325739053 : ℕ)^4357*12500000000000^3333 ≤ 5454959525889^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325739053 2500000000 5454959525889 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709950691/5000000000 : ℝ)^4357 ≤ (11225491716723/25000000000000 : ℝ)^3333 := by
    have hnat : (2709950691 : ℕ)^4357*25000000000000^3333 ≤ 11225491716723^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709950691 5000000000 11225491716723 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76262539/400000000 : ℝ)^4357 ≤ (1432294613479/12500000000000 : ℝ)^3333 := by
    have hnat : (76262539 : ℕ)^4357*12500000000000^3333 ≤ 1432294613479^3333*400000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76262539 400000000 1432294613479 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325739053/2500000000 : ℝ), (2709950691/5000000000 : ℝ), (-76262539/400000000 : ℝ)] ![(5454959525889/12500000000000 : ℝ), (11225491716723/25000000000000 : ℝ), (1432294613479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325739053/2500000000 : ℝ)|^4357 ≤ (5454959525889/12500000000000 : ℝ)^3333
        have hw : |(1325739053/2500000000 : ℝ)|=(1325739053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709950691/5000000000 : ℝ)|^4357 ≤ (11225491716723/25000000000000 : ℝ)^3333
        have hw : |(2709950691/5000000000 : ℝ)|=(2709950691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76262539/400000000 : ℝ)|^4357 ≤ (1432294613479/12500000000000 : ℝ)^3333
        have hw : |(-76262539/400000000 : ℝ)|=(76262539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077925157/2500000000 : ℝ)*x 0 + (225567757/500000000 : ℝ)*x 1 + (824040399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077925157/2500000000 : ℝ)^4357 ≤ (16648358848709/50000000000000 : ℝ)^3333 := by
    have hnat : (1077925157 : ℕ)^4357*50000000000000^3333 ≤ 16648358848709^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077925157 2500000000 16648358848709 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225567757/500000000 : ℝ)^4357 ≤ (17663205260353/50000000000000 : ℝ)^3333 := by
    have hnat : (225567757 : ℕ)^4357*50000000000000^3333 ≤ 17663205260353^3333*500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225567757 500000000 17663205260353 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824040399/2000000000 : ℝ)^4357 ≤ (31376871769539/100000000000000 : ℝ)^3333 := by
    have hnat : (824040399 : ℕ)^4357*100000000000000^3333 ≤ 31376871769539^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824040399 2000000000 31376871769539 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077925157/2500000000 : ℝ), (225567757/500000000 : ℝ), (824040399/2000000000 : ℝ)] ![(16648358848709/50000000000000 : ℝ), (17663205260353/50000000000000 : ℝ), (31376871769539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077925157/2500000000 : ℝ)|^4357 ≤ (16648358848709/50000000000000 : ℝ)^3333
        have hw : |(1077925157/2500000000 : ℝ)|=(1077925157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(225567757/500000000 : ℝ)|^4357 ≤ (17663205260353/50000000000000 : ℝ)^3333
        have hw : |(225567757/500000000 : ℝ)|=(225567757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(824040399/2000000000 : ℝ)|^4357 ≤ (31376871769539/100000000000000 : ℝ)^3333
        have hw : |(824040399/2000000000 : ℝ)|=(824040399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_8 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-82280781/10000000000 : ℝ)*x 0 + (357051533/625000000 : ℝ)*x 1 + (3019050423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82280781/10000000000 : ℝ)^4357 ≤ (94142132423/50000000000000 : ℝ)^3333 := by
    have hnat : (82280781 : ℕ)^4357*50000000000000^3333 ≤ 94142132423^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82280781 10000000000 94142132423 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357051533/625000000 : ℝ)^4357 ≤ (12025081123271/25000000000000 : ℝ)^3333 := by
    have hnat : (357051533 : ℕ)^4357*25000000000000^3333 ≤ 12025081123271^3333*625000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357051533 625000000 12025081123271 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3019050423/5000000000 : ℝ)^4357 ≤ (25855695610871/50000000000000 : ℝ)^3333 := by
    have hnat : (3019050423 : ℕ)^4357*50000000000000^3333 ≤ 25855695610871^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3019050423 5000000000 25855695610871 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82280781/10000000000 : ℝ), (357051533/625000000 : ℝ), (3019050423/5000000000 : ℝ)] ![(94142132423/50000000000000 : ℝ), (12025081123271/25000000000000 : ℝ), (25855695610871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82280781/10000000000 : ℝ)|^4357 ≤ (94142132423/50000000000000 : ℝ)^3333
        have hw : |(-82280781/10000000000 : ℝ)|=(82280781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(357051533/625000000 : ℝ)|^4357 ≤ (12025081123271/25000000000000 : ℝ)^3333
        have hw : |(357051533/625000000 : ℝ)|=(357051533/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3019050423/5000000000 : ℝ)|^4357 ≤ (25855695610871/50000000000000 : ℝ)^3333
        have hw : |(3019050423/5000000000 : ℝ)|=(3019050423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_9 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (258955181/2500000000 : ℝ)*x 0 + (-4203255653/10000000000 : ℝ)*x 1 + (1747821899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258955181/2500000000 : ℝ)^4357 ≤ (645148635701/12500000000000 : ℝ)^3333 := by
    have hnat : (258955181 : ℕ)^4357*12500000000000^3333 ≤ 645148635701^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258955181 2500000000 645148635701 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4203255653/10000000000 : ℝ)^4357 ≤ (6441244673273/20000000000000 : ℝ)^3333 := by
    have hnat : (4203255653 : ℕ)^4357*20000000000000^3333 ≤ 6441244673273^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203255653 10000000000 6441244673273 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1747821899/2500000000 : ℝ)^4357 ≤ (62632587534991/100000000000000 : ℝ)^3333 := by
    have hnat : (1747821899 : ℕ)^4357*100000000000000^3333 ≤ 62632587534991^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1747821899 2500000000 62632587534991 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258955181/2500000000 : ℝ), (-4203255653/10000000000 : ℝ), (1747821899/2500000000 : ℝ)] ![(645148635701/12500000000000 : ℝ), (6441244673273/20000000000000 : ℝ), (62632587534991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258955181/2500000000 : ℝ)|^4357 ≤ (645148635701/12500000000000 : ℝ)^3333
        have hw : |(258955181/2500000000 : ℝ)|=(258955181/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4203255653/10000000000 : ℝ)|^4357 ≤ (6441244673273/20000000000000 : ℝ)^3333
        have hw : |(-4203255653/10000000000 : ℝ)|=(4203255653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1747821899/2500000000 : ℝ)|^4357 ≤ (62632587534991/100000000000000 : ℝ)^3333
        have hw : |(1747821899/2500000000 : ℝ)|=(1747821899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_10 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1035837733/10000000000 : ℝ)*x 0 + (3495662963/5000000000 : ℝ)*x 1 + (-131349993/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1035837733/10000000000 : ℝ)^4357 ≤ (206451994991/4000000000000 : ℝ)^3333 := by
    have hnat : (1035837733 : ℕ)^4357*4000000000000^3333 ≤ 206451994991^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035837733 10000000000 206451994991 4000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3495662963/5000000000 : ℝ)^4357 ≤ (62633036419499/100000000000000 : ℝ)^3333 := by
    have hnat : (3495662963 : ℕ)^4357*100000000000000^3333 ≤ 62633036419499^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495662963 5000000000 62633036419499 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131349993/312500000 : ℝ)^4357 ≤ (8051415922027/25000000000000 : ℝ)^3333 := by
    have hnat : (131349993 : ℕ)^4357*25000000000000^3333 ≤ 8051415922027^3333*312500000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131349993 312500000 8051415922027 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1035837733/10000000000 : ℝ), (3495662963/5000000000 : ℝ), (-131349993/312500000 : ℝ)] ![(206451994991/4000000000000 : ℝ), (62633036419499/100000000000000 : ℝ), (8051415922027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1035837733/10000000000 : ℝ)|^4357 ≤ (206451994991/4000000000000 : ℝ)^3333
        have hw : |(1035837733/10000000000 : ℝ)|=(1035837733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3495662963/5000000000 : ℝ)|^4357 ≤ (62633036419499/100000000000000 : ℝ)^3333
        have hw : |(3495662963/5000000000 : ℝ)|=(3495662963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-131349993/312500000 : ℝ)|^4357 ≤ (8051415922027/25000000000000 : ℝ)^3333
        have hw : |(-131349993/312500000 : ℝ)|=(131349993/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s3_11 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (977748187/10000000000 : ℝ)*x 0 + (582417433/1000000000 : ℝ)*x 1 + (2755184029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977748187/10000000000 : ℝ)^4357 ≤ (4786231892767/100000000000000 : ℝ)^3333 := by
    have hnat : (977748187 : ℕ)^4357*100000000000000^3333 ≤ 4786231892767^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977748187 10000000000 4786231892767 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (582417433/1000000000 : ℝ)^4357 ≤ (6166193702119/12500000000000 : ℝ)^3333 := by
    have hnat : (582417433 : ℕ)^4357*12500000000000^3333 ≤ 6166193702119^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582417433 1000000000 6166193702119 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2755184029/5000000000 : ℝ)^4357 ≤ (22942109239783/50000000000000 : ℝ)^3333 := by
    have hnat : (2755184029 : ℕ)^4357*50000000000000^3333 ≤ 22942109239783^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755184029 5000000000 22942109239783 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(977748187/10000000000 : ℝ), (582417433/1000000000 : ℝ), (2755184029/5000000000 : ℝ)] ![(4786231892767/100000000000000 : ℝ), (6166193702119/12500000000000 : ℝ), (22942109239783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(977748187/10000000000 : ℝ)|^4357 ≤ (4786231892767/100000000000000 : ℝ)^3333
        have hw : |(977748187/10000000000 : ℝ)|=(977748187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(582417433/1000000000 : ℝ)|^4357 ≤ (6166193702119/12500000000000 : ℝ)^3333
        have hw : |(582417433/1000000000 : ℝ)|=(582417433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2755184029/5000000000 : ℝ)|^4357 ≤ (22942109239783/50000000000000 : ℝ)^3333
        have hw : |(2755184029/5000000000 : ℝ)|=(2755184029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15903/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1019/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (553/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2993/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15903/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1019/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15903/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1019/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15903/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1019/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15903/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1019/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15903/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1019/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15903/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1019/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1019/10000 : ℝ) ^ (1089/256 : ℝ) ≤ (754702824649281/12500000000000000000 : ℝ) := by
    have hpowers : (1019/10000 : ℝ)^1089 ≤ (754702824649281/12500000000000000000 : ℝ)^256 := by
      have hnat : (1019 : ℕ)^1089*12500000000000000000^256 ≤ 754702824649281^256*10000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1019 10000 754702824649281 12500000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1019/10000 : ℝ)) (X := (754702824649281/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (15903/100000 : ℝ) ^ (1089/256 : ℝ) ≤ (626594825514047/1562500000000000000 : ℝ) := by
    have hpowers : (15903/100000 : ℝ)^1089 ≤ (626594825514047/1562500000000000000 : ℝ)^256 := by
      have hnat : (15903 : ℕ)^1089*1562500000000000000^256 ≤ 626594825514047^256*100000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15903 100000 626594825514047 1562500000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15903/100000 : ℝ)) (X := (626594825514047/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250754702824649281/6250000000000000000 : ℝ) ≤ (5000141924702287/5000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (6250754702824649281/6250000000000000000 : ℝ)^256 ≤ (5000141924702287/5000000000000000 : ℝ)^1089 := by
      have hnat : (6250754702824649281 : ℕ)^256*5000000000000000^1089 ≤ 5000141924702287^1089*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250754702824649281 6250000000000000000 5000141924702287 5000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000141924702287/5000000000000000 : ℝ)) (X := (6250754702824649281/6250000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505767461428761657/12500000000000000000 : ℝ) ≤ (2500271112883237/2500000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (12505767461428761657/12500000000000000000 : ℝ)^256 ≤ (2500271112883237/2500000000000000 : ℝ)^1089 := by
      have hnat : (12505767461428761657 : ℕ)^256*2500000000000000^1089 ≤ 2500271112883237^1089*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505767461428761657 12500000000000000000 2500271112883237 2500000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500271112883237/2500000000000000 : ℝ)) (X := (12505767461428761657/12500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (781876594825514047/781250000000000000 : ℝ) ≤ (5000942526830661/5000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (781876594825514047/781250000000000000 : ℝ)^256 ≤ (5000942526830661/5000000000000000 : ℝ)^1089 := by
      have hnat : (781876594825514047 : ℕ)^256*5000000000000000^1089 ≤ 5000942526830661^1089*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781876594825514047 781250000000000000 5000942526830661 5000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000942526830661/5000000000000000 : ℝ)) (X := (781876594825514047/781250000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(754702824649281/12500000000000000000 : ℝ) ≤ ((28557652680136034571/28565000000000000000 : ℝ)+2*(400301064187/285650000000000 : ℝ)*(1019/10000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (28557652680136034571/28565000000000000000 : ℝ)+2*(400301064187/285650000000000 : ℝ)*(1019/10000 : ℝ)=(5000141924702287/5000000000000000 : ℝ) by norm_num, show 1+2*(754702824649281/12500000000000000000 : ℝ)=(6250754702824649281/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(626594825514047/1562500000000000000 : ℝ)+(754702824649281/12500000000000000000 : ℝ) ≤ ((28557652680136034571/28565000000000000000 : ℝ)+(400301064187/285650000000000 : ℝ)*((15903/100000 : ℝ)+(1019/10000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (28557652680136034571/28565000000000000000 : ℝ)+(400301064187/285650000000000 : ℝ)*((15903/100000 : ℝ)+(1019/10000 : ℝ))=(2500271112883237/2500000000000000 : ℝ) by norm_num, show 1+(626594825514047/1562500000000000000 : ℝ)+(754702824649281/12500000000000000000 : ℝ)=(12505767461428761657/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(626594825514047/1562500000000000000 : ℝ) ≤ ((28557652680136034571/28565000000000000000 : ℝ)+2*(400301064187/285650000000000 : ℝ)*(15903/100000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (28557652680136034571/28565000000000000000 : ℝ)+2*(400301064187/285650000000000 : ℝ)*(15903/100000 : ℝ)=(5000942526830661/5000000000000000 : ℝ) by norm_num, show 1+2*(626594825514047/1562500000000000000 : ℝ)=(781876594825514047/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28557652680136034571/28565000000000000000 : ℝ)*(X 1 0+X 2 0)+(400301064187/285650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (1019/10000 : ℝ)) (hi := (15903/100000 : ℝ)) (c := (28557652680136034571/28565000000000000000 : ℝ)) (alpha := (400301064187/285650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28557652680136034571/28565000000000000000 : ℝ)*(X 0 1+X 2 1)+(400301064187/285650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (1019/10000 : ℝ)) (hi := (15903/100000 : ℝ)) (c := (28557652680136034571/28565000000000000000 : ℝ)) (alpha := (400301064187/285650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28557652680136034571/28565000000000000000 : ℝ)*(X 0 2+X 1 2)+(400301064187/285650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (1019/10000 : ℝ)) (hi := (15903/100000 : ℝ)) (c := (28557652680136034571/28565000000000000000 : ℝ)) (alpha := (400301064187/285650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-249514461/1250000000 : ℝ)*X 0 0+(5420653111/10000000000 : ℝ)*X 0 1+(5236202147/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337688259/2500000000 : ℝ)*X 1 0+(-41805279/200000000 : ℝ)*X 1 1+(1636313/3125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337688091/2500000000 : ℝ)*X 2 0+(523620221/1000000000 : ℝ)*X 2 1+(-2090264039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4311663161/10000000000 : ℝ)*X 0 0+(4118597467/10000000000 : ℝ)*X 0 1+(902590469/2000000000 : ℝ)*X 0 2+(4311663161/10000000000 : ℝ)*X 1 0+(4118597467/10000000000 : ℝ)*X 1 1+(902590469/2000000000 : ℝ)*X 1 2+(4311663161/10000000000 : ℝ)*X 2 0+(4118597467/10000000000 : ℝ)*X 2 1+(902590469/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-399226539/2000000000 : ℝ)*X 0 0+(2618474473/5000000000 : ℝ)*X 0 1+(541990167/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302955161/10000000000 : ℝ)*X 1 0+(-1906563819/10000000000 : ℝ)*X 1 1+(5419902177/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325739053/2500000000 : ℝ)*X 2 0+(2709950691/5000000000 : ℝ)*X 2 1+(-76262539/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1077925157/2500000000 : ℝ)*X 0 0+(225567757/500000000 : ℝ)*X 0 1+(824040399/2000000000 : ℝ)*X 0 2+(1077925157/2500000000 : ℝ)*X 1 0+(225567757/500000000 : ℝ)*X 1 1+(824040399/2000000000 : ℝ)*X 1 2+(1077925157/2500000000 : ℝ)*X 2 0+(225567757/500000000 : ℝ)*X 2 1+(824040399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-82280781/10000000000 : ℝ)*X 0 0+(357051533/625000000 : ℝ)*X 0 1+(3019050423/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((258955181/2500000000 : ℝ)*X 1 0+(-4203255653/10000000000 : ℝ)*X 1 1+(1747821899/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1035837733/10000000000 : ℝ)*X 2 0+(3495662963/5000000000 : ℝ)*X 2 1+(-131349993/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((977748187/10000000000 : ℝ)*X 0 0+(582417433/1000000000 : ℝ)*X 0 1+(2755184029/5000000000 : ℝ)*X 0 2+(977748187/10000000000 : ℝ)*X 1 0+(582417433/1000000000 : ℝ)*X 1 1+(2755184029/5000000000 : ℝ)*X 1 2+(977748187/10000000000 : ℝ)*X 2 0+(582417433/1000000000 : ℝ)*X 2 1+(2755184029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11117140030645864500767500623/714125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126900541/25000000000000 : ℝ)*(lower2) + (16361761/50000000000000 : ℝ)*(lower5) + (1989319602799071/50000000000000 : ℝ)*(major0) + (1989319602799071/50000000000000 : ℝ)*(major1) + (1989319602799071/50000000000000 : ℝ)*(major2) + (2710745658449443/50000000000000 : ℝ)*(sp0) + (677685090996909/12500000000000 : ℝ)*(sp1) + (1084298871267247/20000000000000 : ℝ)*(sp2) + (1267891399660601/50000000000000 : ℝ)*(sp3) + (38792679/6250000000000 : ℝ)*(sp4) + (6237143079/50000000000000 : ℝ)*(sp5) + (92077777/12500000000000 : ℝ)*(sp6) + (3155376701/100000000000000 : ℝ)*(sp8) + (945348511/50000000000000 : ℝ)*(sp9) + (1267891399660601/50000000000000 : ℝ)*(f.failure) + (5421495092958451/100000000000000 : ℝ)*(f.sum) + (57750583471063/28565000000000000000000000000 : ℝ)*base65 + (7667973970293616459/1428250000000000000000000000000000 : ℝ)*base68 + (10238089429888116459/1428250000000000000000000000000000 : ℝ)*base70 + (15620037964659616459/1428250000000000000000000000000000 : ℝ)*base72 + (7477586640341/14282500000000000000000000000 : ℝ)*base74 + (14278408881995616459/1428250000000000000000000000000000 : ℝ)*base76 + (1943232018824883541/1428250000000000000000000000000000 : ℝ)*base77 + (4508622758863383541/1428250000000000000000000000000000 : ℝ)*base79 + (171072517801517/28565000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25262521/2500000000000000000000 : ℝ)*base89 + (25262521/2500000000000000000000 : ℝ)*base91 + (25262521/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4739691517773198186428199/2856500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14716989/20000000000000 : ℝ)*(lower4) + (8022442227041/200000000000 : ℝ)*(major0) + (8022442227041/200000000000 : ℝ)*(major1) + (8022442227041/200000000000 : ℝ)*(major2) + (9697040959/100000000000000 : ℝ)*(sp1) + (1025441361/50000000000000 : ℝ)*(sp3) + (5465891372829207/100000000000000 : ℝ)*(sp4) + (5465883485107901/100000000000000 : ℝ)*(sp5) + (546589177206203/10000000000000 : ℝ)*(sp6) + (2556545631436343/100000000000000 : ℝ)*(sp7) + (388860549/20000000000000 : ℝ)*(sp8) + (33745773/25000000000000 : ℝ)*(sp9) + (1545069921/100000000000000 : ℝ)*(sp10) + (7326757/625000000000 : ℝ)*(sp11) + (319568606825023/12500000000000 : ℝ)*(f.failure) + (341618332320747/6250000000000 : ℝ)*(f.sum) + (1052331144707/357062500000000000000000000 : ℝ)*base65 + (15760276208153589/5713000000000000000000000000000 : ℝ)*base68 + (22187328761600589/5713000000000000000000000000000 : ℝ)*base70 + (301351554012192589/5713000000000000000000000000000 : ℝ)*base72 + (21805412963637/5713000000000000000000000000 : ℝ)*base74 + (23054355059637589/5713000000000000000000000000000 : ℝ)*base76 + (63772634213572589/5713000000000000000000000000000 : ℝ)*base78 + (23909311542565589/5713000000000000000000000000000 : ℝ)*base80 + (3074852631043/5713000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (9826817/625000000000000000000 : ℝ)*base90 + (9826817/625000000000000000000 : ℝ)*base92 + (9826817/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1397_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15903/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1019/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2993/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1397_s4_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-399439351/2000000000 : ℝ)*x 0 + (1352899823/2500000000 : ℝ)*x 1 + (2622272237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399439351/2000000000 : ℝ)^4357 ≤ (1217555156137/10000000000000 : ℝ)^3333 := by
    have hnat : (399439351 : ℕ)^4357*10000000000000^3333 ≤ 1217555156137^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399439351 2000000000 1217555156137 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352899823/2500000000 : ℝ)^4357 ≤ (11203019214453/25000000000000 : ℝ)^3333 := by
    have hnat : (1352899823 : ℕ)^4357*25000000000000^3333 ≤ 11203019214453^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352899823 2500000000 11203019214453 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622272237/5000000000 : ℝ)^4357 ≤ (8602474314587/20000000000000 : ℝ)^3333 := by
    have hnat : (2622272237 : ℕ)^4357*20000000000000^3333 ≤ 8602474314587^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622272237 5000000000 8602474314587 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399439351/2000000000 : ℝ), (1352899823/2500000000 : ℝ), (2622272237/5000000000 : ℝ)] ![(1217555156137/10000000000000 : ℝ), (11203019214453/25000000000000 : ℝ), (8602474314587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399439351/2000000000 : ℝ)|^4357 ≤ (1217555156137/10000000000000 : ℝ)^3333
        have hw : |(-399439351/2000000000 : ℝ)|=(399439351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352899823/2500000000 : ℝ)|^4357 ≤ (11203019214453/25000000000000 : ℝ)^3333
        have hw : |(1352899823/2500000000 : ℝ)|=(1352899823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622272237/5000000000 : ℝ)|^4357 ≤ (8602474314587/20000000000000 : ℝ)^3333
        have hw : |(2622272237/5000000000 : ℝ)|=(2622272237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348425223/10000000000 : ℝ)*x 0 + (-2082301273/10000000000 : ℝ)*x 1 + (5244544473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348425223/10000000000 : ℝ)^4357 ≤ (8825891401411/20000000000000 : ℝ)^3333 := by
    have hnat : (5348425223 : ℕ)^4357*20000000000000^3333 ≤ 8825891401411^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348425223 10000000000 8825891401411 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082301273/10000000000 : ℝ)^4357 ≤ (12858171418163/100000000000000 : ℝ)^3333 := by
    have hnat : (2082301273 : ℕ)^4357*100000000000000^3333 ≤ 12858171418163^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082301273 10000000000 12858171418163 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244544473/10000000000 : ℝ)^4357 ≤ (21506185781107/50000000000000 : ℝ)^3333 := by
    have hnat : (5244544473 : ℕ)^4357*50000000000000^3333 ≤ 21506185781107^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244544473 10000000000 21506185781107 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348425223/10000000000 : ℝ), (-2082301273/10000000000 : ℝ), (5244544473/10000000000 : ℝ)] ![(8825891401411/20000000000000 : ℝ), (12858171418163/100000000000000 : ℝ), (21506185781107/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348425223/10000000000 : ℝ)|^4357 ≤ (8825891401411/20000000000000 : ℝ)^3333
        have hw : |(5348425223/10000000000 : ℝ)|=(5348425223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082301273/10000000000 : ℝ)|^4357 ≤ (12858171418163/100000000000000 : ℝ)^3333
        have hw : |(-2082301273/10000000000 : ℝ)|=(2082301273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244544473/10000000000 : ℝ)|^4357 ≤ (21506185781107/50000000000000 : ℝ)^3333
        have hw : |(5244544473/10000000000 : ℝ)|=(5244544473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66855317/125000000 : ℝ)*x 0 + (5244544831/10000000000 : ℝ)*x 1 + (-416460123/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66855317/125000000 : ℝ)^4357 ≤ (44129458484719/100000000000000 : ℝ)^3333 := by
    have hnat : (66855317 : ℕ)^4357*100000000000000^3333 ≤ 44129458484719^3333*125000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66855317 125000000 44129458484719 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244544831/10000000000 : ℝ)^4357 ≤ (8602475080071/20000000000000 : ℝ)^3333 := by
    have hnat : (5244544831 : ℕ)^4357*20000000000000^3333 ≤ 8602475080071^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244544831 10000000000 8602475080071 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416460123/2000000000 : ℝ)^4357 ≤ (803635381669/6250000000000 : ℝ)^3333 := by
    have hnat : (416460123 : ℕ)^4357*6250000000000^3333 ≤ 803635381669^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416460123 2000000000 803635381669 6250000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66855317/125000000 : ℝ), (5244544831/10000000000 : ℝ), (-416460123/2000000000 : ℝ)] ![(44129458484719/100000000000000 : ℝ), (8602475080071/20000000000000 : ℝ), (803635381669/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66855317/125000000 : ℝ)|^4357 ≤ (44129458484719/100000000000000 : ℝ)^3333
        have hw : |(66855317/125000000 : ℝ)|=(66855317/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244544831/10000000000 : ℝ)|^4357 ≤ (8602475080071/20000000000000 : ℝ)^3333
        have hw : |(5244544831/10000000000 : ℝ)|=(5244544831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416460123/2000000000 : ℝ)|^4357 ≤ (803635381669/6250000000000 : ℝ)^3333
        have hw : |(-416460123/2000000000 : ℝ)|=(416460123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2156161259/5000000000 : ℝ)*x 0 + (4137112971/10000000000 : ℝ)*x 1 + (4494275257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2156161259/5000000000 : ℝ)^4357 ≤ (33302995797961/100000000000000 : ℝ)^3333 := by
    have hnat : (2156161259 : ℕ)^4357*100000000000000^3333 ≤ 33302995797961^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2156161259 5000000000 33302995797961 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137112971/10000000000 : ℝ)^4357 ≤ (31545327400051/100000000000000 : ℝ)^3333 := by
    have hnat : (4137112971 : ℕ)^4357*100000000000000^3333 ≤ 31545327400051^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137112971 10000000000 31545327400051 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494275257/10000000000 : ℝ)^4357 ≤ (8787919196561/25000000000000 : ℝ)^3333 := by
    have hnat : (4494275257 : ℕ)^4357*25000000000000^3333 ≤ 8787919196561^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494275257 10000000000 8787919196561 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2156161259/5000000000 : ℝ), (4137112971/10000000000 : ℝ), (4494275257/10000000000 : ℝ)] ![(33302995797961/100000000000000 : ℝ), (31545327400051/100000000000000 : ℝ), (8787919196561/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2156161259/5000000000 : ℝ)|^4357 ≤ (33302995797961/100000000000000 : ℝ)^3333
        have hw : |(2156161259/5000000000 : ℝ)|=(2156161259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137112971/10000000000 : ℝ)|^4357 ≤ (31545327400051/100000000000000 : ℝ)^3333
        have hw : |(4137112971/10000000000 : ℝ)|=(4137112971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494275257/10000000000 : ℝ)|^4357 ≤ (8787919196561/25000000000000 : ℝ)^3333
        have hw : |(4494275257/10000000000 : ℝ)|=(4494275257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-199720909/1000000000 : ℝ)*x 0 + (2622578777/5000000000 : ℝ)*x 1 + (2705491493/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (199720909/1000000000 : ℝ)^4357 ≤ (3043912465687/25000000000000 : ℝ)^3333 := by
    have hnat : (199720909 : ℕ)^4357*25000000000000^3333 ≤ 3043912465687^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199720909 1000000000 3043912465687 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622578777/5000000000 : ℝ)^4357 ≤ (5377368070061/12500000000000 : ℝ)^3333 := by
    have hnat : (2622578777 : ℕ)^4357*12500000000000^3333 ≤ 5377368070061^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622578777 5000000000 5377368070061 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705491493/5000000000 : ℝ)^4357 ≤ (11201351389399/25000000000000 : ℝ)^3333 := by
    have hnat : (2705491493 : ℕ)^4357*25000000000000^3333 ≤ 11201351389399^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705491493 5000000000 11201351389399 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-199720909/1000000000 : ℝ), (2622578777/5000000000 : ℝ), (2705491493/5000000000 : ℝ)] ![(3043912465687/25000000000000 : ℝ), (5377368070061/12500000000000 : ℝ), (11201351389399/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-199720909/1000000000 : ℝ)|^4357 ≤ (3043912465687/25000000000000 : ℝ)^3333
        have hw : |(-199720909/1000000000 : ℝ)|=(199720909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622578777/5000000000 : ℝ)|^4357 ≤ (5377368070061/12500000000000 : ℝ)^3333
        have hw : |(2622578777/5000000000 : ℝ)|=(2622578777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705491493/5000000000 : ℝ)|^4357 ≤ (11201351389399/25000000000000 : ℝ)^3333
        have hw : |(2705491493/5000000000 : ℝ)|=(2705491493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305135433/10000000000 : ℝ)*x 0 + (-957931413/5000000000 : ℝ)*x 1 + (676372903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305135433/10000000000 : ℝ)^4357 ≤ (43663120892683/100000000000000 : ℝ)^3333 := by
    have hnat : (5305135433 : ℕ)^4357*100000000000000^3333 ≤ 43663120892683^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305135433 10000000000 43663120892683 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957931413/5000000000 : ℝ)^4357 ≤ (11531470964023/100000000000000 : ℝ)^3333 := by
    have hnat : (957931413 : ℕ)^4357*100000000000000^3333 ≤ 11531470964023^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957931413 5000000000 11531470964023 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676372903/1250000000 : ℝ)^4357 ≤ (44805408133819/100000000000000 : ℝ)^3333 := by
    have hnat : (676372903 : ℕ)^4357*100000000000000^3333 ≤ 44805408133819^3333*1250000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676372903 1250000000 44805408133819 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305135433/10000000000 : ℝ), (-957931413/5000000000 : ℝ), (676372903/1250000000 : ℝ)] ![(43663120892683/100000000000000 : ℝ), (11531470964023/100000000000000 : ℝ), (44805408133819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305135433/10000000000 : ℝ)|^4357 ≤ (43663120892683/100000000000000 : ℝ)^3333
        have hw : |(5305135433/10000000000 : ℝ)|=(5305135433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-957931413/5000000000 : ℝ)|^4357 ≤ (11531470964023/100000000000000 : ℝ)^3333
        have hw : |(-957931413/5000000000 : ℝ)|=(957931413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676372903/1250000000 : ℝ)|^4357 ≤ (44805408133819/100000000000000 : ℝ)^3333
        have hw : |(676372903/1250000000 : ℝ)|=(676372903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652567677/5000000000 : ℝ)*x 0 + (5410983123/10000000000 : ℝ)*x 1 + (-59870721/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652567677/5000000000 : ℝ)^4357 ≤ (1746524801709/4000000000000 : ℝ)^3333 := by
    have hnat : (2652567677 : ℕ)^4357*4000000000000^3333 ≤ 1746524801709^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652567677 5000000000 1746524801709 4000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410983123/10000000000 : ℝ)^4357 ≤ (11201351760137/25000000000000 : ℝ)^3333 := by
    have hnat : (5410983123 : ℕ)^4357*25000000000000^3333 ≤ 11201351760137^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410983123 10000000000 11201351760137 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (59870721/312500000 : ℝ)^4357 ≤ (2882868224897/25000000000000 : ℝ)^3333 := by
    have hnat : (59870721 : ℕ)^4357*25000000000000^3333 ≤ 2882868224897^3333*312500000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59870721 312500000 2882868224897 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652567677/5000000000 : ℝ), (5410983123/10000000000 : ℝ), (-59870721/312500000 : ℝ)] ![(1746524801709/4000000000000 : ℝ), (11201351760137/25000000000000 : ℝ), (2882868224897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652567677/5000000000 : ℝ)|^4357 ≤ (1746524801709/4000000000000 : ℝ)^3333
        have hw : |(2652567677/5000000000 : ℝ)|=(2652567677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410983123/10000000000 : ℝ)|^4357 ≤ (11201351760137/25000000000000 : ℝ)^3333
        have hw : |(5410983123/10000000000 : ℝ)|=(5410983123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-59870721/312500000 : ℝ)|^4357 ≤ (2882868224897/25000000000000 : ℝ)^3333
        have hw : |(-59870721/312500000 : ℝ)|=(59870721/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107808707/250000000 : ℝ)*x 0 + (449296481/1000000000 : ℝ)*x 1 + (4138430967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107808707/250000000 : ℝ)^4357 ≤ (33303255876363/100000000000000 : ℝ)^3333 := by
    have hnat : (107808707 : ℕ)^4357*100000000000000^3333 ≤ 33303255876363^3333*250000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107808707 250000000 33303255876363 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449296481/1000000000 : ℝ)^4357 ≤ (35138278827647/100000000000000 : ℝ)^3333 := by
    have hnat : (449296481 : ℕ)^4357*100000000000000^3333 ≤ 35138278827647^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449296481 1000000000 35138278827647 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4138430967/10000000000 : ℝ)^4357 ≤ (3944808159849/12500000000000 : ℝ)^3333 := by
    have hnat : (4138430967 : ℕ)^4357*12500000000000^3333 ≤ 3944808159849^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138430967 10000000000 3944808159849 12500000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107808707/250000000 : ℝ), (449296481/1000000000 : ℝ), (4138430967/10000000000 : ℝ)] ![(33303255876363/100000000000000 : ℝ), (35138278827647/100000000000000 : ℝ), (3944808159849/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107808707/250000000 : ℝ)|^4357 ≤ (33303255876363/100000000000000 : ℝ)^3333
        have hw : |(107808707/250000000 : ℝ)|=(107808707/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449296481/1000000000 : ℝ)|^4357 ≤ (35138278827647/100000000000000 : ℝ)^3333
        have hw : |(449296481/1000000000 : ℝ)|=(449296481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4138430967/10000000000 : ℝ)|^4357 ≤ (3944808159849/12500000000000 : ℝ)^3333
        have hw : |(4138430967/10000000000 : ℝ)|=(4138430967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_8 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-59394483/10000000000 : ℝ)*x 0 + (5879083277/10000000000 : ℝ)*x 1 + (5879108529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59394483/10000000000 : ℝ)^4357 ≤ (61481225719/50000000000000 : ℝ)^3333 := by
    have hnat : (59394483 : ℕ)^4357*50000000000000^3333 ≤ 61481225719^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59394483 10000000000 61481225719 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5879083277/10000000000 : ℝ)^4357 ≤ (49938378568009/100000000000000 : ℝ)^3333 := by
    have hnat : (5879083277 : ℕ)^4357*100000000000000^3333 ≤ 49938378568009^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5879083277 10000000000 49938378568009 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5879108529/10000000000 : ℝ)^4357 ≤ (9987731792973/20000000000000 : ℝ)^3333 := by
    have hnat : (5879108529 : ℕ)^4357*20000000000000^3333 ≤ 9987731792973^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5879108529 10000000000 9987731792973 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59394483/10000000000 : ℝ), (5879083277/10000000000 : ℝ), (5879108529/10000000000 : ℝ)] ![(61481225719/50000000000000 : ℝ), (49938378568009/100000000000000 : ℝ), (9987731792973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59394483/10000000000 : ℝ)|^4357 ≤ (61481225719/50000000000000 : ℝ)^3333
        have hw : |(-59394483/10000000000 : ℝ)|=(59394483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5879083277/10000000000 : ℝ)|^4357 ≤ (49938378568009/100000000000000 : ℝ)^3333
        have hw : |(5879083277/10000000000 : ℝ)|=(5879083277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5879108529/10000000000 : ℝ)|^4357 ≤ (9987731792973/20000000000000 : ℝ)^3333
        have hw : |(5879108529/10000000000 : ℝ)|=(5879108529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s4_9 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1124018829/10000000000 : ℝ)*x 0 + (17574117/31250000 : ℝ)*x 1 + (2812456957/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1124018829/10000000000 : ℝ)^4357 ≤ (1435760753193/25000000000000 : ℝ)^3333 := by
    have hnat : (1124018829 : ℕ)^4357*25000000000000^3333 ≤ 1435760753193^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124018829 10000000000 1435760753193 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17574117/31250000 : ℝ)^4357 ≤ (23560962750491/50000000000000 : ℝ)^3333 := by
    have hnat : (17574117 : ℕ)^4357*50000000000000^3333 ≤ 23560962750491^3333*31250000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17574117 31250000 23560962750491 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812456957/5000000000 : ℝ)^4357 ≤ (47135031473151/100000000000000 : ℝ)^3333 := by
    have hnat : (2812456957 : ℕ)^4357*100000000000000^3333 ≤ 47135031473151^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812456957 5000000000 47135031473151 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1124018829/10000000000 : ℝ), (17574117/31250000 : ℝ), (2812456957/5000000000 : ℝ)] ![(1435760753193/25000000000000 : ℝ), (23560962750491/50000000000000 : ℝ), (47135031473151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1124018829/10000000000 : ℝ)|^4357 ≤ (1435760753193/25000000000000 : ℝ)^3333
        have hw : |(1124018829/10000000000 : ℝ)|=(1124018829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(17574117/31250000 : ℝ)|^4357 ≤ (23560962750491/50000000000000 : ℝ)^3333
        have hw : |(17574117/31250000 : ℝ)|=(17574117/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812456957/5000000000 : ℝ)|^4357 ≤ (47135031473151/100000000000000 : ℝ)^3333
        have hw : |(2812456957/5000000000 : ℝ)|=(2812456957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2993/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11239/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1847/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2993/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2993/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2993/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2993/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2993/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2993/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (553/5000 : ℝ) ^ (1089/256 : ℝ) ≤ (8555077695720397/100000000000000000000 : ℝ) := by
    have hpowers : (553/5000 : ℝ)^1089 ≤ (8555077695720397/100000000000000000000 : ℝ)^256 := by
      have hnat : (553 : ℕ)^1089*100000000000000000000^256 ≤ 8555077695720397^256*5000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        553 5000 8555077695720397 100000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (553/5000 : ℝ)) (X := (8555077695720397/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2993/20000 : ℝ) ^ (1089/256 : ℝ) ≤ (15481880565324779/50000000000000000000 : ℝ) := by
    have hpowers : (2993/20000 : ℝ)^1089 ≤ (15481880565324779/50000000000000000000 : ℝ)^256 := by
      have hnat : (2993 : ℕ)^1089*50000000000000000000^256 ≤ 15481880565324779^256*20000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2993 20000 15481880565324779 50000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2993/20000 : ℝ)) (X := (15481880565324779/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008555077695720397/50000000000000000000 : ℝ) ≤ (5000201097941701/5000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (50008555077695720397/50000000000000000000 : ℝ)^256 ≤ (5000201097941701/5000000000000000 : ℝ)^1089 := by
      have hnat : (50008555077695720397 : ℕ)^256*5000000000000000^1089 ≤ 5000201097941701^1089*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008555077695720397 50000000000000000000 5000201097941701 5000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000201097941701/5000000000000000 : ℝ)) (X := (50008555077695720397/50000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007903767765273991/20000000000000000000 : ℝ) ≤ (10000928860789397/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (20007903767765273991/20000000000000000000 : ℝ)^256 ≤ (10000928860789397/10000000000000000 : ℝ)^1089 := by
      have hnat : (20007903767765273991 : ℕ)^256*10000000000000000^1089 ≤ 10000928860789397^1089*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007903767765273991 20000000000000000000 10000928860789397 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000928860789397/10000000000000000 : ℝ)) (X := (20007903767765273991/20000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015481880565324779/25000000000000000000 : ℝ) ≤ (312545485177981/312500000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (25015481880565324779/25000000000000000000 : ℝ)^256 ≤ (312545485177981/312500000000000 : ℝ)^1089 := by
      have hnat : (25015481880565324779 : ℕ)^256*312500000000000^1089 ≤ 312545485177981^1089*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015481880565324779 25000000000000000000 312545485177981 312500000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312545485177981/312500000000000 : ℝ)) (X := (25015481880565324779/25000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8555077695720397/100000000000000000000 : ℝ) ≤ ((3903992074720407541/3905000000000000000 : ℝ)+2*(105332981199/78100000000000 : ℝ)*(553/5000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (3903992074720407541/3905000000000000000 : ℝ)+2*(105332981199/78100000000000 : ℝ)*(553/5000 : ℝ)=(5000201097941701/5000000000000000 : ℝ) by norm_num, show 1+2*(8555077695720397/100000000000000000000 : ℝ)=(50008555077695720397/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15481880565324779/50000000000000000000 : ℝ)+(8555077695720397/100000000000000000000 : ℝ) ≤ ((3903992074720407541/3905000000000000000 : ℝ)+(105332981199/78100000000000 : ℝ)*((2993/20000 : ℝ)+(553/5000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (3903992074720407541/3905000000000000000 : ℝ)+(105332981199/78100000000000 : ℝ)*((2993/20000 : ℝ)+(553/5000 : ℝ))=(10000928860789397/10000000000000000 : ℝ) by norm_num, show 1+(15481880565324779/50000000000000000000 : ℝ)+(8555077695720397/100000000000000000000 : ℝ)=(20007903767765273991/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15481880565324779/50000000000000000000 : ℝ) ≤ ((3903992074720407541/3905000000000000000 : ℝ)+2*(105332981199/78100000000000 : ℝ)*(2993/20000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (3903992074720407541/3905000000000000000 : ℝ)+2*(105332981199/78100000000000 : ℝ)*(2993/20000 : ℝ)=(312545485177981/312500000000000 : ℝ) by norm_num, show 1+2*(15481880565324779/50000000000000000000 : ℝ)=(25015481880565324779/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3903992074720407541/3905000000000000000 : ℝ)*(X 1 0+X 2 0)+(105332981199/78100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (2993/20000 : ℝ)) (c := (3903992074720407541/3905000000000000000 : ℝ)) (alpha := (105332981199/78100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3903992074720407541/3905000000000000000 : ℝ)*(X 0 1+X 2 1)+(105332981199/78100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (2993/20000 : ℝ)) (c := (3903992074720407541/3905000000000000000 : ℝ)) (alpha := (105332981199/78100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3903992074720407541/3905000000000000000 : ℝ)*(X 0 2+X 1 2)+(105332981199/78100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (2993/20000 : ℝ)) (c := (3903992074720407541/3905000000000000000 : ℝ)) (alpha := (105332981199/78100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399439351/2000000000 : ℝ)*X 0 0+(1352899823/2500000000 : ℝ)*X 0 1+(2622272237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348425223/10000000000 : ℝ)*X 1 0+(-2082301273/10000000000 : ℝ)*X 1 1+(5244544473/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((66855317/125000000 : ℝ)*X 2 0+(5244544831/10000000000 : ℝ)*X 2 1+(-416460123/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2156161259/5000000000 : ℝ)*X 0 0+(4137112971/10000000000 : ℝ)*X 0 1+(4494275257/10000000000 : ℝ)*X 0 2+(2156161259/5000000000 : ℝ)*X 1 0+(4137112971/10000000000 : ℝ)*X 1 1+(4494275257/10000000000 : ℝ)*X 1 2+(2156161259/5000000000 : ℝ)*X 2 0+(4137112971/10000000000 : ℝ)*X 2 1+(4494275257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-199720909/1000000000 : ℝ)*X 0 0+(2622578777/5000000000 : ℝ)*X 0 1+(2705491493/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305135433/10000000000 : ℝ)*X 1 0+(-957931413/5000000000 : ℝ)*X 1 1+(676372903/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652567677/5000000000 : ℝ)*X 2 0+(5410983123/10000000000 : ℝ)*X 2 1+(-59870721/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((107808707/250000000 : ℝ)*X 0 0+(449296481/1000000000 : ℝ)*X 0 1+(4138430967/10000000000 : ℝ)*X 0 2+(107808707/250000000 : ℝ)*X 1 0+(449296481/1000000000 : ℝ)*X 1 1+(4138430967/10000000000 : ℝ)*X 1 2+(107808707/250000000 : ℝ)*X 2 0+(449296481/1000000000 : ℝ)*X 2 1+(4138430967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-59394483/10000000000 : ℝ)*X 0 0+(5879083277/10000000000 : ℝ)*X 0 1+(5879108529/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1124018829/10000000000 : ℝ)*X 0 0+(17574117/31250000 : ℝ)*X 0 1+(2812456957/5000000000 : ℝ)*X 0 2+(1124018829/10000000000 : ℝ)*X 1 0+(17574117/31250000 : ℝ)*X 1 1+(2812456957/5000000000 : ℝ)*X 1 2+(1124018829/10000000000 : ℝ)*X 2 0+(17574117/31250000 : ℝ)*X 2 1+(2812456957/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s4_9 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53864310838971959919716193/24406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286421839/50000000000000 : ℝ)*(lower2) + (3387617/1000000000000 : ℝ)*(lower3) + (111702017/25000000000000 : ℝ)*(lower4) + (9957239/50000000000000 : ℝ)*(lower5) + (549120091915447/12500000000000 : ℝ)*(major0) + (549120091915447/12500000000000 : ℝ)*(major1) + (549120091915447/12500000000000 : ℝ)*(major2) + (5986054358795133/100000000000000 : ℝ)*(sp0) + (5986060902448803/100000000000000 : ℝ)*(sp1) + (1197214214522981/20000000000000 : ℝ)*(sp2) + (2799850324465959/100000000000000 : ℝ)*(sp3) + (2954148017/25000000000000 : ℝ)*(sp4) + (5085083051/50000000000000 : ℝ)*(sp5) + (979445541/20000000000000 : ℝ)*(sp8) + (2799850324465959/100000000000000 : ℝ)*(f.failure) + (1197214214522981/20000000000000 : ℝ)*(f.sum) + (1278817854717/488125000000000000000000000 : ℝ)*base66 + (66093642759821743/4437500000000000000000000000000 : ℝ)*base68 + (35248143237071743/4437500000000000000000000000000 : ℝ)*base70 + (45784288076384243/4437500000000000000000000000000 : ℝ)*base72 + (5068376285583/1952500000000000000000000000 : ℝ)*base74 + (16212123041571743/4437500000000000000000000000000 : ℝ)*base76 + (9258961833571743/4437500000000000000000000000000 : ℝ)*base78 + (56429607609946743/4437500000000000000000000000000 : ℝ)*base80 + (133329145627/488125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (50739239/5000000000000000000000 : ℝ)*base89 + (50739239/5000000000000000000000 : ℝ)*base91 + (50739239/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6152559112905061689536397/781000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (123171139/50000000000000 : ℝ)*(lower2) + (312323147/100000000000000 : ℝ)*(lower4) + (84917527/100000000000000 : ℝ)*(lower5) + (17702101826913/400000000000 : ℝ)*(major0) + (17702101826913/400000000000 : ℝ)*(major1) + (17702101826913/400000000000 : ℝ)*(major2) + (4775630721/100000000000000 : ℝ)*(sp0) + (4236646011/100000000000000 : ℝ)*(sp1) + (6030437191729919/100000000000000 : ℝ)*(sp4) + (120608819765737/2000000000000 : ℝ)*(sp5) + (6030445224932861/100000000000000 : ℝ)*(sp6) + (176287837290747/6250000000000 : ℝ)*(sp7) + (3257572221/100000000000000 : ℝ)*(sp8) + (114369/390625000000 : ℝ)*(sp9) + (176287839120651/6250000000000 : ℝ)*(f.failure) + (6030445224932861/100000000000000 : ℝ)*(f.sum) + (1196052502851/390500000000000000000000000 : ℝ)*base65 + (1433849734528097/142000000000000000000000000000 : ℝ)*base68 + (148506250252097/142000000000000000000000000000 : ℝ)*base70 + (286511824616097/142000000000000000000000000000 : ℝ)*base72 + (4189654005113/781000000000000000000000000 : ℝ)*base73 + (46469992704097/142000000000000000000000000000 : ℝ)*base76 + (444100057938097/142000000000000000000000000000 : ℝ)*base78 + (296507696504097/142000000000000000000000000000 : ℝ)*base80 + (1207991540511/390500000000000000000000000 : ℝ)*base81 + (831429/312500000000000000000 : ℝ)*base90 + (831429/312500000000000000000 : ℝ)*base92 + (831429/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1397_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2993/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1397_s5_0 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-499340977/2500000000 : ℝ)*x 0 + (1082021757/2000000000 : ℝ)*x 1 + (2622962519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499340977/2500000000 : ℝ)^4357 ≤ (6088441835239/50000000000000 : ℝ)^3333 := by
    have hnat : (499340977 : ℕ)^4357*50000000000000^3333 ≤ 6088441835239^3333*2500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499340977 2500000000 6088441835239 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082021757/2000000000 : ℝ)^4357 ≤ (22397971516617/50000000000000 : ℝ)^3333 := by
    have hnat : (1082021757 : ℕ)^4357*50000000000000^3333 ≤ 22397971516617^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082021757 2000000000 22397971516617 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622962519/5000000000 : ℝ)^4357 ≤ (10756793321383/25000000000000 : ℝ)^3333 := by
    have hnat : (2622962519 : ℕ)^4357*25000000000000^3333 ≤ 10756793321383^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622962519 5000000000 10756793321383 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499340977/2500000000 : ℝ), (1082021757/2000000000 : ℝ), (2622962519/5000000000 : ℝ)] ![(6088441835239/50000000000000 : ℝ), (22397971516617/50000000000000 : ℝ), (10756793321383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499340977/2500000000 : ℝ)|^4357 ≤ (6088441835239/50000000000000 : ℝ)^3333
        have hw : |(-499340977/2500000000 : ℝ)|=(499340977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082021757/2000000000 : ℝ)|^4357 ≤ (22397971516617/50000000000000 : ℝ)^3333
        have hw : |(1082021757/2000000000 : ℝ)|=(1082021757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622962519/5000000000 : ℝ)|^4357 ≤ (10756793321383/25000000000000 : ℝ)^3333
        have hw : |(2622962519/5000000000 : ℝ)|=(2622962519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s5_1 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348041101/10000000000 : ℝ)*x 0 + (-2080977679/10000000000 : ℝ)*x 1 + (2622963661/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348041101/10000000000 : ℝ)^4357 ≤ (22062656982739/50000000000000 : ℝ)^3333 := by
    have hnat : (5348041101 : ℕ)^4357*50000000000000^3333 ≤ 22062656982739^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348041101 10000000000 22062656982739 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080977679/10000000000 : ℝ)^4357 ≤ (2569497648999/20000000000000 : ℝ)^3333 := by
    have hnat : (2080977679 : ℕ)^4357*20000000000000^3333 ≤ 2569497648999^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080977679 10000000000 2569497648999 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622963661/5000000000 : ℝ)^4357 ≤ (43027197774423/100000000000000 : ℝ)^3333 := by
    have hnat : (2622963661 : ℕ)^4357*100000000000000^3333 ≤ 43027197774423^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622963661 5000000000 43027197774423 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348041101/10000000000 : ℝ), (-2080977679/10000000000 : ℝ), (2622963661/5000000000 : ℝ)] ![(22062656982739/50000000000000 : ℝ), (2569497648999/20000000000000 : ℝ), (43027197774423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348041101/10000000000 : ℝ)|^4357 ≤ (22062656982739/50000000000000 : ℝ)^3333
        have hw : |(5348041101/10000000000 : ℝ)|=(5348041101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2080977679/10000000000 : ℝ)|^4357 ≤ (2569497648999/20000000000000 : ℝ)^3333
        have hw : |(-2080977679/10000000000 : ℝ)|=(2080977679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622963661/5000000000 : ℝ)|^4357 ≤ (43027197774423/100000000000000 : ℝ)^3333
        have hw : |(2622963661/5000000000 : ℝ)|=(2622963661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s5_2 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069608377/2000000000 : ℝ)*x 0 + (5245925713/10000000000 : ℝ)*x 1 + (-130061173/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069608377/2000000000 : ℝ)^4357 ≤ (44125322421409/100000000000000 : ℝ)^3333 := by
    have hnat : (1069608377 : ℕ)^4357*100000000000000^3333 ≤ 44125322421409^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069608377 2000000000 44125322421409 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245925713/10000000000 : ℝ)^4357 ≤ (8605436104567/20000000000000 : ℝ)^3333 := by
    have hnat : (5245925713 : ℕ)^4357*20000000000000^3333 ≤ 8605436104567^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245925713 10000000000 8605436104567 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130061173/625000000 : ℝ)^4357 ≤ (12847497033823/100000000000000 : ℝ)^3333 := by
    have hnat : (130061173 : ℕ)^4357*100000000000000^3333 ≤ 12847497033823^3333*625000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130061173 625000000 12847497033823 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069608377/2000000000 : ℝ), (5245925713/10000000000 : ℝ), (-130061173/625000000 : ℝ)] ![(44125322421409/100000000000000 : ℝ), (8605436104567/20000000000000 : ℝ), (12847497033823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069608377/2000000000 : ℝ)|^4357 ≤ (44125322421409/100000000000000 : ℝ)^3333
        have hw : |(1069608377/2000000000 : ℝ)|=(1069608377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245925713/10000000000 : ℝ)|^4357 ≤ (8605436104567/20000000000000 : ℝ)^3333
        have hw : |(5245925713/10000000000 : ℝ)|=(5245925713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130061173/625000000 : ℝ)|^4357 ≤ (12847497033823/100000000000000 : ℝ)^3333
        have hw : |(-130061173/625000000 : ℝ)|=(130061173/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s5_3 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312424941/10000000000 : ℝ)*x 0 + (2070086219/5000000000 : ℝ)*x 1 + (70174857/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312424941/10000000000 : ℝ)^4357 ≤ (33304029804753/100000000000000 : ℝ)^3333 := by
    have hnat : (4312424941 : ℕ)^4357*100000000000000^3333 ≤ 33304029804753^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312424941 10000000000 33304029804753 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070086219/5000000000 : ℝ)^4357 ≤ (3157582635817/10000000000000 : ℝ)^3333 := by
    have hnat : (2070086219 : ℕ)^4357*10000000000000^3333 ≤ 3157582635817^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070086219 5000000000 3157582635817 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70174857/156250000 : ℝ)^4357 ≤ (35120143822533/100000000000000 : ℝ)^3333 := by
    have hnat : (70174857 : ℕ)^4357*100000000000000^3333 ≤ 35120143822533^3333*156250000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70174857 156250000 35120143822533 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312424941/10000000000 : ℝ), (2070086219/5000000000 : ℝ), (70174857/156250000 : ℝ)] ![(33304029804753/100000000000000 : ℝ), (3157582635817/10000000000000 : ℝ), (35120143822533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312424941/10000000000 : ℝ)|^4357 ≤ (33304029804753/100000000000000 : ℝ)^3333
        have hw : |(4312424941/10000000000 : ℝ)|=(4312424941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070086219/5000000000 : ℝ)|^4357 ≤ (3157582635817/10000000000000 : ℝ)^3333
        have hw : |(2070086219/5000000000 : ℝ)|=(2070086219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70174857/156250000 : ℝ)|^4357 ≤ (35120143822533/100000000000000 : ℝ)^3333
        have hw : |(70174857/156250000 : ℝ)|=(70174857/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s5_4 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-998687881/5000000000 : ℝ)*x 0 + (2623259159/5000000000 : ℝ)*x 1 + (5409512347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (998687881/5000000000 : ℝ)^4357 ≤ (6088489070523/50000000000000 : ℝ)^3333 := by
    have hnat : (998687881 : ℕ)^4357*50000000000000^3333 ≤ 6088489070523^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998687881 5000000000 6088489070523 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623259159/5000000000 : ℝ)^4357 ≤ (344268276023/800000000000 : ℝ)^3333 := by
    have hnat : (2623259159 : ℕ)^4357*800000000000^3333 ≤ 344268276023^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623259159 5000000000 344268276023 800000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409512347/10000000000 : ℝ)^4357 ≤ (11197371835011/25000000000000 : ℝ)^3333 := by
    have hnat : (5409512347 : ℕ)^4357*25000000000000^3333 ≤ 11197371835011^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409512347 10000000000 11197371835011 25000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-998687881/5000000000 : ℝ), (2623259159/5000000000 : ℝ), (5409512347/10000000000 : ℝ)] ![(6088489070523/50000000000000 : ℝ), (344268276023/800000000000 : ℝ), (11197371835011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-998687881/5000000000 : ℝ)|^4357 ≤ (6088489070523/50000000000000 : ℝ)^3333
        have hw : |(-998687881/5000000000 : ℝ)|=(998687881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623259159/5000000000 : ℝ)|^4357 ≤ (344268276023/800000000000 : ℝ)^3333
        have hw : |(2623259159/5000000000 : ℝ)|=(2623259159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409512347/10000000000 : ℝ)|^4357 ≤ (11197371835011/25000000000000 : ℝ)^3333
        have hw : |(5409512347/10000000000 : ℝ)|=(5409512347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s5_5 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305496587/10000000000 : ℝ)*x 0 + (-383478449/2000000000 : ℝ)*x 1 + (5409512341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305496587/10000000000 : ℝ)^4357 ≤ (8733401315403/20000000000000 : ℝ)^3333 := by
    have hnat : (5305496587 : ℕ)^4357*20000000000000^3333 ≤ 8733401315403^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305496587 10000000000 8733401315403 20000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383478449/2000000000 : ℝ)^4357 ≤ (11543506135179/100000000000000 : ℝ)^3333 := by
    have hnat : (383478449 : ℕ)^4357*100000000000000^3333 ≤ 11543506135179^3333*2000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383478449 2000000000 11543506135179 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409512341/10000000000 : ℝ)^4357 ≤ (22394743637551/50000000000000 : ℝ)^3333 := by
    have hnat : (5409512341 : ℕ)^4357*50000000000000^3333 ≤ 22394743637551^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409512341 10000000000 22394743637551 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305496587/10000000000 : ℝ), (-383478449/2000000000 : ℝ), (5409512341/10000000000 : ℝ)] ![(8733401315403/20000000000000 : ℝ), (11543506135179/100000000000000 : ℝ), (22394743637551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305496587/10000000000 : ℝ)|^4357 ≤ (8733401315403/20000000000000 : ℝ)^3333
        have hw : |(5305496587/10000000000 : ℝ)|=(5305496587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383478449/2000000000 : ℝ)|^4357 ≤ (11543506135179/100000000000000 : ℝ)^3333
        have hw : |(-383478449/2000000000 : ℝ)|=(383478449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409512341/10000000000 : ℝ)|^4357 ≤ (22394743637551/50000000000000 : ℝ)^3333
        have hw : |(5409512341/10000000000 : ℝ)|=(5409512341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s5_6 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530549661/1000000000 : ℝ)*x 0 + (5409512307/10000000000 : ℝ)*x 1 + (-95869613/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530549661/1000000000 : ℝ)^4357 ≤ (43667006824477/100000000000000 : ℝ)^3333 := by
    have hnat : (530549661 : ℕ)^4357*100000000000000^3333 ≤ 43667006824477^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530549661 1000000000 43667006824477 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5409512307/10000000000 : ℝ)^4357 ≤ (44789486907101/100000000000000 : ℝ)^3333 := by
    have hnat : (5409512307 : ℕ)^4357*100000000000000^3333 ≤ 44789486907101^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409512307 10000000000 44789486907101 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95869613/500000000 : ℝ)^4357 ≤ (1154350625323/10000000000000 : ℝ)^3333 := by
    have hnat : (95869613 : ℕ)^4357*10000000000000^3333 ≤ 1154350625323^3333*500000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95869613 500000000 1154350625323 10000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530549661/1000000000 : ℝ), (5409512307/10000000000 : ℝ), (-95869613/500000000 : ℝ)] ![(43667006824477/100000000000000 : ℝ), (44789486907101/100000000000000 : ℝ), (1154350625323/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530549661/1000000000 : ℝ)|^4357 ≤ (43667006824477/100000000000000 : ℝ)^3333
        have hw : |(530549661/1000000000 : ℝ)|=(530549661/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5409512307/10000000000 : ℝ)|^4357 ≤ (44789486907101/100000000000000 : ℝ)^3333
        have hw : |(5409512307/10000000000 : ℝ)|=(5409512307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95869613/500000000 : ℝ)|^4357 ≤ (1154350625323/10000000000000 : ℝ)^3333
        have hw : |(-95869613/500000000 : ℝ)|=(95869613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1397_s5_7 (p : ℝ) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (431244941/1000000000 : ℝ)*x 0 + (2244962769/5000000000 : ℝ)*x 1 + (4141444889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (431244941/1000000000 : ℝ)^4357 ≤ (33304276831559/100000000000000 : ℝ)^3333 := by
    have hnat : (431244941 : ℕ)^4357*100000000000000^3333 ≤ 33304276831559^3333*1000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431244941 1000000000 33304276831559 100000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244962769/5000000000 : ℝ)^4357 ≤ (17553605025801/50000000000000 : ℝ)^3333 := by
    have hnat : (2244962769 : ℕ)^4357*50000000000000^3333 ≤ 17553605025801^3333*5000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244962769 5000000000 17553605025801 50000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4141444889/10000000000 : ℝ)^4357 ≤ (1579425655013/5000000000000 : ℝ)^3333 := by
    have hnat : (4141444889 : ℕ)^4357*5000000000000^3333 ≤ 1579425655013^3333*10000000000^4357 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4141444889 10000000000 1579425655013 5000000000000 4357 3333 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4357/1024 : ℝ)) 4357 3333 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(431244941/1000000000 : ℝ), (2244962769/5000000000 : ℝ), (4141444889/10000000000 : ℝ)] ![(33304276831559/100000000000000 : ℝ), (17553605025801/50000000000000 : ℝ), (1579425655013/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(431244941/1000000000 : ℝ)|^4357 ≤ (33304276831559/100000000000000 : ℝ)^3333
        have hw : |(431244941/1000000000 : ℝ)|=(431244941/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244962769/5000000000 : ℝ)|^4357 ≤ (17553605025801/50000000000000 : ℝ)^3333
        have hw : |(2244962769/5000000000 : ℝ)|=(2244962769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4141444889/10000000000 : ℝ)|^4357 ≤ (1579425655013/5000000000000 : ℝ)^3333
        have hw : |(4141444889/10000000000 : ℝ)|=(4141444889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1397_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2817/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2949/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1847/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1847/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11239/100000 : ℝ) ^ (1089/256 : ℝ) ≤ (1831953742151537/20000000000000000000 : ℝ) := by
    have hpowers : (11239/100000 : ℝ)^1089 ≤ (1831953742151537/20000000000000000000 : ℝ)^256 := by
      have hnat : (11239 : ℕ)^1089*20000000000000000000^256 ≤ 1831953742151537^256*100000^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11239 100000 1831953742151537 20000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11239/100000 : ℝ)) (X := (1831953742151537/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hpowhi : (1847/12500 : ℝ) ^ (1089/256 : ℝ) ≤ (7333526076454817/25000000000000000000 : ℝ) := by
    have hpowers : (1847/12500 : ℝ)^1089 ≤ (7333526076454817/25000000000000000000 : ℝ)^256 := by
      have hnat : (1847 : ℕ)^1089*25000000000000000000^256 ≤ 7333526076454817^256*12500^1089 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1847 12500 7333526076454817 25000000000000000000 1089 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1847/12500 : ℝ)) (X := (7333526076454817/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001831953742151537/10000000000000000000 : ℝ) ≤ (10000430621948943/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (10001831953742151537/10000000000000000000 : ℝ)^256 ≤ (10000430621948943/10000000000000000 : ℝ)^1089 := by
      have hnat : (10001831953742151537 : ℕ)^256*10000000000000000^1089 ≤ 10000430621948943^1089*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001831953742151537 10000000000000000000 10000430621948943 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000430621948943/10000000000000000 : ℝ)) (X := (10001831953742151537/10000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038493873016576953/100000000000000000000 : ℝ) ≤ (2500226193319823/2500000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (100038493873016576953/100000000000000000000 : ℝ)^256 ≤ (2500226193319823/2500000000000000 : ℝ)^1089 := by
      have hnat : (100038493873016576953 : ℕ)^256*2500000000000000^1089 ≤ 2500226193319823^1089*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038493873016576953 100000000000000000000 2500226193319823 2500000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500226193319823/2500000000000000 : ℝ)) (X := (100038493873016576953/100000000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507333526076454817/12500000000000000000 : ℝ) ≤ (10001378924609641/10000000000000000 : ℝ) ^ (1089/256 : ℝ) := by
    have hpowers : (12507333526076454817/12500000000000000000 : ℝ)^256 ≤ (10001378924609641/10000000000000000 : ℝ)^1089 := by
      have hnat : (12507333526076454817 : ℕ)^256*10000000000000000^1089 ≤ 10001378924609641^1089*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507333526076454817 12500000000000000000 10001378924609641 10000000000000000 256 1089 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001378924609641/10000000000000000 : ℝ)) (X := (12507333526076454817/12500000000000000000 : ℝ)) (by norm_num) 1089 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1831953742151537/20000000000000000000 : ℝ) ≤ ((35360865136229826569/35370000000000000000 : ℝ)+2*(474151330349/353700000000000 : ℝ)*(11239/100000 : ℝ))^(1089/256 : ℝ) := by
    rw [show (35360865136229826569/35370000000000000000 : ℝ)+2*(474151330349/353700000000000 : ℝ)*(11239/100000 : ℝ)=(10000430621948943/10000000000000000 : ℝ) by norm_num, show 1+2*(1831953742151537/20000000000000000000 : ℝ)=(10001831953742151537/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7333526076454817/25000000000000000000 : ℝ)+(1831953742151537/20000000000000000000 : ℝ) ≤ ((35360865136229826569/35370000000000000000 : ℝ)+(474151330349/353700000000000 : ℝ)*((1847/12500 : ℝ)+(11239/100000 : ℝ)))^(1089/256 : ℝ) := by
    rw [show (35360865136229826569/35370000000000000000 : ℝ)+(474151330349/353700000000000 : ℝ)*((1847/12500 : ℝ)+(11239/100000 : ℝ))=(2500226193319823/2500000000000000 : ℝ) by norm_num, show 1+(7333526076454817/25000000000000000000 : ℝ)+(1831953742151537/20000000000000000000 : ℝ)=(100038493873016576953/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7333526076454817/25000000000000000000 : ℝ) ≤ ((35360865136229826569/35370000000000000000 : ℝ)+2*(474151330349/353700000000000 : ℝ)*(1847/12500 : ℝ))^(1089/256 : ℝ) := by
    rw [show (35360865136229826569/35370000000000000000 : ℝ)+2*(474151330349/353700000000000 : ℝ)*(1847/12500 : ℝ)=(10001378924609641/10000000000000000 : ℝ) by norm_num, show 1+2*(7333526076454817/25000000000000000000 : ℝ)=(12507333526076454817/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35360865136229826569/35370000000000000000 : ℝ)*(X 1 0+X 2 0)+(474151330349/353700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (35360865136229826569/35370000000000000000 : ℝ)) (alpha := (474151330349/353700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35360865136229826569/35370000000000000000 : ℝ)*(X 0 1+X 2 1)+(474151330349/353700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (35360865136229826569/35370000000000000000 : ℝ)) (alpha := (474151330349/353700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35360865136229826569/35370000000000000000 : ℝ)*(X 0 2+X 1 2)+(474151330349/353700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1089/256 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (1847/12500 : ℝ)) (c := (35360865136229826569/35370000000000000000 : ℝ)) (alpha := (474151330349/353700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-499340977/2500000000 : ℝ)*X 0 0+(1082021757/2000000000 : ℝ)*X 0 1+(2622962519/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348041101/10000000000 : ℝ)*X 1 0+(-2080977679/10000000000 : ℝ)*X 1 1+(2622963661/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069608377/2000000000 : ℝ)*X 2 0+(5245925713/10000000000 : ℝ)*X 2 1+(-130061173/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4312424941/10000000000 : ℝ)*X 0 0+(2070086219/5000000000 : ℝ)*X 0 1+(70174857/156250000 : ℝ)*X 0 2+(4312424941/10000000000 : ℝ)*X 1 0+(2070086219/5000000000 : ℝ)*X 1 1+(70174857/156250000 : ℝ)*X 1 2+(4312424941/10000000000 : ℝ)*X 2 0+(2070086219/5000000000 : ℝ)*X 2 1+(70174857/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-998687881/5000000000 : ℝ)*X 0 0+(2623259159/5000000000 : ℝ)*X 0 1+(5409512347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305496587/10000000000 : ℝ)*X 1 0+(-383478449/2000000000 : ℝ)*X 1 1+(5409512341/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530549661/1000000000 : ℝ)*X 2 0+(5409512307/10000000000 : ℝ)*X 2 1+(-95869613/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((431244941/1000000000 : ℝ)*X 0 0+(2244962769/5000000000 : ℝ)*X 0 1+(4141444889/10000000000 : ℝ)*X 0 2+(431244941/1000000000 : ℝ)*X 1 0+(2244962769/5000000000 : ℝ)*X 1 1+(4141444889/10000000000 : ℝ)*X 1 2+(431244941/1000000000 : ℝ)*X 2 0+(2244962769/5000000000 : ℝ)*X 2 1+(4141444889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1397_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (242632254738018332320688039/32750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (447919417/100000000000000 : ℝ)*(base19) + (1820429769/100000000000000 : ℝ)*(base23) + (80947371/20000000000000 : ℝ)*(upper3) + (307846617/100000000000000 : ℝ)*(lower4) + (2234945394308679/50000000000000 : ℝ)*(major0) + (2234945394308679/50000000000000 : ℝ)*(major1) + (2234945394308679/50000000000000 : ℝ)*(major2) + (3045413187826321/50000000000000 : ℝ)*(sp0) + (761362405558843/12500000000000 : ℝ)*(sp1) + (3045442901369651/50000000000000 : ℝ)*(sp2) + (712216067895521/25000000000000 : ℝ)*(sp3) + (73316737519/100000000000000 : ℝ)*(sp4) + (1206922109/10000000000000 : ℝ)*(sp6) + (17366308513/100000000000000 : ℝ)*(sp7) + (2848881637890597/100000000000000 : ℝ)*(f.failure) + (76136246154877/1250000000000 : ℝ)*(f.sum) + (1791560719943/2947500000000000000000000000 : ℝ)*base66 + (4713929974848135883/589500000000000000000000000000000 : ℝ)*base68 + (719334729941864117/589500000000000000000000000000000 : ℝ)*base69 + (9445430712288135883/589500000000000000000000000000000 : ℝ)*base72 + (2091666071659/1473750000000000000000000000 : ℝ)*base74 + (7729361631628635883/589500000000000000000000000000000 : ℝ)*base76 + (7832039967615135883/589500000000000000000000000000000 : ℝ)*base78 + (4463173795163864117/589500000000000000000000000000000 : ℝ)*base79 + (12252151396379/5895000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (41292837/5000000000000000000000 : ℝ)*base89 + (41292837/5000000000000000000000 : ℝ)*base91 + (41292837/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44279306879790040005601/5895000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1296459353/100000000000000 : ℝ)*(base19) + (722866633/50000000000000 : ℝ)*(base23) + (145980019/100000000000000 : ℝ)*(upper3) + (5941881/10000000000000 : ℝ)*(lower4) + (8286459/5000000000000 : ℝ)*(upper5) + (1125599138354149/25000000000000 : ℝ)*(major0) + (1125599138354149/25000000000000 : ℝ)*(major1) + (1125599138354149/25000000000000 : ℝ)*(major2) + (27232134927/100000000000000 : ℝ)*(sp1) + (5712750271/20000000000000 : ℝ)*(sp2) + (766899211631237/12500000000000 : ℝ)*(sp4) + (95861955694619/1562500000000 : ℝ)*(sp5) + (245406547342611/4000000000000 : ℝ)*(sp6) + (358699895425691/12500000000000 : ℝ)*(sp7) + (358699895425691/12500000000000 : ℝ)*(f.failure) + (766899211631237/12500000000000 : ℝ)*(f.sum) + (6089850263081/4421250000000000000000000000 : ℝ)*base65 + (2461073749995684781/884250000000000000000000000000000 : ℝ)*base67 + (3432313948640315219/884250000000000000000000000000000 : ℝ)*base70 + (5119317854330934781/884250000000000000000000000000000 : ℝ)*base71 + (21496836512969/17685000000000000000000000000 : ℝ)*base73 + (2317687323291815219/884250000000000000000000000000000 : ℝ)*base76 + (8199068018050434781/884250000000000000000000000000000 : ℝ)*base77 + (9061973189915315219/884250000000000000000000000000000 : ℝ)*base80 + (8907098628077/2210625000000000000000000000 : ℝ)*base82 + (4679589/625000000000000000000 : ℝ)*base90 + (4679589/625000000000000000000 : ℝ)*base92 + (4679589/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1397_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1847/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1397_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1397_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15903/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1019/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1397_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1397_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1397_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1089/256 : ℝ) ≤ p) (hpb : p ≤ (4357/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (78449921/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15903/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1019/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2817/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2949/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1397_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
