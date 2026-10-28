-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:23:11.092633+00:00
-- url     : https://prove2.me/submissions/13024e00-9dcf-4075-8b86-74ca5faca718

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
theorem support_rectangle_w1250_s6_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116270731/10000000000 : ℝ)*x 0 + (5391230371/10000000000 : ℝ)*x 1 + (5267147379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116270731/10000000000 : ℝ)^8443 ≤ (321754987279/2500000000000 : ℝ)^6395 := by
    have hnat : (2116270731 : ℕ)^8443*2500000000000^6395 ≤ 321754987279^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116270731 10000000000 321754987279 2500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391230371/10000000000 : ℝ)^8443 ≤ (11058618929497/25000000000000 : ℝ)^6395 := by
    have hnat : (5391230371 : ℕ)^8443*25000000000000^6395 ≤ 11058618929497^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391230371 10000000000 11058618929497 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267147379/10000000000 : ℝ)^8443 ≤ (42895324780347/100000000000000 : ℝ)^6395 := by
    have hnat : (5267147379 : ℕ)^8443*100000000000000^6395 ≤ 42895324780347^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267147379 10000000000 42895324780347 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116270731/10000000000 : ℝ), (5391230371/10000000000 : ℝ), (5267147379/10000000000 : ℝ)] ![(321754987279/2500000000000 : ℝ), (11058618929497/25000000000000 : ℝ), (42895324780347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116270731/10000000000 : ℝ)|^8443 ≤ (321754987279/2500000000000 : ℝ)^6395
        have hw : |(-2116270731/10000000000 : ℝ)|=(2116270731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391230371/10000000000 : ℝ)|^8443 ≤ (11058618929497/25000000000000 : ℝ)^6395
        have hw : |(5391230371/10000000000 : ℝ)|=(5391230371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267147379/10000000000 : ℝ)|^8443 ≤ (42895324780347/100000000000000 : ℝ)^6395
        have hw : |(5267147379/10000000000 : ℝ)|=(5267147379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s6_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344311961/10000000000 : ℝ)*x 0 + (-2179184487/10000000000 : ℝ)*x 1 + (526714749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344311961/10000000000 : ℝ)^8443 ≤ (10931735266523/25000000000000 : ℝ)^6395 := by
    have hnat : (5344311961 : ℕ)^8443*25000000000000^6395 ≤ 10931735266523^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344311961 10000000000 10931735266523 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179184487/10000000000 : ℝ)^8443 ≤ (13377732954489/100000000000000 : ℝ)^6395 := by
    have hnat : (2179184487 : ℕ)^8443*100000000000000^6395 ≤ 13377732954489^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179184487 10000000000 13377732954489 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526714749/1000000000 : ℝ)^8443 ≤ (42895325973823/100000000000000 : ℝ)^6395 := by
    have hnat : (526714749 : ℕ)^8443*100000000000000^6395 ≤ 42895325973823^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526714749 1000000000 42895325973823 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344311961/10000000000 : ℝ), (-2179184487/10000000000 : ℝ), (526714749/1000000000 : ℝ)] ![(10931735266523/25000000000000 : ℝ), (13377732954489/100000000000000 : ℝ), (42895325973823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344311961/10000000000 : ℝ)|^8443 ≤ (10931735266523/25000000000000 : ℝ)^6395
        have hw : |(5344311961/10000000000 : ℝ)|=(5344311961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2179184487/10000000000 : ℝ)|^8443 ≤ (13377732954489/100000000000000 : ℝ)^6395
        have hw : |(-2179184487/10000000000 : ℝ)|=(2179184487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526714749/1000000000 : ℝ)|^8443 ≤ (42895325973823/100000000000000 : ℝ)^6395
        have hw : |(526714749/1000000000 : ℝ)|=(526714749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s6_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344311803/10000000000 : ℝ)*x 0 + (5267147493/10000000000 : ℝ)*x 1 + (-2179184693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344311803/10000000000 : ℝ)^8443 ≤ (43726939359339/100000000000000 : ℝ)^6395 := by
    have hnat : (5344311803 : ℕ)^8443*100000000000000^6395 ≤ 43726939359339^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344311803 10000000000 43726939359339 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267147493/10000000000 : ℝ)^8443 ≤ (42895326006079/100000000000000 : ℝ)^6395 := by
    have hnat : (5267147493 : ℕ)^8443*100000000000000^6395 ≤ 42895326006079^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267147493 10000000000 42895326006079 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2179184693/10000000000 : ℝ)^8443 ≤ (13377734624087/100000000000000 : ℝ)^6395 := by
    have hnat : (2179184693 : ℕ)^8443*100000000000000^6395 ≤ 13377734624087^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179184693 10000000000 13377734624087 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344311803/10000000000 : ℝ), (5267147493/10000000000 : ℝ), (-2179184693/10000000000 : ℝ)] ![(43726939359339/100000000000000 : ℝ), (42895326006079/100000000000000 : ℝ), (13377734624087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344311803/10000000000 : ℝ)|^8443 ≤ (43726939359339/100000000000000 : ℝ)^6395
        have hw : |(5344311803/10000000000 : ℝ)|=(5344311803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267147493/10000000000 : ℝ)|^8443 ≤ (42895326006079/100000000000000 : ℝ)^6395
        have hw : |(5267147493/10000000000 : ℝ)|=(5267147493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2179184693/10000000000 : ℝ)|^8443 ≤ (13377734624087/100000000000000 : ℝ)^6395
        have hw : |(-2179184693/10000000000 : ℝ)|=(2179184693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s6_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087416963/2500000000 : ℝ)*x 0 + (2112695453/5000000000 : ℝ)*x 1 + (279843163/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087416963/2500000000 : ℝ)^8443 ≤ (2082339828091/6250000000000 : ℝ)^6395 := by
    have hnat : (1087416963 : ℕ)^8443*6250000000000^6395 ≤ 2082339828091^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087416963 2500000000 2082339828091 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112695453/5000000000 : ℝ)^8443 ≤ (32066435958931/100000000000000 : ℝ)^6395 := by
    have hnat : (2112695453 : ℕ)^8443*100000000000000^6395 ≤ 32066435958931^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112695453 5000000000 32066435958931 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279843163/625000000 : ℝ)^8443 ≤ (1384645071077/4000000000000 : ℝ)^6395 := by
    have hnat : (279843163 : ℕ)^8443*4000000000000^6395 ≤ 1384645071077^6395*625000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279843163 625000000 1384645071077 4000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087416963/2500000000 : ℝ), (2112695453/5000000000 : ℝ), (279843163/625000000 : ℝ)] ![(2082339828091/6250000000000 : ℝ), (32066435958931/100000000000000 : ℝ), (1384645071077/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087416963/2500000000 : ℝ)|^8443 ≤ (2082339828091/6250000000000 : ℝ)^6395
        have hw : |(1087416963/2500000000 : ℝ)|=(1087416963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112695453/5000000000 : ℝ)|^8443 ≤ (32066435958931/100000000000000 : ℝ)^6395
        have hw : |(2112695453/5000000000 : ℝ)|=(2112695453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(279843163/625000000 : ℝ)|^8443 ≤ (1384645071077/4000000000000 : ℝ)^6395
        have hw : |(279843163/625000000 : ℝ)|=(279843163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s6_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116275677/10000000000 : ℝ)*x 0 + (5267460939/10000000000 : ℝ)*x 1 + (1347728867/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116275677/10000000000 : ℝ)^8443 ≤ (1608779900427/12500000000000 : ℝ)^6395 := by
    have hnat : (2116275677 : ℕ)^8443*12500000000000^6395 ≤ 1608779900427^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116275677 10000000000 1608779900427 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267460939/10000000000 : ℝ)^8443 ≤ (42898696221053/100000000000000 : ℝ)^6395 := by
    have hnat : (5267460939 : ℕ)^8443*100000000000000^6395 ≤ 42898696221053^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267460939 10000000000 42898696221053 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347728867/2500000000 : ℝ)^8443 ≤ (44231064558927/100000000000000 : ℝ)^6395 := by
    have hnat : (1347728867 : ℕ)^8443*100000000000000^6395 ≤ 44231064558927^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347728867 2500000000 44231064558927 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116275677/10000000000 : ℝ), (5267460939/10000000000 : ℝ), (1347728867/2500000000 : ℝ)] ![(1608779900427/12500000000000 : ℝ), (42898696221053/100000000000000 : ℝ), (44231064558927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116275677/10000000000 : ℝ)|^8443 ≤ (1608779900427/12500000000000 : ℝ)^6395
        have hw : |(-2116275677/10000000000 : ℝ)|=(2116275677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267460939/10000000000 : ℝ)|^8443 ≤ (42898696221053/100000000000000 : ℝ)^6395
        have hw : |(5267460939/10000000000 : ℝ)|=(5267460939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347728867/2500000000 : ℝ)|^8443 ≤ (44231064558927/100000000000000 : ℝ)^6395
        have hw : |(1347728867/2500000000 : ℝ)|=(1347728867/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s6_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312635021/10000000000 : ℝ)*x 0 + (-2055416689/10000000000 : ℝ)*x 1 + (2695457447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312635021/10000000000 : ℝ)^8443 ≤ (21692542291851/50000000000000 : ℝ)^6395 := by
    have hnat : (5312635021 : ℕ)^8443*50000000000000^6395 ≤ 21692542291851^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312635021 10000000000 21692542291851 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2055416689/10000000000 : ℝ)^8443 ≤ (2476771410277/20000000000000 : ℝ)^6395 := by
    have hnat : (2055416689 : ℕ)^8443*20000000000000^6395 ≤ 2476771410277^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055416689 10000000000 2476771410277 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695457447/5000000000 : ℝ)^8443 ≤ (44231058341181/100000000000000 : ℝ)^6395 := by
    have hnat : (2695457447 : ℕ)^8443*100000000000000^6395 ≤ 44231058341181^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695457447 5000000000 44231058341181 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312635021/10000000000 : ℝ), (-2055416689/10000000000 : ℝ), (2695457447/5000000000 : ℝ)] ![(21692542291851/50000000000000 : ℝ), (2476771410277/20000000000000 : ℝ), (44231058341181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312635021/10000000000 : ℝ)|^8443 ≤ (21692542291851/50000000000000 : ℝ)^6395
        have hw : |(5312635021/10000000000 : ℝ)|=(5312635021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2055416689/10000000000 : ℝ)|^8443 ≤ (2476771410277/20000000000000 : ℝ)^6395
        have hw : |(-2055416689/10000000000 : ℝ)|=(2055416689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695457447/5000000000 : ℝ)|^8443 ≤ (44231058341181/100000000000000 : ℝ)^6395
        have hw : |(2695457447/5000000000 : ℝ)|=(2695457447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s6_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656317631/5000000000 : ℝ)*x 0 + (5390914571/10000000000 : ℝ)*x 1 + (-513854201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656317631/5000000000 : ℝ)^8443 ≤ (43385087182089/100000000000000 : ℝ)^6395 := by
    have hnat : (2656317631 : ℕ)^8443*100000000000000^6395 ≤ 43385087182089^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656317631 5000000000 43385087182089 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390914571/10000000000 : ℝ)^8443 ≤ (5528881855293/12500000000000 : ℝ)^6395 := by
    have hnat : (5390914571 : ℕ)^8443*12500000000000^6395 ≤ 5528881855293^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390914571 10000000000 5528881855293 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (513854201/2500000000 : ℝ)^8443 ≤ (1547982245769/12500000000000 : ℝ)^6395 := by
    have hnat : (513854201 : ℕ)^8443*12500000000000^6395 ≤ 1547982245769^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513854201 2500000000 1547982245769 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656317631/5000000000 : ℝ), (5390914571/10000000000 : ℝ), (-513854201/2500000000 : ℝ)] ![(43385087182089/100000000000000 : ℝ), (5528881855293/12500000000000 : ℝ), (1547982245769/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656317631/5000000000 : ℝ)|^8443 ≤ (43385087182089/100000000000000 : ℝ)^6395
        have hw : |(2656317631/5000000000 : ℝ)|=(2656317631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390914571/10000000000 : ℝ)|^8443 ≤ (5528881855293/12500000000000 : ℝ)^6395
        have hw : |(5390914571/10000000000 : ℝ)|=(5390914571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-513854201/2500000000 : ℝ)|^8443 ≤ (1547982245769/12500000000000 : ℝ)^6395
        have hw : |(-513854201/2500000000 : ℝ)|=(513854201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s6_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4349677479/10000000000 : ℝ)*x 0 + (179074117/400000000 : ℝ)*x 1 + (1056507697/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349677479/10000000000 : ℝ)^8443 ≤ (33317534605487/100000000000000 : ℝ)^6395 := by
    have hnat : (4349677479 : ℕ)^8443*100000000000000^6395 ≤ 33317534605487^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349677479 10000000000 33317534605487 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179074117/400000000 : ℝ)^8443 ≤ (6921923613257/20000000000000 : ℝ)^6395 := by
    have hnat : (179074117 : ℕ)^8443*20000000000000^6395 ≤ 6921923613257^6395*400000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179074117 400000000 6921923613257 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056507697/2500000000 : ℝ)^8443 ≤ (8018211830843/25000000000000 : ℝ)^6395 := by
    have hnat : (1056507697 : ℕ)^8443*25000000000000^6395 ≤ 8018211830843^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056507697 2500000000 8018211830843 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349677479/10000000000 : ℝ), (179074117/400000000 : ℝ), (1056507697/2500000000 : ℝ)] ![(33317534605487/100000000000000 : ℝ), (6921923613257/20000000000000 : ℝ), (8018211830843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349677479/10000000000 : ℝ)|^8443 ≤ (33317534605487/100000000000000 : ℝ)^6395
        have hw : |(4349677479/10000000000 : ℝ)|=(4349677479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179074117/400000000 : ℝ)|^8443 ≤ (6921923613257/20000000000000 : ℝ)^6395
        have hw : |(179074117/400000000 : ℝ)|=(179074117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056507697/2500000000 : ℝ)|^8443 ≤ (8018211830843/25000000000000 : ℝ)^6395
        have hw : |(1056507697/2500000000 : ℝ)|=(1056507697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2871/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14113/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1433/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14133/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1433/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1433/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14133/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1433/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1433/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14133/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1433/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1433/12500 : ℝ) ^ (4221/1024 : ℝ) ≤ (2651841595362279/20000000000000000000 : ℝ) := by
    have hpowers : (1433/12500 : ℝ)^4221 ≤ (2651841595362279/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1433 : ℕ)^4221*20000000000000000000^1024 ≤ 2651841595362279^1024*12500^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1433 12500 2651841595362279 20000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1433/12500 : ℝ)) (X := (2651841595362279/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14133/100000 : ℝ) ^ (4221/1024 : ℝ) ≤ (31420007073667929/100000000000000000000 : ℝ) := by
    have hpowers : (14133/100000 : ℝ)^4221 ≤ (31420007073667929/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14133 : ℕ)^4221*100000000000000000000^1024 ≤ 31420007073667929^1024*100000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14133 100000 31420007073667929 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14133/100000 : ℝ)) (X := (31420007073667929/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002651841595362279/10000000000000000000 : ℝ) ≤ (10000643263002001/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (10002651841595362279/10000000000000000000 : ℝ)^1024 ≤ (10000643263002001/10000000000000000 : ℝ)^4221 := by
      have hnat : (10002651841595362279 : ℕ)^1024*10000000000000000^4221 ≤ 10000643263002001^4221*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002651841595362279 10000000000000000000 10000643263002001 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000643263002001/10000000000000000 : ℝ)) (X := (10002651841595362279/10000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011169803762619831/25000000000000000000 : ℝ) ≤ (400043348758149/400000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (25011169803762619831/25000000000000000000 : ℝ)^1024 ≤ (400043348758149/400000000000000 : ℝ)^4221 := by
      have hnat : (25011169803762619831 : ℕ)^1024*400000000000000^4221 ≤ 400043348758149^4221*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011169803762619831 25000000000000000000 400043348758149 400000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400043348758149/400000000000000 : ℝ)) (X := (25011169803762619831/25000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031420007073667929/50000000000000000000 : ℝ) ≤ (10001524174905449/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50031420007073667929/50000000000000000000 : ℝ)^1024 ≤ (10001524174905449/10000000000000000 : ℝ)^4221 := by
      have hnat : (50031420007073667929 : ℕ)^1024*10000000000000000^4221 ≤ 10001524174905449^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031420007073667929 50000000000000000000 10001524174905449 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001524174905449/10000000000000000 : ℝ)) (X := (50031420007073667929/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2651841595362279/20000000000000000000 : ℝ) ≤ ((26681618094891212797/26690000000000000000 : ℝ)+2*(110113987931/66725000000000 : ℝ)*(1433/12500 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (26681618094891212797/26690000000000000000 : ℝ)+2*(110113987931/66725000000000 : ℝ)*(1433/12500 : ℝ)=(10000643263002001/10000000000000000 : ℝ) by norm_num, show 1+2*(2651841595362279/20000000000000000000 : ℝ)=(10002651841595362279/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31420007073667929/100000000000000000000 : ℝ)+(2651841595362279/20000000000000000000 : ℝ) ≤ ((26681618094891212797/26690000000000000000 : ℝ)+(110113987931/66725000000000 : ℝ)*((14133/100000 : ℝ)+(1433/12500 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (26681618094891212797/26690000000000000000 : ℝ)+(110113987931/66725000000000 : ℝ)*((14133/100000 : ℝ)+(1433/12500 : ℝ))=(400043348758149/400000000000000 : ℝ) by norm_num, show 1+(31420007073667929/100000000000000000000 : ℝ)+(2651841595362279/20000000000000000000 : ℝ)=(25011169803762619831/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31420007073667929/100000000000000000000 : ℝ) ≤ ((26681618094891212797/26690000000000000000 : ℝ)+2*(110113987931/66725000000000 : ℝ)*(14133/100000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (26681618094891212797/26690000000000000000 : ℝ)+2*(110113987931/66725000000000 : ℝ)*(14133/100000 : ℝ)=(10001524174905449/10000000000000000 : ℝ) by norm_num, show 1+2*(31420007073667929/100000000000000000000 : ℝ)=(50031420007073667929/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26681618094891212797/26690000000000000000 : ℝ)*(X 1 0+X 2 0)+(110113987931/66725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (1433/12500 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (26681618094891212797/26690000000000000000 : ℝ)) (alpha := (110113987931/66725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26681618094891212797/26690000000000000000 : ℝ)*(X 0 1+X 2 1)+(110113987931/66725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (1433/12500 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (26681618094891212797/26690000000000000000 : ℝ)) (alpha := (110113987931/66725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26681618094891212797/26690000000000000000 : ℝ)*(X 0 2+X 1 2)+(110113987931/66725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (1433/12500 : ℝ)) (hi := (14133/100000 : ℝ)) (c := (26681618094891212797/26690000000000000000 : ℝ)) (alpha := (110113987931/66725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2116270731/10000000000 : ℝ)*X 0 0+(5391230371/10000000000 : ℝ)*X 0 1+(5267147379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344311961/10000000000 : ℝ)*X 1 0+(-2179184487/10000000000 : ℝ)*X 1 1+(526714749/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344311803/10000000000 : ℝ)*X 2 0+(5267147493/10000000000 : ℝ)*X 2 1+(-2179184693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1087416963/2500000000 : ℝ)*X 0 0+(2112695453/5000000000 : ℝ)*X 0 1+(279843163/625000000 : ℝ)*X 0 2+(1087416963/2500000000 : ℝ)*X 1 0+(2112695453/5000000000 : ℝ)*X 1 1+(279843163/625000000 : ℝ)*X 1 2+(1087416963/2500000000 : ℝ)*X 2 0+(2112695453/5000000000 : ℝ)*X 2 1+(279843163/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116275677/10000000000 : ℝ)*X 0 0+(5267460939/10000000000 : ℝ)*X 0 1+(1347728867/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312635021/10000000000 : ℝ)*X 1 0+(-2055416689/10000000000 : ℝ)*X 1 1+(2695457447/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656317631/5000000000 : ℝ)*X 2 0+(5390914571/10000000000 : ℝ)*X 2 1+(-513854201/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349677479/10000000000 : ℝ)*X 0 0+(179074117/400000000 : ℝ)*X 0 1+(1056507697/2500000000 : ℝ)*X 0 2+(4349677479/10000000000 : ℝ)*X 1 0+(179074117/400000000 : ℝ)*X 1 1+(1056507697/2500000000 : ℝ)*X 1 2+(4349677479/10000000000 : ℝ)*X 2 0+(179074117/400000000 : ℝ)*X 2 1+(1056507697/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (142157312998414533678373941/16681250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1270259257/100000000000000 : ℝ)*(base19) + (63302823/6250000000000 : ℝ)*(base23) + (6499619/50000000000000 : ℝ)*(upper2) + (5888671/3125000000000 : ℝ)*(upper3) + (75162143135767/1250000000000 : ℝ)*(major0) + (75162143135767/1250000000000 : ℝ)*(major1) + (75162143135767/1250000000000 : ℝ)*(major2) + (8059175486896429/100000000000000 : ℝ)*(sp0) + (2014803698429963/25000000000000 : ℝ)*(sp1) + (2014801929111077/25000000000000 : ℝ)*(sp2) + (49583804712877/1250000000000 : ℝ)*(sp3) + (1014427067/2500000000000 : ℝ)*(sp4) + (3667344817/50000000000000 : ℝ)*(sp6) + (22176647371/100000000000000 : ℝ)*(sp7) + (396672655367753/10000000000000 : ℝ)*(f.failure) + (8059216063979109/100000000000000 : ℝ)*(f.sum) + (6817383404951/1334500000000000000000000000 : ℝ)*base66 + (396327171717464701/33362500000000000000000000000000 : ℝ)*base68 + (425799025211277201/33362500000000000000000000000000 : ℝ)*base70 + (382418578571252201/33362500000000000000000000000000 : ℝ)*base72 + (10639399197231/2669000000000000000000000000 : ℝ)*base74 + (273875129651039701/33362500000000000000000000000000 : ℝ)*base76 + (553371086578002201/33362500000000000000000000000000 : ℝ)*base78 + (977498424626852201/33362500000000000000000000000000 : ℝ)*base80 + (77100907019/41703125000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6984931/1000000000000000000000 : ℝ)*base89 + (6984931/1000000000000000000000 : ℝ)*base91 + (6984931/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (485800945432146379396435479/133450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486313983/20000000000000 : ℝ)*(base19) + (1588865947/50000000000000 : ℝ)*(base23) + (107988463/50000000000000 : ℝ)*(upper2) + (16556661/6250000000000 : ℝ)*(upper5) + (1208705149151569/20000000000000 : ℝ)*(major0) + (1208705149151569/20000000000000 : ℝ)*(major1) + (1208705149151569/20000000000000 : ℝ)*(major2) + (4904413947/100000000000000 : ℝ)*(sp0) + (28944721273/50000000000000 : ℝ)*(sp1) + (2128941549/4000000000000 : ℝ)*(sp2) + (1620032679959823/20000000000000 : ℝ)*(sp4) + (8100107983200601/100000000000000 : ℝ)*(sp5) + (8100111902942443/100000000000000 : ℝ)*(sp6) + (1993441532979281/50000000000000 : ℝ)*(sp7) + (1993441532979281/50000000000000 : ℝ)*(f.failure) + (4050084152106531/50000000000000 : ℝ)*(f.sum) + (141310020289/1334500000000000000000000000 : ℝ)*base66 + (1373139076932571507/533800000000000000000000000000000 : ℝ)*base68 + (6213298736527171507/533800000000000000000000000000000 : ℝ)*base70 + (5107186633763971507/533800000000000000000000000000000 : ℝ)*base72 + (3149129417743/533800000000000000000000000 : ℝ)*base74 + (1817698669440971507/533800000000000000000000000000000 : ℝ)*base76 + (6672478220657171507/533800000000000000000000000000000 : ℝ)*base78 + (770841903174628493/533800000000000000000000000000000 : ℝ)*base79 + (254427247663/533800000000000000000000000 : ℝ)*base82 + (46681787/5000000000000000000000 : ℝ)*base89 + (46681787/5000000000000000000000 : ℝ)*base91 + (46681787/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1250_s7_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-211628389/1000000000 : ℝ)*x 0 + (2695522287/5000000000 : ℝ)*x 1 + (2633662369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211628389/1000000000 : ℝ)^8443 ≤ (514812205881/4000000000000 : ℝ)^6395 := by
    have hnat : (211628389 : ℕ)^8443*4000000000000^6395 ≤ 514812205881^6395*1000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211628389 1000000000 514812205881 4000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695522287/5000000000 : ℝ)^8443 ≤ (44232463080603/100000000000000 : ℝ)^6395 := by
    have hnat : (2695522287 : ℕ)^8443*100000000000000^6395 ≤ 44232463080603^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695522287 5000000000 44232463080603 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633662369/5000000000 : ℝ)^8443 ≤ (42897231761073/100000000000000 : ℝ)^6395 := by
    have hnat : (2633662369 : ℕ)^8443*100000000000000^6395 ≤ 42897231761073^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633662369 5000000000 42897231761073 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-211628389/1000000000 : ℝ), (2695522287/5000000000 : ℝ), (2633662369/5000000000 : ℝ)] ![(514812205881/4000000000000 : ℝ), (44232463080603/100000000000000 : ℝ), (42897231761073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-211628389/1000000000 : ℝ)|^8443 ≤ (514812205881/4000000000000 : ℝ)^6395
        have hw : |(-211628389/1000000000 : ℝ)|=(211628389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695522287/5000000000 : ℝ)|^8443 ≤ (44232463080603/100000000000000 : ℝ)^6395
        have hw : |(2695522287/5000000000 : ℝ)|=(2695522287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633662369/5000000000 : ℝ)|^8443 ≤ (42897231761073/100000000000000 : ℝ)^6395
        have hw : |(2633662369/5000000000 : ℝ)|=(2633662369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s7_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672132747/5000000000 : ℝ)*x 0 + (-544752831/2500000000 : ℝ)*x 1 + (52673247/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672132747/5000000000 : ℝ)^8443 ≤ (8745287823887/20000000000000 : ℝ)^6395 := by
    have hnat : (2672132747 : ℕ)^8443*20000000000000^6395 ≤ 8745287823887^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672132747 5000000000 8745287823887 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (544752831/2500000000 : ℝ)^8443 ≤ (13376329512909/100000000000000 : ℝ)^6395 := by
    have hnat : (544752831 : ℕ)^8443*100000000000000^6395 ≤ 13376329512909^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544752831 2500000000 13376329512909 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52673247/100000000 : ℝ)^8443 ≤ (42897231352491/100000000000000 : ℝ)^6395 := by
    have hnat : (52673247 : ℕ)^8443*100000000000000^6395 ≤ 42897231352491^6395*100000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52673247 100000000 42897231352491 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672132747/5000000000 : ℝ), (-544752831/2500000000 : ℝ), (52673247/100000000 : ℝ)] ![(8745287823887/20000000000000 : ℝ), (13376329512909/100000000000000 : ℝ), (42897231352491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672132747/5000000000 : ℝ)|^8443 ≤ (8745287823887/20000000000000 : ℝ)^6395
        have hw : |(2672132747/5000000000 : ℝ)|=(2672132747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-544752831/2500000000 : ℝ)|^8443 ≤ (13376329512909/100000000000000 : ℝ)^6395
        have hw : |(-544752831/2500000000 : ℝ)|=(544752831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52673247/100000000 : ℝ)|^8443 ≤ (42897231352491/100000000000000 : ℝ)^6395
        have hw : |(52673247/100000000 : ℝ)|=(52673247/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s7_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672132717/5000000000 : ℝ)*x 0 + (5267324729/10000000000 : ℝ)*x 1 + (-544752841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672132717/5000000000 : ℝ)^8443 ≤ (21863219235651/50000000000000 : ℝ)^6395 := by
    have hnat : (2672132717 : ℕ)^8443*50000000000000^6395 ≤ 21863219235651^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672132717 5000000000 21863219235651 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267324729/10000000000 : ℝ)^8443 ≤ (42897231664303/100000000000000 : ℝ)^6395 := by
    have hnat : (5267324729 : ℕ)^8443*100000000000000^6395 ≤ 42897231664303^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267324729 10000000000 42897231664303 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544752841/2500000000 : ℝ)^8443 ≤ (6688164918547/50000000000000 : ℝ)^6395 := by
    have hnat : (544752841 : ℕ)^8443*50000000000000^6395 ≤ 6688164918547^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544752841 2500000000 6688164918547 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672132717/5000000000 : ℝ), (5267324729/10000000000 : ℝ), (-544752841/2500000000 : ℝ)] ![(21863219235651/50000000000000 : ℝ), (42897231664303/100000000000000 : ℝ), (6688164918547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672132717/5000000000 : ℝ)|^8443 ≤ (21863219235651/50000000000000 : ℝ)^6395
        have hw : |(2672132717/5000000000 : ℝ)|=(2672132717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267324729/10000000000 : ℝ)|^8443 ≤ (42897231664303/100000000000000 : ℝ)^6395
        have hw : |(5267324729/10000000000 : ℝ)|=(5267324729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-544752841/2500000000 : ℝ)|^8443 ≤ (6688164918547/50000000000000 : ℝ)^6395
        have hw : |(-544752841/2500000000 : ℝ)|=(544752841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s7_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (6796371/15625000 : ℝ)*x 0 + (2112878913/5000000000 : ℝ)*x 1 + (179084837/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6796371/15625000 : ℝ)^8443 ≤ (33317534211087/100000000000000 : ℝ)^6395 := by
    have hnat : (6796371 : ℕ)^8443*100000000000000^6395 ≤ 33317534211087^6395*15625000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6796371 15625000 33317534211087 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2112878913/5000000000 : ℝ)^8443 ≤ (8017528078529/25000000000000 : ℝ)^6395 := by
    have hnat : (2112878913 : ℕ)^8443*25000000000000^6395 ≤ 8017528078529^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112878913 5000000000 8017528078529 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179084837/400000000 : ℝ)^8443 ≤ (17306176727897/50000000000000 : ℝ)^6395 := by
    have hnat : (179084837 : ℕ)^8443*50000000000000^6395 ≤ 17306176727897^6395*400000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179084837 400000000 17306176727897 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6796371/15625000 : ℝ), (2112878913/5000000000 : ℝ), (179084837/400000000 : ℝ)] ![(33317534211087/100000000000000 : ℝ), (8017528078529/25000000000000 : ℝ), (17306176727897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6796371/15625000 : ℝ)|^8443 ≤ (33317534211087/100000000000000 : ℝ)^6395
        have hw : |(6796371/15625000 : ℝ)|=(6796371/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2112878913/5000000000 : ℝ)|^8443 ≤ (8017528078529/25000000000000 : ℝ)^6395
        have hw : |(2112878913/5000000000 : ℝ)|=(2112878913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179084837/400000000 : ℝ)|^8443 ≤ (17306176727897/50000000000000 : ℝ)^6395
        have hw : |(179084837/400000000 : ℝ)|=(179084837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s7_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116288377/10000000000 : ℝ)*x 0 + (658454631/1250000000 : ℝ)*x 1 + (2695365623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116288377/10000000000 : ℝ)^8443 ≤ (2574068234793/20000000000000 : ℝ)^6395 := by
    have hnat : (2116288377 : ℕ)^8443*20000000000000^6395 ≤ 2574068234793^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116288377 10000000000 2574068234793 20000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658454631/1250000000 : ℝ)^8443 ≤ (42900589797687/100000000000000 : ℝ)^6395 := by
    have hnat : (658454631 : ℕ)^8443*100000000000000^6395 ≤ 42900589797687^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658454631 1250000000 42900589797687 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695365623/5000000000 : ℝ)^8443 ≤ (22114534509947/50000000000000 : ℝ)^6395 := by
    have hnat : (2695365623 : ℕ)^8443*50000000000000^6395 ≤ 22114534509947^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695365623 5000000000 22114534509947 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116288377/10000000000 : ℝ), (658454631/1250000000 : ℝ), (2695365623/5000000000 : ℝ)] ![(2574068234793/20000000000000 : ℝ), (42900589797687/100000000000000 : ℝ), (22114534509947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116288377/10000000000 : ℝ)|^8443 ≤ (2574068234793/20000000000000 : ℝ)^6395
        have hw : |(-2116288377/10000000000 : ℝ)|=(2116288377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658454631/1250000000 : ℝ)|^8443 ≤ (42900589797687/100000000000000 : ℝ)^6395
        have hw : |(658454631/1250000000 : ℝ)|=(658454631/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695365623/5000000000 : ℝ)|^8443 ≤ (22114534509947/50000000000000 : ℝ)^6395
        have hw : |(2695365623/5000000000 : ℝ)|=(2695365623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s7_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66408509/125000000 : ℝ)*x 0 + (-2055604623/10000000000 : ℝ)*x 1 + (5390731401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66408509/125000000 : ℝ)^8443 ≤ (21692788648341/50000000000000 : ℝ)^6395 := by
    have hnat : (66408509 : ℕ)^8443*50000000000000^6395 ≤ 21692788648341^6395*125000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66408509 125000000 21692788648341 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2055604623/10000000000 : ℝ)^8443 ≤ (1238535199223/10000000000000 : ℝ)^6395 := by
    have hnat : (2055604623 : ℕ)^8443*10000000000000^6395 ≤ 1238535199223^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055604623 10000000000 1238535199223 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390731401/10000000000 : ℝ)^8443 ≤ (44229070698883/100000000000000 : ℝ)^6395 := by
    have hnat : (5390731401 : ℕ)^8443*100000000000000^6395 ≤ 44229070698883^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390731401 10000000000 44229070698883 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66408509/125000000 : ℝ), (-2055604623/10000000000 : ℝ), (5390731401/10000000000 : ℝ)] ![(21692788648341/50000000000000 : ℝ), (1238535199223/10000000000000 : ℝ), (44229070698883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66408509/125000000 : ℝ)|^8443 ≤ (21692788648341/50000000000000 : ℝ)^6395
        have hw : |(66408509/125000000 : ℝ)|=(66408509/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2055604623/10000000000 : ℝ)|^8443 ≤ (1238535199223/10000000000000 : ℝ)^6395
        have hw : |(-2055604623/10000000000 : ℝ)|=(2055604623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390731401/10000000000 : ℝ)|^8443 ≤ (44229070698883/100000000000000 : ℝ)^6395
        have hw : |(5390731401/10000000000 : ℝ)|=(5390731401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s7_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656340269/5000000000 : ℝ)*x 0 + (2695365937/5000000000 : ℝ)*x 1 + (-82224169/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656340269/5000000000 : ℝ)^8443 ≤ (4338557533441/10000000000000 : ℝ)^6395 := by
    have hnat : (2656340269 : ℕ)^8443*10000000000000^6395 ≤ 4338557533441^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656340269 5000000000 4338557533441 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695365937/5000000000 : ℝ)^8443 ≤ (4422907582251/10000000000000 : ℝ)^6395 := by
    have hnat : (2695365937 : ℕ)^8443*10000000000000^6395 ≤ 4422907582251^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695365937 5000000000 4422907582251 10000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82224169/400000000 : ℝ)^8443 ≤ (12385348826251/100000000000000 : ℝ)^6395 := by
    have hnat : (82224169 : ℕ)^8443*100000000000000^6395 ≤ 12385348826251^6395*400000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82224169 400000000 12385348826251 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656340269/5000000000 : ℝ), (2695365937/5000000000 : ℝ), (-82224169/400000000 : ℝ)] ![(4338557533441/10000000000000 : ℝ), (4422907582251/10000000000000 : ℝ), (12385348826251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656340269/5000000000 : ℝ)|^8443 ≤ (4338557533441/10000000000000 : ℝ)^6395
        have hw : |(2656340269/5000000000 : ℝ)|=(2656340269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695365937/5000000000 : ℝ)|^8443 ≤ (4422907582251/10000000000000 : ℝ)^6395
        have hw : |(2695365937/5000000000 : ℝ)|=(2695365937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82224169/400000000 : ℝ)|^8443 ≤ (12385348826251/100000000000000 : ℝ)^6395
        have hw : |(-82224169/400000000 : ℝ)|=(82224169/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s7_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1087421691/2500000000 : ℝ)*x 0 + (4476486717/10000000000 : ℝ)*x 1 + (2113197219/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087421691/2500000000 : ℝ)^8443 ≤ (16658814251501/50000000000000 : ℝ)^6395 := by
    have hnat : (1087421691 : ℕ)^8443*50000000000000^6395 ≤ 16658814251501^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087421691 2500000000 16658814251501 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476486717/10000000000 : ℝ)^8443 ≤ (173029401921/500000000000 : ℝ)^6395 := by
    have hnat : (4476486717 : ℕ)^8443*500000000000^6395 ≤ 173029401921^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476486717 10000000000 173029401921 500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113197219/5000000000 : ℝ)^8443 ≤ (32076491091027/100000000000000 : ℝ)^6395 := by
    have hnat : (2113197219 : ℕ)^8443*100000000000000^6395 ≤ 32076491091027^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113197219 5000000000 32076491091027 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087421691/2500000000 : ℝ), (4476486717/10000000000 : ℝ), (2113197219/5000000000 : ℝ)] ![(16658814251501/50000000000000 : ℝ), (173029401921/500000000000 : ℝ), (32076491091027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087421691/2500000000 : ℝ)|^8443 ≤ (16658814251501/50000000000000 : ℝ)^6395
        have hw : |(1087421691/2500000000 : ℝ)|=(1087421691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476486717/10000000000 : ℝ)|^8443 ≤ (173029401921/500000000000 : ℝ)^6395
        have hw : |(4476486717/10000000000 : ℝ)|=(4476486717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113197219/5000000000 : ℝ)|^8443 ≤ (32076491091027/100000000000000 : ℝ)^6395
        have hw : |(2113197219/5000000000 : ℝ)|=(2113197219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (359/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2871/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2871/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2871/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2871/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2871/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2871/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2871/25000 : ℝ) ^ (4221/1024 : ℝ) ≤ (6677409656702191/50000000000000000000 : ℝ) := by
    have hpowers : (2871/25000 : ℝ)^4221 ≤ (6677409656702191/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2871 : ℕ)^4221*50000000000000000000^1024 ≤ 6677409656702191^1024*25000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2871 25000 6677409656702191 50000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2871/25000 : ℝ)) (X := (6677409656702191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14113/100000 : ℝ) ^ (4221/1024 : ℝ) ≤ (195232066280563/625000000000000000 : ℝ) := by
    have hpowers : (14113/100000 : ℝ)^4221 ≤ (195232066280563/625000000000000000 : ℝ)^1024 := by
      have hnat : (14113 : ℕ)^4221*625000000000000000^1024 ≤ 195232066280563^1024*100000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14113 100000 195232066280563 625000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14113/100000 : ℝ)) (X := (195232066280563/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006677409656702191/25000000000000000000 : ℝ) ≤ (10000647901063021/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (25006677409656702191/25000000000000000000 : ℝ)^1024 ≤ (10000647901063021/10000000000000000 : ℝ)^4221 := by
      have hnat : (25006677409656702191 : ℕ)^1024*10000000000000000^4221 ≤ 10000647901063021^4221*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006677409656702191 25000000000000000000 10000647901063021 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000647901063021/10000000000000000 : ℝ)) (X := (25006677409656702191/25000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022295974959147231/50000000000000000000 : ℝ) ≤ (5000540801323613/5000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50022295974959147231/50000000000000000000 : ℝ)^1024 ≤ (5000540801323613/5000000000000000 : ℝ)^4221 := by
      have hnat : (50022295974959147231 : ℕ)^1024*5000000000000000^4221 ≤ 5000540801323613^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022295974959147231 50000000000000000000 5000540801323613 5000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000540801323613/5000000000000000 : ℝ)) (X := (50022295974959147231/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (312695232066280563/312500000000000000 : ℝ) ≤ (10001515304231431/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (312695232066280563/312500000000000000 : ℝ)^1024 ≤ (10001515304231431/10000000000000000 : ℝ)^4221 := by
      have hnat : (312695232066280563 : ℕ)^1024*10000000000000000^4221 ≤ 10001515304231431^4221*312500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        312695232066280563 312500000000000000 10001515304231431 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001515304231431/10000000000000000 : ℝ)) (X := (312695232066280563/312500000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6677409656702191/50000000000000000000 : ℝ) ≤ ((2389249279446241979/2390000000000000000 : ℝ)+2*(86740316841/52580000000000 : ℝ)*(2871/25000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (2389249279446241979/2390000000000000000 : ℝ)+2*(86740316841/52580000000000 : ℝ)*(2871/25000 : ℝ)=(10000647901063021/10000000000000000 : ℝ) by norm_num, show 1+2*(6677409656702191/50000000000000000000 : ℝ)=(25006677409656702191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(195232066280563/625000000000000000 : ℝ)+(6677409656702191/50000000000000000000 : ℝ) ≤ ((2389249279446241979/2390000000000000000 : ℝ)+(86740316841/52580000000000 : ℝ)*((14113/100000 : ℝ)+(2871/25000 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (2389249279446241979/2390000000000000000 : ℝ)+(86740316841/52580000000000 : ℝ)*((14113/100000 : ℝ)+(2871/25000 : ℝ))=(5000540801323613/5000000000000000 : ℝ) by norm_num, show 1+(195232066280563/625000000000000000 : ℝ)+(6677409656702191/50000000000000000000 : ℝ)=(50022295974959147231/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(195232066280563/625000000000000000 : ℝ) ≤ ((2389249279446241979/2390000000000000000 : ℝ)+2*(86740316841/52580000000000 : ℝ)*(14113/100000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (2389249279446241979/2390000000000000000 : ℝ)+2*(86740316841/52580000000000 : ℝ)*(14113/100000 : ℝ)=(10001515304231431/10000000000000000 : ℝ) by norm_num, show 1+2*(195232066280563/625000000000000000 : ℝ)=(312695232066280563/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2389249279446241979/2390000000000000000 : ℝ)*(X 1 0+X 2 0)+(86740316841/52580000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2871/25000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (2389249279446241979/2390000000000000000 : ℝ)) (alpha := (86740316841/52580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2389249279446241979/2390000000000000000 : ℝ)*(X 0 1+X 2 1)+(86740316841/52580000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2871/25000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (2389249279446241979/2390000000000000000 : ℝ)) (alpha := (86740316841/52580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2389249279446241979/2390000000000000000 : ℝ)*(X 0 2+X 1 2)+(86740316841/52580000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (2871/25000 : ℝ)) (hi := (14113/100000 : ℝ)) (c := (2389249279446241979/2390000000000000000 : ℝ)) (alpha := (86740316841/52580000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-211628389/1000000000 : ℝ)*X 0 0+(2695522287/5000000000 : ℝ)*X 0 1+(2633662369/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672132747/5000000000 : ℝ)*X 1 0+(-544752831/2500000000 : ℝ)*X 1 1+(52673247/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672132717/5000000000 : ℝ)*X 2 0+(5267324729/10000000000 : ℝ)*X 2 1+(-544752841/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6796371/15625000 : ℝ)*X 0 0+(2112878913/5000000000 : ℝ)*X 0 1+(179084837/400000000 : ℝ)*X 0 2+(6796371/15625000 : ℝ)*X 1 0+(2112878913/5000000000 : ℝ)*X 1 1+(179084837/400000000 : ℝ)*X 1 2+(6796371/15625000 : ℝ)*X 2 0+(2112878913/5000000000 : ℝ)*X 2 1+(179084837/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116288377/10000000000 : ℝ)*X 0 0+(658454631/1250000000 : ℝ)*X 0 1+(2695365623/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66408509/125000000 : ℝ)*X 1 0+(-2055604623/10000000000 : ℝ)*X 1 1+(5390731401/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656340269/5000000000 : ℝ)*X 2 0+(2695365937/5000000000 : ℝ)*X 2 1+(-82224169/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087421691/2500000000 : ℝ)*X 0 0+(4476486717/10000000000 : ℝ)*X 0 1+(2113197219/5000000000 : ℝ)*X 0 2+(1087421691/2500000000 : ℝ)*X 1 0+(4476486717/10000000000 : ℝ)*X 1 1+(2113197219/5000000000 : ℝ)*X 1 2+(1087421691/2500000000 : ℝ)*X 2 0+(4476486717/10000000000 : ℝ)*X 2 1+(2113197219/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (843315302251240364631/131450000000000000000000000 : ℝ) := by norm_num
    linear_combination (840433503/100000000000000 : ℝ)*(base19) + (549439481/100000000000000 : ℝ)*(base23) + (145201809/100000000000000 : ℝ)*(lower2) + (57554427/25000000000000 : ℝ)*(upper3) + (38183733/100000000000000 : ℝ)*(lower4) + (188455456660101/3125000000000 : ℝ)*(major0) + (188455456660101/3125000000000 : ℝ)*(major1) + (188455456660101/3125000000000 : ℝ)*(major2) + (1616559731150727/20000000000000 : ℝ)*(sp0) + (8082808902053489/100000000000000 : ℝ)*(sp1) + (8082809193047511/100000000000000 : ℝ)*(sp2) + (795664251450723/20000000000000 : ℝ)*(sp3) + (5543366679/50000000000000 : ℝ)*(sp4) + (4503164099/25000000000000 : ℝ)*(sp7) + (397833926991001/10000000000000 : ℝ)*(f.failure) + (505175608905437/6250000000000 : ℝ)*(f.sum) + (3135622209/5258000000000000000000000 : ℝ)*base65 + (738674334899253669/82156250000000000000000000000000 : ℝ)*base67 + (884900716610902581/82156250000000000000000000000000 : ℝ)*base70 + (1180248384154058831/82156250000000000000000000000000 : ℝ)*base72 + (316790802709/1314500000000000000000000000 : ℝ)*base73 + (1035842443962284919/82156250000000000000000000000000 : ℝ)*base75 + (1110582037305058831/82156250000000000000000000000000 : ℝ)*base78 + (1246693599070972419/82156250000000000000000000000000 : ℝ)*base79 + (3000783595461/2629000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6457773/1000000000000000000000 : ℝ)*base90 + (6457773/1000000000000000000000 : ℝ)*base92 + (6457773/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (150562463309801545791/16431250000000000000000000 : ℝ) := by norm_num
    linear_combination (105475439/20000000000000 : ℝ)*(base19) + (214943077/20000000000000 : ℝ)*(base23) + (86870141/50000000000000 : ℝ)*(upper3) + (286519303/100000000000000 : ℝ)*(lower4) + (6061188950133327/100000000000000 : ℝ)*(major0) + (6061188950133327/100000000000000 : ℝ)*(major1) + (6061188950133327/100000000000000 : ℝ)*(major2) + (3164521629/20000000000000 : ℝ)*(sp1) + (6398414693/10000000000000 : ℝ)*(sp2) + (1067471341/20000000000000 : ℝ)*(sp3) + (8123842203160679/100000000000000 : ℝ)*(sp4) + (8123825853175339/100000000000000 : ℝ)*(sp5) + (2030944286074591/25000000000000 : ℝ)*(sp6) + (3998530054310009/100000000000000 : ℝ)*(sp7) + (1999267695833357/50000000000000 : ℝ)*(f.failure) + (8123842203160679/100000000000000 : ℝ)*(f.sum) + (2254172329649/262900000000000000000000000 : ℝ)*base66 + (1444151044173824537/2629000000000000000000000000000000 : ℝ)*base68 + (7523315844827824537/2629000000000000000000000000000000 : ℝ)*base70 + (26538242964307175463/2629000000000000000000000000000000 : ℝ)*base71 + (2320032396167/2629000000000000000000000000 : ℝ)*base74 + (8666262265427175463/2629000000000000000000000000000000 : ℝ)*base75 + (24392440062410824537/2629000000000000000000000000000000 : ℝ)*base78 + (21843398154520175463/2629000000000000000000000000000000 : ℝ)*base79 + (19264772489/657250000000000000000000000 : ℝ)*base82 + (25017039/5000000000000000000000 : ℝ)*base89 + (25017039/5000000000000000000000 : ℝ)*base91 + (25017039/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2871/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (359/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1250_s8_0 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529071651/2500000000 : ℝ)*x 0 + (5391007859/10000000000 : ℝ)*x 1 + (5267359699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529071651/2500000000 : ℝ)^8443 ≤ (6435163469111/50000000000000 : ℝ)^6395 := by
    have hnat : (529071651 : ℕ)^8443*50000000000000^6395 ≤ 6435163469111^6395*2500000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529071651 2500000000 6435163469111 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391007859/10000000000 : ℝ)^8443 ≤ (44232065369697/100000000000000 : ℝ)^6395 := by
    have hnat : (5391007859 : ℕ)^8443*100000000000000^6395 ≤ 44232065369697^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391007859 10000000000 44232065369697 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267359699/10000000000 : ℝ)^8443 ≤ (21448803833737/50000000000000 : ℝ)^6395 := by
    have hnat : (5267359699 : ℕ)^8443*50000000000000^6395 ≤ 21448803833737^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267359699 10000000000 21448803833737 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529071651/2500000000 : ℝ), (5391007859/10000000000 : ℝ), (5267359699/10000000000 : ℝ)] ![(6435163469111/50000000000000 : ℝ), (44232065369697/100000000000000 : ℝ), (21448803833737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529071651/2500000000 : ℝ)|^8443 ≤ (6435163469111/50000000000000 : ℝ)^6395
        have hw : |(-529071651/2500000000 : ℝ)|=(529071651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391007859/10000000000 : ℝ)|^8443 ≤ (44232065369697/100000000000000 : ℝ)^6395
        have hw : |(5391007859/10000000000 : ℝ)|=(5391007859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267359699/10000000000 : ℝ)|^8443 ≤ (21448803833737/50000000000000 : ℝ)^6395
        have hw : |(5267359699/10000000000 : ℝ)|=(5267359699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s8_1 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213770253/400000000 : ℝ)*x 0 + (-1089488491/5000000000 : ℝ)*x 1 + (2633679899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213770253/400000000 : ℝ)^8443 ≤ (2732896254629/6250000000000 : ℝ)^6395 := by
    have hnat : (213770253 : ℕ)^8443*6250000000000^6395 ≤ 2732896254629^6395*400000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213770253 400000000 2732896254629 6250000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1089488491/5000000000 : ℝ)^8443 ≤ (535042047363/4000000000000 : ℝ)^6395 := by
    have hnat : (1089488491 : ℕ)^8443*4000000000000^6395 ≤ 535042047363^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089488491 5000000000 535042047363 4000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633679899/5000000000 : ℝ)^8443 ≤ (2144880436597/5000000000000 : ℝ)^6395 := by
    have hnat : (2633679899 : ℕ)^8443*5000000000000^6395 ≤ 2144880436597^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633679899 5000000000 2144880436597 5000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213770253/400000000 : ℝ), (-1089488491/5000000000 : ℝ), (2633679899/5000000000 : ℝ)] ![(2732896254629/6250000000000 : ℝ), (535042047363/4000000000000 : ℝ), (2144880436597/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213770253/400000000 : ℝ)|^8443 ≤ (2732896254629/6250000000000 : ℝ)^6395
        have hw : |(213770253/400000000 : ℝ)|=(213770253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1089488491/5000000000 : ℝ)|^8443 ≤ (535042047363/4000000000000 : ℝ)^6395
        have hw : |(-1089488491/5000000000 : ℝ)|=(1089488491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633679899/5000000000 : ℝ)|^8443 ≤ (2144880436597/5000000000000 : ℝ)^6395
        have hw : |(2633679899/5000000000 : ℝ)|=(2633679899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s8_2 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167008013/312500000 : ℝ)*x 0 + (2633679861/5000000000 : ℝ)*x 1 + (-2178976961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167008013/312500000 : ℝ)^8443 ≤ (5465792632133/12500000000000 : ℝ)^6395 := by
    have hnat : (167008013 : ℕ)^8443*12500000000000^6395 ≤ 5465792632133^6395*312500000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167008013 312500000 5465792632133 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633679861/5000000000 : ℝ)^8443 ≤ (21448803957387/50000000000000 : ℝ)^6395 := by
    have hnat : (2633679861 : ℕ)^8443*50000000000000^6395 ≤ 21448803957387^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633679861 5000000000 21448803957387 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2178976961/10000000000 : ℝ)^8443 ≤ (6688025506939/50000000000000 : ℝ)^6395 := by
    have hnat : (2178976961 : ℕ)^8443*50000000000000^6395 ≤ 6688025506939^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178976961 10000000000 6688025506939 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167008013/312500000 : ℝ), (2633679861/5000000000 : ℝ), (-2178976961/10000000000 : ℝ)] ![(5465792632133/12500000000000 : ℝ), (21448803957387/50000000000000 : ℝ), (6688025506939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167008013/312500000 : ℝ)|^8443 ≤ (5465792632133/12500000000000 : ℝ)^6395
        have hw : |(167008013/312500000 : ℝ)|=(167008013/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633679861/5000000000 : ℝ)|^8443 ≤ (21448803957387/50000000000000 : ℝ)^6395
        have hw : |(2633679861/5000000000 : ℝ)|=(2633679861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2178976961/10000000000 : ℝ)|^8443 ≤ (6688025506939/50000000000000 : ℝ)^6395
        have hw : |(-2178976961/10000000000 : ℝ)|=(2178976961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s8_3 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869935821/2000000000 : ℝ)*x 0 + (4225831001/10000000000 : ℝ)*x 1 + (4477047441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869935821/2000000000 : ℝ)^8443 ≤ (1332702041957/4000000000000 : ℝ)^6395 := by
    have hnat : (869935821 : ℕ)^8443*4000000000000^6395 ≤ 1332702041957^6395*2000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869935821 2000000000 1332702041957 4000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225831001/10000000000 : ℝ)^8443 ≤ (4008855687913/12500000000000 : ℝ)^6395 := by
    have hnat : (4225831001 : ℕ)^8443*12500000000000^6395 ≤ 4008855687913^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225831001 10000000000 4008855687913 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4477047441/10000000000 : ℝ)^8443 ≤ (34611603423103/100000000000000 : ℝ)^6395 := by
    have hnat : (4477047441 : ℕ)^8443*100000000000000^6395 ≤ 34611603423103^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4477047441 10000000000 34611603423103 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869935821/2000000000 : ℝ), (4225831001/10000000000 : ℝ), (4477047441/10000000000 : ℝ)] ![(1332702041957/4000000000000 : ℝ), (4008855687913/12500000000000 : ℝ), (34611603423103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869935821/2000000000 : ℝ)|^8443 ≤ (1332702041957/4000000000000 : ℝ)^6395
        have hw : |(869935821/2000000000 : ℝ)|=(869935821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225831001/10000000000 : ℝ)|^8443 ≤ (4008855687913/12500000000000 : ℝ)^6395
        have hw : |(4225831001/10000000000 : ℝ)|=(4225831001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4477047441/10000000000 : ℝ)|^8443 ≤ (34611603423103/100000000000000 : ℝ)^6395
        have hw : |(4477047441/10000000000 : ℝ)|=(4477047441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s8_4 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116291101/10000000000 : ℝ)*x 0 + (2633835773/5000000000 : ℝ)*x 1 + (5390694983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116291101/10000000000 : ℝ)^8443 ≤ (12870363045469/100000000000000 : ℝ)^6395 := by
    have hnat : (2116291101 : ℕ)^8443*100000000000000^6395 ≤ 12870363045469^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116291101 10000000000 12870363045469 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633835773/5000000000 : ℝ)^8443 ≤ (343207685863/800000000000 : ℝ)^6395 := by
    have hnat : (2633835773 : ℕ)^8443*800000000000^6395 ≤ 343207685863^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633835773 5000000000 343207685863 800000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390694983/10000000000 : ℝ)^8443 ≤ (44228676212531/100000000000000 : ℝ)^6395 := by
    have hnat : (5390694983 : ℕ)^8443*100000000000000^6395 ≤ 44228676212531^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390694983 10000000000 44228676212531 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116291101/10000000000 : ℝ), (2633835773/5000000000 : ℝ), (5390694983/10000000000 : ℝ)] ![(12870363045469/100000000000000 : ℝ), (343207685863/800000000000 : ℝ), (44228676212531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116291101/10000000000 : ℝ)|^8443 ≤ (12870363045469/100000000000000 : ℝ)^6395
        have hw : |(-2116291101/10000000000 : ℝ)|=(2116291101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633835773/5000000000 : ℝ)|^8443 ≤ (343207685863/800000000000 : ℝ)^6395
        have hw : |(2633835773/5000000000 : ℝ)|=(2633835773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390694983/10000000000 : ℝ)|^8443 ≤ (44228676212531/100000000000000 : ℝ)^6395
        have hw : |(5390694983/10000000000 : ℝ)|=(5390694983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s8_5 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312689779/10000000000 : ℝ)*x 0 + (-2055641831/10000000000 : ℝ)*x 1 + (5390695059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312689779/10000000000 : ℝ)^8443 ≤ (21692837484139/50000000000000 : ℝ)^6395 := by
    have hnat : (5312689779 : ℕ)^8443*50000000000000^6395 ≤ 21692837484139^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312689779 10000000000 21692837484139 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2055641831/10000000000 : ℝ)^8443 ≤ (6192823986193/50000000000000 : ℝ)^6395 := by
    have hnat : (2055641831 : ℕ)^8443*50000000000000^6395 ≤ 6192823986193^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055641831 10000000000 6192823986193 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390695059/10000000000 : ℝ)^8443 ≤ (1769147081431/4000000000000 : ℝ)^6395 := by
    have hnat : (5390695059 : ℕ)^8443*4000000000000^6395 ≤ 1769147081431^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390695059 10000000000 1769147081431 4000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312689779/10000000000 : ℝ), (-2055641831/10000000000 : ℝ), (5390695059/10000000000 : ℝ)] ![(21692837484139/50000000000000 : ℝ), (6192823986193/50000000000000 : ℝ), (1769147081431/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312689779/10000000000 : ℝ)|^8443 ≤ (21692837484139/50000000000000 : ℝ)^6395
        have hw : |(5312689779/10000000000 : ℝ)|=(5312689779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2055641831/10000000000 : ℝ)|^8443 ≤ (6192823986193/50000000000000 : ℝ)^6395
        have hw : |(-2055641831/10000000000 : ℝ)|=(2055641831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390695059/10000000000 : ℝ)|^8443 ≤ (1769147081431/4000000000000 : ℝ)^6395
        have hw : |(5390695059/10000000000 : ℝ)|=(5390695059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s8_6 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664086217/1250000000 : ℝ)*x 0 + (5390695167/10000000000 : ℝ)*x 1 + (-2055641743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664086217/1250000000 : ℝ)^8443 ≤ (5423209313083/12500000000000 : ℝ)^6395 := by
    have hnat : (664086217 : ℕ)^8443*12500000000000^6395 ≤ 5423209313083^6395*1250000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664086217 1250000000 5423209313083 12500000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5390695167/10000000000 : ℝ)^8443 ≤ (884573564113/2000000000000 : ℝ)^6395 := by
    have hnat : (5390695167 : ℕ)^8443*2000000000000^6395 ≤ 884573564113^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390695167 10000000000 884573564113 2000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055641743/10000000000 : ℝ)^8443 ≤ (6192823636183/50000000000000 : ℝ)^6395 := by
    have hnat : (2055641743 : ℕ)^8443*50000000000000^6395 ≤ 6192823636183^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055641743 10000000000 6192823636183 50000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664086217/1250000000 : ℝ), (5390695167/10000000000 : ℝ), (-2055641743/10000000000 : ℝ)] ![(5423209313083/12500000000000 : ℝ), (884573564113/2000000000000 : ℝ), (6192823636183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664086217/1250000000 : ℝ)|^8443 ≤ (5423209313083/12500000000000 : ℝ)^6395
        have hw : |(664086217/1250000000 : ℝ)|=(664086217/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5390695167/10000000000 : ℝ)|^8443 ≤ (884573564113/2000000000000 : ℝ)^6395
        have hw : |(5390695167/10000000000 : ℝ)|=(5390695167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2055641743/10000000000 : ℝ)|^8443 ≤ (6192823636183/50000000000000 : ℝ)^6395
        have hw : |(-2055641743/10000000000 : ℝ)|=(2055641743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1250_s8_7 (p : ℝ) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2174844257/5000000000 : ℝ)*x 0 + (4476414113/10000000000 : ℝ)*x 1 + (33811733/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174844257/5000000000 : ℝ)^8443 ≤ (33317646200441/100000000000000 : ℝ)^6395 := by
    have hnat : (2174844257 : ℕ)^8443*100000000000000^6395 ≤ 33317646200441^6395*5000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174844257 5000000000 33317646200441 100000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4476414113/10000000000 : ℝ)^8443 ≤ (8651284841761/25000000000000 : ℝ)^6395 := by
    have hnat : (4476414113 : ℕ)^8443*25000000000000^6395 ≤ 8651284841761^6395*10000000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4476414113 10000000000 8651284841761 25000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33811733/80000000 : ℝ)^8443 ≤ (641544288313/2000000000000 : ℝ)^6395 := by
    have hnat : (33811733 : ℕ)^8443*2000000000000^6395 ≤ 641544288313^6395*80000000^8443 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33811733 80000000 641544288313 2000000000000 8443 6395 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8443/2048 : ℝ)) 8443 6395 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174844257/5000000000 : ℝ), (4476414113/10000000000 : ℝ), (33811733/80000000 : ℝ)] ![(33317646200441/100000000000000 : ℝ), (8651284841761/25000000000000 : ℝ), (641544288313/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174844257/5000000000 : ℝ)|^8443 ≤ (33317646200441/100000000000000 : ℝ)^6395
        have hw : |(2174844257/5000000000 : ℝ)|=(2174844257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4476414113/10000000000 : ℝ)|^8443 ≤ (8651284841761/25000000000000 : ℝ)^6395
        have hw : |(4476414113/10000000000 : ℝ)|=(4476414113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33811733/80000000 : ℝ)|^8443 ≤ (641544288313/2000000000000 : ℝ)^6395
        have hw : |(33811733/80000000 : ℝ)|=(33811733/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1250_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (11489/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3527/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (359/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (359/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (359/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (359/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (359/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (359/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (359/3125 : ℝ) ^ (4221/1024 : ℝ) ≤ (3343501018128233/25000000000000000000 : ℝ) := by
    have hpowers : (359/3125 : ℝ)^4221 ≤ (3343501018128233/25000000000000000000 : ℝ)^1024 := by
      have hnat : (359 : ℕ)^4221*25000000000000000000^1024 ≤ 3343501018128233^1024*3125^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        359 3125 3343501018128233 25000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (359/3125 : ℝ)) (X := (3343501018128233/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14109/100000 : ℝ) ^ (4221/1024 : ℝ) ≤ (31200652268329901/100000000000000000000 : ℝ) := by
    have hpowers : (14109/100000 : ℝ)^4221 ≤ (31200652268329901/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14109 : ℕ)^4221*100000000000000000000^1024 ≤ 31200652268329901^1024*100000^4221 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14109 100000 31200652268329901 100000000000000000000 4221 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14109/100000 : ℝ)) (X := (31200652268329901/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503343501018128233/12500000000000000000 : ℝ) ≤ (1250081103963233/1250000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (12503343501018128233/12500000000000000000 : ℝ)^1024 ≤ (1250081103963233/1250000000000000 : ℝ)^4221 := by
      have hnat : (12503343501018128233 : ℕ)^1024*1250000000000000^4221 ≤ 1250081103963233^4221*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503343501018128233 12500000000000000000 1250081103963233 1250000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250081103963233/1250000000000000 : ℝ)) (X := (12503343501018128233/12500000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044574656340842833/100000000000000000000 : ℝ) ≤ (10001081183252631/10000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (100044574656340842833/100000000000000000000 : ℝ)^1024 ≤ (10001081183252631/10000000000000000 : ℝ)^4221 := by
      have hnat : (100044574656340842833 : ℕ)^1024*10000000000000000^4221 ≤ 10001081183252631^4221*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044574656340842833 100000000000000000000 10001081183252631 10000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001081183252631/10000000000000000 : ℝ)) (X := (100044574656340842833/100000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031200652268329901/50000000000000000000 : ℝ) ≤ (5000756767399699/5000000000000000 : ℝ) ^ (4221/1024 : ℝ) := by
    have hpowers : (50031200652268329901/50000000000000000000 : ℝ)^1024 ≤ (5000756767399699/5000000000000000 : ℝ)^4221 := by
      have hnat : (50031200652268329901 : ℕ)^1024*5000000000000000^4221 ≤ 5000756767399699^4221*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031200652268329901 50000000000000000000 5000756767399699 5000000000000000 1024 4221 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000756767399699/5000000000000000 : ℝ)) (X := (50031200652268329901/50000000000000000000 : ℝ)) (by norm_num) 4221 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3343501018128233/25000000000000000000 : ℝ) ≤ ((3275220859845318869/3276250000000000000 : ℝ)+2*(432351546767/262100000000000 : ℝ)*(359/3125 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (3275220859845318869/3276250000000000000 : ℝ)+2*(432351546767/262100000000000 : ℝ)*(359/3125 : ℝ)=(1250081103963233/1250000000000000 : ℝ) by norm_num, show 1+2*(3343501018128233/25000000000000000000 : ℝ)=(12503343501018128233/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31200652268329901/100000000000000000000 : ℝ)+(3343501018128233/25000000000000000000 : ℝ) ≤ ((3275220859845318869/3276250000000000000 : ℝ)+(432351546767/262100000000000 : ℝ)*((14109/100000 : ℝ)+(359/3125 : ℝ)))^(4221/1024 : ℝ) := by
    rw [show (3275220859845318869/3276250000000000000 : ℝ)+(432351546767/262100000000000 : ℝ)*((14109/100000 : ℝ)+(359/3125 : ℝ))=(10001081183252631/10000000000000000 : ℝ) by norm_num, show 1+(31200652268329901/100000000000000000000 : ℝ)+(3343501018128233/25000000000000000000 : ℝ)=(100044574656340842833/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31200652268329901/100000000000000000000 : ℝ) ≤ ((3275220859845318869/3276250000000000000 : ℝ)+2*(432351546767/262100000000000 : ℝ)*(14109/100000 : ℝ))^(4221/1024 : ℝ) := by
    rw [show (3275220859845318869/3276250000000000000 : ℝ)+2*(432351546767/262100000000000 : ℝ)*(14109/100000 : ℝ)=(5000756767399699/5000000000000000 : ℝ) by norm_num, show 1+2*(31200652268329901/100000000000000000000 : ℝ)=(50031200652268329901/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3275220859845318869/3276250000000000000 : ℝ)*(X 1 0+X 2 0)+(432351546767/262100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (359/3125 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (3275220859845318869/3276250000000000000 : ℝ)) (alpha := (432351546767/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3275220859845318869/3276250000000000000 : ℝ)*(X 0 1+X 2 1)+(432351546767/262100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (359/3125 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (3275220859845318869/3276250000000000000 : ℝ)) (alpha := (432351546767/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3275220859845318869/3276250000000000000 : ℝ)*(X 0 2+X 1 2)+(432351546767/262100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4221/1024 : ℝ)) (lo := (359/3125 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (3275220859845318869/3276250000000000000 : ℝ)) (alpha := (432351546767/262100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529071651/2500000000 : ℝ)*X 0 0+(5391007859/10000000000 : ℝ)*X 0 1+(5267359699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213770253/400000000 : ℝ)*X 1 0+(-1089488491/5000000000 : ℝ)*X 1 1+(2633679899/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167008013/312500000 : ℝ)*X 2 0+(2633679861/5000000000 : ℝ)*X 2 1+(-2178976961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869935821/2000000000 : ℝ)*X 0 0+(4225831001/10000000000 : ℝ)*X 0 1+(4477047441/10000000000 : ℝ)*X 0 2+(869935821/2000000000 : ℝ)*X 1 0+(4225831001/10000000000 : ℝ)*X 1 1+(4477047441/10000000000 : ℝ)*X 1 2+(869935821/2000000000 : ℝ)*X 2 0+(4225831001/10000000000 : ℝ)*X 2 1+(4477047441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116291101/10000000000 : ℝ)*X 0 0+(2633835773/5000000000 : ℝ)*X 0 1+(5390694983/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312689779/10000000000 : ℝ)*X 1 0+(-2055641831/10000000000 : ℝ)*X 1 1+(5390695059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664086217/1250000000 : ℝ)*X 2 0+(5390695167/10000000000 : ℝ)*X 2 1+(-2055641743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2174844257/5000000000 : ℝ)*X 0 0+(4476414113/10000000000 : ℝ)*X 0 1+(33811733/80000000 : ℝ)*X 0 2+(2174844257/5000000000 : ℝ)*X 1 0+(4476414113/10000000000 : ℝ)*X 1 1+(33811733/80000000 : ℝ)*X 1 2+(2174844257/5000000000 : ℝ)*X 2 0+(4476414113/10000000000 : ℝ)*X 2 1+(33811733/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1250_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8230586139807261589635147/2559570312500000000000000000000 : ℝ) := by norm_num
    linear_combination (426202043/100000000000000 : ℝ)*(base19) + (104009247/20000000000000 : ℝ)*(base23) + (23443489/100000000000000 : ℝ)*(lower2) + (44840811/100000000000000 : ℝ)*(upper3) + (17926117/25000000000000 : ℝ)*(upper5) + (1508518188818887/25000000000000 : ℝ)*(major0) + (1508518188818887/25000000000000 : ℝ)*(major1) + (1508518188818887/25000000000000 : ℝ)*(major2) + (4043739608292013/50000000000000 : ℝ)*(sp0) + (8087498000741523/100000000000000 : ℝ)*(sp1) + (808749790689733/10000000000000 : ℝ)*(sp2) + (1990319429659613/50000000000000 : ℝ)*(sp3) + (19210359539/100000000000000 : ℝ)*(sp4) + (4058550603/50000000000000 : ℝ)*(sp7) + (248790436026277/6250000000000 : ℝ)*(f.failure) + (4043749213471783/50000000000000 : ℝ)*(f.sum) + (47289688530861/13105000000000000000000000000 : ℝ)*base65 + (1993516614296583697/81906250000000000000000000000000 : ℝ)*base68 + (1736865697458927447/81906250000000000000000000000000 : ℝ)*base70 + (1677081683602739947/81906250000000000000000000000000 : ℝ)*base72 + (4628219841037/6552500000000000000000000000 : ℝ)*base74 + (2795621214646521197/81906250000000000000000000000000 : ℝ)*base76 + (1474190590021646197/81906250000000000000000000000000 : ℝ)*base78 + (1396543290561333697/81906250000000000000000000000000 : ℝ)*base80 + (24180973987357/6552500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2009879/625000000000000000000 : ℝ)*base89 + (2009879/625000000000000000000 : ℝ)*base91 + (2009879/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (231824508122613185878846263/32762500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (215454951/100000000000000 : ℝ)*(base19) + (275296327/50000000000000 : ℝ)*(base23) + (9892347/20000000000000 : ℝ)*(lower1) + (111624789/100000000000000 : ℝ)*(upper3) + (79836409/50000000000000 : ℝ)*(lower4) + (50644021/100000000000000 : ℝ)*(upper5) + (1212935906595091/20000000000000 : ℝ)*(major0) + (1212935906595091/20000000000000 : ℝ)*(major1) + (1212935906595091/20000000000000 : ℝ)*(major2) + (4223447717/25000000000000 : ℝ)*(sp2) + (8128520718748393/100000000000000 : ℝ)*(sp4) + (8128520503293443/100000000000000 : ℝ)*(sp5) + (8128503274364871/100000000000000 : ℝ)*(sp6) + (62513095489669/1562500000000 : ℝ)*(sp7) + (62513095489669/1562500000000 : ℝ)*(f.failure) + (8128520718748393/100000000000000 : ℝ)*(f.sum) + (4497305318423/1310500000000000000000000000 : ℝ)*base65 + (6063976792402615421/65525000000000000000000000000000 : ℝ)*base68 + (504743568127440421/65525000000000000000000000000000 : ℝ)*base70 + (3257410332386509579/65525000000000000000000000000000 : ℝ)*base71 + (22357554111/1310500000000000000000000000 : ℝ)*base73 + (5377908391148109579/65525000000000000000000000000000 : ℝ)*base75 + (80230590956834579/65525000000000000000000000000000 : ℝ)*base77 + (59362530145509579/65525000000000000000000000000000 : ℝ)*base79 + (9620455592141/1310500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (3082363/156250000000000000000 : ℝ)*base89 + (3082363/156250000000000000000 : ℝ)*base91 + (3082363/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1250_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1250_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1250_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1250_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1250_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1250_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4221/1024 : ℝ) ≤ p) (hpb : p ≤ (8443/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151585227/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14133/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1433/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11489/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3527/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1250_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
