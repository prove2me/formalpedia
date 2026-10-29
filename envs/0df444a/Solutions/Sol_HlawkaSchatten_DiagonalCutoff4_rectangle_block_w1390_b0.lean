-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1390_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:25:38.767386+00:00
-- url     : https://prove2.me/submissions/bfc85191-4fd0-4071-b6ca-8f0aa7d025b3

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
theorem support_rectangle_w1390_s0_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-890553947/5000000000 : ℝ)*x 0 + (1195288369/2000000000 : ℝ)*x 1 + (2411115731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (890553947/5000000000 : ℝ)^2175 ≤ (1308894821853/12500000000000 : ℝ)^1663 := by
    have hnat : (890553947 : ℕ)^2175*12500000000000^1663 ≤ 1308894821853^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890553947 5000000000 1308894821853 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195288369/2000000000 : ℝ)^2175 ≤ (10201040416031/20000000000000 : ℝ)^1663 := by
    have hnat : (1195288369 : ℕ)^2175*20000000000000^1663 ≤ 10201040416031^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195288369 2000000000 10201040416031 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2411115731/5000000000 : ℝ)^2175 ≤ (9630909832729/25000000000000 : ℝ)^1663 := by
    have hnat : (2411115731 : ℕ)^2175*25000000000000^1663 ≤ 9630909832729^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411115731 5000000000 9630909832729 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-890553947/5000000000 : ℝ), (1195288369/2000000000 : ℝ), (2411115731/5000000000 : ℝ)] ![(1308894821853/12500000000000 : ℝ), (10201040416031/20000000000000 : ℝ), (9630909832729/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-890553947/5000000000 : ℝ)|^2175 ≤ (1308894821853/12500000000000 : ℝ)^1663
        have hw : |(-890553947/5000000000 : ℝ)|=(890553947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195288369/2000000000 : ℝ)|^2175 ≤ (10201040416031/20000000000000 : ℝ)^1663
        have hw : |(1195288369/2000000000 : ℝ)|=(1195288369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2411115731/5000000000 : ℝ)|^2175 ≤ (9630909832729/25000000000000 : ℝ)^1663
        have hw : |(2411115731/5000000000 : ℝ)|=(2411115731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s0_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1099289033/2000000000 : ℝ)*x 0 + (-1217450581/5000000000 : ℝ)*x 1 + (4822231573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099289033/2000000000 : ℝ)^2175 ≤ (11428757492271/25000000000000 : ℝ)^1663 := by
    have hnat : (1099289033 : ℕ)^2175*25000000000000^1663 ≤ 11428757492271^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099289033 2000000000 11428757492271 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1217450581/5000000000 : ℝ)^2175 ≤ (3940332380963/25000000000000 : ℝ)^1663 := by
    have hnat : (1217450581 : ℕ)^2175*25000000000000^1663 ≤ 3940332380963^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217450581 5000000000 3940332380963 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4822231573/10000000000 : ℝ)^2175 ≤ (38523640490679/100000000000000 : ℝ)^1663 := by
    have hnat : (4822231573 : ℕ)^2175*100000000000000^1663 ≤ 38523640490679^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822231573 10000000000 38523640490679 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1099289033/2000000000 : ℝ), (-1217450581/5000000000 : ℝ), (4822231573/10000000000 : ℝ)] ![(11428757492271/25000000000000 : ℝ), (3940332380963/25000000000000 : ℝ), (38523640490679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1099289033/2000000000 : ℝ)|^2175 ≤ (11428757492271/25000000000000 : ℝ)^1663
        have hw : |(1099289033/2000000000 : ℝ)|=(1099289033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1217450581/5000000000 : ℝ)|^2175 ≤ (3940332380963/25000000000000 : ℝ)^1663
        have hw : |(-1217450581/5000000000 : ℝ)|=(1217450581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4822231573/10000000000 : ℝ)|^2175 ≤ (38523640490679/100000000000000 : ℝ)^1663
        have hw : |(4822231573/10000000000 : ℝ)|=(4822231573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s0_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (687055647/1250000000 : ℝ)*x 0 + (2411115773/5000000000 : ℝ)*x 1 + (-1217450591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (687055647/1250000000 : ℝ)^2175 ≤ (45715030088741/100000000000000 : ℝ)^1663 := by
    have hnat : (687055647 : ℕ)^2175*100000000000000^1663 ≤ 45715030088741^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687055647 1250000000 45715030088741 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411115773/5000000000 : ℝ)^2175 ≤ (19261820104287/50000000000000 : ℝ)^1663 := by
    have hnat : (2411115773 : ℕ)^2175*50000000000000^1663 ≤ 19261820104287^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411115773 5000000000 19261820104287 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1217450591/5000000000 : ℝ)^2175 ≤ (3940332423293/25000000000000 : ℝ)^1663 := by
    have hnat : (1217450591 : ℕ)^2175*25000000000000^1663 ≤ 3940332423293^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1217450591 5000000000 3940332423293 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(687055647/1250000000 : ℝ), (2411115773/5000000000 : ℝ), (-1217450591/5000000000 : ℝ)] ![(45715030088741/100000000000000 : ℝ), (19261820104287/50000000000000 : ℝ), (3940332423293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(687055647/1250000000 : ℝ)|^2175 ≤ (45715030088741/100000000000000 : ℝ)^1663
        have hw : |(687055647/1250000000 : ℝ)|=(687055647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2411115773/5000000000 : ℝ)|^2175 ≤ (19261820104287/50000000000000 : ℝ)^1663
        have hw : |(2411115773/5000000000 : ℝ)|=(2411115773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1217450591/5000000000 : ℝ)|^2175 ≤ (3940332423293/25000000000000 : ℝ)^1663
        have hw : |(-1217450591/5000000000 : ℝ)|=(1217450591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s0_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1042911823/2500000000 : ℝ)*x 0 + (3104527599/10000000000 : ℝ)*x 1 + (556583639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042911823/2500000000 : ℝ)^2175 ≤ (6374393800221/20000000000000 : ℝ)^1663 := by
    have hnat : (1042911823 : ℕ)^2175*20000000000000^1663 ≤ 6374393800221^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042911823 2500000000 6374393800221 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3104527599/10000000000 : ℝ)^2175 ≤ (10828354565289/50000000000000 : ℝ)^1663 := by
    have hnat : (3104527599 : ℕ)^2175*50000000000000^1663 ≤ 10828354565289^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3104527599 10000000000 10828354565289 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556583639/1000000000 : ℝ)^2175 ≤ (46471321852953/100000000000000 : ℝ)^1663 := by
    have hnat : (556583639 : ℕ)^2175*100000000000000^1663 ≤ 46471321852953^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556583639 1000000000 46471321852953 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042911823/2500000000 : ℝ), (3104527599/10000000000 : ℝ), (556583639/1000000000 : ℝ)] ![(6374393800221/20000000000000 : ℝ), (10828354565289/50000000000000 : ℝ), (46471321852953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042911823/2500000000 : ℝ)|^2175 ≤ (6374393800221/20000000000000 : ℝ)^1663
        have hw : |(1042911823/2500000000 : ℝ)|=(1042911823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3104527599/10000000000 : ℝ)|^2175 ≤ (10828354565289/50000000000000 : ℝ)^1663
        have hw : |(3104527599/10000000000 : ℝ)|=(3104527599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(556583639/1000000000 : ℝ)|^2175 ≤ (46471321852953/100000000000000 : ℝ)^1663
        have hw : |(556583639/1000000000 : ℝ)|=(556583639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s0_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1785318259/10000000000 : ℝ)*x 0 + (4851846519/10000000000 : ℝ)*x 1 + (148644207/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1785318259/10000000000 : ℝ)^2175 ≤ (1312942996151/12500000000000 : ℝ)^1663 := by
    have hnat : (1785318259 : ℕ)^2175*12500000000000^1663 ≤ 1312942996151^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1785318259 10000000000 1312942996151 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4851846519/10000000000 : ℝ)^2175 ≤ (60677123281/156250000000 : ℝ)^1663 := by
    have hnat : (4851846519 : ℕ)^2175*156250000000^1663 ≤ 60677123281^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4851846519 10000000000 60677123281 156250000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148644207/250000000 : ℝ)^2175 ≤ (2533154855963/5000000000000 : ℝ)^1663 := by
    have hnat : (148644207 : ℕ)^2175*5000000000000^1663 ≤ 2533154855963^1663*250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148644207 250000000 2533154855963 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1785318259/10000000000 : ℝ), (4851846519/10000000000 : ℝ), (148644207/250000000 : ℝ)] ![(1312942996151/12500000000000 : ℝ), (60677123281/156250000000 : ℝ), (2533154855963/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1785318259/10000000000 : ℝ)|^2175 ≤ (1312942996151/12500000000000 : ℝ)^1663
        have hw : |(-1785318259/10000000000 : ℝ)|=(1785318259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4851846519/10000000000 : ℝ)|^2175 ≤ (60677123281/156250000000 : ℝ)^1663
        have hw : |(4851846519/10000000000 : ℝ)|=(4851846519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148644207/250000000 : ℝ)|^2175 ≤ (2533154855963/5000000000000 : ℝ)^1663
        have hw : |(148644207/250000000 : ℝ)|=(148644207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s0_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1295402743/2500000000 : ℝ)*x 0 + (-262272969/2000000000 : ℝ)*x 1 + (92902597/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1295402743/2500000000 : ℝ)^2175 ≤ (21160454623099/50000000000000 : ℝ)^1663 := by
    have hnat : (1295402743 : ℕ)^2175*50000000000000^1663 ≤ 21160454623099^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295402743 2500000000 21160454623099 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262272969/2000000000 : ℝ)^2175 ≤ (877002089453/12500000000000 : ℝ)^1663 := by
    have hnat : (262272969 : ℕ)^2175*12500000000000^1663 ≤ 877002089453^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262272969 2000000000 877002089453 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92902597/156250000 : ℝ)^2175 ≤ (2533153701419/5000000000000 : ℝ)^1663 := by
    have hnat : (92902597 : ℕ)^2175*5000000000000^1663 ≤ 2533153701419^1663*156250000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92902597 156250000 2533153701419 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1295402743/2500000000 : ℝ), (-262272969/2000000000 : ℝ), (92902597/156250000 : ℝ)] ![(21160454623099/50000000000000 : ℝ), (877002089453/12500000000000 : ℝ), (2533153701419/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1295402743/2500000000 : ℝ)|^2175 ≤ (21160454623099/50000000000000 : ℝ)^1663
        have hw : |(1295402743/2500000000 : ℝ)|=(1295402743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-262272969/2000000000 : ℝ)|^2175 ≤ (877002089453/12500000000000 : ℝ)^1663
        have hw : |(-262272969/2000000000 : ℝ)|=(262272969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(92902597/156250000 : ℝ)|^2175 ≤ (2533153701419/5000000000000 : ℝ)^1663
        have hw : |(92902597/156250000 : ℝ)|=(92902597/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s0_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2590803429/5000000000 : ℝ)*x 0 + (59457713/100000000 : ℝ)*x 1 + (-262272603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2590803429/5000000000 : ℝ)^2175 ≤ (10580216324997/25000000000000 : ℝ)^1663 := by
    have hnat : (2590803429 : ℕ)^2175*25000000000000^1663 ≤ 10580216324997^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590803429 5000000000 10580216324997 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (59457713/100000000 : ℝ)^2175 ≤ (12665782693723/25000000000000 : ℝ)^1663 := by
    have hnat : (59457713 : ℕ)^2175*25000000000000^1663 ≤ 12665782693723^1663*100000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59457713 100000000 12665782693723 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262272603/2000000000 : ℝ)^2175 ≤ (3508001955231/50000000000000 : ℝ)^1663 := by
    have hnat : (262272603 : ℕ)^2175*50000000000000^1663 ≤ 3508001955231^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262272603 2000000000 3508001955231 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2590803429/5000000000 : ℝ), (59457713/100000000 : ℝ), (-262272603/2000000000 : ℝ)] ![(10580216324997/25000000000000 : ℝ), (12665782693723/25000000000000 : ℝ), (3508001955231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2590803429/5000000000 : ℝ)|^2175 ≤ (10580216324997/25000000000000 : ℝ)^1663
        have hw : |(2590803429/5000000000 : ℝ)|=(2590803429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(59457713/100000000 : ℝ)|^2175 ≤ (12665782693723/25000000000000 : ℝ)^1663
        have hw : |(59457713/100000000 : ℝ)|=(59457713/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262272603/2000000000 : ℝ)|^2175 ≤ (3508001955231/50000000000000 : ℝ)^1663
        have hw : |(-262272603/2000000000 : ℝ)|=(262272603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s0_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4180617813/10000000000 : ℝ)*x 0 + (5502685547/10000000000 : ℝ)*x 1 + (3169941277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180617813/10000000000 : ℝ)^2175 ≤ (1997602211589/6250000000000 : ℝ)^1663 := by
    have hnat : (4180617813 : ℕ)^2175*6250000000000^1663 ≤ 1997602211589^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180617813 10000000000 1997602211589 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5502685547/10000000000 : ℝ)^2175 ≤ (45782923934319/100000000000000 : ℝ)^1663 := by
    have hnat : (5502685547 : ℕ)^2175*100000000000000^1663 ≤ 45782923934319^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502685547 10000000000 45782923934319 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3169941277/10000000000 : ℝ)^2175 ≤ (22255440662739/100000000000000 : ℝ)^1663 := by
    have hnat : (3169941277 : ℕ)^2175*100000000000000^1663 ≤ 22255440662739^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3169941277 10000000000 22255440662739 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180617813/10000000000 : ℝ), (5502685547/10000000000 : ℝ), (3169941277/10000000000 : ℝ)] ![(1997602211589/6250000000000 : ℝ), (45782923934319/100000000000000 : ℝ), (22255440662739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180617813/10000000000 : ℝ)|^2175 ≤ (1997602211589/6250000000000 : ℝ)^1663
        have hw : |(4180617813/10000000000 : ℝ)|=(4180617813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5502685547/10000000000 : ℝ)|^2175 ≤ (45782923934319/100000000000000 : ℝ)^1663
        have hw : |(5502685547/10000000000 : ℝ)|=(5502685547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3169941277/10000000000 : ℝ)|^2175 ≤ (22255440662739/100000000000000 : ℝ)^1663
        have hw : |(3169941277/10000000000 : ℝ)|=(3169941277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1769/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2653/10000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4349/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4349 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4349*1^1024 ≤ 0^1024*1^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4349/1024 : ℝ) ≤ (510341412943153223/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4349 ≤ (510341412943153223/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4349*25000000000000000000^1024 ≤ 510341412943153223^1024*5^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 510341412943153223 25000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (510341412943153223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4349 := by
      have hnat : (1 : ℕ)^1024*1^4349 ≤ 1^4349*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25510341412943153223/25000000000000000000 : ℝ) ≤ (10047694626767999/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (25510341412943153223/25000000000000000000 : ℝ)^1024 ≤ (10047694626767999/10000000000000000 : ℝ)^4349 := by
      have hnat : (25510341412943153223 : ℕ)^1024*10000000000000000^4349 ≤ 10047694626767999^4349*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25510341412943153223 25000000000000000000 10047694626767999 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10047694626767999/10000000000000000 : ℝ)) (X := (25510341412943153223/25000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13010341412943153223/12500000000000000000 : ℝ) ≤ (5047694626767999/5000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (13010341412943153223/12500000000000000000 : ℝ)^1024 ≤ (5047694626767999/5000000000000000 : ℝ)^4349 := by
      have hnat : (13010341412943153223 : ℕ)^1024*5000000000000000^4349 ≤ 5047694626767999^4349*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13010341412943153223 12500000000000000000 5047694626767999 5000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5047694626767999/5000000000000000 : ℝ)) (X := (13010341412943153223/12500000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(47694626767999/4000000000000000 : ℝ)*(0 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47694626767999/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(510341412943153223/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(47694626767999/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (1 : ℝ)+(47694626767999/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10047694626767999/10000000000000000 : ℝ) by norm_num, show 1+(510341412943153223/25000000000000000000 : ℝ)+(0 : ℝ)=(25510341412943153223/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(510341412943153223/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(47694626767999/4000000000000000 : ℝ)*(2/5 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(47694626767999/4000000000000000 : ℝ)*(2/5 : ℝ)=(5047694626767999/5000000000000000 : ℝ) by norm_num, show 1+2*(510341412943153223/25000000000000000000 : ℝ)=(13010341412943153223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(47694626767999/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47694626767999/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(47694626767999/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47694626767999/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(47694626767999/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (47694626767999/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-890553947/5000000000 : ℝ)*X 0 0+(1195288369/2000000000 : ℝ)*X 0 1+(2411115731/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1099289033/2000000000 : ℝ)*X 1 0+(-1217450581/5000000000 : ℝ)*X 1 1+(4822231573/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((687055647/1250000000 : ℝ)*X 2 0+(2411115773/5000000000 : ℝ)*X 2 1+(-1217450591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042911823/2500000000 : ℝ)*X 0 0+(3104527599/10000000000 : ℝ)*X 0 1+(556583639/1000000000 : ℝ)*X 0 2+(1042911823/2500000000 : ℝ)*X 1 0+(3104527599/10000000000 : ℝ)*X 1 1+(556583639/1000000000 : ℝ)*X 1 2+(1042911823/2500000000 : ℝ)*X 2 0+(3104527599/10000000000 : ℝ)*X 2 1+(556583639/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1785318259/10000000000 : ℝ)*X 0 0+(4851846519/10000000000 : ℝ)*X 0 1+(148644207/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1295402743/2500000000 : ℝ)*X 1 0+(-262272969/2000000000 : ℝ)*X 1 1+(92902597/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2590803429/5000000000 : ℝ)*X 2 0+(59457713/100000000 : ℝ)*X 2 1+(-262272603/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4180617813/10000000000 : ℝ)*X 0 0+(5502685547/10000000000 : ℝ)*X 0 1+(3169941277/10000000000 : ℝ)*X 0 2+(4180617813/10000000000 : ℝ)*X 1 0+(5502685547/10000000000 : ℝ)*X 1 1+(3169941277/10000000000 : ℝ)*X 1 2+(4180617813/10000000000 : ℝ)*X 2 0+(5502685547/10000000000 : ℝ)*X 2 1+(3169941277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (134759257799304180785037/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16267137/5000000000000 : ℝ)*(base19) + (65101579/20000000000000 : ℝ)*(base23) + (45437533/100000000000000 : ℝ)*(upper3) + (431129/50000000000000 : ℝ)*(upper4) + (19717577/50000000000000 : ℝ)*(upper5) + (318171138333679/50000000000000 : ℝ)*(major0) + (318171138333679/50000000000000 : ℝ)*(major1) + (318171138333679/50000000000000 : ℝ)*(major2) + (866394327756963/100000000000000 : ℝ)*(sp0) + (433197591460997/50000000000000 : ℝ)*(sp1) + (866395182756839/100000000000000 : ℝ)*(sp2) + (203144215258243/50000000000000 : ℝ)*(sp3) + (1180507771/100000000000000 : ℝ)*(sp4) + (569633739/100000000000000 : ℝ)*(sp7) + (203144500075113/50000000000000 : ℝ)*(f.failure) + (433197754132367/50000000000000 : ℝ)*(f.sum) + (542978970338321/100000000000000000000000000000 : ℝ)*base65 + (467318465061679/200000000000000000000000000000 : ℝ)*base68 + (655850624661679/200000000000000000000000000000 : ℝ)*base70 + (273996635338321/200000000000000000000000000000 : ℝ)*base71 + (44737149238321/100000000000000000000000000000 : ℝ)*base73 + (566260820138321/200000000000000000000000000000 : ℝ)*base75 + (47823295461679/200000000000000000000000000000 : ℝ)*base78 + (286496092938321/200000000000000000000000000000 : ℝ)*base79 + (101020473361679/100000000000000000000000000000 : ℝ)*base82 + (28131119/5000000000000000000000 : ℝ)*base89 + (28131119/5000000000000000000000 : ℝ)*base91 + (28131119/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (431286027823062274708929/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1498639011/100000000000000 : ℝ)*(base19) + (1625873803/100000000000000 : ℝ)*(base23) + (89459921/25000000000000 : ℝ)*(base39) + (229362631/100000000000000 : ℝ)*(upper2) + (313795463/100000000000000 : ℝ)*(upper5) + (167852307583139/25000000000000 : ℝ)*(major0) + (167852307583139/25000000000000 : ℝ)*(major1) + (83926109061609/12500000000000 : ℝ)*(major2) + (3721946711/100000000000000 : ℝ)*(sp1) + (1180524089/25000000000000 : ℝ)*(sp2) + (457069710896341/50000000000000 : ℝ)*(sp4) + (11426677515087/1250000000000 : ℝ)*(sp5) + (7141667434861/781250000000 : ℝ)*(sp6) + (107169598377181/25000000000000 : ℝ)*(sp7) + (107169598377181/25000000000000 : ℝ)*(f.failure) + (457069889816183/50000000000000 : ℝ)*(f.sum) + (79163441069643/100000000000000000000000000000 : ℝ)*base65 + (33682858649609/50000000000000000000000000000 : ℝ)*base68 + (138989806368861/100000000000000000000000000000 : ℝ)*base69 + (118336961699609/50000000000000000000000000000 : ℝ)*base72 + (51415826130357/100000000000000000000000000000 : ℝ)*base74 + (237151094068861/100000000000000000000000000000 : ℝ)*base75 + (115207616031139/100000000000000000000000000000 : ℝ)*base78 + (712026323231139/100000000000000000000000000000 : ℝ)*base80 + (56140974631139/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (17525403/2500000000000000000000 : ℝ)*base89 + (17525403/2500000000000000000000 : ℝ)*base91 + (17525403/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1390_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2653/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1390_s1_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-195901843/1000000000 : ℝ)*x 0 + (5621258033/10000000000 : ℝ)*x 1 + (1012684491/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (195901843/1000000000 : ℝ)^2175 ≤ (11859687128163/100000000000000 : ℝ)^1663 := by
    have hnat : (195901843 : ℕ)^2175*100000000000000^1663 ≤ 11859687128163^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      195901843 1000000000 11859687128163 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5621258033/10000000000 : ℝ)^2175 ≤ (47077450307117/100000000000000 : ℝ)^1663 := by
    have hnat : (5621258033 : ℕ)^2175*100000000000000^1663 ≤ 47077450307117^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621258033 10000000000 47077450307117 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012684491/2000000000 : ℝ)^2175 ≤ (1283214454599/3125000000000 : ℝ)^1663 := by
    have hnat : (1012684491 : ℕ)^2175*3125000000000^1663 ≤ 1283214454599^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012684491 2000000000 1283214454599 3125000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-195901843/1000000000 : ℝ), (5621258033/10000000000 : ℝ), (1012684491/2000000000 : ℝ)] ![(11859687128163/100000000000000 : ℝ), (47077450307117/100000000000000 : ℝ), (1283214454599/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-195901843/1000000000 : ℝ)|^2175 ≤ (11859687128163/100000000000000 : ℝ)^1663
        have hw : |(-195901843/1000000000 : ℝ)|=(195901843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5621258033/10000000000 : ℝ)|^2175 ≤ (47077450307117/100000000000000 : ℝ)^1663
        have hw : |(5621258033/10000000000 : ℝ)|=(5621258033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1012684491/2000000000 : ℝ)|^2175 ≤ (1283214454599/3125000000000 : ℝ)^1663
        have hw : |(1012684491/2000000000 : ℝ)|=(1012684491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s1_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2700380507/5000000000 : ℝ)*x 0 + (-451102057/2000000000 : ℝ)*x 1 + (5063423879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700380507/5000000000 : ℝ)^2175 ≤ (2792311884337/6250000000000 : ℝ)^1663 := by
    have hnat : (2700380507 : ℕ)^2175*6250000000000^1663 ≤ 2792311884337^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700380507 5000000000 2792311884337 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451102057/2000000000 : ℝ)^2175 ≤ (7130066091821/50000000000000 : ℝ)^1663 := by
    have hnat : (451102057 : ℕ)^2175*50000000000000^1663 ≤ 7130066091821^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451102057 2000000000 7130066091821 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5063423879/10000000000 : ℝ)^2175 ≤ (5132859706353/12500000000000 : ℝ)^1663 := by
    have hnat : (5063423879 : ℕ)^2175*12500000000000^1663 ≤ 5132859706353^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063423879 10000000000 5132859706353 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700380507/5000000000 : ℝ), (-451102057/2000000000 : ℝ), (5063423879/10000000000 : ℝ)] ![(2792311884337/6250000000000 : ℝ), (7130066091821/50000000000000 : ℝ), (5132859706353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700380507/5000000000 : ℝ)|^2175 ≤ (2792311884337/6250000000000 : ℝ)^1663
        have hw : |(2700380507/5000000000 : ℝ)|=(2700380507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-451102057/2000000000 : ℝ)|^2175 ≤ (7130066091821/50000000000000 : ℝ)^1663
        have hw : |(-451102057/2000000000 : ℝ)|=(451102057/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5063423879/10000000000 : ℝ)|^2175 ≤ (5132859706353/12500000000000 : ℝ)^1663
        have hw : |(5063423879/10000000000 : ℝ)|=(5063423879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s1_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (540076187/1000000000 : ℝ)*x 0 + (5063422637/10000000000 : ℝ)*x 1 + (-1127755379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540076187/1000000000 : ℝ)^2175 ≤ (8935399882129/20000000000000 : ℝ)^1663 := by
    have hnat : (540076187 : ℕ)^2175*20000000000000^1663 ≤ 8935399882129^1663*1000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540076187 1000000000 8935399882129 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5063422637/10000000000 : ℝ)^2175 ≤ (41062864477551/100000000000000 : ℝ)^1663 := by
    have hnat : (5063422637 : ℕ)^2175*100000000000000^1663 ≤ 41062864477551^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5063422637 10000000000 41062864477551 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127755379/5000000000 : ℝ)^2175 ≤ (7130068047407/50000000000000 : ℝ)^1663 := by
    have hnat : (1127755379 : ℕ)^2175*50000000000000^1663 ≤ 7130068047407^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127755379 5000000000 7130068047407 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540076187/1000000000 : ℝ), (5063422637/10000000000 : ℝ), (-1127755379/5000000000 : ℝ)] ![(8935399882129/20000000000000 : ℝ), (41062864477551/100000000000000 : ℝ), (7130068047407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540076187/1000000000 : ℝ)|^2175 ≤ (8935399882129/20000000000000 : ℝ)^1663
        have hw : |(540076187/1000000000 : ℝ)|=(540076187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5063422637/10000000000 : ℝ)|^2175 ≤ (41062864477551/100000000000000 : ℝ)^1663
        have hw : |(5063422637/10000000000 : ℝ)|=(5063422637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127755379/5000000000 : ℝ)|^2175 ≤ (7130068047407/50000000000000 : ℝ)^1663
        have hw : |(-1127755379/5000000000 : ℝ)|=(1127755379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s1_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4283700699/10000000000 : ℝ)*x 0 + (745280227/2000000000 : ℝ)*x 1 + (4915959799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283700699/10000000000 : ℝ)^2175 ≤ (32996249024863/100000000000000 : ℝ)^1663 := by
    have hnat : (4283700699 : ℕ)^2175*100000000000000^1663 ≤ 32996249024863^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283700699 10000000000 32996249024863 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745280227/2000000000 : ℝ)^2175 ≤ (13748945660631/50000000000000 : ℝ)^1663 := by
    have hnat : (745280227 : ℕ)^2175*50000000000000^1663 ≤ 13748945660631^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745280227 2000000000 13748945660631 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4915959799/10000000000 : ℝ)^2175 ≤ (4938232455977/12500000000000 : ℝ)^1663 := by
    have hnat : (4915959799 : ℕ)^2175*12500000000000^1663 ≤ 4938232455977^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4915959799 10000000000 4938232455977 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283700699/10000000000 : ℝ), (745280227/2000000000 : ℝ), (4915959799/10000000000 : ℝ)] ![(32996249024863/100000000000000 : ℝ), (13748945660631/50000000000000 : ℝ), (4938232455977/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283700699/10000000000 : ℝ)|^2175 ≤ (32996249024863/100000000000000 : ℝ)^1663
        have hw : |(4283700699/10000000000 : ℝ)|=(4283700699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(745280227/2000000000 : ℝ)|^2175 ≤ (13748945660631/50000000000000 : ℝ)^1663
        have hw : |(745280227/2000000000 : ℝ)|=(745280227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4915959799/10000000000 : ℝ)|^2175 ≤ (4938232455977/12500000000000 : ℝ)^1663
        have hw : |(4915959799/10000000000 : ℝ)|=(4915959799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s1_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1959473617/10000000000 : ℝ)*x 0 + (1267541743/2500000000 : ℝ)*x 1 + (1403598851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1959473617/10000000000 : ℝ)^2175 ≤ (1482911414177/12500000000000 : ℝ)^1663 := by
    have hnat : (1959473617 : ℕ)^2175*12500000000000^1663 ≤ 1482911414177^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1959473617 10000000000 1482911414177 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1267541743/2500000000 : ℝ)^2175 ≤ (20567206463067/50000000000000 : ℝ)^1663 := by
    have hnat : (1267541743 : ℕ)^2175*50000000000000^1663 ≤ 20567206463067^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1267541743 2500000000 20567206463067 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403598851/2500000000 : ℝ)^2175 ≤ (2350114787703/5000000000000 : ℝ)^1663 := by
    have hnat : (1403598851 : ℕ)^2175*5000000000000^1663 ≤ 2350114787703^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403598851 2500000000 2350114787703 5000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1959473617/10000000000 : ℝ), (1267541743/2500000000 : ℝ), (1403598851/2500000000 : ℝ)] ![(1482911414177/12500000000000 : ℝ), (20567206463067/50000000000000 : ℝ), (2350114787703/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1959473617/10000000000 : ℝ)|^2175 ≤ (1482911414177/12500000000000 : ℝ)^1663
        have hw : |(-1959473617/10000000000 : ℝ)|=(1959473617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1267541743/2500000000 : ℝ)|^2175 ≤ (20567206463067/50000000000000 : ℝ)^1663
        have hw : |(1267541743/2500000000 : ℝ)|=(1267541743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1403598851/2500000000 : ℝ)|^2175 ≤ (2350114787703/5000000000000 : ℝ)^1663
        have hw : |(1403598851/2500000000 : ℝ)|=(1403598851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s1_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1051089303/2000000000 : ℝ)*x 0 + (-8522693/50000000 : ℝ)*x 1 + (5614395433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051089303/2000000000 : ℝ)^2175 ≤ (8622270672167/20000000000000 : ℝ)^1663 := by
    have hnat : (1051089303 : ℕ)^2175*20000000000000^1663 ≤ 8622270672167^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051089303 2000000000 8622270672167 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8522693/50000000 : ℝ)^2175 ≤ (617896909959/6250000000000 : ℝ)^1663 := by
    have hnat : (8522693 : ℕ)^2175*6250000000000^1663 ≤ 617896909959^1663*50000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8522693 50000000 617896909959 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5614395433/10000000000 : ℝ)^2175 ≤ (47002296071587/100000000000000 : ℝ)^1663 := by
    have hnat : (5614395433 : ℕ)^2175*100000000000000^1663 ≤ 47002296071587^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614395433 10000000000 47002296071587 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051089303/2000000000 : ℝ), (-8522693/50000000 : ℝ), (5614395433/10000000000 : ℝ)] ![(8622270672167/20000000000000 : ℝ), (617896909959/6250000000000 : ℝ), (47002296071587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051089303/2000000000 : ℝ)|^2175 ≤ (8622270672167/20000000000000 : ℝ)^1663
        have hw : |(1051089303/2000000000 : ℝ)|=(1051089303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8522693/50000000 : ℝ)|^2175 ≤ (617896909959/6250000000000 : ℝ)^1663
        have hw : |(-8522693/50000000 : ℝ)|=(8522693/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5614395433/10000000000 : ℝ)|^2175 ≤ (47002296071587/100000000000000 : ℝ)^1663
        have hw : |(5614395433/10000000000 : ℝ)|=(5614395433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s1_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5255446931/10000000000 : ℝ)*x 0 + (5614395797/10000000000 : ℝ)*x 1 + (-340907497/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5255446931/10000000000 : ℝ)^2175 ≤ (8622271564799/20000000000000 : ℝ)^1663 := by
    have hnat : (5255446931 : ℕ)^2175*20000000000000^1663 ≤ 8622271564799^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255446931 10000000000 8622271564799 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5614395797/10000000000 : ℝ)^2175 ≤ (23501150028551/50000000000000 : ℝ)^1663 := by
    have hnat : (5614395797 : ℕ)^2175*50000000000000^1663 ≤ 23501150028551^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614395797 10000000000 23501150028551 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340907497/2000000000 : ℝ)^2175 ≤ (9886342101279/100000000000000 : ℝ)^1663 := by
    have hnat : (340907497 : ℕ)^2175*100000000000000^1663 ≤ 9886342101279^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340907497 2000000000 9886342101279 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5255446931/10000000000 : ℝ), (5614395797/10000000000 : ℝ), (-340907497/2000000000 : ℝ)] ![(8622271564799/20000000000000 : ℝ), (23501150028551/50000000000000 : ℝ), (9886342101279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5255446931/10000000000 : ℝ)|^2175 ≤ (8622271564799/20000000000000 : ℝ)^1663
        have hw : |(5255446931/10000000000 : ℝ)|=(5255446931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5614395797/10000000000 : ℝ)|^2175 ≤ (23501150028551/50000000000000 : ℝ)^1663
        have hw : |(5614395797/10000000000 : ℝ)|=(5614395797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-340907497/2000000000 : ℝ)|^2175 ≤ (9886342101279/100000000000000 : ℝ)^1663
        have hw : |(-340907497/2000000000 : ℝ)|=(340907497/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s1_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4284672901/10000000000 : ℝ)*x 0 + (245078897/500000000 : ℝ)*x 1 + (3741032781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284672901/10000000000 : ℝ)^2175 ≤ (33006043567193/100000000000000 : ℝ)^1663 := by
    have hnat : (4284672901 : ℕ)^2175*100000000000000^1663 ≤ 33006043567193^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284672901 10000000000 33006043567193 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245078897/500000000 : ℝ)^2175 ≤ (9838692085927/25000000000000 : ℝ)^1663 := by
    have hnat : (245078897 : ℕ)^2175*25000000000000^1663 ≤ 9838692085927^1663*500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245078897 500000000 9838692085927 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3741032781/10000000000 : ℝ)^2175 ≤ (13819594035567/50000000000000 : ℝ)^1663 := by
    have hnat : (3741032781 : ℕ)^2175*50000000000000^1663 ≤ 13819594035567^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741032781 10000000000 13819594035567 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284672901/10000000000 : ℝ), (245078897/500000000 : ℝ), (3741032781/10000000000 : ℝ)] ![(33006043567193/100000000000000 : ℝ), (9838692085927/25000000000000 : ℝ), (13819594035567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284672901/10000000000 : ℝ)|^2175 ≤ (33006043567193/100000000000000 : ℝ)^1663
        have hw : |(4284672901/10000000000 : ℝ)|=(4284672901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(245078897/500000000 : ℝ)|^2175 ≤ (9838692085927/25000000000000 : ℝ)^1663
        have hw : |(245078897/500000000 : ℝ)|=(245078897/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3741032781/10000000000 : ℝ)|^2175 ≤ (13819594035567/50000000000000 : ℝ)^1663
        have hw : |(3741032781/10000000000 : ℝ)|=(3741032781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2653/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3661/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19113/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2653/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2653/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2653/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2653/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2653/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2653/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1769/100000 : ℝ) ^ (4349/1024 : ℝ) ≤ (3613906396391/100000000000000000000 : ℝ) := by
    have hpowers : (1769/100000 : ℝ)^4349 ≤ (3613906396391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1769 : ℕ)^4349*100000000000000000000^1024 ≤ 3613906396391^1024*100000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1769 100000 3613906396391 100000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1769/100000 : ℝ)) (X := (3613906396391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2653/10000 : ℝ) ^ (4349/1024 : ℝ) ≤ (356920573550478119/100000000000000000000 : ℝ) := by
    have hpowers : (2653/10000 : ℝ)^4349 ≤ (356920573550478119/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2653 : ℕ)^4349*100000000000000000000^1024 ≤ 356920573550478119^1024*10000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2653 10000 356920573550478119 100000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2653/10000 : ℝ)) (X := (356920573550478119/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000003613906396391/50000000000000000000 : ℝ) ≤ (10000000170183493/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50000003613906396391/50000000000000000000 : ℝ)^1024 ≤ (10000000170183493/10000000000000000 : ℝ)^4349 := by
      have hnat : (50000003613906396391 : ℕ)^1024*10000000000000000^4349 ≤ 10000000170183493^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000003613906396391 50000000000000000000 10000000170183493 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000170183493/10000000000000000 : ℝ)) (X := (50000003613906396391/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10035692418745687451/10000000000000000000 : ℝ) ≤ (10008392566791351/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (10035692418745687451/10000000000000000000 : ℝ)^1024 ≤ (10008392566791351/10000000000000000 : ℝ)^4349 := by
      have hnat : (10035692418745687451 : ℕ)^1024*10000000000000000^4349 ≤ 10008392566791351^4349*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10035692418745687451 10000000000000000000 10008392566791351 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008392566791351/10000000000000000 : ℝ)) (X := (10035692418745687451/10000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50356920573550478119/50000000000000000000 : ℝ) ≤ (10016784963399209/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50356920573550478119/50000000000000000000 : ℝ)^1024 ≤ (10016784963399209/10000000000000000 : ℝ)^4349 := by
      have hnat : (50356920573550478119 : ℕ)^1024*10000000000000000^4349 ≤ 10016784963399209^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50356920573550478119 50000000000000000000 10016784963399209 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10016784963399209/10000000000000000 : ℝ)) (X := (50356920573550478119/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3613906396391/100000000000000000000 : ℝ) ≤ ((247580311914714868569/247610000000000000000 : ℝ)+2*(4196198303929/1238050000000000 : ℝ)*(1769/100000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (247580311914714868569/247610000000000000000 : ℝ)+2*(4196198303929/1238050000000000 : ℝ)*(1769/100000 : ℝ)=(10000000170183493/10000000000000000 : ℝ) by norm_num, show 1+2*(3613906396391/100000000000000000000 : ℝ)=(50000003613906396391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(356920573550478119/100000000000000000000 : ℝ)+(3613906396391/100000000000000000000 : ℝ) ≤ ((247580311914714868569/247610000000000000000 : ℝ)+(4196198303929/1238050000000000 : ℝ)*((2653/10000 : ℝ)+(1769/100000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (247580311914714868569/247610000000000000000 : ℝ)+(4196198303929/1238050000000000 : ℝ)*((2653/10000 : ℝ)+(1769/100000 : ℝ))=(10008392566791351/10000000000000000 : ℝ) by norm_num, show 1+(356920573550478119/100000000000000000000 : ℝ)+(3613906396391/100000000000000000000 : ℝ)=(10035692418745687451/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(356920573550478119/100000000000000000000 : ℝ) ≤ ((247580311914714868569/247610000000000000000 : ℝ)+2*(4196198303929/1238050000000000 : ℝ)*(2653/10000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (247580311914714868569/247610000000000000000 : ℝ)+2*(4196198303929/1238050000000000 : ℝ)*(2653/10000 : ℝ)=(10016784963399209/10000000000000000 : ℝ) by norm_num, show 1+2*(356920573550478119/100000000000000000000 : ℝ)=(50356920573550478119/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (247580311914714868569/247610000000000000000 : ℝ)*(X 1 0+X 2 0)+(4196198303929/1238050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (1769/100000 : ℝ)) (hi := (2653/10000 : ℝ)) (c := (247580311914714868569/247610000000000000000 : ℝ)) (alpha := (4196198303929/1238050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (247580311914714868569/247610000000000000000 : ℝ)*(X 0 1+X 2 1)+(4196198303929/1238050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (1769/100000 : ℝ)) (hi := (2653/10000 : ℝ)) (c := (247580311914714868569/247610000000000000000 : ℝ)) (alpha := (4196198303929/1238050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (247580311914714868569/247610000000000000000 : ℝ)*(X 0 2+X 1 2)+(4196198303929/1238050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (1769/100000 : ℝ)) (hi := (2653/10000 : ℝ)) (c := (247580311914714868569/247610000000000000000 : ℝ)) (alpha := (4196198303929/1238050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-195901843/1000000000 : ℝ)*X 0 0+(5621258033/10000000000 : ℝ)*X 0 1+(1012684491/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2700380507/5000000000 : ℝ)*X 1 0+(-451102057/2000000000 : ℝ)*X 1 1+(5063423879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((540076187/1000000000 : ℝ)*X 2 0+(5063422637/10000000000 : ℝ)*X 2 1+(-1127755379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283700699/10000000000 : ℝ)*X 0 0+(745280227/2000000000 : ℝ)*X 0 1+(4915959799/10000000000 : ℝ)*X 0 2+(4283700699/10000000000 : ℝ)*X 1 0+(745280227/2000000000 : ℝ)*X 1 1+(4915959799/10000000000 : ℝ)*X 1 2+(4283700699/10000000000 : ℝ)*X 2 0+(745280227/2000000000 : ℝ)*X 2 1+(4915959799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1959473617/10000000000 : ℝ)*X 0 0+(1267541743/2500000000 : ℝ)*X 0 1+(1403598851/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1051089303/2000000000 : ℝ)*X 1 0+(-8522693/50000000 : ℝ)*X 1 1+(5614395433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5255446931/10000000000 : ℝ)*X 2 0+(5614395797/10000000000 : ℝ)*X 2 1+(-340907497/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4284672901/10000000000 : ℝ)*X 0 0+(245078897/500000000 : ℝ)*X 0 1+(3741032781/10000000000 : ℝ)*X 0 2+(4284672901/10000000000 : ℝ)*X 1 0+(245078897/500000000 : ℝ)*X 1 1+(3741032781/10000000000 : ℝ)*X 1 2+(4284672901/10000000000 : ℝ)*X 2 0+(245078897/500000000 : ℝ)*X 2 1+(3741032781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11773422401571573430797330009/6190250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171256261/100000000000000 : ℝ)*(base19) + (256722031/50000000000000 : ℝ)*(base23) + (20287861/50000000000000 : ℝ)*(upper2) + (2977827/100000000000000 : ℝ)*(upper3) + (1316652675940587/100000000000000 : ℝ)*(major0) + (1316652675940587/100000000000000 : ℝ)*(major1) + (1316652675940587/100000000000000 : ℝ)*(major2) + (11204053764771/625000000000 : ℝ)*(sp0) + (1792654544622497/100000000000000 : ℝ)*(sp1) + (14005105999901/781250000000 : ℝ)*(sp2) + (840649093834749/100000000000000 : ℝ)*(sp3) + (6113515397/100000000000000 : ℝ)*(sp4) + (79305921/12500000000000 : ℝ)*(sp6) + (739384997/50000000000000 : ℝ)*(sp7) + (840650572604743/100000000000000 : ℝ)*(f.failure) + (896327357939379/50000000000000 : ℝ)*(f.sum) + (131729552287067/61902500000000000000000000000 : ℝ)*base66 + (78665777669456689997/24761000000000000000000000000000000 : ℝ)*base68 + (75629875290189310003/24761000000000000000000000000000000 : ℝ)*base69 + (119752766324960689997/24761000000000000000000000000000000 : ℝ)*base72 + (1226374492219/7737812500000000000000000000 : ℝ)*base74 + (222916514504485689997/24761000000000000000000000000000000 : ℝ)*base76 + (159302991891570689997/24761000000000000000000000000000000 : ℝ)*base78 + (142388643694604689997/24761000000000000000000000000000000 : ℝ)*base80 + (408164664477541/123805000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (36987809/10000000000000000000000 : ℝ)*base89 + (36987809/10000000000000000000000 : ℝ)*base91 + (36987809/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (75056616633863415918429268209/12380500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188238937/100000000000000 : ℝ)*(base1) + (1558253221/100000000000000 : ℝ)*(base19) + (448406857/25000000000000 : ℝ)*(base23) + (151029871/100000000000000 : ℝ)*(upper3) + (114114433/50000000000000 : ℝ)*(upper5) + (1349564712347729/100000000000000 : ℝ)*(major0) + (1349564712347729/100000000000000 : ℝ)*(major1) + (1349564712347729/100000000000000 : ℝ)*(major2) + (1960183957/25000000000000 : ℝ)*(sp1) + (2773259963/25000000000000 : ℝ)*(sp2) + (918732653460409/50000000000000 : ℝ)*(sp4) + (57420491240401/3125000000000 : ℝ)*(sp5) + (918726116007301/50000000000000 : ℝ)*(sp6) + (43083195784587/5000000000000 : ℝ)*(sp7) + (215416025982669/25000000000000 : ℝ)*(f.failure) + (1837465118681881/100000000000000 : ℝ)*(f.sum) + (1860578882421/967226562500000000000000000 : ℝ)*base66 + (193724374942547170199/24761000000000000000000000000000000 : ℝ)*base68 + (164011440281423170199/24761000000000000000000000000000000 : ℝ)*base70 + (180942477243823170199/24761000000000000000000000000000000 : ℝ)*base72 + (220995205444309/61902500000000000000000000000 : ℝ)*base74 + (30266201110979170199/24761000000000000000000000000000000 : ℝ)*base76 + (264135466322253170199/24761000000000000000000000000000000 : ℝ)*base78 + (85482515765689170199/24761000000000000000000000000000000 : ℝ)*base80 + (55727551179561/15475625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (21304853/2500000000000000000000 : ℝ)*base90 + (21304853/2500000000000000000000 : ℝ)*base92 + (21304853/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1390_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2653/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3661/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19113/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1390_s2_0 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-498791241/2500000000 : ℝ)*x 0 + (5467311901/10000000000 : ℝ)*x 1 + (129853799/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (498791241/2500000000 : ℝ)^2175 ≤ (6073347893033/50000000000000 : ℝ)^1663 := by
    have hnat : (498791241 : ℕ)^2175*50000000000000^1663 ≤ 6073347893033^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498791241 2500000000 6073347893033 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467311901/10000000000 : ℝ)^2175 ≤ (11349595204007/25000000000000 : ℝ)^1663 := by
    have hnat : (5467311901 : ℕ)^2175*25000000000000^1663 ≤ 11349595204007^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467311901 10000000000 11349595204007 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129853799/250000000 : ℝ)^2175 ≤ (2653432711907/6250000000000 : ℝ)^1663 := by
    have hnat : (129853799 : ℕ)^2175*6250000000000^1663 ≤ 2653432711907^1663*250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129853799 250000000 2653432711907 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-498791241/2500000000 : ℝ), (5467311901/10000000000 : ℝ), (129853799/250000000 : ℝ)] ![(6073347893033/50000000000000 : ℝ), (11349595204007/25000000000000 : ℝ), (2653432711907/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-498791241/2500000000 : ℝ)|^2175 ≤ (6073347893033/50000000000000 : ℝ)^1663
        have hw : |(-498791241/2500000000 : ℝ)|=(498791241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467311901/10000000000 : ℝ)|^2175 ≤ (11349595204007/25000000000000 : ℝ)^1663
        have hw : |(5467311901/10000000000 : ℝ)|=(5467311901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129853799/250000000 : ℝ)|^2175 ≤ (2653432711907/6250000000000 : ℝ)^1663
        have hw : |(129853799/250000000 : ℝ)|=(129853799/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s2_1 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681335511/5000000000 : ℝ)*x 0 + (-533989657/2500000000 : ℝ)*x 1 + (51941519/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681335511/5000000000 : ℝ)^2175 ≤ (44265334284087/100000000000000 : ℝ)^1663 := by
    have hnat : (2681335511 : ℕ)^2175*100000000000000^1663 ≤ 44265334284087^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681335511 5000000000 44265334284087 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533989657/2500000000 : ℝ)^2175 ≤ (13279742955641/100000000000000 : ℝ)^1663 := by
    have hnat : (533989657 : ℕ)^2175*100000000000000^1663 ≤ 13279742955641^1663*2500000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533989657 2500000000 13279742955641 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51941519/100000000 : ℝ)^2175 ≤ (10613730687277/25000000000000 : ℝ)^1663 := by
    have hnat : (51941519 : ℕ)^2175*25000000000000^1663 ≤ 10613730687277^1663*100000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51941519 100000000 10613730687277 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681335511/5000000000 : ℝ), (-533989657/2500000000 : ℝ), (51941519/100000000 : ℝ)] ![(44265334284087/100000000000000 : ℝ), (13279742955641/100000000000000 : ℝ), (10613730687277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681335511/5000000000 : ℝ)|^2175 ≤ (44265334284087/100000000000000 : ℝ)^1663
        have hw : |(2681335511/5000000000 : ℝ)|=(2681335511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-533989657/2500000000 : ℝ)|^2175 ≤ (13279742955641/100000000000000 : ℝ)^1663
        have hw : |(-533989657/2500000000 : ℝ)|=(533989657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51941519/100000000 : ℝ)|^2175 ≤ (10613730687277/25000000000000 : ℝ)^1663
        have hw : |(51941519/100000000 : ℝ)|=(51941519/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s2_2 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2681335429/5000000000 : ℝ)*x 0 + (207766083/400000000 : ℝ)*x 1 + (-266994827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681335429/5000000000 : ℝ)^2175 ≤ (44265332513597/100000000000000 : ℝ)^1663 := by
    have hnat : (2681335429 : ℕ)^2175*100000000000000^1663 ≤ 44265332513597^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681335429 5000000000 44265332513597 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207766083/400000000 : ℝ)^2175 ≤ (42454924619869/100000000000000 : ℝ)^1663 := by
    have hnat : (207766083 : ℕ)^2175*100000000000000^1663 ≤ 42454924619869^1663*400000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207766083 400000000 42454924619869 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266994827/1250000000 : ℝ)^2175 ≤ (829983928629/6250000000000 : ℝ)^1663 := by
    have hnat : (266994827 : ℕ)^2175*6250000000000^1663 ≤ 829983928629^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266994827 1250000000 829983928629 6250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681335429/5000000000 : ℝ), (207766083/400000000 : ℝ), (-266994827/1250000000 : ℝ)] ![(44265332513597/100000000000000 : ℝ), (42454924619869/100000000000000 : ℝ), (829983928629/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681335429/5000000000 : ℝ)|^2175 ≤ (44265332513597/100000000000000 : ℝ)^1663
        have hw : |(2681335429/5000000000 : ℝ)|=(2681335429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207766083/400000000 : ℝ)|^2175 ≤ (42454924619869/100000000000000 : ℝ)^1663
        have hw : |(207766083/400000000 : ℝ)|=(207766083/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266994827/1250000000 : ℝ)|^2175 ≤ (829983928629/6250000000000 : ℝ)^1663
        have hw : |(-266994827/1250000000 : ℝ)|=(266994827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s2_3 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2154556361/5000000000 : ℝ)*x 0 + (2013423067/5000000000 : ℝ)*x 1 + (4609349467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154556361/5000000000 : ℝ)^2175 ≤ (33252489412579/100000000000000 : ℝ)^1663 := by
    have hnat : (2154556361 : ℕ)^2175*100000000000000^1663 ≤ 33252489412579^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154556361 5000000000 33252489412579 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2013423067/5000000000 : ℝ)^2175 ≤ (15216428500717/50000000000000 : ℝ)^1663 := by
    have hnat : (2013423067 : ℕ)^2175*50000000000000^1663 ≤ 15216428500717^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013423067 5000000000 15216428500717 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4609349467/10000000000 : ℝ)^2175 ≤ (18157326786651/50000000000000 : ℝ)^1663 := by
    have hnat : (4609349467 : ℕ)^2175*50000000000000^1663 ≤ 18157326786651^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4609349467 10000000000 18157326786651 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154556361/5000000000 : ℝ), (2013423067/5000000000 : ℝ), (4609349467/10000000000 : ℝ)] ![(33252489412579/100000000000000 : ℝ), (15216428500717/50000000000000 : ℝ), (18157326786651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154556361/5000000000 : ℝ)|^2175 ≤ (33252489412579/100000000000000 : ℝ)^1663
        have hw : |(2154556361/5000000000 : ℝ)|=(2154556361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2013423067/5000000000 : ℝ)|^2175 ≤ (15216428500717/50000000000000 : ℝ)^1663
        have hw : |(2013423067/5000000000 : ℝ)|=(2013423067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4609349467/10000000000 : ℝ)|^2175 ≤ (18157326786651/50000000000000 : ℝ)^1663
        have hw : |(4609349467/10000000000 : ℝ)|=(4609349467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s2_4 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1995218167/10000000000 : ℝ)*x 0 + (162368087/312500000 : ℝ)*x 1 + (1093134277/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1995218167/10000000000 : ℝ)^2175 ≤ (151838992671/1250000000000 : ℝ)^1663 := by
    have hnat : (1995218167 : ℕ)^2175*1250000000000^1663 ≤ 151838992671^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1995218167 10000000000 151838992671 1250000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162368087/312500000 : ℝ)^2175 ≤ (21236157543151/50000000000000 : ℝ)^1663 := by
    have hnat : (162368087 : ℕ)^2175*50000000000000^1663 ≤ 21236157543151^1663*312500000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162368087 312500000 21236157543151 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093134277/2000000000 : ℝ)^2175 ≤ (45380565483481/100000000000000 : ℝ)^1663 := by
    have hnat : (1093134277 : ℕ)^2175*100000000000000^1663 ≤ 45380565483481^1663*2000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093134277 2000000000 45380565483481 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1995218167/10000000000 : ℝ), (162368087/312500000 : ℝ), (1093134277/2000000000 : ℝ)] ![(151838992671/1250000000000 : ℝ), (21236157543151/50000000000000 : ℝ), (45380565483481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1995218167/10000000000 : ℝ)|^2175 ≤ (151838992671/1250000000000 : ℝ)^1663
        have hw : |(-1995218167/10000000000 : ℝ)|=(1995218167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162368087/312500000 : ℝ)|^2175 ≤ (21236157543151/50000000000000 : ℝ)^1663
        have hw : |(162368087/312500000 : ℝ)|=(162368087/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093134277/2000000000 : ℝ)|^2175 ≤ (45380565483481/100000000000000 : ℝ)^1663
        have hw : |(1093134277/2000000000 : ℝ)|=(1093134277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s2_5 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645954721/5000000000 : ℝ)*x 0 + (-1864439781/10000000000 : ℝ)*x 1 + (5465671071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645954721/5000000000 : ℝ)^2175 ≤ (5437871509143/12500000000000 : ℝ)^1663 := by
    have hnat : (2645954721 : ℕ)^2175*12500000000000^1663 ≤ 5437871509143^1663*5000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645954721 5000000000 5437871509143 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1864439781/10000000000 : ℝ)^2175 ≤ (2779116459091/25000000000000 : ℝ)^1663 := by
    have hnat : (1864439781 : ℕ)^2175*25000000000000^1663 ≤ 2779116459091^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864439781 10000000000 2779116459091 25000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465671071/10000000000 : ℝ)^2175 ≤ (45380562073727/100000000000000 : ℝ)^1663 := by
    have hnat : (5465671071 : ℕ)^2175*100000000000000^1663 ≤ 45380562073727^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465671071 10000000000 45380562073727 100000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645954721/5000000000 : ℝ), (-1864439781/10000000000 : ℝ), (5465671071/10000000000 : ℝ)] ![(5437871509143/12500000000000 : ℝ), (2779116459091/25000000000000 : ℝ), (45380562073727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645954721/5000000000 : ℝ)|^2175 ≤ (5437871509143/12500000000000 : ℝ)^1663
        have hw : |(2645954721/5000000000 : ℝ)|=(2645954721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1864439781/10000000000 : ℝ)|^2175 ≤ (2779116459091/25000000000000 : ℝ)^1663
        have hw : |(-1864439781/10000000000 : ℝ)|=(1864439781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465671071/10000000000 : ℝ)|^2175 ≤ (45380562073727/100000000000000 : ℝ)^1663
        have hw : |(5465671071/10000000000 : ℝ)|=(5465671071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s2_6 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5291910883/10000000000 : ℝ)*x 0 + (5465671089/10000000000 : ℝ)*x 1 + (-233054721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5291910883/10000000000 : ℝ)^2175 ≤ (5437873445777/12500000000000 : ℝ)^1663 := by
    have hnat : (5291910883 : ℕ)^2175*12500000000000^1663 ≤ 5437873445777^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5291910883 10000000000 5437873445777 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465671089/10000000000 : ℝ)^2175 ≤ (4538056226919/10000000000000 : ℝ)^1663 := by
    have hnat : (5465671089 : ℕ)^2175*10000000000000^1663 ≤ 4538056226919^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465671089 10000000000 4538056226919 10000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233054721/1250000000 : ℝ)^2175 ≤ (5558225069457/50000000000000 : ℝ)^1663 := by
    have hnat : (233054721 : ℕ)^2175*50000000000000^1663 ≤ 5558225069457^1663*1250000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233054721 1250000000 5558225069457 50000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5291910883/10000000000 : ℝ), (5465671089/10000000000 : ℝ), (-233054721/1250000000 : ℝ)] ![(5437873445777/12500000000000 : ℝ), (4538056226919/10000000000000 : ℝ), (5558225069457/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5291910883/10000000000 : ℝ)|^2175 ≤ (5437873445777/12500000000000 : ℝ)^1663
        have hw : |(5291910883/10000000000 : ℝ)|=(5291910883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465671089/10000000000 : ℝ)|^2175 ≤ (4538056226919/10000000000000 : ℝ)^1663
        have hw : |(5465671089/10000000000 : ℝ)|=(5465671089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233054721/1250000000 : ℝ)|^2175 ≤ (5558225069457/50000000000000 : ℝ)^1663
        have hw : |(-233054721/1250000000 : ℝ)|=(233054721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1390_s2_7 (p : ℝ) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4309227609/10000000000 : ℝ)*x 0 + (4605880847/10000000000 : ℝ)*x 1 + (4030343879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309227609/10000000000 : ℝ)^2175 ≤ (4156706115821/12500000000000 : ℝ)^1663 := by
    have hnat : (4309227609 : ℕ)^2175*12500000000000^1663 ≤ 4156706115821^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309227609 10000000000 4156706115821 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4605880847/10000000000 : ℝ)^2175 ≤ (4534864596431/12500000000000 : ℝ)^1663 := by
    have hnat : (4605880847 : ℕ)^2175*12500000000000^1663 ≤ 4534864596431^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4605880847 10000000000 4534864596431 12500000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4030343879/10000000000 : ℝ)^2175 ≤ (6093486857473/20000000000000 : ℝ)^1663 := by
    have hnat : (4030343879 : ℕ)^2175*20000000000000^1663 ≤ 6093486857473^1663*10000000000^2175 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030343879 10000000000 6093486857473 20000000000000 2175 1663 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2175/512 : ℝ)) 2175 1663 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309227609/10000000000 : ℝ), (4605880847/10000000000 : ℝ), (4030343879/10000000000 : ℝ)] ![(4156706115821/12500000000000 : ℝ), (4534864596431/12500000000000 : ℝ), (6093486857473/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309227609/10000000000 : ℝ)|^2175 ≤ (4156706115821/12500000000000 : ℝ)^1663
        have hw : |(4309227609/10000000000 : ℝ)|=(4309227609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4605880847/10000000000 : ℝ)|^2175 ≤ (4534864596431/12500000000000 : ℝ)^1663
        have hw : |(4605880847/10000000000 : ℝ)|=(4605880847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4030343879/10000000000 : ℝ)|^2175 ≤ (6093486857473/20000000000000 : ℝ)^1663
        have hw : |(4030343879/10000000000 : ℝ)|=(4030343879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1390_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10149/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7963/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19113/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3661/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19113/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3661/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19113/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3661/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3661/50000 : ℝ) ^ (4349/1024 : ℝ) ≤ (188327014817159/12500000000000000000 : ℝ) := by
    have hpowers : (3661/50000 : ℝ)^4349 ≤ (188327014817159/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3661 : ℕ)^4349*12500000000000000000^1024 ≤ 188327014817159^1024*50000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3661 50000 188327014817159 12500000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3661/50000 : ℝ)) (X := (188327014817159/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19113/100000 : ℝ) ^ (4349/1024 : ℝ) ≤ (44332593669004237/50000000000000000000 : ℝ) := by
    have hpowers : (19113/100000 : ℝ)^4349 ≤ (44332593669004237/50000000000000000000 : ℝ)^1024 := by
      have hnat : (19113 : ℕ)^4349*50000000000000000000^1024 ≤ 44332593669004237^1024*100000^4349 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19113 100000 44332593669004237 50000000000000000000 4349 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19113/100000 : ℝ)) (X := (44332593669004237/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250188327014817159/6250000000000000000 : ℝ) ≤ (10000070947672333/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (6250188327014817159/6250000000000000000 : ℝ)^1024 ≤ (10000070947672333/10000000000000000 : ℝ)^4349 := by
      have hnat : (6250188327014817159 : ℕ)^1024*10000000000000000^4349 ≤ 10000070947672333^4349*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250188327014817159 6250000000000000000 10000070947672333 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000070947672333/10000000000000000 : ℝ)) (X := (6250188327014817159/6250000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50045085901728272873/50000000000000000000 : ℝ) ≤ (10002122421597839/10000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (50045085901728272873/50000000000000000000 : ℝ)^1024 ≤ (10002122421597839/10000000000000000 : ℝ)^4349 := by
      have hnat : (50045085901728272873 : ℕ)^1024*10000000000000000^4349 ≤ 10002122421597839^4349*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50045085901728272873 50000000000000000000 10002122421597839 10000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002122421597839/10000000000000000 : ℝ)) (X := (50045085901728272873/50000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25044332593669004237/25000000000000000000 : ℝ) ≤ (2000834779104669/2000000000000000 : ℝ) ^ (4349/1024 : ℝ) := by
    have hpowers : (25044332593669004237/25000000000000000000 : ℝ)^1024 ≤ (2000834779104669/2000000000000000 : ℝ)^4349 := by
      have hnat : (25044332593669004237 : ℕ)^1024*2000000000000000^4349 ≤ 2000834779104669^4349*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25044332593669004237 25000000000000000000 2000834779104669 2000000000000000 1024 4349 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000834779104669/2000000000000000 : ℝ)) (X := (25044332593669004237/25000000000000000000 : ℝ)) (by norm_num) 4349 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(188327014817159/12500000000000000000 : ℝ) ≤ ((117880794759839368539/117910000000000000000 : ℝ)+2*(1025736962753/589550000000000 : ℝ)*(3661/50000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (117880794759839368539/117910000000000000000 : ℝ)+2*(1025736962753/589550000000000 : ℝ)*(3661/50000 : ℝ)=(10000070947672333/10000000000000000 : ℝ) by norm_num, show 1+2*(188327014817159/12500000000000000000 : ℝ)=(6250188327014817159/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(44332593669004237/50000000000000000000 : ℝ)+(188327014817159/12500000000000000000 : ℝ) ≤ ((117880794759839368539/117910000000000000000 : ℝ)+(1025736962753/589550000000000 : ℝ)*((19113/100000 : ℝ)+(3661/50000 : ℝ)))^(4349/1024 : ℝ) := by
    rw [show (117880794759839368539/117910000000000000000 : ℝ)+(1025736962753/589550000000000 : ℝ)*((19113/100000 : ℝ)+(3661/50000 : ℝ))=(10002122421597839/10000000000000000 : ℝ) by norm_num, show 1+(44332593669004237/50000000000000000000 : ℝ)+(188327014817159/12500000000000000000 : ℝ)=(50045085901728272873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(44332593669004237/50000000000000000000 : ℝ) ≤ ((117880794759839368539/117910000000000000000 : ℝ)+2*(1025736962753/589550000000000 : ℝ)*(19113/100000 : ℝ))^(4349/1024 : ℝ) := by
    rw [show (117880794759839368539/117910000000000000000 : ℝ)+2*(1025736962753/589550000000000 : ℝ)*(19113/100000 : ℝ)=(2000834779104669/2000000000000000 : ℝ) by norm_num, show 1+2*(44332593669004237/50000000000000000000 : ℝ)=(25044332593669004237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (117880794759839368539/117910000000000000000 : ℝ)*(X 1 0+X 2 0)+(1025736962753/589550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (3661/50000 : ℝ)) (hi := (19113/100000 : ℝ)) (c := (117880794759839368539/117910000000000000000 : ℝ)) (alpha := (1025736962753/589550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (117880794759839368539/117910000000000000000 : ℝ)*(X 0 1+X 2 1)+(1025736962753/589550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (3661/50000 : ℝ)) (hi := (19113/100000 : ℝ)) (c := (117880794759839368539/117910000000000000000 : ℝ)) (alpha := (1025736962753/589550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (117880794759839368539/117910000000000000000 : ℝ)*(X 0 2+X 1 2)+(1025736962753/589550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4349/1024 : ℝ)) (lo := (3661/50000 : ℝ)) (hi := (19113/100000 : ℝ)) (c := (117880794759839368539/117910000000000000000 : ℝ)) (alpha := (1025736962753/589550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-498791241/2500000000 : ℝ)*X 0 0+(5467311901/10000000000 : ℝ)*X 0 1+(129853799/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2681335511/5000000000 : ℝ)*X 1 0+(-533989657/2500000000 : ℝ)*X 1 1+(51941519/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681335429/5000000000 : ℝ)*X 2 0+(207766083/400000000 : ℝ)*X 2 1+(-266994827/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2154556361/5000000000 : ℝ)*X 0 0+(2013423067/5000000000 : ℝ)*X 0 1+(4609349467/10000000000 : ℝ)*X 0 2+(2154556361/5000000000 : ℝ)*X 1 0+(2013423067/5000000000 : ℝ)*X 1 1+(4609349467/10000000000 : ℝ)*X 1 2+(2154556361/5000000000 : ℝ)*X 2 0+(2013423067/5000000000 : ℝ)*X 2 1+(4609349467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1995218167/10000000000 : ℝ)*X 0 0+(162368087/312500000 : ℝ)*X 0 1+(1093134277/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645954721/5000000000 : ℝ)*X 1 0+(-1864439781/10000000000 : ℝ)*X 1 1+(5465671071/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5291910883/10000000000 : ℝ)*X 2 0+(5465671089/10000000000 : ℝ)*X 2 1+(-233054721/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309227609/10000000000 : ℝ)*X 0 0+(4605880847/10000000000 : ℝ)*X 0 1+(4030343879/10000000000 : ℝ)*X 0 2+(4309227609/10000000000 : ℝ)*X 1 0+(4605880847/10000000000 : ℝ)*X 1 1+(4030343879/10000000000 : ℝ)*X 1 2+(4309227609/10000000000 : ℝ)*X 2 0+(4605880847/10000000000 : ℝ)*X 2 1+(4030343879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1390_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (835265153771168615724447009/92117187500000000000000000000000 : ℝ) := by norm_num
    linear_combination (41831171/2500000000000 : ℝ)*(base19) + (1398962687/100000000000000 : ℝ)*(base23) + (87050853/100000000000000 : ℝ)*(lower2) + (276312911/100000000000000 : ℝ)*(upper3) + (2084913/1562500000000 : ℝ)*(upper5) + (21006434245399/781250000000 : ℝ)*(major0) + (21006434245399/781250000000 : ℝ)*(major1) + (21006434245399/781250000000 : ℝ)*(major2) + (457610006746993/12500000000000 : ℝ)*(sp0) + (1830448505696453/50000000000000 : ℝ)*(sp1) + (3660897285677059/100000000000000 : ℝ)*(sp2) + (1716737451819829/100000000000000 : ℝ)*(sp3) + (18630663803/100000000000000 : ℝ)*(sp4) + (42912461/400000000000 : ℝ)*(sp7) + (858374089967539/50000000000000 : ℝ)*(f.failure) + (1830449342319873/50000000000000 : ℝ)*(f.sum) + (363448792513627/58955000000000000000000000000 : ℝ)*base65 + (256685527056033311/92117187500000000000000000000000 : ℝ)*base67 + (920967344722060439/92117187500000000000000000000000 : ℝ)*base70 + (74945448016685439/92117187500000000000000000000000 : ℝ)*base72 + (53411797889873/14738750000000000000000000000 : ℝ)*base73 + (476913952540957247/184234375000000000000000000000000 : ℝ)*base75 + (228014689851852593/46058593750000000000000000000000 : ℝ)*base77 + (1743746736280207247/184234375000000000000000000000000 : ℝ)*base79 + (274059854738863/58955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (71248043/5000000000000000000000 : ℝ)*base90 + (71248043/5000000000000000000000 : ℝ)*base92 + (71248043/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32632030762066589321499/29477500000000000000000000000 : ℝ) := by norm_num
    linear_combination (384657191/100000000000000 : ℝ)*(base19) + (849252373/50000000000000 : ℝ)*(base23) + (168179947/100000000000000 : ℝ)*(lower2) + (58073461/100000000000000 : ℝ)*(upper3) + (28827931/25000000000000 : ℝ)*(lower4) + (1360674651928329/50000000000000 : ℝ)*(major0) + (1360674651928329/50000000000000 : ℝ)*(major1) + (1360674651928329/50000000000000 : ℝ)*(major2) + (6055054501/20000000000000 : ℝ)*(sp2) + (81163957/5000000000000 : ℝ)*(sp3) + (231573969553561/6250000000000 : ℝ)*(sp4) + (1852591564099893/50000000000000 : ℝ)*(sp5) + (1852575769539863/50000000000000 : ℝ)*(sp6) + (1737513434676697/100000000000000 : ℝ)*(sp7) + (868757528977919/50000000000000 : ℝ)*(f.failure) + (231573969553561/6250000000000 : ℝ)*(f.sum) + (336881253880193/58955000000000000000000000000 : ℝ)*base65 + (40705248433656341331/5895500000000000000000000000000000 : ℝ)*base67 + (2325110114406341331/5895500000000000000000000000000000 : ℝ)*base69 + (3824995105335341331/5895500000000000000000000000000000 : ℝ)*base71 + (214100586803333/58955000000000000000000000000 : ℝ)*base73 + (5502693341286658669/5895500000000000000000000000000000 : ℝ)*base76 + (45699786746352658669/5895500000000000000000000000000000 : ℝ)*base78 + (6301001575471158669/5895500000000000000000000000000000 : ℝ)*base80 + (25345475076723/58955000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33145897/5000000000000000000000 : ℝ)*base89 + (33145897/5000000000000000000000 : ℝ)*base91 + (33145897/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1390_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19113/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3661/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7963/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1390_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1390_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7963/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1390_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1390_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1390_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4349/1024 : ℝ) ≤ p) (hpb : p ≤ (2175/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156623063/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10149/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7963/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1390_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
