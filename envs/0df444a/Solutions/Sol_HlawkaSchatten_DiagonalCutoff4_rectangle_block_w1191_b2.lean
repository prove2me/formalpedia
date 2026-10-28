-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:18.178634+00:00
-- url     : https://prove2.me/submissions/bd5d6856-ffe6-470f-8451-c32db5a5c528

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
theorem support_rectangle_w1191_s6_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071824243/5000000000 : ℝ)*x 0 + (1348100901/2500000000 : ℝ)*x 1 + (5266249791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071824243/5000000000 : ℝ)^131 ≤ (1628811397461/12500000000000 : ℝ)^99 := by
    have hnat : (1071824243 : ℕ)^131*12500000000000^99 ≤ 1628811397461^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071824243 5000000000 1628811397461 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348100901/2500000000 : ℝ)^131 ≤ (8833153648071/20000000000000 : ℝ)^99 := by
    have hnat : (1348100901 : ℕ)^131*20000000000000^99 ≤ 8833153648071^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348100901 2500000000 8833153648071 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266249791/10000000000 : ℝ)^131 ≤ (21401870283971/50000000000000 : ℝ)^99 := by
    have hnat : (5266249791 : ℕ)^131*50000000000000^99 ≤ 21401870283971^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266249791 10000000000 21401870283971 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071824243/5000000000 : ℝ), (1348100901/2500000000 : ℝ), (5266249791/10000000000 : ℝ)] ![(1628811397461/12500000000000 : ℝ), (8833153648071/20000000000000 : ℝ), (21401870283971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071824243/5000000000 : ℝ)|^131 ≤ (1628811397461/12500000000000 : ℝ)^99
        have hw : |(-1071824243/5000000000 : ℝ)|=(1071824243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348100901/2500000000 : ℝ)|^131 ≤ (8833153648071/20000000000000 : ℝ)^99
        have hw : |(1348100901/2500000000 : ℝ)|=(1348100901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266249791/10000000000 : ℝ)|^131 ≤ (21401870283971/50000000000000 : ℝ)^99
        have hw : |(5266249791/10000000000 : ℝ)|=(5266249791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s6_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5344624131/10000000000 : ℝ)*x 0 + (-1103813757/5000000000 : ℝ)*x 1 + (5266249829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344624131/10000000000 : ℝ)^131 ≤ (4364868882489/10000000000000 : ℝ)^99 := by
    have hnat : (5344624131 : ℕ)^131*10000000000000^99 ≤ 4364868882489^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344624131 10000000000 4364868882489 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103813757/5000000000 : ℝ)^131 ≤ (13547570185113/100000000000000 : ℝ)^99 := by
    have hnat : (1103813757 : ℕ)^131*100000000000000^99 ≤ 13547570185113^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103813757 5000000000 13547570185113 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266249829/10000000000 : ℝ)^131 ≤ (21401870488319/50000000000000 : ℝ)^99 := by
    have hnat : (5266249829 : ℕ)^131*50000000000000^99 ≤ 21401870488319^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266249829 10000000000 21401870488319 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344624131/10000000000 : ℝ), (-1103813757/5000000000 : ℝ), (5266249829/10000000000 : ℝ)] ![(4364868882489/10000000000000 : ℝ), (13547570185113/100000000000000 : ℝ), (21401870488319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344624131/10000000000 : ℝ)|^131 ≤ (4364868882489/10000000000000 : ℝ)^99
        have hw : |(5344624131/10000000000 : ℝ)|=(5344624131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103813757/5000000000 : ℝ)|^131 ≤ (13547570185113/100000000000000 : ℝ)^99
        have hw : |(-1103813757/5000000000 : ℝ)|=(1103813757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266249829/10000000000 : ℝ)|^131 ≤ (21401870488319/50000000000000 : ℝ)^99
        have hw : |(5266249829/10000000000 : ℝ)|=(5266249829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s6_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5344624201/10000000000 : ℝ)*x 0 + (526624971/1000000000 : ℝ)*x 1 + (-1103813789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344624201/10000000000 : ℝ)^131 ≤ (21824344790677/50000000000000 : ℝ)^99 := by
    have hnat : (5344624201 : ℕ)^131*50000000000000^99 ≤ 21824344790677^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344624201 10000000000 21824344790677 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526624971/1000000000 : ℝ)^131 ≤ (1712149587871/4000000000000 : ℝ)^99 := by
    have hnat : (526624971 : ℕ)^131*4000000000000^99 ≤ 1712149587871^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526624971 1000000000 1712149587871 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103813789/5000000000 : ℝ)^131 ≤ (13547570704811/100000000000000 : ℝ)^99 := by
    have hnat : (1103813789 : ℕ)^131*100000000000000^99 ≤ 13547570704811^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103813789 5000000000 13547570704811 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344624201/10000000000 : ℝ), (526624971/1000000000 : ℝ), (-1103813789/5000000000 : ℝ)] ![(21824344790677/50000000000000 : ℝ), (1712149587871/4000000000000 : ℝ), (13547570704811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344624201/10000000000 : ℝ)|^131 ≤ (21824344790677/50000000000000 : ℝ)^99
        have hw : |(5344624201/10000000000 : ℝ)|=(5344624201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526624971/1000000000 : ℝ)|^131 ≤ (1712149587871/4000000000000 : ℝ)^99
        have hw : |(526624971/1000000000 : ℝ)|=(526624971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103813789/5000000000 : ℝ)|^131 ≤ (13547570704811/100000000000000 : ℝ)^99
        have hw : |(-1103813789/5000000000 : ℝ)|=(1103813789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s6_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (435780273/1000000000 : ℝ)*x 0 + (4232917161/10000000000 : ℝ)*x 1 + (280394481/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435780273/1000000000 : ℝ)^131 ≤ (208231871047/625000000000 : ℝ)^99 := by
    have hnat : (435780273 : ℕ)^131*625000000000^99 ≤ 208231871047^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435780273 1000000000 208231871047 625000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4232917161/10000000000 : ℝ)^131 ≤ (32059568634373/100000000000000 : ℝ)^99 := by
    have hnat : (4232917161 : ℕ)^131*100000000000000^99 ≤ 32059568634373^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232917161 10000000000 32059568634373 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280394481/625000000 : ℝ)^131 ≤ (34623331986623/100000000000000 : ℝ)^99 := by
    have hnat : (280394481 : ℕ)^131*100000000000000^99 ≤ 34623331986623^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280394481 625000000 34623331986623 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435780273/1000000000 : ℝ), (4232917161/10000000000 : ℝ), (280394481/625000000 : ℝ)] ![(208231871047/625000000000 : ℝ), (32059568634373/100000000000000 : ℝ), (34623331986623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435780273/1000000000 : ℝ)|^131 ≤ (208231871047/625000000000 : ℝ)^99
        have hw : |(435780273/1000000000 : ℝ)|=(435780273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4232917161/10000000000 : ℝ)|^131 ≤ (32059568634373/100000000000000 : ℝ)^99
        have hw : |(4232917161/10000000000 : ℝ)|=(4232917161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(280394481/625000000 : ℝ)|^131 ≤ (34623331986623/100000000000000 : ℝ)^99
        have hw : |(280394481/625000000 : ℝ)|=(280394481/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s6_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-535913201/2500000000 : ℝ)*x 0 + (5266568733/10000000000 : ℝ)*x 1 + (2696041941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535913201/2500000000 : ℝ)^131 ≤ (13030525911393/100000000000000 : ℝ)^99 := by
    have hnat : (535913201 : ℕ)^131*100000000000000^99 ≤ 13030525911393^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535913201 2500000000 13030525911393 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266568733/10000000000 : ℝ)^131 ≤ (42807170869759/100000000000000 : ℝ)^99 := by
    have hnat : (5266568733 : ℕ)^131*100000000000000^99 ≤ 42807170869759^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266568733 10000000000 42807170869759 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696041941/5000000000 : ℝ)^131 ≤ (44162303203491/100000000000000 : ℝ)^99 := by
    have hnat : (2696041941 : ℕ)^131*100000000000000^99 ≤ 44162303203491^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696041941 5000000000 44162303203491 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535913201/2500000000 : ℝ), (5266568733/10000000000 : ℝ), (2696041941/5000000000 : ℝ)] ![(13030525911393/100000000000000 : ℝ), (42807170869759/100000000000000 : ℝ), (44162303203491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535913201/2500000000 : ℝ)|^131 ≤ (13030525911393/100000000000000 : ℝ)^99
        have hw : |(-535913201/2500000000 : ℝ)|=(535913201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266568733/10000000000 : ℝ)|^131 ≤ (42807170869759/100000000000000 : ℝ)^99
        have hw : |(5266568733/10000000000 : ℝ)|=(5266568733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696041941/5000000000 : ℝ)|^131 ≤ (44162303203491/100000000000000 : ℝ)^99
        have hw : |(2696041941/5000000000 : ℝ)|=(2696041941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s6_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312548383/10000000000 : ℝ)*x 0 + (-32528031/156250000 : ℝ)*x 1 + (134802097/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312548383/10000000000 : ℝ)^131 ≤ (10825598717129/25000000000000 : ℝ)^99 := by
    have hnat : (5312548383 : ℕ)^131*25000000000000^99 ≤ 10825598717129^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312548383 10000000000 10825598717129 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32528031/156250000 : ℝ)^131 ≤ (12535301941771/100000000000000 : ℝ)^99 := by
    have hnat : (32528031 : ℕ)^131*100000000000000^99 ≤ 12535301941771^99*156250000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32528031 156250000 12535301941771 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134802097/250000000 : ℝ)^131 ≤ (5520287897727/12500000000000 : ℝ)^99 := by
    have hnat : (134802097 : ℕ)^131*12500000000000^99 ≤ 5520287897727^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134802097 250000000 5520287897727 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312548383/10000000000 : ℝ), (-32528031/156250000 : ℝ), (134802097/250000000 : ℝ)] ![(10825598717129/25000000000000 : ℝ), (12535301941771/100000000000000 : ℝ), (5520287897727/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312548383/10000000000 : ℝ)|^131 ≤ (10825598717129/25000000000000 : ℝ)^99
        have hw : |(5312548383/10000000000 : ℝ)|=(5312548383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32528031/156250000 : ℝ)|^131 ≤ (12535301941771/100000000000000 : ℝ)^99
        have hw : |(-32528031/156250000 : ℝ)|=(32528031/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134802097/250000000 : ℝ)|^131 ≤ (5520287897727/12500000000000 : ℝ)^99
        have hw : |(134802097/250000000 : ℝ)|=(134802097/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s6_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312548417/10000000000 : ℝ)*x 0 + (5392083971/10000000000 : ℝ)*x 1 + (-2081793813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312548417/10000000000 : ℝ)^131 ≤ (43302395235227/100000000000000 : ℝ)^99 := by
    have hnat : (5312548417 : ℕ)^131*100000000000000^99 ≤ 43302395235227^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312548417 10000000000 43302395235227 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392083971/10000000000 : ℝ)^131 ≤ (22081152084017/50000000000000 : ℝ)^99 := by
    have hnat : (5392083971 : ℕ)^131*50000000000000^99 ≤ 22081152084017^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392083971 10000000000 22081152084017 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2081793813/10000000000 : ℝ)^131 ≤ (12535300579293/100000000000000 : ℝ)^99 := by
    have hnat : (2081793813 : ℕ)^131*100000000000000^99 ≤ 12535300579293^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2081793813 10000000000 12535300579293 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312548417/10000000000 : ℝ), (5392083971/10000000000 : ℝ), (-2081793813/10000000000 : ℝ)] ![(43302395235227/100000000000000 : ℝ), (22081152084017/50000000000000 : ℝ), (12535300579293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312548417/10000000000 : ℝ)|^131 ≤ (43302395235227/100000000000000 : ℝ)^99
        have hw : |(5312548417/10000000000 : ℝ)|=(5312548417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392083971/10000000000 : ℝ)|^131 ≤ (22081152084017/50000000000000 : ℝ)^99
        have hw : |(5392083971/10000000000 : ℝ)|=(5392083971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2081793813/10000000000 : ℝ)|^131 ≤ (12535300579293/100000000000000 : ℝ)^99
        have hw : |(-2081793813/10000000000 : ℝ)|=(2081793813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s6_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4357811757/10000000000 : ℝ)*x 0 + (1121417937/2500000000 : ℝ)*x 1 + (2116780053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357811757/10000000000 : ℝ)^131 ≤ (33317190690339/100000000000000 : ℝ)^99 := by
    have hnat : (4357811757 : ℕ)^131*100000000000000^99 ≤ 33317190690339^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357811757 10000000000 33317190690339 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121417937/2500000000 : ℝ)^131 ≤ (1730839845871/5000000000000 : ℝ)^99 := by
    have hnat : (1121417937 : ℕ)^131*5000000000000^99 ≤ 1730839845871^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121417937 2500000000 1730839845871 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2116780053/5000000000 : ℝ)^131 ≤ (32066012381519/100000000000000 : ℝ)^99 := by
    have hnat : (2116780053 : ℕ)^131*100000000000000^99 ≤ 32066012381519^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116780053 5000000000 32066012381519 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357811757/10000000000 : ℝ), (1121417937/2500000000 : ℝ), (2116780053/5000000000 : ℝ)] ![(33317190690339/100000000000000 : ℝ), (1730839845871/5000000000000 : ℝ), (32066012381519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357811757/10000000000 : ℝ)|^131 ≤ (33317190690339/100000000000000 : ℝ)^99
        have hw : |(4357811757/10000000000 : ℝ)|=(4357811757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121417937/2500000000 : ℝ)|^131 ≤ (1730839845871/5000000000000 : ℝ)^99
        have hw : |(1121417937/2500000000 : ℝ)|=(1121417937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2116780053/5000000000 : ℝ)|^131 ≤ (32066012381519/100000000000000 : ℝ)^99
        have hw : |(2116780053/5000000000 : ℝ)|=(2116780053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1141/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2277/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14109/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2277/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14109/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2277/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (2277/20000 : ℝ) ^ (8383/2048 : ℝ) ≤ (13719053089366599/100000000000000000000 : ℝ) := by
    have hpowers : (2277/20000 : ℝ)^8383 ≤ (13719053089366599/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2277 : ℕ)^8383*100000000000000000000^2048 ≤ 13719053089366599^2048*20000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2277 20000 13719053089366599 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2277/20000 : ℝ)) (X := (13719053089366599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14109/100000 : ℝ) ^ (8383/2048 : ℝ) ≤ (33011517652421779/100000000000000000000 : ℝ) := by
    have hpowers : (14109/100000 : ℝ)^8383 ≤ (33011517652421779/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14109 : ℕ)^8383*100000000000000000000^2048 ≤ 33011517652421779^2048*100000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14109 100000 33011517652421779 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14109/100000 : ℝ)) (X := (33011517652421779/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013719053089366599/50000000000000000000 : ℝ) ≤ (5000335127141787/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50013719053089366599/50000000000000000000 : ℝ)^2048 ≤ (5000335127141787/5000000000000000 : ℝ)^8383 := by
      have hnat : (50013719053089366599 : ℕ)^2048*5000000000000000^8383 ≤ 5000335127141787^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013719053089366599 50000000000000000000 5000335127141787 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000335127141787/5000000000000000 : ℝ)) (X := (50013719053089366599/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023365285370894189/50000000000000000000 : ℝ) ≤ (2500285361192161/2500000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50023365285370894189/50000000000000000000 : ℝ)^2048 ≤ (2500285361192161/2500000000000000 : ℝ)^8383 := by
      have hnat : (50023365285370894189 : ℕ)^2048*2500000000000000^8383 ≤ 2500285361192161^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023365285370894189 50000000000000000000 2500285361192161 2500000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500285361192161/2500000000000000 : ℝ)) (X := (50023365285370894189/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033011517652421779/50000000000000000000 : ℝ) ≤ (5000806317626857/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50033011517652421779/50000000000000000000 : ℝ)^2048 ≤ (5000806317626857/5000000000000000 : ℝ)^8383 := by
      have hnat : (50033011517652421779 : ℕ)^2048*5000000000000000^8383 ≤ 5000806317626857^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033011517652421779 50000000000000000000 5000806317626857 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000806317626857/5000000000000000 : ℝ)) (X := (50033011517652421779/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13719053089366599/100000000000000000000 : ℝ) ≤ ((2269258063776950973/2270000000000000000 : ℝ)+2*(47119048507/27240000000000 : ℝ)*(2277/20000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (2269258063776950973/2270000000000000000 : ℝ)+2*(47119048507/27240000000000 : ℝ)*(2277/20000 : ℝ)=(5000335127141787/5000000000000000 : ℝ) by norm_num, show 1+2*(13719053089366599/100000000000000000000 : ℝ)=(50013719053089366599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33011517652421779/100000000000000000000 : ℝ)+(13719053089366599/100000000000000000000 : ℝ) ≤ ((2269258063776950973/2270000000000000000 : ℝ)+(47119048507/27240000000000 : ℝ)*((14109/100000 : ℝ)+(2277/20000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (2269258063776950973/2270000000000000000 : ℝ)+(47119048507/27240000000000 : ℝ)*((14109/100000 : ℝ)+(2277/20000 : ℝ))=(2500285361192161/2500000000000000 : ℝ) by norm_num, show 1+(33011517652421779/100000000000000000000 : ℝ)+(13719053089366599/100000000000000000000 : ℝ)=(50023365285370894189/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33011517652421779/100000000000000000000 : ℝ) ≤ ((2269258063776950973/2270000000000000000 : ℝ)+2*(47119048507/27240000000000 : ℝ)*(14109/100000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (2269258063776950973/2270000000000000000 : ℝ)+2*(47119048507/27240000000000 : ℝ)*(14109/100000 : ℝ)=(5000806317626857/5000000000000000 : ℝ) by norm_num, show 1+2*(33011517652421779/100000000000000000000 : ℝ)=(50033011517652421779/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2269258063776950973/2270000000000000000 : ℝ)*(X 1 0+X 2 0)+(47119048507/27240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (2269258063776950973/2270000000000000000 : ℝ)) (alpha := (47119048507/27240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2269258063776950973/2270000000000000000 : ℝ)*(X 0 1+X 2 1)+(47119048507/27240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (2269258063776950973/2270000000000000000 : ℝ)) (alpha := (47119048507/27240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2269258063776950973/2270000000000000000 : ℝ)*(X 0 2+X 1 2)+(47119048507/27240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2277/20000 : ℝ)) (hi := (14109/100000 : ℝ)) (c := (2269258063776950973/2270000000000000000 : ℝ)) (alpha := (47119048507/27240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071824243/5000000000 : ℝ)*X 0 0+(1348100901/2500000000 : ℝ)*X 0 1+(5266249791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344624131/10000000000 : ℝ)*X 1 0+(-1103813757/5000000000 : ℝ)*X 1 1+(5266249829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344624201/10000000000 : ℝ)*X 2 0+(526624971/1000000000 : ℝ)*X 2 1+(-1103813789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((435780273/1000000000 : ℝ)*X 0 0+(4232917161/10000000000 : ℝ)*X 0 1+(280394481/625000000 : ℝ)*X 0 2+(435780273/1000000000 : ℝ)*X 1 0+(4232917161/10000000000 : ℝ)*X 1 1+(280394481/625000000 : ℝ)*X 1 2+(435780273/1000000000 : ℝ)*X 2 0+(4232917161/10000000000 : ℝ)*X 2 1+(280394481/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-535913201/2500000000 : ℝ)*X 0 0+(5266568733/10000000000 : ℝ)*X 0 1+(2696041941/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312548383/10000000000 : ℝ)*X 1 0+(-32528031/156250000 : ℝ)*X 1 1+(134802097/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312548417/10000000000 : ℝ)*X 2 0+(5392083971/10000000000 : ℝ)*X 2 1+(-2081793813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357811757/10000000000 : ℝ)*X 0 0+(1121417937/2500000000 : ℝ)*X 0 1+(2116780053/5000000000 : ℝ)*X 0 2+(4357811757/10000000000 : ℝ)*X 1 0+(1121417937/2500000000 : ℝ)*X 1 1+(2116780053/5000000000 : ℝ)*X 1 2+(4357811757/10000000000 : ℝ)*X 2 0+(1121417937/2500000000 : ℝ)*X 2 1+(2116780053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1114704118501272225223153967/113500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (92929917/5000000000000 : ℝ)*(base19) + (1671253473/100000000000000 : ℝ)*(base23) + (155617271/100000000000000 : ℝ)*(lower2) + (361156761/100000000000000 : ℝ)*(upper3) + (61487569/100000000000000 : ℝ)*(upper5) + (5936698173267593/100000000000000 : ℝ)*(major0) + (5936698173267593/100000000000000 : ℝ)*(major1) + (5936698173267593/100000000000000 : ℝ)*(major2) + (7926883989073627/100000000000000 : ℝ)*(sp0) + (1981731435458867/25000000000000 : ℝ)*(sp1) + (1585385185836067/20000000000000 : ℝ)*(sp2) + (394643754742061/10000000000000 : ℝ)*(sp3) + (43611360181/100000000000000 : ℝ)*(sp4) + (30871308037/100000000000000 : ℝ)*(sp7) + (1973234209364323/50000000000000 : ℝ)*(f.failure) + (495432975027113/6250000000000 : ℝ)*(f.sum) + (1099867662431/272400000000000000000000000 : ℝ)*base66 + (2572861946497903967/681000000000000000000000000000000 : ℝ)*base67 + (17047355378836096033/681000000000000000000000000000000 : ℝ)*base70 + (225430873147903967/681000000000000000000000000000000 : ℝ)*base71 + (5097112841257/1362000000000000000000000000 : ℝ)*base74 + (5444525302849096033/681000000000000000000000000000000 : ℝ)*base76 + (1156869074239096033/681000000000000000000000000000000 : ℝ)*base78 + (164404252891096033/681000000000000000000000000000000 : ℝ)*base80 + (9947314040773/1362000000000000000000000000 : ℝ)*base82 + (8892851/1250000000000000000000 : ℝ)*base90 + (8892851/1250000000000000000000 : ℝ)*base92 + (8892851/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (893374599031038267877544389/56750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11266321/12500000000000 : ℝ)*(base8) + (40153379/25000000000000 : ℝ)*(lower2) + (23502863/50000000000000 : ℝ)*(upper3) + (21452827/20000000000000 : ℝ)*(lower4) + (7151829/12500000000000 : ℝ)*(upper5) + (2983418158901869/50000000000000 : ℝ)*(major0) + (2983418158901869/50000000000000 : ℝ)*(major1) + (2983418158901869/50000000000000 : ℝ)*(major2) + (4093589657/50000000000000 : ℝ)*(sp2) + (267678727/10000000000000 : ℝ)*(sp3) + (1991792256296299/25000000000000 : ℝ)*(sp4) + (1991792278828941/25000000000000 : ℝ)*(sp5) + (159343218562729/2000000000000 : ℝ)*(sp6) + (3966500318761627/100000000000000 : ℝ)*(sp7) + (1983251497774449/50000000000000 : ℝ)*(f.failure) + (1991792278828941/25000000000000 : ℝ)*(f.sum) + (783285042007/170250000000000000000000000 : ℝ)*base65 + (9235022543038044389/340500000000000000000000000000000 : ℝ)*base68 + (1495676184898044389/340500000000000000000000000000000 : ℝ)*base70 + (50972706986073455611/340500000000000000000000000000000 : ℝ)*base71 + (3322060099693/681000000000000000000000000 : ℝ)*base73 + (3694336006057955611/340500000000000000000000000000000 : ℝ)*base75 + (4948728880317455611/340500000000000000000000000000000 : ℝ)*base77 + (4307253148870955611/340500000000000000000000000000000 : ℝ)*base79 + (3007335284657/681000000000000000000000000 : ℝ)*base82 + (3002687/1250000000000000000000 : ℝ)*base89 + (3002687/1250000000000000000000 : ℝ)*base91 + (3002687/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1191_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1191_s7_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1071834973/5000000000 : ℝ)*x 0 + (539215361/1000000000 : ℝ)*x 1 + (1316621413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071834973/5000000000 : ℝ)^131 ≤ (6515331896391/50000000000000 : ℝ)^99 := by
    have hnat : (1071834973 : ℕ)^131*50000000000000^99 ≤ 6515331896391^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071834973 5000000000 6515331896391 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539215361/1000000000 : ℝ)^131 ≤ (22081529442933/50000000000000 : ℝ)^99 := by
    have hnat : (539215361 : ℕ)^131*50000000000000^99 ≤ 22081529442933^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539215361 1000000000 22081529442933 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316621413/2500000000 : ℝ)^131 ≤ (42806277306139/100000000000000 : ℝ)^99 := by
    have hnat : (1316621413 : ℕ)^131*100000000000000^99 ≤ 42806277306139^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316621413 2500000000 42806277306139 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1071834973/5000000000 : ℝ), (539215361/1000000000 : ℝ), (1316621413/2500000000 : ℝ)] ![(6515331896391/50000000000000 : ℝ), (22081529442933/50000000000000 : ℝ), (42806277306139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1071834973/5000000000 : ℝ)|^131 ≤ (6515331896391/50000000000000 : ℝ)^99
        have hw : |(-1071834973/5000000000 : ℝ)|=(1071834973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539215361/1000000000 : ℝ)|^131 ≤ (22081529442933/50000000000000 : ℝ)^99
        have hw : |(539215361/1000000000 : ℝ)|=(539215361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316621413/2500000000 : ℝ)|^131 ≤ (42806277306139/100000000000000 : ℝ)^99
        have hw : |(1316621413/2500000000 : ℝ)|=(1316621413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s7_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1336140157/2500000000 : ℝ)*x 0 + (-2207399271/10000000000 : ℝ)*x 1 + (2633242979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336140157/2500000000 : ℝ)^131 ≤ (5456000321627/12500000000000 : ℝ)^99 := by
    have hnat : (1336140157 : ℕ)^131*12500000000000^99 ≤ 5456000321627^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336140157 2500000000 5456000321627 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207399271/10000000000 : ℝ)^131 ≤ (13545716815993/100000000000000 : ℝ)^99 := by
    have hnat : (2207399271 : ℕ)^131*100000000000000^99 ≤ 13545716815993^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207399271 10000000000 13545716815993 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633242979/5000000000 : ℝ)^131 ≤ (21403140298631/50000000000000 : ℝ)^99 := by
    have hnat : (2633242979 : ℕ)^131*50000000000000^99 ≤ 21403140298631^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633242979 5000000000 21403140298631 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336140157/2500000000 : ℝ), (-2207399271/10000000000 : ℝ), (2633242979/5000000000 : ℝ)] ![(5456000321627/12500000000000 : ℝ), (13545716815993/100000000000000 : ℝ), (21403140298631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336140157/2500000000 : ℝ)|^131 ≤ (5456000321627/12500000000000 : ℝ)^99
        have hw : |(1336140157/2500000000 : ℝ)|=(1336140157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207399271/10000000000 : ℝ)|^131 ≤ (13545716815993/100000000000000 : ℝ)^99
        have hw : |(-2207399271/10000000000 : ℝ)|=(2207399271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633242979/5000000000 : ℝ)|^131 ≤ (21403140298631/50000000000000 : ℝ)^99
        have hw : |(2633242979/5000000000 : ℝ)|=(2633242979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s7_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (334035051/625000000 : ℝ)*x 0 + (1053297213/2000000000 : ℝ)*x 1 + (-1103699439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334035051/625000000 : ℝ)^131 ≤ (21824002302327/50000000000000 : ℝ)^99 := by
    have hnat : (334035051 : ℕ)^131*50000000000000^99 ≤ 21824002302327^99*625000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334035051 625000000 21824002302327 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053297213/2000000000 : ℝ)^131 ≤ (535078521851/1250000000000 : ℝ)^99 := by
    have hnat : (1053297213 : ℕ)^131*1250000000000^99 ≤ 535078521851^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053297213 2000000000 535078521851 1250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103699439/5000000000 : ℝ)^131 ≤ (541828544993/4000000000000 : ℝ)^99 := by
    have hnat : (1103699439 : ℕ)^131*4000000000000^99 ≤ 541828544993^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103699439 5000000000 541828544993 4000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334035051/625000000 : ℝ), (1053297213/2000000000 : ℝ), (-1103699439/5000000000 : ℝ)] ![(21824002302327/50000000000000 : ℝ), (535078521851/1250000000000 : ℝ), (541828544993/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334035051/625000000 : ℝ)|^131 ≤ (21824002302327/50000000000000 : ℝ)^99
        have hw : |(334035051/625000000 : ℝ)|=(334035051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053297213/2000000000 : ℝ)|^131 ≤ (535078521851/1250000000000 : ℝ)^99
        have hw : |(1053297213/2000000000 : ℝ)|=(1053297213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1103699439/5000000000 : ℝ)|^131 ≤ (541828544993/4000000000000 : ℝ)^99
        have hw : |(-1103699439/5000000000 : ℝ)|=(1103699439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s7_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4357815509/10000000000 : ℝ)*x 0 + (4233403427/10000000000 : ℝ)*x 1 + (897164361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357815509/10000000000 : ℝ)^131 ≤ (2082326790497/6250000000000 : ℝ)^99 := by
    have hnat : (4357815509 : ℕ)^131*6250000000000^99 ≤ 2082326790497^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357815509 10000000000 2082326790497 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233403427/10000000000 : ℝ)^131 ≤ (16032221039151/50000000000000 : ℝ)^99 := by
    have hnat : (4233403427 : ℕ)^131*50000000000000^99 ≤ 16032221039151^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233403427 10000000000 16032221039151 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897164361/2000000000 : ℝ)^131 ≤ (17309164626877/50000000000000 : ℝ)^99 := by
    have hnat : (897164361 : ℕ)^131*50000000000000^99 ≤ 17309164626877^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897164361 2000000000 17309164626877 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357815509/10000000000 : ℝ), (4233403427/10000000000 : ℝ), (897164361/2000000000 : ℝ)] ![(2082326790497/6250000000000 : ℝ), (16032221039151/50000000000000 : ℝ), (17309164626877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357815509/10000000000 : ℝ)|^131 ≤ (2082326790497/6250000000000 : ℝ)^99
        have hw : |(4357815509/10000000000 : ℝ)|=(4357815509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233403427/10000000000 : ℝ)|^131 ≤ (16032221039151/50000000000000 : ℝ)^99
        have hw : |(4233403427/10000000000 : ℝ)|=(4233403427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(897164361/2000000000 : ℝ)|^131 ≤ (17309164626877/50000000000000 : ℝ)^99
        have hw : |(897164361/2000000000 : ℝ)|=(897164361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s7_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-535918587/2500000000 : ℝ)*x 0 + (2633401007/5000000000 : ℝ)*x 1 + (5391836377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535918587/2500000000 : ℝ)^131 ≤ (13030699200253/100000000000000 : ℝ)^99 := by
    have hnat : (535918587 : ℕ)^131*100000000000000^99 ≤ 13030699200253^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535918587 2500000000 13030699200253 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633401007/5000000000 : ℝ)^131 ≤ (4280967990839/10000000000000 : ℝ)^99 := by
    have hnat : (2633401007 : ℕ)^131*10000000000000^99 ≤ 4280967990839^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633401007 5000000000 4280967990839 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391836377/10000000000 : ℝ)^131 ≤ (44159620875193/100000000000000 : ℝ)^99 := by
    have hnat : (5391836377 : ℕ)^131*100000000000000^99 ≤ 44159620875193^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391836377 10000000000 44159620875193 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535918587/2500000000 : ℝ), (2633401007/5000000000 : ℝ), (5391836377/10000000000 : ℝ)] ![(13030699200253/100000000000000 : ℝ), (4280967990839/10000000000000 : ℝ), (44159620875193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535918587/2500000000 : ℝ)|^131 ≤ (13030699200253/100000000000000 : ℝ)^99
        have hw : |(-535918587/2500000000 : ℝ)|=(535918587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633401007/5000000000 : ℝ)|^131 ≤ (4280967990839/10000000000000 : ℝ)^99
        have hw : |(2633401007/5000000000 : ℝ)|=(2633401007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391836377/10000000000 : ℝ)|^131 ≤ (44159620875193/100000000000000 : ℝ)^99
        have hw : |(5391836377/10000000000 : ℝ)|=(5391836377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s7_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1062521861/2000000000 : ℝ)*x 0 + (-41640963/200000000 : ℝ)*x 1 + (2695918191/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062521861/2000000000 : ℝ)^131 ≤ (43303051951281/100000000000000 : ℝ)^99 := by
    have hnat : (1062521861 : ℕ)^131*100000000000000^99 ≤ 43303051951281^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062521861 2000000000 43303051951281 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41640963/200000000 : ℝ)^131 ≤ (2507465420199/20000000000000 : ℝ)^99 := by
    have hnat : (41640963 : ℕ)^131*20000000000000^99 ≤ 2507465420199^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41640963 200000000 2507465420199 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695918191/5000000000 : ℝ)^131 ≤ (44159620929379/100000000000000 : ℝ)^99 := by
    have hnat : (2695918191 : ℕ)^131*100000000000000^99 ≤ 44159620929379^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695918191 5000000000 44159620929379 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062521861/2000000000 : ℝ), (-41640963/200000000 : ℝ), (2695918191/5000000000 : ℝ)] ![(43303051951281/100000000000000 : ℝ), (2507465420199/20000000000000 : ℝ), (44159620929379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062521861/2000000000 : ℝ)|^131 ≤ (43303051951281/100000000000000 : ℝ)^99
        have hw : |(1062521861/2000000000 : ℝ)|=(1062521861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41640963/200000000 : ℝ)|^131 ≤ (2507465420199/20000000000000 : ℝ)^99
        have hw : |(-41640963/200000000 : ℝ)|=(41640963/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695918191/5000000000 : ℝ)|^131 ≤ (44159620929379/100000000000000 : ℝ)^99
        have hw : |(2695918191/5000000000 : ℝ)|=(2695918191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s7_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2656304689/5000000000 : ℝ)*x 0 + (673979541/1250000000 : ℝ)*x 1 + (-3331277/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656304689/5000000000 : ℝ)^131 ≤ (21651526369317/50000000000000 : ℝ)^99 := by
    have hnat : (2656304689 : ℕ)^131*50000000000000^99 ≤ 21651526369317^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656304689 5000000000 21651526369317 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673979541/1250000000 : ℝ)^131 ≤ (275997627151/625000000000 : ℝ)^99 := by
    have hnat : (673979541 : ℕ)^131*625000000000^99 ≤ 275997627151^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673979541 1250000000 275997627151 625000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3331277/16000000 : ℝ)^131 ≤ (2507465380359/20000000000000 : ℝ)^99 := by
    have hnat : (3331277 : ℕ)^131*20000000000000^99 ≤ 2507465380359^99*16000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331277 16000000 2507465380359 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656304689/5000000000 : ℝ), (673979541/1250000000 : ℝ), (-3331277/16000000 : ℝ)] ![(21651526369317/50000000000000 : ℝ), (275997627151/625000000000 : ℝ), (2507465380359/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656304689/5000000000 : ℝ)|^131 ≤ (21651526369317/50000000000000 : ℝ)^99
        have hw : |(2656304689/5000000000 : ℝ)|=(2656304689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673979541/1250000000 : ℝ)|^131 ≤ (275997627151/625000000000 : ℝ)^99
        have hw : |(673979541/1250000000 : ℝ)|=(673979541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3331277/16000000 : ℝ)|^131 ≤ (2507465380359/20000000000000 : ℝ)^99
        have hw : |(-3331277/16000000 : ℝ)|=(3331277/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s7_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (871564903/2000000000 : ℝ)*x 0 + (1121296709/2500000000 : ℝ)*x 1 + (2117020637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871564903/2000000000 : ℝ)^131 ≤ (4164664969801/12500000000000 : ℝ)^99 := by
    have hnat : (871564903 : ℕ)^131*12500000000000^99 ≤ 4164664969801^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871564903 2000000000 4164664969801 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1121296709/2500000000 : ℝ)^131 ≤ (34611845257207/100000000000000 : ℝ)^99 := by
    have hnat : (1121296709 : ℕ)^131*100000000000000^99 ≤ 34611845257207^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121296709 2500000000 34611845257207 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117020637/5000000000 : ℝ)^131 ≤ (4008854371023/12500000000000 : ℝ)^99 := by
    have hnat : (2117020637 : ℕ)^131*12500000000000^99 ≤ 4008854371023^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117020637 5000000000 4008854371023 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871564903/2000000000 : ℝ), (1121296709/2500000000 : ℝ), (2117020637/5000000000 : ℝ)] ![(4164664969801/12500000000000 : ℝ), (34611845257207/100000000000000 : ℝ), (4008854371023/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871564903/2000000000 : ℝ)|^131 ≤ (4164664969801/12500000000000 : ℝ)^99
        have hw : |(871564903/2000000000 : ℝ)|=(871564903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1121296709/2500000000 : ℝ)|^131 ≤ (34611845257207/100000000000000 : ℝ)^99
        have hw : |(1121296709/2500000000 : ℝ)|=(1121296709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117020637/5000000000 : ℝ)|^131 ≤ (4008854371023/12500000000000 : ℝ)^99
        have hw : |(2117020637/5000000000 : ℝ)|=(2117020637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2283/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14077/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1141/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14083/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1141/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14083/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1141/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1141/10000 : ℝ) ^ (8383/2048 : ℝ) ≤ (1730347897503587/12500000000000000000 : ℝ) := by
    have hpowers : (1141/10000 : ℝ)^8383 ≤ (1730347897503587/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1141 : ℕ)^8383*12500000000000000000^2048 ≤ 1730347897503587^2048*10000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1141 10000 1730347897503587 12500000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1141/10000 : ℝ)) (X := (1730347897503587/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14083/100000 : ℝ) ^ (8383/2048 : ℝ) ≤ (16381609559622711/50000000000000000000 : ℝ) := by
    have hpowers : (14083/100000 : ℝ)^8383 ≤ (16381609559622711/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14083 : ℕ)^8383*50000000000000000000^2048 ≤ 16381609559622711^2048*100000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14083 100000 16381609559622711 50000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14083/100000 : ℝ)) (X := (16381609559622711/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251730347897503587/6250000000000000000 : ℝ) ≤ (2500169074643657/2500000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (6251730347897503587/6250000000000000000 : ℝ)^2048 ≤ (2500169074643657/2500000000000000 : ℝ)^8383 := by
      have hnat : (6251730347897503587 : ℕ)^2048*2500000000000000^8383 ≤ 2500169074643657^8383*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251730347897503587 6250000000000000000 2500169074643657 2500000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500169074643657/2500000000000000 : ℝ)) (X := (6251730347897503587/6250000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023303001149637059/50000000000000000000 : ℝ) ≤ (2000227680517047/2000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50023303001149637059/50000000000000000000 : ℝ)^2048 ≤ (2000227680517047/2000000000000000 : ℝ)^8383 := by
      have hnat : (50023303001149637059 : ℕ)^2048*2000000000000000^8383 ≤ 2000227680517047^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023303001149637059 50000000000000000000 2000227680517047 2000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000227680517047/2000000000000000 : ℝ)) (X := (50023303001149637059/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016381609559622711/25000000000000000000 : ℝ) ≤ (5000800253297921/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (25016381609559622711/25000000000000000000 : ℝ)^2048 ≤ (5000800253297921/5000000000000000 : ℝ)^8383 := by
      have hnat : (25016381609559622711 : ℕ)^2048*5000000000000000^8383 ≤ 5000800253297921^8383*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016381609559622711 25000000000000000000 5000800253297921 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000800253297921/5000000000000000 : ℝ)) (X := (25016381609559622711/25000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1730347897503587/12500000000000000000 : ℝ) ≤ ((3340157816570991113/3341250000000000000 : ℝ)+2*(462104010607/267300000000000 : ℝ)*(1141/10000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (3340157816570991113/3341250000000000000 : ℝ)+2*(462104010607/267300000000000 : ℝ)*(1141/10000 : ℝ)=(2500169074643657/2500000000000000 : ℝ) by norm_num, show 1+2*(1730347897503587/12500000000000000000 : ℝ)=(6251730347897503587/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16381609559622711/50000000000000000000 : ℝ)+(1730347897503587/12500000000000000000 : ℝ) ≤ ((3340157816570991113/3341250000000000000 : ℝ)+(462104010607/267300000000000 : ℝ)*((14083/100000 : ℝ)+(1141/10000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (3340157816570991113/3341250000000000000 : ℝ)+(462104010607/267300000000000 : ℝ)*((14083/100000 : ℝ)+(1141/10000 : ℝ))=(2000227680517047/2000000000000000 : ℝ) by norm_num, show 1+(16381609559622711/50000000000000000000 : ℝ)+(1730347897503587/12500000000000000000 : ℝ)=(50023303001149637059/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16381609559622711/50000000000000000000 : ℝ) ≤ ((3340157816570991113/3341250000000000000 : ℝ)+2*(462104010607/267300000000000 : ℝ)*(14083/100000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (3340157816570991113/3341250000000000000 : ℝ)+2*(462104010607/267300000000000 : ℝ)*(14083/100000 : ℝ)=(5000800253297921/5000000000000000 : ℝ) by norm_num, show 1+2*(16381609559622711/50000000000000000000 : ℝ)=(25016381609559622711/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3340157816570991113/3341250000000000000 : ℝ)*(X 1 0+X 2 0)+(462104010607/267300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (3340157816570991113/3341250000000000000 : ℝ)) (alpha := (462104010607/267300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3340157816570991113/3341250000000000000 : ℝ)*(X 0 1+X 2 1)+(462104010607/267300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (3340157816570991113/3341250000000000000 : ℝ)) (alpha := (462104010607/267300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3340157816570991113/3341250000000000000 : ℝ)*(X 0 2+X 1 2)+(462104010607/267300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (1141/10000 : ℝ)) (hi := (14083/100000 : ℝ)) (c := (3340157816570991113/3341250000000000000 : ℝ)) (alpha := (462104010607/267300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1071834973/5000000000 : ℝ)*X 0 0+(539215361/1000000000 : ℝ)*X 0 1+(1316621413/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336140157/2500000000 : ℝ)*X 1 0+(-2207399271/10000000000 : ℝ)*X 1 1+(2633242979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334035051/625000000 : ℝ)*X 2 0+(1053297213/2000000000 : ℝ)*X 2 1+(-1103699439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4357815509/10000000000 : ℝ)*X 0 0+(4233403427/10000000000 : ℝ)*X 0 1+(897164361/2000000000 : ℝ)*X 0 2+(4357815509/10000000000 : ℝ)*X 1 0+(4233403427/10000000000 : ℝ)*X 1 1+(897164361/2000000000 : ℝ)*X 1 2+(4357815509/10000000000 : ℝ)*X 2 0+(4233403427/10000000000 : ℝ)*X 2 1+(897164361/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-535918587/2500000000 : ℝ)*X 0 0+(2633401007/5000000000 : ℝ)*X 0 1+(5391836377/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062521861/2000000000 : ℝ)*X 1 0+(-41640963/200000000 : ℝ)*X 1 1+(2695918191/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656304689/5000000000 : ℝ)*X 2 0+(673979541/1250000000 : ℝ)*X 2 1+(-3331277/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871564903/2000000000 : ℝ)*X 0 0+(1121296709/2500000000 : ℝ)*X 0 1+(2117020637/5000000000 : ℝ)*X 0 2+(871564903/2000000000 : ℝ)*X 1 0+(1121296709/2500000000 : ℝ)*X 1 1+(2117020637/5000000000 : ℝ)*X 1 2+(871564903/2000000000 : ℝ)*X 2 0+(1121296709/2500000000 : ℝ)*X 2 1+(2117020637/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31502813782883916182083523/2784375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (171076047/12500000000000 : ℝ)*(base19) + (31189253/2000000000000 : ℝ)*(base23) + (217854291/100000000000000 : ℝ)*(upper3) + (2974917/6250000000000 : ℝ)*(upper4) + (21073387/2500000000000 : ℝ)*(upper5) + (595963167310321/10000000000000 : ℝ)*(major0) + (595963167310321/10000000000000 : ℝ)*(major1) + (595963167310321/10000000000000 : ℝ)*(major2) + (7957495592105329/100000000000000 : ℝ)*(sp0) + (7957547951101323/100000000000000 : ℝ)*(sp1) + (7957547760247049/100000000000000 : ℝ)*(sp2) + (495212560086033/12500000000000 : ℝ)*(sp3) + (5372760437/10000000000000 : ℝ)*(sp4) + (6584335193/50000000000000 : ℝ)*(sp7) + (79234272987173/2000000000000 : ℝ)*(f.failure) + (7957549319709699/100000000000000 : ℝ)*(f.sum) + (909494050969/1336500000000000000000000000 : ℝ)*base65 + (461127883533510227/33412500000000000000000000000000 : ℝ)*base68 + (430859733270060227/33412500000000000000000000000000 : ℝ)*base70 + (191976172880639773/33412500000000000000000000000000 : ℝ)*base71 + (22761459390949/2673000000000000000000000000 : ℝ)*base74 + (7634135275410227/33412500000000000000000000000000 : ℝ)*base76 + (490324489709610227/33412500000000000000000000000000 : ℝ)*base78 + (592675679795947727/33412500000000000000000000000000 : ℝ)*base80 + (104420201977/167062500000000000000000000 : ℝ)*base82 + (506699/50000000000000000000 : ℝ)*base89 + (506699/50000000000000000000 : ℝ)*base91 + (506699/50000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13741897229580355340719183/6187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37788711/12500000000000 : ℝ)*(base19) + (104610379/20000000000000 : ℝ)*(base23) + (2992377/6250000000000 : ℝ)*(upper2) + (12827313/20000000000000 : ℝ)*(upper3) + (100637031/100000000000000 : ℝ)*(upper5) + (5989778602284827/100000000000000 : ℝ)*(major0) + (5989778602284827/100000000000000 : ℝ)*(major1) + (5989778602284827/100000000000000 : ℝ)*(major2) + (631602073/10000000000000 : ℝ)*(sp1) + (1952352923/20000000000000 : ℝ)*(sp2) + (7997803064695759/100000000000000 : ℝ)*(sp4) + (7997796446365341/100000000000000 : ℝ)*(sp5) + (7997792779879249/100000000000000 : ℝ)*(sp6) + (199087703292173/5000000000000 : ℝ)*(sp7) + (199087703292173/5000000000000 : ℝ)*(f.failure) + (7997803064695759/100000000000000 : ℝ)*(f.sum) + (50641008080669/13365000000000000000000000000 : ℝ)*base65 + (4516256466689354951/334125000000000000000000000000000 : ℝ)*base67 + (2027879909441729951/334125000000000000000000000000000 : ℝ)*base69 + (3017944019688479951/334125000000000000000000000000000 : ℝ)*base71 + (112054468633289/13365000000000000000000000000 : ℝ)*base73 + (3887044811078354951/334125000000000000000000000000000 : ℝ)*base75 + (2659292067195854951/334125000000000000000000000000000 : ℝ)*base77 + (4141806247547729951/334125000000000000000000000000000 : ℝ)*base79 + (13752251496883/1670625000000000000000000000 : ℝ)*base81 + (1028301/125000000000000000000 : ℝ)*base90 + (1028301/125000000000000000000 : ℝ)*base92 + (1028301/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1191_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1141/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1191_s8_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143676401/10000000000 : ℝ)*x 0 + (1078419863/2000000000 : ℝ)*x 1 + (1053307107/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143676401/10000000000 : ℝ)^131 ≤ (13030715713559/100000000000000 : ℝ)^99 := by
    have hnat : (2143676401 : ℕ)^131*100000000000000^99 ≤ 13030715713559^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143676401 10000000000 13030715713559 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078419863/2000000000 : ℝ)^131 ≤ (22081235229751/50000000000000 : ℝ)^99 := by
    have hnat : (1078419863 : ℕ)^131*50000000000000^99 ≤ 22081235229751^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078419863 2000000000 22081235229751 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053307107/2000000000 : ℝ)^131 ≤ (10701703453437/25000000000000 : ℝ)^99 := by
    have hnat : (1053307107 : ℕ)^131*25000000000000^99 ≤ 10701703453437^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053307107 2000000000 10701703453437 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143676401/10000000000 : ℝ), (1078419863/2000000000 : ℝ), (1053307107/2000000000 : ℝ)] ![(13030715713559/100000000000000 : ℝ), (22081235229751/50000000000000 : ℝ), (10701703453437/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143676401/10000000000 : ℝ)|^131 ≤ (13030715713559/100000000000000 : ℝ)^99
        have hw : |(-2143676401/10000000000 : ℝ)|=(2143676401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078419863/2000000000 : ℝ)|^131 ≤ (22081235229751/50000000000000 : ℝ)^99
        have hw : |(1078419863/2000000000 : ℝ)|=(1078419863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053307107/2000000000 : ℝ)|^131 ≤ (10701703453437/25000000000000 : ℝ)^99
        have hw : |(1053307107/2000000000 : ℝ)|=(1053307107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s8_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1336136711/2500000000 : ℝ)*x 0 + (-2207352019/10000000000 : ℝ)*x 1 + (2633267741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336136711/2500000000 : ℝ)^131 ≤ (5455981701889/12500000000000 : ℝ)^99 := by
    have hnat : (1336136711 : ℕ)^131*12500000000000^99 ≤ 5455981701889^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336136711 2500000000 5455981701889 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2207352019/10000000000 : ℝ)^131 ≤ (211645830157/1562500000000 : ℝ)^99 := by
    have hnat : (2207352019 : ℕ)^131*1562500000000^99 ≤ 211645830157^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207352019 10000000000 211645830157 1562500000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633267741/5000000000 : ℝ)^131 ≤ (8561362648743/20000000000000 : ℝ)^99 := by
    have hnat : (2633267741 : ℕ)^131*20000000000000^99 ≤ 8561362648743^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633267741 5000000000 8561362648743 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336136711/2500000000 : ℝ), (-2207352019/10000000000 : ℝ), (2633267741/5000000000 : ℝ)] ![(5455981701889/12500000000000 : ℝ), (211645830157/1562500000000 : ℝ), (8561362648743/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336136711/2500000000 : ℝ)|^131 ≤ (5455981701889/12500000000000 : ℝ)^99
        have hw : |(1336136711/2500000000 : ℝ)|=(1336136711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2207352019/10000000000 : ℝ)|^131 ≤ (211645830157/1562500000000 : ℝ)^99
        have hw : |(-2207352019/10000000000 : ℝ)|=(2207352019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633267741/5000000000 : ℝ)|^131 ≤ (8561362648743/20000000000000 : ℝ)^99
        have hw : |(2633267741/5000000000 : ℝ)|=(2633267741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s8_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1068909369/2000000000 : ℝ)*x 0 + (658316941/1250000000 : ℝ)*x 1 + (-2207351957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068909369/2000000000 : ℝ)^131 ≤ (43647853625919/100000000000000 : ℝ)^99 := by
    have hnat : (1068909369 : ℕ)^131*100000000000000^99 ≤ 43647853625919^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068909369 2000000000 43647853625919 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658316941/1250000000 : ℝ)^131 ≤ (42806813738461/100000000000000 : ℝ)^99 := by
    have hnat : (658316941 : ℕ)^131*100000000000000^99 ≤ 42806813738461^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658316941 1250000000 42806813738461 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2207351957/10000000000 : ℝ)^131 ≤ (1354533262661/10000000000000 : ℝ)^99 := by
    have hnat : (2207351957 : ℕ)^131*10000000000000^99 ≤ 1354533262661^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2207351957 10000000000 1354533262661 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068909369/2000000000 : ℝ), (658316941/1250000000 : ℝ), (-2207351957/10000000000 : ℝ)] ![(43647853625919/100000000000000 : ℝ), (42806813738461/100000000000000 : ℝ), (1354533262661/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068909369/2000000000 : ℝ)|^131 ≤ (43647853625919/100000000000000 : ℝ)^99
        have hw : |(1068909369/2000000000 : ℝ)|=(1068909369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658316941/1250000000 : ℝ)|^131 ≤ (42806813738461/100000000000000 : ℝ)^99
        have hw : |(658316941/1250000000 : ℝ)|=(658316941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2207351957/10000000000 : ℝ)|^131 ≤ (1354533262661/10000000000000 : ℝ)^99
        have hw : |(-2207351957/10000000000 : ℝ)|=(2207351957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s8_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2178908787/5000000000 : ℝ)*x 0 + (4233507993/10000000000 : ℝ)*x 1 + (1121429283/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178908787/5000000000 : ℝ)^131 ≤ (33317249538807/100000000000000 : ℝ)^99 := by
    have hnat : (2178908787 : ℕ)^131*100000000000000^99 ≤ 33317249538807^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178908787 5000000000 33317249538807 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233507993/10000000000 : ℝ)^131 ≤ (32065490080903/100000000000000 : ℝ)^99 := by
    have hnat : (4233507993 : ℕ)^131*100000000000000^99 ≤ 32065490080903^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233507993 10000000000 32065490080903 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121429283/2500000000 : ℝ)^131 ≤ (8654315090811/25000000000000 : ℝ)^99 := by
    have hnat : (1121429283 : ℕ)^131*25000000000000^99 ≤ 8654315090811^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121429283 2500000000 8654315090811 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178908787/5000000000 : ℝ), (4233507993/10000000000 : ℝ), (1121429283/2500000000 : ℝ)] ![(33317249538807/100000000000000 : ℝ), (32065490080903/100000000000000 : ℝ), (8654315090811/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178908787/5000000000 : ℝ)|^131 ≤ (33317249538807/100000000000000 : ℝ)^99
        have hw : |(2178908787/5000000000 : ℝ)|=(2178908787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233507993/10000000000 : ℝ)|^131 ≤ (32065490080903/100000000000000 : ℝ)^99
        have hw : |(4233507993/10000000000 : ℝ)|=(4233507993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121429283/2500000000 : ℝ)|^131 ≤ (8654315090811/25000000000000 : ℝ)^99
        have hw : |(1121429283/2500000000 : ℝ)|=(1121429283/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s8_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143681169/10000000000 : ℝ)*x 0 + (105337027/200000000 : ℝ)*x 1 + (5391782351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143681169/10000000000 : ℝ)^131 ≤ (13030754064987/100000000000000 : ℝ)^99 := by
    have hnat : (2143681169 : ℕ)^131*100000000000000^99 ≤ 13030754064987^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143681169 10000000000 13030754064987 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105337027/200000000 : ℝ)^131 ≤ (42810210543133/100000000000000 : ℝ)^99 := by
    have hnat : (105337027 : ℕ)^131*100000000000000^99 ≤ 42810210543133^99*200000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105337027 200000000 42810210543133 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391782351/10000000000 : ℝ)^131 ≤ (11039758843817/25000000000000 : ℝ)^99 := by
    have hnat : (5391782351 : ℕ)^131*25000000000000^99 ≤ 11039758843817^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391782351 10000000000 11039758843817 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143681169/10000000000 : ℝ), (105337027/200000000 : ℝ), (5391782351/10000000000 : ℝ)] ![(13030754064987/100000000000000 : ℝ), (42810210543133/100000000000000 : ℝ), (11039758843817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143681169/10000000000 : ℝ)|^131 ≤ (13030754064987/100000000000000 : ℝ)^99
        have hw : |(-2143681169/10000000000 : ℝ)|=(2143681169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105337027/200000000 : ℝ)|^131 ≤ (42810210543133/100000000000000 : ℝ)^99
        have hw : |(105337027/200000000 : ℝ)|=(105337027/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391782351/10000000000 : ℝ)|^131 ≤ (11039758843817/25000000000000 : ℝ)^99
        have hw : |(5391782351/10000000000 : ℝ)|=(5391782351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s8_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312621513/10000000000 : ℝ)*x 0 + (-2082105107/10000000000 : ℝ)*x 1 + (1347945589/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312621513/10000000000 : ℝ)^131 ≤ (10825795905667/25000000000000 : ℝ)^99 := by
    have hnat : (5312621513 : ℕ)^131*25000000000000^99 ≤ 10825795905667^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312621513 10000000000 10825795905667 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082105107/10000000000 : ℝ)^131 ≤ (2507556187477/20000000000000 : ℝ)^99 := by
    have hnat : (2082105107 : ℕ)^131*20000000000000^99 ≤ 2507556187477^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082105107 10000000000 2507556187477 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347945589/2500000000 : ℝ)^131 ≤ (22079517714727/50000000000000 : ℝ)^99 := by
    have hnat : (1347945589 : ℕ)^131*50000000000000^99 ≤ 22079517714727^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347945589 2500000000 22079517714727 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312621513/10000000000 : ℝ), (-2082105107/10000000000 : ℝ), (1347945589/2500000000 : ℝ)] ![(10825795905667/25000000000000 : ℝ), (2507556187477/20000000000000 : ℝ), (22079517714727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312621513/10000000000 : ℝ)|^131 ≤ (10825795905667/25000000000000 : ℝ)^99
        have hw : |(5312621513/10000000000 : ℝ)|=(5312621513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2082105107/10000000000 : ℝ)|^131 ≤ (2507556187477/20000000000000 : ℝ)^99
        have hw : |(-2082105107/10000000000 : ℝ)|=(2082105107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347945589/2500000000 : ℝ)|^131 ≤ (22079517714727/50000000000000 : ℝ)^99
        have hw : |(1347945589/2500000000 : ℝ)|=(1347945589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s8_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1328155367/2500000000 : ℝ)*x 0 + (5391782359/10000000000 : ℝ)*x 1 + (-1041052581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328155367/2500000000 : ℝ)^131 ≤ (43303183137313/100000000000000 : ℝ)^99 := by
    have hnat : (1328155367 : ℕ)^131*100000000000000^99 ≤ 43303183137313^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328155367 2500000000 43303183137313 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391782359/10000000000 : ℝ)^131 ≤ (22079517730983/50000000000000 : ℝ)^99 := by
    have hnat : (5391782359 : ℕ)^131*50000000000000^99 ≤ 22079517730983^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391782359 10000000000 22079517730983 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041052581/5000000000 : ℝ)^131 ≤ (12537781375629/100000000000000 : ℝ)^99 := by
    have hnat : (1041052581 : ℕ)^131*100000000000000^99 ≤ 12537781375629^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041052581 5000000000 12537781375629 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328155367/2500000000 : ℝ), (5391782359/10000000000 : ℝ), (-1041052581/5000000000 : ℝ)] ![(43303183137313/100000000000000 : ℝ), (22079517730983/50000000000000 : ℝ), (12537781375629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328155367/2500000000 : ℝ)|^131 ≤ (43303183137313/100000000000000 : ℝ)^99
        have hw : |(1328155367/2500000000 : ℝ)|=(1328155367/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391782359/10000000000 : ℝ)|^131 ≤ (22079517730983/50000000000000 : ℝ)^99
        have hw : |(5391782359/10000000000 : ℝ)|=(5391782359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1041052581/5000000000 : ℝ)|^131 ≤ (12537781375629/100000000000000 : ℝ)^99
        have hw : |(-1041052581/5000000000 : ℝ)|=(1041052581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s8_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4357827091/10000000000 : ℝ)*x 0 + (4485082739/10000000000 : ℝ)*x 1 + (4234144727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357827091/10000000000 : ℝ)^131 ≤ (16658672909441/50000000000000 : ℝ)^99 := by
    have hnat : (4357827091 : ℕ)^131*50000000000000^99 ≤ 16658672909441^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357827091 10000000000 16658672909441 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4485082739/10000000000 : ℝ)^131 ≤ (1730539114863/5000000000000 : ℝ)^99 := by
    have hnat : (4485082739 : ℕ)^131*5000000000000^99 ≤ 1730539114863^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485082739 10000000000 1730539114863 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4234144727/10000000000 : ℝ)^131 ≤ (32071871866299/100000000000000 : ℝ)^99 := by
    have hnat : (4234144727 : ℕ)^131*100000000000000^99 ≤ 32071871866299^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234144727 10000000000 32071871866299 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357827091/10000000000 : ℝ), (4485082739/10000000000 : ℝ), (4234144727/10000000000 : ℝ)] ![(16658672909441/50000000000000 : ℝ), (1730539114863/5000000000000 : ℝ), (32071871866299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357827091/10000000000 : ℝ)|^131 ≤ (16658672909441/50000000000000 : ℝ)^99
        have hw : |(4357827091/10000000000 : ℝ)|=(4357827091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4485082739/10000000000 : ℝ)|^131 ≤ (1730539114863/5000000000000 : ℝ)^99
        have hw : |(4485082739/10000000000 : ℝ)|=(4485082739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4234144727/10000000000 : ℝ)|^131 ≤ (32071871866299/100000000000000 : ℝ)^99
        have hw : |(4234144727/10000000000 : ℝ)|=(4234144727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (1427/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2283/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2283/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2283/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14077/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2283/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2283/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14077/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2283/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2283/20000 : ℝ) ^ (8383/2048 : ℝ) ≤ (13867630046422261/100000000000000000000 : ℝ) := by
    have hpowers : (2283/20000 : ℝ)^8383 ≤ (13867630046422261/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2283 : ℕ)^8383*100000000000000000000^2048 ≤ 13867630046422261^2048*20000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2283 20000 13867630046422261 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2283/20000 : ℝ)) (X := (13867630046422261/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14077/100000 : ℝ) ^ (8383/2048 : ℝ) ≤ (32706120452158273/100000000000000000000 : ℝ) := by
    have hpowers : (14077/100000 : ℝ)^8383 ≤ (32706120452158273/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14077 : ℕ)^8383*100000000000000000000^2048 ≤ 32706120452158273^2048*100000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14077 100000 32706120452158273 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14077/100000 : ℝ)) (X := (32706120452158273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013867630046422261/50000000000000000000 : ℝ) ≤ (1250084689044747/1250000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50013867630046422261/50000000000000000000 : ℝ)^2048 ≤ (1250084689044747/1250000000000000 : ℝ)^8383 := by
      have hnat : (50013867630046422261 : ℕ)^2048*1250000000000000^8383 ≤ 1250084689044747^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013867630046422261 50000000000000000000 1250084689044747 1250000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250084689044747/1250000000000000 : ℝ)) (X := (50013867630046422261/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023286875249290267/50000000000000000000 : ℝ) ≤ (10001137614938307/10000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50023286875249290267/50000000000000000000 : ℝ)^2048 ≤ (10001137614938307/10000000000000000 : ℝ)^8383 := by
      have hnat : (50023286875249290267 : ℕ)^2048*10000000000000000^8383 ≤ 10001137614938307^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023286875249290267 50000000000000000000 10001137614938307 10000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001137614938307/10000000000000000 : ℝ)) (X := (50023286875249290267/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032706120452158273/50000000000000000000 : ℝ) ≤ (5000798858759319/5000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50032706120452158273/50000000000000000000 : ℝ)^2048 ≤ (5000798858759319/5000000000000000 : ℝ)^8383 := by
      have hnat : (50032706120452158273 : ℕ)^2048*5000000000000000^8383 ≤ 5000798858759319^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032706120452158273 50000000000000000000 5000798858759319 5000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000798858759319/5000000000000000 : ℝ)) (X := (50032706120452158273/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13867630046422261/100000000000000000000 : ℝ) ≤ ((13305649697993987691/13310000000000000000 : ℝ)+2*(460102580331/266200000000000 : ℝ)*(2283/20000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (13305649697993987691/13310000000000000000 : ℝ)+2*(460102580331/266200000000000 : ℝ)*(2283/20000 : ℝ)=(1250084689044747/1250000000000000 : ℝ) by norm_num, show 1+2*(13867630046422261/100000000000000000000 : ℝ)=(50013867630046422261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32706120452158273/100000000000000000000 : ℝ)+(13867630046422261/100000000000000000000 : ℝ) ≤ ((13305649697993987691/13310000000000000000 : ℝ)+(460102580331/266200000000000 : ℝ)*((14077/100000 : ℝ)+(2283/20000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (13305649697993987691/13310000000000000000 : ℝ)+(460102580331/266200000000000 : ℝ)*((14077/100000 : ℝ)+(2283/20000 : ℝ))=(10001137614938307/10000000000000000 : ℝ) by norm_num, show 1+(32706120452158273/100000000000000000000 : ℝ)+(13867630046422261/100000000000000000000 : ℝ)=(50023286875249290267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32706120452158273/100000000000000000000 : ℝ) ≤ ((13305649697993987691/13310000000000000000 : ℝ)+2*(460102580331/266200000000000 : ℝ)*(14077/100000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (13305649697993987691/13310000000000000000 : ℝ)+2*(460102580331/266200000000000 : ℝ)*(14077/100000 : ℝ)=(5000798858759319/5000000000000000 : ℝ) by norm_num, show 1+2*(32706120452158273/100000000000000000000 : ℝ)=(50032706120452158273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13305649697993987691/13310000000000000000 : ℝ)*(X 1 0+X 2 0)+(460102580331/266200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (13305649697993987691/13310000000000000000 : ℝ)) (alpha := (460102580331/266200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13305649697993987691/13310000000000000000 : ℝ)*(X 0 1+X 2 1)+(460102580331/266200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (13305649697993987691/13310000000000000000 : ℝ)) (alpha := (460102580331/266200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13305649697993987691/13310000000000000000 : ℝ)*(X 0 2+X 1 2)+(460102580331/266200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2283/20000 : ℝ)) (hi := (14077/100000 : ℝ)) (c := (13305649697993987691/13310000000000000000 : ℝ)) (alpha := (460102580331/266200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2143676401/10000000000 : ℝ)*X 0 0+(1078419863/2000000000 : ℝ)*X 0 1+(1053307107/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336136711/2500000000 : ℝ)*X 1 0+(-2207352019/10000000000 : ℝ)*X 1 1+(2633267741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068909369/2000000000 : ℝ)*X 2 0+(658316941/1250000000 : ℝ)*X 2 1+(-2207351957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178908787/5000000000 : ℝ)*X 0 0+(4233507993/10000000000 : ℝ)*X 0 1+(1121429283/2500000000 : ℝ)*X 0 2+(2178908787/5000000000 : ℝ)*X 1 0+(4233507993/10000000000 : ℝ)*X 1 1+(1121429283/2500000000 : ℝ)*X 1 2+(2178908787/5000000000 : ℝ)*X 2 0+(4233507993/10000000000 : ℝ)*X 2 1+(1121429283/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2143681169/10000000000 : ℝ)*X 0 0+(105337027/200000000 : ℝ)*X 0 1+(5391782351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312621513/10000000000 : ℝ)*X 1 0+(-2082105107/10000000000 : ℝ)*X 1 1+(1347945589/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328155367/2500000000 : ℝ)*X 2 0+(5391782359/10000000000 : ℝ)*X 2 1+(-1041052581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357827091/10000000000 : ℝ)*X 0 0+(4485082739/10000000000 : ℝ)*X 0 1+(4234144727/10000000000 : ℝ)*X 0 2+(4357827091/10000000000 : ℝ)*X 1 0+(4485082739/10000000000 : ℝ)*X 1 1+(4234144727/10000000000 : ℝ)*X 1 2+(4357827091/10000000000 : ℝ)*X 2 0+(4485082739/10000000000 : ℝ)*X 2 1+(4234144727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79904502537025635241596201/7562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2056248051/100000000000000 : ℝ)*(base19) + (58706477/3125000000000 : ℝ)*(base23) + (11967171/12500000000000 : ℝ)*(lower2) + (28051647/12500000000000 : ℝ)*(upper3) + (193739733/100000000000000 : ℝ)*(upper5) + (1491151507687093/25000000000000 : ℝ)*(major0) + (1491151507687093/25000000000000 : ℝ)*(major1) + (1491151507687093/25000000000000 : ℝ)*(major2) + (7964134891084757/100000000000000 : ℝ)*(sp0) + (1592837851794391/20000000000000 : ℝ)*(sp1) + (3982094718306371/50000000000000 : ℝ)*(sp2) + (991247750715979/25000000000000 : ℝ)*(sp3) + (56424135249/100000000000000 : ℝ)*(sp4) + (14695608327/50000000000000 : ℝ)*(sp7) + (396502039408057/10000000000000 : ℝ)*(f.failure) + (3982095657610003/50000000000000 : ℝ)*(f.sum) + (5675203820867/3327500000000000000000000000 : ℝ)*base66 + (4785276089918472263/332750000000000000000000000000000 : ℝ)*base67 + (13897551989722263/332750000000000000000000000000000 : ℝ)*base69 + (8497801175146222263/332750000000000000000000000000000 : ℝ)*base71 + (1003261610971/6655000000000000000000000000 : ℝ)*base73 + (1456150991809277737/332750000000000000000000000000000 : ℝ)*base76 + (2853316682878722263/332750000000000000000000000000000 : ℝ)*base77 + (7076053478018222263/332750000000000000000000000000000 : ℝ)*base79 + (8154086890607/3327500000000000000000000000 : ℝ)*base82 + (2859209/250000000000000000000 : ℝ)*base90 + (2859209/250000000000000000000 : ℝ)*base92 + (2859209/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2435074880285294229845823153/665500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670970741/100000000000000 : ℝ)*(base19) + (625703407/100000000000000 : ℝ)*(base23) + (106603737/50000000000000 : ℝ)*(lower1) + (29248931/50000000000000 : ℝ)*(upper3) + (22547967/100000000000000 : ℝ)*(lower4) + (34199613/50000000000000 : ℝ)*(upper5) + (5994719460543013/100000000000000 : ℝ)*(major0) + (5994719460543013/100000000000000 : ℝ)*(major1) + (5994719460543013/100000000000000 : ℝ)*(major2) + (662607931/20000000000000 : ℝ)*(sp1) + (2001100064385881/25000000000000 : ℝ)*(sp4) + (8004396273533129/100000000000000 : ℝ)*(sp5) + (8004399631840117/100000000000000 : ℝ)*(sp6) + (1992519270787649/50000000000000 : ℝ)*(sp7) + (1992519270787649/50000000000000 : ℝ)*(f.failure) + (2001100064385881/25000000000000 : ℝ)*(f.sum) + (57488761417083/13310000000000000000000000000 : ℝ)*base65 + (24444955934081202983/1331000000000000000000000000000000 : ℝ)*base67 + (24639734543293202983/1331000000000000000000000000000000 : ℝ)*base69 + (9566821655898202983/1331000000000000000000000000000000 : ℝ)*base71 + (7328969443363/13310000000000000000000000000 : ℝ)*base73 + (32976232483283202983/1331000000000000000000000000000000 : ℝ)*base75 + (1451543277669202983/1331000000000000000000000000000000 : ℝ)*base77 + (37108171653488202983/1331000000000000000000000000000000 : ℝ)*base79 + (53606618676783/13310000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (14345713/1250000000000000000000 : ℝ)*base90 + (14345713/1250000000000000000000 : ℝ)*base92 + (14345713/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1191_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14077/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2283/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1427/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1191_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1427/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1191_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1191_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1191_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1427/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
