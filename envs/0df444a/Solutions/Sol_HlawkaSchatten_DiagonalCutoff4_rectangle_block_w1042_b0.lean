-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:48:01.993999+00:00
-- url     : https://prove2.me/submissions/cef0283a-a138-4187-a9f0-f480a2261a19

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
theorem support_rectangle_w1042_s0_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5501251009/10000000000 : ℝ)*x 0 + (-334734281/1250000000 : ℝ)*x 1 + (598817183/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501251009/10000000000 : ℝ)^8235 ≤ (5642348373703/12500000000000 : ℝ)^6187 := by
    have hnat : (5501251009 : ℕ)^8235*12500000000000^6187 ≤ 5642348373703^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501251009 10000000000 5642348373703 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (334734281/1250000000 : ℝ)^8235 ≤ (17313273990861/100000000000000 : ℝ)^6187 := by
    have hnat : (334734281 : ℕ)^8235*100000000000000^6187 ≤ 17313273990861^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334734281 1250000000 17313273990861 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (598817183/1250000000 : ℝ)^8235 ≤ (586686546961/1562500000000 : ℝ)^6187 := by
    have hnat : (598817183 : ℕ)^8235*1562500000000^6187 ≤ 586686546961^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598817183 1250000000 586686546961 1562500000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501251009/10000000000 : ℝ), (-334734281/1250000000 : ℝ), (598817183/1250000000 : ℝ)] ![(5642348373703/12500000000000 : ℝ), (17313273990861/100000000000000 : ℝ), (586686546961/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501251009/10000000000 : ℝ)|^8235 ≤ (5642348373703/12500000000000 : ℝ)^6187
        have hw : |(5501251009/10000000000 : ℝ)|=(5501251009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-334734281/1250000000 : ℝ)|^8235 ≤ (17313273990861/100000000000000 : ℝ)^6187
        have hw : |(-334734281/1250000000 : ℝ)|=(334734281/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(598817183/1250000000 : ℝ)|^8235 ≤ (586686546961/1562500000000 : ℝ)^6187
        have hw : |(598817183/1250000000 : ℝ)|=(598817183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s0_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5506457771/10000000000 : ℝ)*x 0 + (4775663801/10000000000 : ℝ)*x 1 + (-168079963/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506457771/10000000000 : ℝ)^8235 ≤ (45195660187549/100000000000000 : ℝ)^6187 := by
    have hnat : (5506457771 : ℕ)^8235*100000000000000^6187 ≤ 45195660187549^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506457771 10000000000 45195660187549 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4775663801/10000000000 : ℝ)^8235 ≤ (9348212598807/25000000000000 : ℝ)^6187 := by
    have hnat : (4775663801 : ℕ)^8235*25000000000000^6187 ≤ 9348212598807^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775663801 10000000000 9348212598807 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168079963/625000000 : ℝ)^8235 ≤ (17411489400351/100000000000000 : ℝ)^6187 := by
    have hnat : (168079963 : ℕ)^8235*100000000000000^6187 ≤ 17411489400351^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168079963 625000000 17411489400351 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506457771/10000000000 : ℝ), (4775663801/10000000000 : ℝ), (-168079963/625000000 : ℝ)] ![(45195660187549/100000000000000 : ℝ), (9348212598807/25000000000000 : ℝ), (17411489400351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506457771/10000000000 : ℝ)|^8235 ≤ (45195660187549/100000000000000 : ℝ)^6187
        have hw : |(5506457771/10000000000 : ℝ)|=(5506457771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4775663801/10000000000 : ℝ)|^8235 ≤ (9348212598807/25000000000000 : ℝ)^6187
        have hw : |(4775663801/10000000000 : ℝ)|=(4775663801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-168079963/625000000 : ℝ)|^8235 ≤ (17411489400351/100000000000000 : ℝ)^6187
        have hw : |(-168079963/625000000 : ℝ)|=(168079963/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s0_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-964658067/5000000000 : ℝ)*x 0 + (1200383071/2500000000 : ℝ)*x 1 + (3021357447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964658067/5000000000 : ℝ)^8235 ≤ (11190771387523/100000000000000 : ℝ)^6187 := by
    have hnat : (964658067 : ℕ)^8235*100000000000000^6187 ≤ 11190771387523^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964658067 5000000000 11190771387523 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1200383071/2500000000 : ℝ)^8235 ≤ (37662685210127/100000000000000 : ℝ)^6187 := by
    have hnat : (1200383071 : ℕ)^8235*100000000000000^6187 ≤ 37662685210127^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200383071 2500000000 37662685210127 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021357447/5000000000 : ℝ)^8235 ≤ (399582370239/781250000000 : ℝ)^6187 := by
    have hnat : (3021357447 : ℕ)^8235*781250000000^6187 ≤ 399582370239^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021357447 5000000000 399582370239 781250000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-964658067/5000000000 : ℝ), (1200383071/2500000000 : ℝ), (3021357447/5000000000 : ℝ)] ![(11190771387523/100000000000000 : ℝ), (37662685210127/100000000000000 : ℝ), (399582370239/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-964658067/5000000000 : ℝ)|^8235 ≤ (11190771387523/100000000000000 : ℝ)^6187
        have hw : |(-964658067/5000000000 : ℝ)|=(964658067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1200383071/2500000000 : ℝ)|^8235 ≤ (37662685210127/100000000000000 : ℝ)^6187
        have hw : |(1200383071/2500000000 : ℝ)|=(1200383071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3021357447/5000000000 : ℝ)|^8235 ≤ (399582370239/781250000000 : ℝ)^6187
        have hw : |(3021357447/5000000000 : ℝ)|=(3021357447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s0_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2583497839/5000000000 : ℝ)*x 0 + (-701817651/5000000000 : ℝ)*x 1 + (3021357549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2583497839/5000000000 : ℝ)^8235 ≤ (10381381321187/25000000000000 : ℝ)^6187 := by
    have hnat : (2583497839 : ℕ)^8235*25000000000000^6187 ≤ 10381381321187^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2583497839 5000000000 10381381321187 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701817651/5000000000 : ℝ)^8235 ≤ (3663964505559/50000000000000 : ℝ)^6187 := by
    have hnat : (701817651 : ℕ)^8235*50000000000000^6187 ≤ 3663964505559^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701817651 5000000000 3663964505559 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021357549/5000000000 : ℝ)^8235 ≤ (10229309137769/20000000000000 : ℝ)^6187 := by
    have hnat : (3021357549 : ℕ)^8235*20000000000000^6187 ≤ 10229309137769^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021357549 5000000000 10229309137769 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2583497839/5000000000 : ℝ), (-701817651/5000000000 : ℝ), (3021357549/5000000000 : ℝ)] ![(10381381321187/25000000000000 : ℝ), (3663964505559/50000000000000 : ℝ), (10229309137769/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2583497839/5000000000 : ℝ)|^8235 ≤ (10381381321187/25000000000000 : ℝ)^6187
        have hw : |(2583497839/5000000000 : ℝ)|=(2583497839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-701817651/5000000000 : ℝ)|^8235 ≤ (3663964505559/50000000000000 : ℝ)^6187
        have hw : |(-701817651/5000000000 : ℝ)|=(701817651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3021357549/5000000000 : ℝ)|^8235 ≤ (10229309137769/20000000000000 : ℝ)^6187
        have hw : |(3021357549/5000000000 : ℝ)|=(3021357549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s0_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (516699193/1000000000 : ℝ)*x 0 + (3021359331/5000000000 : ℝ)*x 1 + (-701817647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (516699193/1000000000 : ℝ)^8235 ≤ (10381371298133/25000000000000 : ℝ)^6187 := by
    have hnat : (516699193 : ℕ)^8235*25000000000000^6187 ≤ 10381371298133^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516699193 1000000000 10381371298133 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3021359331/5000000000 : ℝ)^8235 ≤ (25573292920341/50000000000000 : ℝ)^6187 := by
    have hnat : (3021359331 : ℕ)^8235*50000000000000^6187 ≤ 25573292920341^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021359331 5000000000 25573292920341 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (701817647/5000000000 : ℝ)^8235 ≤ (7327928955527/100000000000000 : ℝ)^6187 := by
    have hnat : (701817647 : ℕ)^8235*100000000000000^6187 ≤ 7327928955527^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701817647 5000000000 7327928955527 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(516699193/1000000000 : ℝ), (3021359331/5000000000 : ℝ), (-701817647/5000000000 : ℝ)] ![(10381371298133/25000000000000 : ℝ), (25573292920341/50000000000000 : ℝ), (7327928955527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(516699193/1000000000 : ℝ)|^8235 ≤ (10381371298133/25000000000000 : ℝ)^6187
        have hw : |(516699193/1000000000 : ℝ)|=(516699193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3021359331/5000000000 : ℝ)|^8235 ≤ (25573292920341/50000000000000 : ℝ)^6187
        have hw : |(3021359331/5000000000 : ℝ)|=(3021359331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-701817647/5000000000 : ℝ)|^8235 ≤ (7327928955527/100000000000000 : ℝ)^6187
        have hw : |(-701817647/5000000000 : ℝ)|=(701817647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s0_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4219823541/10000000000 : ℝ)*x 0 + (2807721379/5000000000 : ℝ)*x 1 + (638895351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4219823541/10000000000 : ℝ)^8235 ≤ (7928672355173/25000000000000 : ℝ)^6187 := by
    have hnat : (4219823541 : ℕ)^8235*25000000000000^6187 ≤ 7928672355173^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219823541 10000000000 7928672355173 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2807721379/5000000000 : ℝ)^8235 ≤ (23195083601781/50000000000000 : ℝ)^6187 := by
    have hnat : (2807721379 : ℕ)^8235*50000000000000^6187 ≤ 23195083601781^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2807721379 5000000000 23195083601781 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638895351/2000000000 : ℝ)^8235 ≤ (1368446459679/6250000000000 : ℝ)^6187 := by
    have hnat : (638895351 : ℕ)^8235*6250000000000^6187 ≤ 1368446459679^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638895351 2000000000 1368446459679 6250000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4219823541/10000000000 : ℝ), (2807721379/5000000000 : ℝ), (638895351/2000000000 : ℝ)] ![(7928672355173/25000000000000 : ℝ), (23195083601781/50000000000000 : ℝ), (1368446459679/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4219823541/10000000000 : ℝ)|^8235 ≤ (7928672355173/25000000000000 : ℝ)^6187
        have hw : |(4219823541/10000000000 : ℝ)|=(4219823541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2807721379/5000000000 : ℝ)|^8235 ≤ (23195083601781/50000000000000 : ℝ)^6187
        have hw : |(2807721379/5000000000 : ℝ)|=(2807721379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638895351/2000000000 : ℝ)|^8235 ≤ (1368446459679/6250000000000 : ℝ)^6187
        have hw : |(638895351/2000000000 : ℝ)|=(638895351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28203/100000 : ℝ)*pair X 0 0 := by
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
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (4117/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4117 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4117*1^1024 ≤ 0^1024*1^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4117/1024 : ℝ) ≤ (502468778927156833/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4117 ≤ (502468778927156833/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4117*20000000000000000000^1024 ≤ 502468778927156833^1024*5^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 502468778927156833 20000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (502468778927156833/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4117 := by
      have hnat : (1 : ℕ)^1024*1^4117 ≤ 1^4117*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20502468778927156833/20000000000000000000 : ℝ) ≤ (1257738375588387/1250000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (20502468778927156833/20000000000000000000 : ℝ)^1024 ≤ (1257738375588387/1250000000000000 : ℝ)^4117 := by
      have hnat : (20502468778927156833 : ℕ)^1024*1250000000000000^4117 ≤ 1257738375588387^4117*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20502468778927156833 20000000000000000000 1257738375588387 1250000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1257738375588387/1250000000000000 : ℝ)) (X := (20502468778927156833/20000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10502468778927156833/10000000000000000000 : ℝ) ≤ (632738375588387/625000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (10502468778927156833/10000000000000000000 : ℝ)^1024 ≤ (632738375588387/625000000000000 : ℝ)^4117 := by
      have hnat : (10502468778927156833 : ℕ)^1024*625000000000000^4117 ≤ 632738375588387^4117*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10502468778927156833 10000000000000000000 632738375588387 625000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (632738375588387/625000000000000 : ℝ)) (X := (10502468778927156833/10000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7738375588387/500000000000000 : ℝ)*(0 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7738375588387/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(502468778927156833/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7738375588387/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7738375588387/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1257738375588387/1250000000000000 : ℝ) by norm_num, show 1+(502468778927156833/20000000000000000000 : ℝ)+(0 : ℝ)=(20502468778927156833/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(502468778927156833/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7738375588387/500000000000000 : ℝ)*(2/5 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7738375588387/500000000000000 : ℝ)*(2/5 : ℝ)=(632738375588387/625000000000000 : ℝ) by norm_num, show 1+2*(502468778927156833/20000000000000000000 : ℝ)=(10502468778927156833/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7738375588387/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7738375588387/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7738375588387/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7738375588387/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7738375588387/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7738375588387/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5501251009/10000000000 : ℝ)*X 1 0+(-334734281/1250000000 : ℝ)*X 1 1+(598817183/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5506457771/10000000000 : ℝ)*X 2 0+(4775663801/10000000000 : ℝ)*X 2 1+(-168079963/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-964658067/5000000000 : ℝ)*X 0 0+(1200383071/2500000000 : ℝ)*X 0 1+(3021357447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2583497839/5000000000 : ℝ)*X 1 0+(-701817651/5000000000 : ℝ)*X 1 1+(3021357549/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((516699193/1000000000 : ℝ)*X 2 0+(3021359331/5000000000 : ℝ)*X 2 1+(-701817647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4219823541/10000000000 : ℝ)*X 0 0+(2807721379/5000000000 : ℝ)*X 0 1+(638895351/2000000000 : ℝ)*X 0 2+(4219823541/10000000000 : ℝ)*X 1 0+(2807721379/5000000000 : ℝ)*X 1 1+(638895351/2000000000 : ℝ)*X 1 2+(4219823541/10000000000 : ℝ)*X 2 0+(2807721379/5000000000 : ℝ)*X 2 1+(638895351/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91942421723650928258901/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (185178817/25000000000000 : ℝ)*(base19) + (982185221/100000000000000 : ℝ)*(base23) + (173713953/25000000000000 : ℝ)*(base39) + (51233247/50000000000000 : ℝ)*(upper2) + (29452949/10000000000000 : ℝ)*(upper5) + (609368209581471/100000000000000 : ℝ)*(major0) + (609368209581471/100000000000000 : ℝ)*(major1) + (609367514725659/100000000000000 : ℝ)*(major2) + (2472157043/100000000000000 : ℝ)*(sp0) + (431742213/25000000000000 : ℝ)*(sp1) + (80567848078563/10000000000000 : ℝ)*(sp2) + (805675267913319/100000000000000 : ℝ)*(sp3) + (805676466487369/100000000000000 : ℝ)*(sp4) + (413057120931601/100000000000000 : ℝ)*(sp5) + (413057120931601/100000000000000 : ℝ)*(f.failure) + (402839587820721/50000000000000 : ℝ)*(f.sum) + (391841324931/5000000000000000000000000000 : ℝ)*base65 + (136497287422033/50000000000000000000000000000 : ℝ)*base67 + (279699760772723/50000000000000000000000000000 : ℝ)*base70 + (20272029177967/50000000000000000000000000000 : ℝ)*base72 + (23558767149931/5000000000000000000000000000 : ℝ)*base73 + (271568560472723/50000000000000000000000000000 : ℝ)*base76 + (161164372172723/50000000000000000000000000000 : ℝ)*base78 + (13784476422723/50000000000000000000000000000 : ℝ)*base80 + (46759796652277/25000000000000000000000000000 : ℝ)*base81 + (9364411/5000000000000000000000 : ℝ)*base90 + (9364411/5000000000000000000000 : ℝ)*base92 + (9364411/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1042_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28203/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1042_s1_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-427141367/2000000000 : ℝ)*x 0 + (2864528713/5000000000 : ℝ)*x 1 + (622586471/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427141367/2000000000 : ℝ)^8235 ≤ (1281175892019/10000000000000 : ℝ)^6187 := by
    have hnat : (427141367 : ℕ)^8235*10000000000000^6187 ≤ 1281175892019^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427141367 2000000000 1281175892019 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2864528713/5000000000 : ℝ)^8235 ≤ (23821806000119/50000000000000 : ℝ)^6187 := by
    have hnat : (2864528713 : ℕ)^8235*50000000000000^6187 ≤ 23821806000119^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2864528713 5000000000 23821806000119 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622586471/1250000000 : ℝ)^8235 ≤ (39544629060569/100000000000000 : ℝ)^6187 := by
    have hnat : (622586471 : ℕ)^8235*100000000000000^6187 ≤ 39544629060569^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622586471 1250000000 39544629060569 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-427141367/2000000000 : ℝ), (2864528713/5000000000 : ℝ), (622586471/1250000000 : ℝ)] ![(1281175892019/10000000000000 : ℝ), (23821806000119/50000000000000 : ℝ), (39544629060569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-427141367/2000000000 : ℝ)|^8235 ≤ (1281175892019/10000000000000 : ℝ)^6187
        have hw : |(-427141367/2000000000 : ℝ)|=(427141367/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2864528713/5000000000 : ℝ)|^8235 ≤ (23821806000119/50000000000000 : ℝ)^6187
        have hw : |(2864528713/5000000000 : ℝ)|=(2864528713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622586471/1250000000 : ℝ)|^8235 ≤ (39544629060569/100000000000000 : ℝ)^6187
        have hw : |(622586471/1250000000 : ℝ)|=(622586471/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1084927729/2000000000 : ℝ)*x 0 + (-2541692293/10000000000 : ℝ)*x 1 + (4980692089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084927729/2000000000 : ℝ)^8235 ≤ (8860803923011/20000000000000 : ℝ)^6187 := by
    have hnat : (1084927729 : ℕ)^8235*20000000000000^6187 ≤ 8860803923011^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084927729 2000000000 8860803923011 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541692293/10000000000 : ℝ)^8235 ≤ (4037836979267/25000000000000 : ℝ)^6187 := by
    have hnat : (2541692293 : ℕ)^8235*25000000000000^6187 ≤ 4037836979267^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541692293 10000000000 4037836979267 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4980692089/10000000000 : ℝ)^8235 ≤ (39544632452807/100000000000000 : ℝ)^6187 := by
    have hnat : (4980692089 : ℕ)^8235*100000000000000^6187 ≤ 39544632452807^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980692089 10000000000 39544632452807 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084927729/2000000000 : ℝ), (-2541692293/10000000000 : ℝ), (4980692089/10000000000 : ℝ)] ![(8860803923011/20000000000000 : ℝ), (4037836979267/25000000000000 : ℝ), (39544632452807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084927729/2000000000 : ℝ)|^8235 ≤ (8860803923011/20000000000000 : ℝ)^6187
        have hw : |(1084927729/2000000000 : ℝ)|=(1084927729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2541692293/10000000000 : ℝ)|^8235 ≤ (4037836979267/25000000000000 : ℝ)^6187
        have hw : |(-2541692293/10000000000 : ℝ)|=(2541692293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4980692089/10000000000 : ℝ)|^8235 ≤ (39544632452807/100000000000000 : ℝ)^6187
        have hw : |(4980692089/10000000000 : ℝ)|=(4980692089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (542463903/1000000000 : ℝ)*x 0 + (622586451/1250000000 : ℝ)*x 1 + (-6354231/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542463903/1000000000 : ℝ)^8235 ≤ (44304023800259/100000000000000 : ℝ)^6187 := by
    have hnat : (542463903 : ℕ)^8235*100000000000000^6187 ≤ 44304023800259^6187*1000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542463903 1000000000 44304023800259 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622586451/1250000000 : ℝ)^8235 ≤ (19772313684867/50000000000000 : ℝ)^6187 := by
    have hnat : (622586451 : ℕ)^8235*50000000000000^6187 ≤ 19772313684867^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622586451 1250000000 19772313684867 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6354231/25000000 : ℝ)^8235 ≤ (8075674411039/50000000000000 : ℝ)^6187 := by
    have hnat : (6354231 : ℕ)^8235*50000000000000^6187 ≤ 8075674411039^6187*25000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6354231 25000000 8075674411039 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542463903/1000000000 : ℝ), (622586451/1250000000 : ℝ), (-6354231/25000000 : ℝ)] ![(44304023800259/100000000000000 : ℝ), (19772313684867/50000000000000 : ℝ), (8075674411039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542463903/1000000000 : ℝ)|^8235 ≤ (44304023800259/100000000000000 : ℝ)^6187
        have hw : |(542463903/1000000000 : ℝ)|=(542463903/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(622586451/1250000000 : ℝ)|^8235 ≤ (19772313684867/50000000000000 : ℝ)^6187
        have hw : |(622586451/1250000000 : ℝ)|=(622586451/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6354231/25000000 : ℝ)|^8235 ≤ (8075674411039/50000000000000 : ℝ)^6187
        have hw : |(-6354231/25000000 : ℝ)|=(6354231/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4325795253/10000000000 : ℝ)*x 0 + (3657973901/10000000000 : ℝ)*x 1 + (5117680433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325795253/10000000000 : ℝ)^8235 ≤ (16389576737497/50000000000000 : ℝ)^6187 := by
    have hnat : (4325795253 : ℕ)^8235*50000000000000^6187 ≤ 16389576737497^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325795253 10000000000 16389576737497 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3657973901/10000000000 : ℝ)^8235 ≤ (51214862363/195312500000 : ℝ)^6187 := by
    have hnat : (3657973901 : ℕ)^8235*195312500000^6187 ≤ 51214862363^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3657973901 10000000000 51214862363 195312500000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5117680433/10000000000 : ℝ)^8235 ≤ (8199767396719/20000000000000 : ℝ)^6187 := by
    have hnat : (5117680433 : ℕ)^8235*20000000000000^6187 ≤ 8199767396719^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117680433 10000000000 8199767396719 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325795253/10000000000 : ℝ), (3657973901/10000000000 : ℝ), (5117680433/10000000000 : ℝ)] ![(16389576737497/50000000000000 : ℝ), (51214862363/195312500000 : ℝ), (8199767396719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325795253/10000000000 : ℝ)|^8235 ≤ (16389576737497/50000000000000 : ℝ)^6187
        have hw : |(4325795253/10000000000 : ℝ)|=(4325795253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3657973901/10000000000 : ℝ)|^8235 ≤ (51214862363/195312500000 : ℝ)^6187
        have hw : |(3657973901/10000000000 : ℝ)|=(3657973901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5117680433/10000000000 : ℝ)|^8235 ≤ (8199767396719/20000000000000 : ℝ)^6187
        have hw : |(5117680433/10000000000 : ℝ)|=(5117680433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-534166729/2500000000 : ℝ)*x 0 + (623912843/1250000000 : ℝ)*x 1 + (2859113671/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534166729/2500000000 : ℝ)^8235 ≤ (12819425308113/100000000000000 : ℝ)^6187 := by
    have hnat : (534166729 : ℕ)^8235*100000000000000^6187 ≤ 12819425308113^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534166729 2500000000 12819425308113 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623912843/1250000000 : ℝ)^8235 ≤ (39656802411447/100000000000000 : ℝ)^6187 := by
    have hnat : (623912843 : ℕ)^8235*100000000000000^6187 ≤ 39656802411447^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623912843 1250000000 39656802411447 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2859113671/5000000000 : ℝ)^8235 ≤ (11880943065031/25000000000000 : ℝ)^6187 := by
    have hnat : (2859113671 : ℕ)^8235*25000000000000^6187 ≤ 11880943065031^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2859113671 5000000000 11880943065031 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-534166729/2500000000 : ℝ), (623912843/1250000000 : ℝ), (2859113671/5000000000 : ℝ)] ![(12819425308113/100000000000000 : ℝ), (39656802411447/100000000000000 : ℝ), (11880943065031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-534166729/2500000000 : ℝ)|^8235 ≤ (12819425308113/100000000000000 : ℝ)^6187
        have hw : |(-534166729/2500000000 : ℝ)|=(534166729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623912843/1250000000 : ℝ)|^8235 ≤ (39656802411447/100000000000000 : ℝ)^6187
        have hw : |(623912843/1250000000 : ℝ)|=(623912843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2859113671/5000000000 : ℝ)|^8235 ≤ (11880943065031/25000000000000 : ℝ)^6187
        have hw : |(2859113671/5000000000 : ℝ)|=(2859113671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5233758269/10000000000 : ℝ)*x 0 + (-72166219/400000000 : ℝ)*x 1 + (5718228501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233758269/10000000000 : ℝ)^8235 ≤ (42241205168343/100000000000000 : ℝ)^6187 := by
    have hnat : (5233758269 : ℕ)^8235*100000000000000^6187 ≤ 42241205168343^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233758269 10000000000 42241205168343 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (72166219/400000000 : ℝ)^8235 ≤ (1023500973681/10000000000000 : ℝ)^6187 := by
    have hnat : (72166219 : ℕ)^8235*10000000000000^6187 ≤ 1023500973681^6187*400000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72166219 400000000 1023500973681 10000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5718228501/10000000000 : ℝ)^8235 ≤ (47523785080963/100000000000000 : ℝ)^6187 := by
    have hnat : (5718228501 : ℕ)^8235*100000000000000^6187 ≤ 47523785080963^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5718228501 10000000000 47523785080963 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233758269/10000000000 : ℝ), (-72166219/400000000 : ℝ), (5718228501/10000000000 : ℝ)] ![(42241205168343/100000000000000 : ℝ), (1023500973681/10000000000000 : ℝ), (47523785080963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233758269/10000000000 : ℝ)|^8235 ≤ (42241205168343/100000000000000 : ℝ)^6187
        have hw : |(5233758269/10000000000 : ℝ)|=(5233758269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-72166219/400000000 : ℝ)|^8235 ≤ (1023500973681/10000000000000 : ℝ)^6187
        have hw : |(-72166219/400000000 : ℝ)|=(72166219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5718228501/10000000000 : ℝ)|^8235 ≤ (47523785080963/100000000000000 : ℝ)^6187
        have hw : |(5718228501/10000000000 : ℝ)|=(5718228501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5233756389/10000000000 : ℝ)*x 0 + (1429557641/2500000000 : ℝ)*x 1 + (-225519391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233756389/10000000000 : ℝ)^8235 ≤ (42241184972409/100000000000000 : ℝ)^6187 := by
    have hnat : (5233756389 : ℕ)^8235*100000000000000^6187 ≤ 42241184972409^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233756389 10000000000 42241184972409 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429557641/2500000000 : ℝ)^8235 ≤ (11880951975459/25000000000000 : ℝ)^6187 := by
    have hnat : (1429557641 : ℕ)^8235*25000000000000^6187 ≤ 11880951975459^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429557641 2500000000 11880951975459 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225519391/1250000000 : ℝ)^8235 ≤ (10235007116653/100000000000000 : ℝ)^6187 := by
    have hnat : (225519391 : ℕ)^8235*100000000000000^6187 ≤ 10235007116653^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225519391 1250000000 10235007116653 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233756389/10000000000 : ℝ), (1429557641/2500000000 : ℝ), (-225519391/1250000000 : ℝ)] ![(42241184972409/100000000000000 : ℝ), (11880951975459/25000000000000 : ℝ), (10235007116653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233756389/10000000000 : ℝ)|^8235 ≤ (42241184972409/100000000000000 : ℝ)^6187
        have hw : |(5233756389/10000000000 : ℝ)|=(5233756389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1429557641/2500000000 : ℝ)|^8235 ≤ (11880951975459/25000000000000 : ℝ)^6187
        have hw : |(1429557641/2500000000 : ℝ)|=(1429557641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-225519391/1250000000 : ℝ)|^8235 ≤ (10235007116653/100000000000000 : ℝ)^6187
        have hw : |(-225519391/1250000000 : ℝ)|=(225519391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4327664861/10000000000 : ℝ)*x 0 + (5096980107/10000000000 : ℝ)*x 1 + (3679095751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327664861/10000000000 : ℝ)^8235 ≤ (8199502882317/25000000000000 : ℝ)^6187 := by
    have hnat : (4327664861 : ℕ)^8235*25000000000000^6187 ≤ 8199502882317^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327664861 10000000000 8199502882317 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5096980107/10000000000 : ℝ)^8235 ≤ (40778256063563/100000000000000 : ℝ)^6187 := by
    have hnat : (5096980107 : ℕ)^8235*100000000000000^6187 ≤ 40778256063563^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096980107 10000000000 40778256063563 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679095751/10000000000 : ℝ)^8235 ≤ (13211866196671/50000000000000 : ℝ)^6187 := by
    have hnat : (3679095751 : ℕ)^8235*50000000000000^6187 ≤ 13211866196671^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679095751 10000000000 13211866196671 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327664861/10000000000 : ℝ), (5096980107/10000000000 : ℝ), (3679095751/10000000000 : ℝ)] ![(8199502882317/25000000000000 : ℝ), (40778256063563/100000000000000 : ℝ), (13211866196671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327664861/10000000000 : ℝ)|^8235 ≤ (8199502882317/25000000000000 : ℝ)^6187
        have hw : |(4327664861/10000000000 : ℝ)|=(4327664861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5096980107/10000000000 : ℝ)|^8235 ≤ (40778256063563/100000000000000 : ℝ)^6187
        have hw : |(5096980107/10000000000 : ℝ)|=(5096980107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679095751/10000000000 : ℝ)|^8235 ≤ (13211866196671/50000000000000 : ℝ)^6187
        have hw : |(3679095751/10000000000 : ℝ)|=(3679095751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_8 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (9710393/10000000000 : ℝ)*x 0 + (171556477/312500000 : ℝ)*x 1 + (6379592219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9710393/10000000000 : ℝ)^8235 ≤ (4885758977/50000000000000 : ℝ)^6187 := by
    have hnat : (9710393 : ℕ)^8235*50000000000000^6187 ≤ 4885758977^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9710393 10000000000 4885758977 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171556477/312500000 : ℝ)^8235 ≤ (45013850165191/100000000000000 : ℝ)^6187 := by
    have hnat : (171556477 : ℕ)^8235*100000000000000^6187 ≤ 45013850165191^6187*312500000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171556477 312500000 45013850165191 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6379592219/10000000000 : ℝ)^8235 ≤ (54976378306987/100000000000000 : ℝ)^6187 := by
    have hnat : (6379592219 : ℕ)^8235*100000000000000^6187 ≤ 54976378306987^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6379592219 10000000000 54976378306987 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9710393/10000000000 : ℝ), (171556477/312500000 : ℝ), (6379592219/10000000000 : ℝ)] ![(4885758977/50000000000000 : ℝ), (45013850165191/100000000000000 : ℝ), (54976378306987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9710393/10000000000 : ℝ)|^8235 ≤ (4885758977/50000000000000 : ℝ)^6187
        have hw : |(9710393/10000000000 : ℝ)|=(9710393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(171556477/312500000 : ℝ)|^8235 ≤ (45013850165191/100000000000000 : ℝ)^6187
        have hw : |(171556477/312500000 : ℝ)|=(171556477/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6379592219/10000000000 : ℝ)|^8235 ≤ (54976378306987/100000000000000 : ℝ)^6187
        have hw : |(6379592219/10000000000 : ℝ)|=(6379592219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_9 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1534173/16000000 : ℝ)*x 0 + (-4474685363/10000000000 : ℝ)*x 1 + (3461604231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1534173/16000000 : ℝ)^8235 ≤ (2206317939057/50000000000000 : ℝ)^6187 := by
    have hnat : (1534173 : ℕ)^8235*50000000000000^6187 ≤ 2206317939057^6187*16000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534173 16000000 2206317939057 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4474685363/10000000000 : ℝ)^8235 ≤ (342893362117/1000000000000 : ℝ)^6187 := by
    have hnat : (4474685363 : ℕ)^8235*1000000000000^6187 ≤ 342893362117^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474685363 10000000000 342893362117 1000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3461604231/5000000000 : ℝ)^8235 ≤ (15324506972823/25000000000000 : ℝ)^6187 := by
    have hnat : (3461604231 : ℕ)^8235*25000000000000^6187 ≤ 15324506972823^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3461604231 5000000000 15324506972823 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1534173/16000000 : ℝ), (-4474685363/10000000000 : ℝ), (3461604231/5000000000 : ℝ)] ![(2206317939057/50000000000000 : ℝ), (342893362117/1000000000000 : ℝ), (15324506972823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1534173/16000000 : ℝ)|^8235 ≤ (2206317939057/50000000000000 : ℝ)^6187
        have hw : |(1534173/16000000 : ℝ)|=(1534173/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4474685363/10000000000 : ℝ)|^8235 ≤ (342893362117/1000000000000 : ℝ)^6187
        have hw : |(-4474685363/10000000000 : ℝ)|=(4474685363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3461604231/5000000000 : ℝ)|^8235 ≤ (15324506972823/25000000000000 : ℝ)^6187
        have hw : |(3461604231/5000000000 : ℝ)|=(3461604231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_10 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (119856609/1250000000 : ℝ)*x 0 + (1730799319/2500000000 : ℝ)*x 1 + (-2237350721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (119856609/1250000000 : ℝ)^8235 ≤ (68946932843/1562500000000 : ℝ)^6187 := by
    have hnat : (119856609 : ℕ)^8235*1562500000000^6187 ≤ 68946932843^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119856609 1250000000 68946932843 1562500000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1730799319/2500000000 : ℝ)^8235 ≤ (15324474016611/25000000000000 : ℝ)^6187 := by
    have hnat : (1730799319 : ℕ)^8235*25000000000000^6187 ≤ 15324474016611^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730799319 2500000000 15324474016611 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237350721/5000000000 : ℝ)^8235 ≤ (8572375052501/25000000000000 : ℝ)^6187 := by
    have hnat : (2237350721 : ℕ)^8235*25000000000000^6187 ≤ 8572375052501^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237350721 5000000000 8572375052501 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(119856609/1250000000 : ℝ), (1730799319/2500000000 : ℝ), (-2237350721/5000000000 : ℝ)] ![(68946932843/1562500000000 : ℝ), (15324474016611/25000000000000 : ℝ), (8572375052501/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(119856609/1250000000 : ℝ)|^8235 ≤ (68946932843/1562500000000 : ℝ)^6187
        have hw : |(119856609/1250000000 : ℝ)|=(119856609/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1730799319/2500000000 : ℝ)|^8235 ≤ (15324474016611/25000000000000 : ℝ)^6187
        have hw : |(1730799319/2500000000 : ℝ)|=(1730799319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237350721/5000000000 : ℝ)|^8235 ≤ (8572375052501/25000000000000 : ℝ)^6187
        have hw : |(-2237350721/5000000000 : ℝ)|=(2237350721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s1_11 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (964041761/5000000000 : ℝ)*x 0 + (5836274829/10000000000 : ℝ)*x 1 + (5022276493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (964041761/5000000000 : ℝ)^8235 ≤ (559062806469/5000000000000 : ℝ)^6187 := by
    have hnat : (964041761 : ℕ)^8235*5000000000000^6187 ≤ 559062806469^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964041761 5000000000 559062806469 5000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5836274829/10000000000 : ℝ)^8235 ≤ (48834052903213/100000000000000 : ℝ)^6187 := by
    have hnat : (5836274829 : ℕ)^8235*100000000000000^6187 ≤ 48834052903213^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5836274829 10000000000 48834052903213 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022276493/10000000000 : ℝ)^8235 ≤ (9996172740073/25000000000000 : ℝ)^6187 := by
    have hnat : (5022276493 : ℕ)^8235*25000000000000^6187 ≤ 9996172740073^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022276493 10000000000 9996172740073 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(964041761/5000000000 : ℝ), (5836274829/10000000000 : ℝ), (5022276493/10000000000 : ℝ)] ![(559062806469/5000000000000 : ℝ), (48834052903213/100000000000000 : ℝ), (9996172740073/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(964041761/5000000000 : ℝ)|^8235 ≤ (559062806469/5000000000000 : ℝ)^6187
        have hw : |(964041761/5000000000 : ℝ)|=(964041761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5836274829/10000000000 : ℝ)|^8235 ≤ (48834052903213/100000000000000 : ℝ)^6187
        have hw : |(5836274829/10000000000 : ℝ)|=(5836274829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022276493/10000000000 : ℝ)|^8235 ≤ (9996172740073/25000000000000 : ℝ)^6187
        have hw : |(5022276493/10000000000 : ℝ)|=(5022276493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (317/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4181/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28203/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28203/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28203/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28203/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4117/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4117 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4117*1^1024 ≤ 0^1024*1^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (28203/100000 : ℝ) ^ (4117/1024 : ℝ) ≤ (61646438171417183/10000000000000000000 : ℝ) := by
    have hpowers : (28203/100000 : ℝ)^4117 ≤ (61646438171417183/10000000000000000000 : ℝ)^1024 := by
      have hnat : (28203 : ℕ)^4117*10000000000000000000^1024 ≤ 61646438171417183^1024*100000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28203 100000 61646438171417183 10000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28203/100000 : ℝ)) (X := (61646438171417183/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4117 := by
      have hnat : (1 : ℕ)^1024*1^4117 ≤ 1^4117*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10061646438171417183/10000000000000000000 : ℝ) ≤ (1251912202377777/1250000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (10061646438171417183/10000000000000000000 : ℝ)^1024 ≤ (1251912202377777/1250000000000000 : ℝ)^4117 := by
      have hnat : (10061646438171417183 : ℕ)^1024*1250000000000000^4117 ≤ 1251912202377777^4117*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10061646438171417183 10000000000000000000 1251912202377777 1250000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1251912202377777/1250000000000000 : ℝ)) (X := (10061646438171417183/10000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5061646438171417183/5000000000000000000 : ℝ) ≤ (626912202377777/625000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (5061646438171417183/5000000000000000000 : ℝ)^1024 ≤ (626912202377777/625000000000000 : ℝ)^4117 := by
      have hnat : (5061646438171417183 : ℕ)^1024*625000000000000^4117 ≤ 626912202377777^4117*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5061646438171417183 5000000000000000000 626912202377777 625000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626912202377777/625000000000000 : ℝ)) (X := (5061646438171417183/5000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1912202377777/352537500000000 : ℝ)*(0 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1912202377777/352537500000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(61646438171417183/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1912202377777/352537500000000 : ℝ)*((28203/100000 : ℝ)+(0 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1912202377777/352537500000000 : ℝ)*((28203/100000 : ℝ)+(0 : ℝ))=(1251912202377777/1250000000000000 : ℝ) by norm_num, show 1+(61646438171417183/10000000000000000000 : ℝ)+(0 : ℝ)=(10061646438171417183/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(61646438171417183/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1912202377777/352537500000000 : ℝ)*(28203/100000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1912202377777/352537500000000 : ℝ)*(28203/100000 : ℝ)=(626912202377777/625000000000000 : ℝ) by norm_num, show 1+2*(61646438171417183/10000000000000000000 : ℝ)=(5061646438171417183/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1912202377777/352537500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (28203/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (1912202377777/352537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1912202377777/352537500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (28203/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (1912202377777/352537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1912202377777/352537500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (28203/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (1912202377777/352537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-427141367/2000000000 : ℝ)*X 0 0+(2864528713/5000000000 : ℝ)*X 0 1+(622586471/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1084927729/2000000000 : ℝ)*X 1 0+(-2541692293/10000000000 : ℝ)*X 1 1+(4980692089/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((542463903/1000000000 : ℝ)*X 2 0+(622586451/1250000000 : ℝ)*X 2 1+(-6354231/25000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325795253/10000000000 : ℝ)*X 0 0+(3657973901/10000000000 : ℝ)*X 0 1+(5117680433/10000000000 : ℝ)*X 0 2+(4325795253/10000000000 : ℝ)*X 1 0+(3657973901/10000000000 : ℝ)*X 1 1+(5117680433/10000000000 : ℝ)*X 1 2+(4325795253/10000000000 : ℝ)*X 2 0+(3657973901/10000000000 : ℝ)*X 2 1+(5117680433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-534166729/2500000000 : ℝ)*X 0 0+(623912843/1250000000 : ℝ)*X 0 1+(2859113671/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5233758269/10000000000 : ℝ)*X 1 0+(-72166219/400000000 : ℝ)*X 1 1+(5718228501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5233756389/10000000000 : ℝ)*X 2 0+(1429557641/2500000000 : ℝ)*X 2 1+(-225519391/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327664861/10000000000 : ℝ)*X 0 0+(5096980107/10000000000 : ℝ)*X 0 1+(3679095751/10000000000 : ℝ)*X 0 2+(4327664861/10000000000 : ℝ)*X 1 0+(5096980107/10000000000 : ℝ)*X 1 1+(3679095751/10000000000 : ℝ)*X 1 2+(4327664861/10000000000 : ℝ)*X 2 0+(5096980107/10000000000 : ℝ)*X 2 1+(3679095751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((9710393/10000000000 : ℝ)*X 0 0+(171556477/312500000 : ℝ)*X 0 1+(6379592219/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1534173/16000000 : ℝ)*X 1 0+(-4474685363/10000000000 : ℝ)*X 1 1+(3461604231/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((119856609/1250000000 : ℝ)*X 2 0+(1730799319/2500000000 : ℝ)*X 2 1+(-2237350721/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((964041761/5000000000 : ℝ)*X 0 0+(5836274829/10000000000 : ℝ)*X 0 1+(5022276493/10000000000 : ℝ)*X 0 2+(964041761/5000000000 : ℝ)*X 1 0+(5836274829/10000000000 : ℝ)*X 1 1+(5022276493/10000000000 : ℝ)*X 1 2+(964041761/5000000000 : ℝ)*X 2 0+(5836274829/10000000000 : ℝ)*X 2 1+(5022276493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7030161911052357356481/940100000000000000000000000 : ℝ) := by norm_num
    linear_combination (126332487364269/12500000000000 : ℝ)*(major0) + (126332487364269/12500000000000 : ℝ)*(major1) + (126332487364269/12500000000000 : ℝ)*(major2) + (334061761456953/25000000000000 : ℝ)*(sp0) + (267249551925673/20000000000000 : ℝ)*(sp1) + (668123567550219/50000000000000 : ℝ)*(sp2) + (685069689799997/100000000000000 : ℝ)*(sp3) + (1159460039/100000000000000 : ℝ)*(sp4) + (136585723/20000000000000 : ℝ)*(sp5) + (1215000629/100000000000000 : ℝ)*(sp6) + (8816463/1250000000000 : ℝ)*(sp8) + (468047911/100000000000000 : ℝ)*(sp9) + (35031489/6250000000000 : ℝ)*(sp10) + (14814897/1562500000000 : ℝ)*(sp11) + (342535318976703/50000000000000 : ℝ)*(f.failure) + (1336248910604891/100000000000000 : ℝ)*(f.sum) + (59909565749979/47005000000000000000000000000 : ℝ)*base65 + (83363818319387/47005000000000000000000000000 : ℝ)*base67 + (94083612127677/47005000000000000000000000000 : ℝ)*base69 + (7969723274411/5875625000000000000000000000 : ℝ)*base72 + (18550862855557/23502500000000000000000000000 : ℝ)*base73 + (76154317862837/47005000000000000000000000000 : ℝ)*base75 + (34861470756821/23502500000000000000000000000 : ℝ)*base77 + (44576467632407/47005000000000000000000000000 : ℝ)*base79 + (43629537612319/47005000000000000000000000000 : ℝ)*base81 + (29985867/2500000000000000000000 : ℝ)*base89 + (29985867/2500000000000000000000 : ℝ)*base91 + (29985867/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1991160693505764939/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10973273/5000000000000 : ℝ)*(base59) + (40296997/100000000000000 : ℝ)*(upper5) + (208093462370791/20000000000000 : ℝ)*(major0) + (208093462370791/20000000000000 : ℝ)*(major1) + (208093462370791/20000000000000 : ℝ)*(major2) + (613550043/50000000000000 : ℝ)*(sp0) + (979314433/100000000000000 : ℝ)*(sp1) + (757686033/25000000000000 : ℝ)*(sp2) + (6878276014779/500000000000 : ℝ)*(sp4) + (85978633613699/6250000000000 : ℝ)*(sp5) + (687828043194743/50000000000000 : ℝ)*(sp6) + (352637345894447/50000000000000 : ℝ)*(sp7) + (2687077731/100000000000000 : ℝ)*(sp8) + (748413369/100000000000000 : ℝ)*(sp11) + (88159430025283/12500000000000 : ℝ)*(f.failure) + (1375659117133617/100000000000000 : ℝ)*(f.sum) + (89629343263219/28203000000000000000000000000 : ℝ)*base66 + (155415238121491/28203000000000000000000000000 : ℝ)*base67 + (2692471633079/7050750000000000000000000000 : ℝ)*base70 + (31800301969571/28203000000000000000000000000 : ℝ)*base72 + (79804425972493/14101500000000000000000000000 : ℝ)*base73 + (19486135004983/7050750000000000000000000000 : ℝ)*base75 + (8653392704687/2820300000000000000000000000 : ℝ)*base78 + (107730104714129/28203000000000000000000000000 : ℝ)*base80 + (106899700818347/28203000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5957487/625000000000000000000 : ℝ)*base89 + (5957487/625000000000000000000 : ℝ)*base91 + (5957487/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1042_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28203/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (317/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4181/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1042_s2_0 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-548627093/2500000000 : ℝ)*x 0 + (2765453177/5000000000 : ℝ)*x 1 + (1285389981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (548627093/2500000000 : ℝ)^8235 ≤ (13283389391713/100000000000000 : ℝ)^6187 := by
    have hnat : (548627093 : ℕ)^8235*100000000000000^6187 ≤ 13283389391713^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548627093 2500000000 13283389391713 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2765453177/5000000000 : ℝ)^8235 ≤ (1818517948471/4000000000000 : ℝ)^6187 := by
    have hnat : (2765453177 : ℕ)^8235*4000000000000^6187 ≤ 1818517948471^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765453177 5000000000 1818517948471 4000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1285389981/2500000000 : ℝ)^8235 ≤ (41253661872657/100000000000000 : ℝ)^6187 := by
    have hnat : (1285389981 : ℕ)^8235*100000000000000^6187 ≤ 41253661872657^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285389981 2500000000 41253661872657 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-548627093/2500000000 : ℝ), (2765453177/5000000000 : ℝ), (1285389981/2500000000 : ℝ)] ![(13283389391713/100000000000000 : ℝ), (1818517948471/4000000000000 : ℝ), (41253661872657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-548627093/2500000000 : ℝ)|^8235 ≤ (13283389391713/100000000000000 : ℝ)^6187
        have hw : |(-548627093/2500000000 : ℝ)|=(548627093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2765453177/5000000000 : ℝ)|^8235 ≤ (1818517948471/4000000000000 : ℝ)^6187
        have hw : |(2765453177/5000000000 : ℝ)|=(2765453177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1285389981/2500000000 : ℝ)|^8235 ≤ (41253661872657/100000000000000 : ℝ)^6187
        have hw : |(1285389981/2500000000 : ℝ)|=(1285389981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s2_1 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (215131109/400000000 : ℝ)*x 0 + (-2397765897/10000000000 : ℝ)*x 1 + (2570780309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215131109/400000000 : ℝ)^8235 ≤ (43800760172859/100000000000000 : ℝ)^6187 := by
    have hnat : (215131109 : ℕ)^8235*100000000000000^6187 ≤ 43800760172859^6187*400000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215131109 400000000 43800760172859 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397765897/10000000000 : ℝ)^8235 ≤ (14945570516927/100000000000000 : ℝ)^6187 := by
    have hnat : (2397765897 : ℕ)^8235*100000000000000^6187 ≤ 14945570516927^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397765897 10000000000 14945570516927 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570780309/5000000000 : ℝ)^8235 ≤ (41253669284233/100000000000000 : ℝ)^6187 := by
    have hnat : (2570780309 : ℕ)^8235*100000000000000^6187 ≤ 41253669284233^6187*5000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570780309 5000000000 41253669284233 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215131109/400000000 : ℝ), (-2397765897/10000000000 : ℝ), (2570780309/5000000000 : ℝ)] ![(43800760172859/100000000000000 : ℝ), (14945570516927/100000000000000 : ℝ), (41253669284233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215131109/400000000 : ℝ)|^8235 ≤ (43800760172859/100000000000000 : ℝ)^6187
        have hw : |(215131109/400000000 : ℝ)|=(215131109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2397765897/10000000000 : ℝ)|^8235 ≤ (14945570516927/100000000000000 : ℝ)^6187
        have hw : |(-2397765897/10000000000 : ℝ)|=(2397765897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570780309/5000000000 : ℝ)|^8235 ≤ (41253669284233/100000000000000 : ℝ)^6187
        have hw : |(2570780309/5000000000 : ℝ)|=(2570780309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s2_2 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5378277903/10000000000 : ℝ)*x 0 + (5141560379/10000000000 : ℝ)*x 1 + (-599441493/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378277903/10000000000 : ℝ)^8235 ≤ (21900381051173/50000000000000 : ℝ)^6187 := by
    have hnat : (5378277903 : ℕ)^8235*50000000000000^6187 ≤ 21900381051173^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378277903 10000000000 21900381051173 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5141560379/10000000000 : ℝ)^8235 ≤ (41253666731831/100000000000000 : ℝ)^6187 := by
    have hnat : (5141560379 : ℕ)^8235*100000000000000^6187 ≤ 41253666731831^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5141560379 10000000000 41253666731831 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (599441493/2500000000 : ℝ)^8235 ≤ (3736392784789/25000000000000 : ℝ)^6187 := by
    have hnat : (599441493 : ℕ)^8235*25000000000000^6187 ≤ 3736392784789^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599441493 2500000000 3736392784789 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378277903/10000000000 : ℝ), (5141560379/10000000000 : ℝ), (-599441493/2500000000 : ℝ)] ![(21900381051173/50000000000000 : ℝ), (41253666731831/100000000000000 : ℝ), (3736392784789/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378277903/10000000000 : ℝ)|^8235 ≤ (21900381051173/50000000000000 : ℝ)^6187
        have hw : |(5378277903/10000000000 : ℝ)|=(5378277903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5141560379/10000000000 : ℝ)|^8235 ≤ (41253666731831/100000000000000 : ℝ)^6187
        have hw : |(5141560379/10000000000 : ℝ)|=(5141560379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-599441493/2500000000 : ℝ)|^8235 ≤ (3736392784789/25000000000000 : ℝ)^6187
        have hw : |(-599441493/2500000000 : ℝ)|=(599441493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s2_3 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873165403/2000000000 : ℝ)*x 0 + (4002857663/10000000000 : ℝ)*x 1 + (148821461/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873165403/2000000000 : ℝ)^8235 ≤ (6636705505223/20000000000000 : ℝ)^6187 := by
    have hnat : (873165403 : ℕ)^8235*20000000000000^6187 ≤ 6636705505223^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873165403 2000000000 6636705505223 20000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4002857663/10000000000 : ℝ)^8235 ≤ (7390742224573/25000000000000 : ℝ)^6187 := by
    have hnat : (4002857663 : ℕ)^8235*25000000000000^6187 ≤ 7390742224573^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002857663 10000000000 7390742224573 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (148821461/312500000 : ℝ)^8235 ≤ (18626751778537/50000000000000 : ℝ)^6187 := by
    have hnat : (148821461 : ℕ)^8235*50000000000000^6187 ≤ 18626751778537^6187*312500000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148821461 312500000 18626751778537 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873165403/2000000000 : ℝ), (4002857663/10000000000 : ℝ), (148821461/312500000 : ℝ)] ![(6636705505223/20000000000000 : ℝ), (7390742224573/25000000000000 : ℝ), (18626751778537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873165403/2000000000 : ℝ)|^8235 ≤ (6636705505223/20000000000000 : ℝ)^6187
        have hw : |(873165403/2000000000 : ℝ)|=(873165403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4002857663/10000000000 : ℝ)|^8235 ≤ (7390742224573/25000000000000 : ℝ)^6187
        have hw : |(4002857663/10000000000 : ℝ)|=(4002857663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(148821461/312500000 : ℝ)|^8235 ≤ (18626751778537/50000000000000 : ℝ)^6187
        have hw : |(148821461/312500000 : ℝ)|=(148821461/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s2_4 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194642717/10000000000 : ℝ)*x 0 + (643055043/1250000000 : ℝ)*x 1 + (5527995253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194642717/10000000000 : ℝ)^8235 ≤ (13284471774949/100000000000000 : ℝ)^6187 := by
    have hnat : (2194642717 : ℕ)^8235*100000000000000^6187 ≤ 13284471774949^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194642717 10000000000 13284471774949 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643055043/1250000000 : ℝ)^8235 ≤ (41284426182001/100000000000000 : ℝ)^6187 := by
    have hnat : (643055043 : ℕ)^8235*100000000000000^6187 ≤ 41284426182001^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643055043 1250000000 41284426182001 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527995253/10000000000 : ℝ)^8235 ≤ (22715551013927/50000000000000 : ℝ)^6187 := by
    have hnat : (5527995253 : ℕ)^8235*50000000000000^6187 ≤ 22715551013927^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527995253 10000000000 22715551013927 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194642717/10000000000 : ℝ), (643055043/1250000000 : ℝ), (5527995253/10000000000 : ℝ)] ![(13284471774949/100000000000000 : ℝ), (41284426182001/100000000000000 : ℝ), (22715551013927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194642717/10000000000 : ℝ)|^8235 ≤ (13284471774949/100000000000000 : ℝ)^6187
        have hw : |(-2194642717/10000000000 : ℝ)|=(2194642717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643055043/1250000000 : ℝ)|^8235 ≤ (41284426182001/100000000000000 : ℝ)^6187
        have hw : |(643055043/1250000000 : ℝ)|=(643055043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527995253/10000000000 : ℝ)|^8235 ≤ (22715551013927/50000000000000 : ℝ)^6187
        have hw : |(5527995253/10000000000 : ℝ)|=(5527995253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s2_5 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5280170699/10000000000 : ℝ)*x 0 + (-80453253/400000000 : ℝ)*x 1 + (345499707/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280170699/10000000000 : ℝ)^8235 ≤ (42740521915299/100000000000000 : ℝ)^6187 := by
    have hnat : (5280170699 : ℕ)^8235*100000000000000^6187 ≤ 42740521915299^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280170699 10000000000 42740521915299 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80453253/400000000 : ℝ)^8235 ≤ (5914187700027/50000000000000 : ℝ)^6187 := by
    have hnat : (80453253 : ℕ)^8235*50000000000000^6187 ≤ 5914187700027^6187*400000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80453253 400000000 5914187700027 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345499707/625000000 : ℝ)^8235 ≤ (45431102673243/100000000000000 : ℝ)^6187 := by
    have hnat : (345499707 : ℕ)^8235*100000000000000^6187 ≤ 45431102673243^6187*625000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345499707 625000000 45431102673243 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280170699/10000000000 : ℝ), (-80453253/400000000 : ℝ), (345499707/625000000 : ℝ)] ![(42740521915299/100000000000000 : ℝ), (5914187700027/50000000000000 : ℝ), (45431102673243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280170699/10000000000 : ℝ)|^8235 ≤ (42740521915299/100000000000000 : ℝ)^6187
        have hw : |(5280170699/10000000000 : ℝ)|=(5280170699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80453253/400000000 : ℝ)|^8235 ≤ (5914187700027/50000000000000 : ℝ)^6187
        have hw : |(-80453253/400000000 : ℝ)|=(80453253/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345499707/625000000 : ℝ)|^8235 ≤ (45431102673243/100000000000000 : ℝ)^6187
        have hw : |(345499707/625000000 : ℝ)|=(345499707/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s2_6 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1056034183/2000000000 : ℝ)*x 0 + (1381998789/2500000000 : ℝ)*x 1 + (-402266249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056034183/2000000000 : ℝ)^8235 ≤ (21370262121237/50000000000000 : ℝ)^6187 := by
    have hnat : (1056034183 : ℕ)^8235*50000000000000^6187 ≤ 21370262121237^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056034183 2000000000 21370262121237 50000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1381998789/2500000000 : ℝ)^8235 ≤ (5678887620849/12500000000000 : ℝ)^6187 := by
    have hnat : (1381998789 : ℕ)^8235*12500000000000^6187 ≤ 5678887620849^6187*2500000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1381998789 2500000000 5678887620849 12500000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (402266249/2000000000 : ℝ)^8235 ≤ (2957093693463/25000000000000 : ℝ)^6187 := by
    have hnat : (402266249 : ℕ)^8235*25000000000000^6187 ≤ 2957093693463^6187*2000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402266249 2000000000 2957093693463 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056034183/2000000000 : ℝ), (1381998789/2500000000 : ℝ), (-402266249/2000000000 : ℝ)] ![(21370262121237/50000000000000 : ℝ), (5678887620849/12500000000000 : ℝ), (2957093693463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056034183/2000000000 : ℝ)|^8235 ≤ (21370262121237/50000000000000 : ℝ)^6187
        have hw : |(1056034183/2000000000 : ℝ)|=(1056034183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1381998789/2500000000 : ℝ)|^8235 ≤ (5678887620849/12500000000000 : ℝ)^6187
        have hw : |(1381998789/2500000000 : ℝ)|=(1381998789/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-402266249/2000000000 : ℝ)|^8235 ≤ (2957093693463/25000000000000 : ℝ)^6187
        have hw : |(-402266249/2000000000 : ℝ)|=(402266249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1042_s2_7 (p : ℝ) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366089219/10000000000 : ℝ)*x 0 + (148645923/312500000 : ℝ)*x 1 + (501066877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366089219/10000000000 : ℝ)^8235 ≤ (33186180195617/100000000000000 : ℝ)^6187 := by
    have hnat : (4366089219 : ℕ)^8235*100000000000000^6187 ≤ 33186180195617^6187*10000000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366089219 10000000000 33186180195617 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (148645923/312500000 : ℝ)^8235 ≤ (9298757100619/25000000000000 : ℝ)^6187 := by
    have hnat : (148645923 : ℕ)^8235*25000000000000^6187 ≤ 9298757100619^6187*312500000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      148645923 312500000 9298757100619 25000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (501066877/1250000000 : ℝ)^8235 ≤ (29618791386267/100000000000000 : ℝ)^6187 := by
    have hnat : (501066877 : ℕ)^8235*100000000000000^6187 ≤ 29618791386267^6187*1250000000^8235 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501066877 1250000000 29618791386267 100000000000000 8235 6187 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8235/2048 : ℝ)) 8235 6187 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366089219/10000000000 : ℝ), (148645923/312500000 : ℝ), (501066877/1250000000 : ℝ)] ![(33186180195617/100000000000000 : ℝ), (9298757100619/25000000000000 : ℝ), (29618791386267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366089219/10000000000 : ℝ)|^8235 ≤ (33186180195617/100000000000000 : ℝ)^6187
        have hw : |(4366089219/10000000000 : ℝ)|=(4366089219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(148645923/312500000 : ℝ)|^8235 ≤ (9298757100619/25000000000000 : ℝ)^6187
        have hw : |(148645923/312500000 : ℝ)|=(148645923/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(501066877/1250000000 : ℝ)|^8235 ≤ (29618791386267/100000000000000 : ℝ)^6187
        have hw : |(501066877/1250000000 : ℝ)|=(501066877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1042_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (8593/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (841/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4181/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (317/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4181/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (317/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4181/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (317/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4181/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (317/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4181/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (317/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4181/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (317/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (317/6250 : ℝ) ^ (4117/1024 : ℝ) ≤ (622533946397517/100000000000000000000 : ℝ) := by
    have hpowers : (317/6250 : ℝ)^4117 ≤ (622533946397517/100000000000000000000 : ℝ)^1024 := by
      have hnat : (317 : ℕ)^4117*100000000000000000000^1024 ≤ 622533946397517^1024*6250^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        317 6250 622533946397517 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (317/6250 : ℝ)) (X := (622533946397517/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4181/20000 : ℝ) ^ (4117/1024 : ℝ) ≤ (184952627539756959/100000000000000000000 : ℝ) := by
    have hpowers : (4181/20000 : ℝ)^4117 ≤ (184952627539756959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4181 : ℕ)^4117*100000000000000000000^1024 ≤ 184952627539756959^1024*20000^4117 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4181 20000 184952627539756959 100000000000000000000 4117 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4181/20000 : ℝ)) (X := (184952627539756959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000622533946397517/50000000000000000000 : ℝ) ≤ (500001548389069/500000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50000622533946397517/50000000000000000000 : ℝ)^1024 ≤ (500001548389069/500000000000000 : ℝ)^4117 := by
      have hnat : (50000622533946397517 : ℕ)^1024*500000000000000^4117 ≤ 500001548389069^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000622533946397517 50000000000000000000 500001548389069 500000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500001548389069/500000000000000 : ℝ)) (X := (50000622533946397517/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25046393790371538619/25000000000000000000 : ℝ) ≤ (10004612500397739/10000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (25046393790371538619/25000000000000000000 : ℝ)^1024 ≤ (10004612500397739/10000000000000000 : ℝ)^4117 := by
      have hnat : (25046393790371538619 : ℕ)^1024*10000000000000000^4117 ≤ 10004612500397739^4117*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25046393790371538619 25000000000000000000 10004612500397739 10000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004612500397739/10000000000000000 : ℝ)) (X := (25046393790371538619/25000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50184952627539756959/50000000000000000000 : ℝ) ≤ (5004597016507049/5000000000000000 : ℝ) ^ (4117/1024 : ℝ) := by
    have hpowers : (50184952627539756959/50000000000000000000 : ℝ)^1024 ≤ (5004597016507049/5000000000000000 : ℝ)^4117 := by
      have hnat : (50184952627539756959 : ℕ)^1024*5000000000000000^4117 ≤ 5004597016507049^4117*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50184952627539756959 50000000000000000000 5004597016507049 5000000000000000 1024 4117 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004597016507049/5000000000000000 : ℝ)) (X := (50184952627539756959/50000000000000000000 : ℝ)) (by norm_num) 4117 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(622533946397517/100000000000000000000 : ℝ) ≤ ((39571003811505560961/39582500000000000000 : ℝ)+2*(4581532616359/1583300000000000 : ℝ)*(317/6250 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (39571003811505560961/39582500000000000000 : ℝ)+2*(4581532616359/1583300000000000 : ℝ)*(317/6250 : ℝ)=(500001548389069/500000000000000 : ℝ) by norm_num, show 1+2*(622533946397517/100000000000000000000 : ℝ)=(50000622533946397517/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(184952627539756959/100000000000000000000 : ℝ)+(622533946397517/100000000000000000000 : ℝ) ≤ ((39571003811505560961/39582500000000000000 : ℝ)+(4581532616359/1583300000000000 : ℝ)*((4181/20000 : ℝ)+(317/6250 : ℝ)))^(4117/1024 : ℝ) := by
    rw [show (39571003811505560961/39582500000000000000 : ℝ)+(4581532616359/1583300000000000 : ℝ)*((4181/20000 : ℝ)+(317/6250 : ℝ))=(10004612500397739/10000000000000000 : ℝ) by norm_num, show 1+(184952627539756959/100000000000000000000 : ℝ)+(622533946397517/100000000000000000000 : ℝ)=(25046393790371538619/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(184952627539756959/100000000000000000000 : ℝ) ≤ ((39571003811505560961/39582500000000000000 : ℝ)+2*(4581532616359/1583300000000000 : ℝ)*(4181/20000 : ℝ))^(4117/1024 : ℝ) := by
    rw [show (39571003811505560961/39582500000000000000 : ℝ)+2*(4581532616359/1583300000000000 : ℝ)*(4181/20000 : ℝ)=(5004597016507049/5000000000000000 : ℝ) by norm_num, show 1+2*(184952627539756959/100000000000000000000 : ℝ)=(50184952627539756959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39571003811505560961/39582500000000000000 : ℝ)*(X 1 0+X 2 0)+(4581532616359/1583300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (317/6250 : ℝ)) (hi := (4181/20000 : ℝ)) (c := (39571003811505560961/39582500000000000000 : ℝ)) (alpha := (4581532616359/1583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39571003811505560961/39582500000000000000 : ℝ)*(X 0 1+X 2 1)+(4581532616359/1583300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (317/6250 : ℝ)) (hi := (4181/20000 : ℝ)) (c := (39571003811505560961/39582500000000000000 : ℝ)) (alpha := (4581532616359/1583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39571003811505560961/39582500000000000000 : ℝ)*(X 0 2+X 1 2)+(4581532616359/1583300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4117/1024 : ℝ)) (lo := (317/6250 : ℝ)) (hi := (4181/20000 : ℝ)) (c := (39571003811505560961/39582500000000000000 : ℝ)) (alpha := (4581532616359/1583300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-548627093/2500000000 : ℝ)*X 0 0+(2765453177/5000000000 : ℝ)*X 0 1+(1285389981/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((215131109/400000000 : ℝ)*X 1 0+(-2397765897/10000000000 : ℝ)*X 1 1+(2570780309/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378277903/10000000000 : ℝ)*X 2 0+(5141560379/10000000000 : ℝ)*X 2 1+(-599441493/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((873165403/2000000000 : ℝ)*X 0 0+(4002857663/10000000000 : ℝ)*X 0 1+(148821461/312500000 : ℝ)*X 0 2+(873165403/2000000000 : ℝ)*X 1 0+(4002857663/10000000000 : ℝ)*X 1 1+(148821461/312500000 : ℝ)*X 1 2+(873165403/2000000000 : ℝ)*X 2 0+(4002857663/10000000000 : ℝ)*X 2 1+(148821461/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2194642717/10000000000 : ℝ)*X 0 0+(643055043/1250000000 : ℝ)*X 0 1+(5527995253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280170699/10000000000 : ℝ)*X 1 0+(-80453253/400000000 : ℝ)*X 1 1+(345499707/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056034183/2000000000 : ℝ)*X 2 0+(1381998789/2500000000 : ℝ)*X 2 1+(-402266249/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366089219/10000000000 : ℝ)*X 0 0+(148645923/312500000 : ℝ)*X 0 1+(501066877/1250000000 : ℝ)*X 0 2+(4366089219/10000000000 : ℝ)*X 1 0+(148645923/312500000 : ℝ)*X 1 1+(501066877/1250000000 : ℝ)*X 1 2+(4366089219/10000000000 : ℝ)*X 2 0+(148645923/312500000 : ℝ)*X 2 1+(501066877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1042_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1527096000387918541328475459/247390625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9604123/100000000000000 : ℝ)*(base1) + (71555497/5000000000000 : ℝ)*(base19) + (379028823/25000000000000 : ℝ)*(base23) + (46316651/25000000000000 : ℝ)*(upper3) + (80643037/50000000000000 : ℝ)*(upper5) + (242827232751599/12500000000000 : ℝ)*(major0) + (242827232751599/12500000000000 : ℝ)*(major1) + (242827232751599/12500000000000 : ℝ)*(major2) + (10273697092019/400000000000 : ℝ)*(sp0) + (642110128872793/25000000000000 : ℝ)*(sp1) + (2568440430485819/100000000000000 : ℝ)*(sp2) + (1316785876658543/100000000000000 : ℝ)*(sp3) + (3536640097/20000000000000 : ℝ)*(sp4) + (61483211/800000000000 : ℝ)*(sp7) + (32919839291601/2500000000000 : ℝ)*(f.failure) + (321055243325139/12500000000000 : ℝ)*(f.sum) + (55721700452703/79165000000000000000000000000 : ℝ)*base65 + (5415166754569154611/494781250000000000000000000000000 : ℝ)*base68 + (5916865388832779611/494781250000000000000000000000000 : ℝ)*base70 + (1902434427109560861/494781250000000000000000000000000 : ℝ)*base72 + (319717140405297/79165000000000000000000000000 : ℝ)*base74 + (2103550468467248361/494781250000000000000000000000000 : ℝ)*base76 + (1942419608293342111/494781250000000000000000000000000 : ℝ)*base78 + (3406675535217939139/494781250000000000000000000000000 : ℝ)*base79 + (63720301680473/19791250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (675589/125000000000000000000 : ℝ)*base89 + (675589/125000000000000000000 : ℝ)*base91 + (675589/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (940602040631510699025590739/395825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (399965143/100000000000000 : ℝ)*(base19) + (52495617/10000000000000 : ℝ)*(base23) + (291369/50000000000000 : ℝ)*(upper2) + (71609457/100000000000000 : ℝ)*(upper3) + (58227921/100000000000000 : ℝ)*(upper5) + (394384723013233/20000000000000 : ℝ)*(major0) + (394384723013233/20000000000000 : ℝ)*(major1) + (394384723013233/20000000000000 : ℝ)*(major2) + (396695607/12500000000000 : ℝ)*(sp1) + (4101062713/100000000000000 : ℝ)*(sp2) + (260718882459471/10000000000000 : ℝ)*(sp4) + (2607185251064711/100000000000000 : ℝ)*(sp5) + (1303592099287913/50000000000000 : ℝ)*(sp6) + (668329163163677/50000000000000 : ℝ)*(sp7) + (668329163163677/50000000000000 : ℝ)*(f.failure) + (260718882459471/10000000000000 : ℝ)*(f.sum) + (42044614881799/15833000000000000000000000000 : ℝ)*base65 + (6110098990676228087/791650000000000000000000000000000 : ℝ)*base68 + (4055982023237728087/791650000000000000000000000000000 : ℝ)*base70 + (6225809824982378087/791650000000000000000000000000000 : ℝ)*base72 + (7735013329713/7916500000000000000000000000 : ℝ)*base73 + (4979175920084228087/791650000000000000000000000000000 : ℝ)*base76 + (2031340304951621913/791650000000000000000000000000000 : ℝ)*base77 + (2116120738062821913/791650000000000000000000000000000 : ℝ)*base79 + (24402888892267/15833000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19485953/2500000000000000000000 : ℝ)*base89 + (19485953/2500000000000000000000 : ℝ)*base91 + (19485953/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1042_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4181/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (317/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (841/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1042_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1042_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (841/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1042_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1042_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1042_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4117/1024 : ℝ) ≤ p) (hpb : p ≤ (8235/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73763189/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8593/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (841/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1042_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
